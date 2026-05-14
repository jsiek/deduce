#!/usr/bin/env python3
"""Deduce test harness.

Replaces the older subprocess-per-file harness with an in-process
multiprocessing runner. The parent pays the ~2.3s prelude bootstrap
once; workers fork from the populated ``uniquified_modules`` cache
via copy-on-write and run ``lsp.library.check_file`` directly.

Modes
-----
Default (no flags): runs ``--cli + --lib + --passable + --errors``.

Per-category flags (combinable):
    --cli          One subprocess invocation of ``deduce.py example.pf``
                   to sanity-check the CLI entry point itself.
    --lib          ``lib/`` with both parsers, no shared cache.
    --passable     ``test/should-validate``, ``example.pf``,
                   ``test/prelude`` with both parsers.
    --errors       ``test/should-error`` (RD only, ``.err`` diff).
    --equiv        Parse ``lib/`` and ``test/should-validate/`` with both
                   parsers and compare structural ASTs. Known historical
                   divergences are allowlisted so CI catches new drift.

Standalone modes (mutually exclusive with the above):
    --site             Generate ``doc_*.pf`` from ``gh_pages/doc/``
                       and check them with both parsers.
    --parser           ``test/parse`` parser-error fixtures (RD only).
                       These stay RD-only because RD diagnostics are the
                       user-facing diagnostics; LALR is checked for accepted
                       syntax and AST shape by ``--equiv`` instead.
    --regenerate-errors      Regenerate every ``test/should-error/*.err``.
    --generate-error <path>  Regenerate one ``.err`` fixture.
    --gen-parse              Regenerate every ``test/parse/*.err``.

Pool sizing:
    --workers N         Worker count (default ``os.cpu_count()``).
    --max-threads N     Alias for ``--workers`` (legacy).
    --serial            Equivalent to ``--workers 1``.
"""

from __future__ import annotations

import contextlib
import io
import multiprocessing as mp
import os
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ProcessPoolExecutor
from dataclasses import fields as dc_fields, is_dataclass
from pathlib import Path
from signal import signal, SIGINT
from lark import Token

# Work around macOS sandbox profiles (notably Claude Code's seatbelt
# sandbox) that deny ``sysconf(_SC_SEM_NSEMS_MAX)``. Python's
# ``concurrent.futures.process._check_system_limits`` calls that
# sysconf to verify enough POSIX semaphores are available; it catches
# ``AttributeError``/``ValueError`` but lets ``PermissionError``
# propagate, which would crash the pool before any worker spawns.
# The check is purely advisory -- if the sysconf is denied we wrap it
# and treat the limit as undetermined (matching the existing -1 path).
import concurrent.futures.process as _ppmod

_orig_check_system_limits = _ppmod._check_system_limits


def _patched_check_system_limits() -> None:
    try:
        _orig_check_system_limits()
    except PermissionError:
        pass


_ppmod._check_system_limits = _patched_check_system_limits


REPO_ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(REPO_ROOT))
sys.setrecursionlimit(10000)

# ``lsp.library`` derives the location of ``Deduce.lark`` from
# ``os.path.dirname(sys.argv[0])``. When this script is invoked as
# ``python test-deduce.py`` from the repo root that's an empty string,
# which produces ``/Deduce.lark`` -- a non-existent absolute path.
# Spoof argv[0] to a real ``deduce.py`` path so the lookup works
# regardless of how the script was invoked.
sys.argv = [str(REPO_ROOT / "deduce.py")] + sys.argv[1:]

from abstract_syntax import add_import_directory, init_import_directories
from flags import set_quiet_mode, set_recursive_descent
from lsp.library import check_file, reset_prelude_cache
import parser as _equiv_lark_parser
import rec_desc_parser as _equiv_rd_parser


# Keep these as relative paths -- ``deduce.py``'s error messages
# encode the filename as given to the checker, and the ``.err``
# fixtures were captured against relative-path invocations.
LIB_DIR = Path("lib")
PASS_DIR = Path("test/should-validate")
ERROR_DIR = Path("test/should-error")
PRELUDE_DIR = Path("test/prelude")
IMPORTS_DIR = Path("test/test-imports")
PARSE_DIR = Path("test/parse")
EXAMPLE_FILE = Path("example.pf")


# Current parser-equivalence baseline. These files parse successfully with
# both parsers but produce structurally different ASTs today. Keeping the
# baseline explicit makes any new drift fail CI, and also fails when a listed
# file becomes equivalent so the list gets smaller over time.
PARSER_EQUIV_EXPECTED_DIVERGENCES = frozenset({
    "./lib/List.pf",
    "./lib/MultiSet.pf",
    "./lib/Set.pf",
    "./test/should-validate/all-elim-types-tlet.pf",
    "./test/should-validate/bicond2.pf",
    "./test/should-validate/expand-repeat.pf",
    "./test/should-validate/inst3.pf",
    "./test/should-validate/map_append_cross_type.pf",
})


# Module-level globals consumed by worker functions. The parent
# populates these before forking the pool; workers inherit them via
# copy-on-write. Avoids pickling a 32-entry tuple per task.
_WORKER_PREWARM: tuple[str, ...] = ()
_WORKER_PRELUDE: tuple[str, ...] = ()


def handle_sigint(signum, frame):
    print('SIGINT caught, exiting...')
    sys.exit(137)


def discover_lib_modules() -> tuple[str, ...]:
    return tuple(sorted(p.stem for p in LIB_DIR.glob("*.pf")))


def setup_paths() -> None:
    # Run from the repo root so the relative paths above resolve and so
    # error messages match the existing ``.err`` fixtures. The import
    # directories must be ``./``-prefixed because the legacy harness
    # invoked ``deduce.py --dir ./lib --dir ./test/test-imports`` and
    # that prefix ends up in some error messages (the "declared as
    # `lemma` in module X (<file>:<line>)" hint, in particular).
    os.chdir(REPO_ROOT)
    init_import_directories()
    add_import_directory("./" + LIB_DIR.as_posix())
    add_import_directory("./" + IMPORTS_DIR.as_posix())


def list_pf(d: Path) -> list[str]:
    # Return ``./test/<...>/foo.pf``-style paths to match how the
    # ``.err`` fixtures were captured.
    return sorted(
        f"./{d.as_posix()}/{p.name}" for p in d.iterdir() if p.suffix == ".pf"
    )


# ---------------------------------------------------------------------------
# Worker functions (must be picklable for multiprocessing).
# ---------------------------------------------------------------------------


def _worker_validate(task: tuple[str, bool]) -> tuple[str, bool, str, str]:
    f, recursive_descent = task
    set_recursive_descent(recursive_descent)
    label = "recursive-descent" if recursive_descent else "lalr"
    result = check_file(f, prewarm_modules=_WORKER_PREWARM)
    return (f, result.ok, label, result.error_message or "")


def _worker_lib(task: tuple[str, bool]) -> tuple[str, bool, str, str]:
    """Each lib file is checked with no prewarm so the file (and its
    transitive imports of other lib modules) is freshly parsed --
    otherwise we'd just typecheck a cached AST that was parsed once by
    the parent and never exercise the LALR parser on lib code.
    """
    f, recursive_descent = task
    set_recursive_descent(recursive_descent)
    label = "recursive-descent" if recursive_descent else "lalr"
    result = check_file(f)
    return (f, result.ok, label, result.error_message or "")


def _worker_prelude(task: tuple[str, bool]) -> tuple[str, bool, str, str]:
    """``test/prelude`` worker. Uses ``prelude=`` (injected imports),
    not ``prewarm=``."""
    f, recursive_descent = task
    set_recursive_descent(recursive_descent)
    label = "recursive-descent" if recursive_descent else "lalr"
    result = check_file(f, prelude=_WORKER_PRELUDE)
    return (f, result.ok, label, result.error_message or "")


def _check_against_err(f: str) -> tuple[str, bool, str]:
    """Run ``f`` and diff its captured stdout against ``f + '.err'``.

    Shared between ``--errors`` (``test/should-error``) and
    ``--parser`` (``test/parse``); both use the same fixture format.
    Reproduces the CLI's full stdout (warnings + ``error_message``)
    and runs ``diff --ignore-space-change`` to match the historical
    matching semantics exactly.
    """
    err_file = f + ".err"
    if not os.path.isfile(err_file):
        return (f, False, "missing .pf.err fixture")
    set_recursive_descent(True)
    set_quiet_mode(True)
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        result = check_file(f, prewarm_modules=_WORKER_PREWARM)
        if not result.ok:
            print(result.error_message)
    if result.ok:
        return (f, False, "expected error but file was valid")
    actual = buf.getvalue()
    with tempfile.NamedTemporaryFile(
        "w", suffix=".tmp", delete=False, encoding="utf-8"
    ) as tf:
        tf.write(actual)
        tmp_path = tf.name
    try:
        cp = subprocess.run(
            ["diff", "--ignore-space-change", err_file, tmp_path],
            capture_output=True, text=True,
        )
        if cp.returncode != 0:
            return (f, False, f"error message diverged:\n{cp.stdout[:500]}")
        return (f, True, "")
    finally:
        os.unlink(tmp_path)


# ---------------------------------------------------------------------------
# Orchestration.
# ---------------------------------------------------------------------------


def _make_fork_pool(workers: int):
    """Fork-based ``ProcessPoolExecutor``: children inherit the
    parent's populated AST cache via copy-on-write. macOS Python
    defaults to ``spawn``; we override.
    """
    fork_ctx = mp.get_context("fork")
    return ProcessPoolExecutor(max_workers=workers, mp_context=fork_ctx)


def bootstrap_prewarm(lib_modules: tuple[str, ...]) -> None:
    """Pay the prelude bootstrap once in the parent (prewarm flavour)."""
    global _WORKER_PREWARM
    _WORKER_PREWARM = lib_modules
    set_recursive_descent(True)
    # ``content=""`` runs the pipeline on an empty buffer -- cheapest
    # valid trigger for ``_prepare_state``'s bootstrap path.
    check_file("__warmup__.pf", content="", prewarm_modules=lib_modules)


def bootstrap_prelude(lib_modules: tuple[str, ...]) -> None:
    """Bootstrap with ``prelude=`` (implicit imports) for prelude tests."""
    global _WORKER_PRELUDE
    _WORKER_PRELUDE = lib_modules
    set_recursive_descent(True)
    check_file("__warmup__.pf", content="", prelude=lib_modules)


def _map_or_serial(workers: int, fn, tasks, chunksize: int = 4):
    """Run ``fn(task)`` over ``tasks`` in a pool, or in-line when
    ``workers <= 1`` (handy for debugging and the ``--serial`` flag)."""
    if workers <= 1:
        return [fn(t) for t in tasks]
    with _make_fork_pool(workers) as ex:
        return list(ex.map(fn, tasks, chunksize=chunksize))


def run_lib_parallel(workers: int) -> list[tuple[str, str, str]]:
    """``lib/*.pf`` × both parsers with no shared cache."""
    files = list_pf(LIB_DIR)
    tasks = [(f, p) for f in files for p in (True, False)]
    failures: list[tuple[str, str, str]] = []
    for f, ok, label, msg in _map_or_serial(workers, _worker_lib, tasks, 2):
        if not ok:
            failures.append((f, label, msg))
    return failures


def run_validate_parallel(workers: int) -> list[tuple[str, str, str]]:
    """``test/should-validate`` + ``example.pf`` × both parsers."""
    files = list_pf(PASS_DIR) + [f"./{EXAMPLE_FILE.as_posix()}"]
    tasks = [(f, p) for f in files for p in (True, False)]
    failures: list[tuple[str, str, str]] = []
    for f, ok, label, msg in _map_or_serial(workers, _worker_validate, tasks, 4):
        if not ok:
            failures.append((f, label, msg))
    return failures


def run_prelude_parallel(workers: int) -> list[tuple[str, str, str]]:
    """``test/prelude`` × both parsers (uses ``prelude=`` bootstrap)."""
    files = list_pf(PRELUDE_DIR)
    tasks = [(f, p) for f in files for p in (True, False)]
    failures: list[tuple[str, str, str]] = []
    for f, ok, label, msg in _map_or_serial(workers, _worker_prelude, tasks, 2):
        if not ok:
            failures.append((f, label, msg))
    return failures


def run_err_diff_parallel(directory: Path, label: str,
                          workers: int) -> list[tuple[str, str, str]]:
    """Run ``.err``-fixture tests in ``directory`` (RD only)."""
    files = list_pf(directory)
    failures: list[tuple[str, str, str]] = []
    for f, ok, msg in _map_or_serial(workers, _check_against_err, files, 4):
        if not ok:
            failures.append((f, label, msg))
    return failures


def _canonical_ast(value, *, parent_class: str | None = None,
                   field_name: str | None = None):
    """Canonical structural form for comparing parser ASTs.

    Source locations are intentionally ignored. Lark ``Token`` values are
    converted to plain strings because the RD parser usually emits strings for
    the same identifier/operator leaves. The RD parser also preserves the
    historical ``default`` visibility sentinel; normalize it to the LALR
    parser's concrete visibility for this comparison.
    """
    if isinstance(value, Token):
        return str(value)
    if field_name == "visibility" and value == "default":
        value = "private" if parent_class == "Import" else "public"
    if is_dataclass(value):
        cls_name = type(value).__name__
        return (
            cls_name,
            tuple(
                (fld.name, _canonical_ast(
                    getattr(value, fld.name),
                    parent_class=cls_name,
                    field_name=fld.name,
                ))
                for fld in dc_fields(value)
                if fld.name != "location"
            ),
        )
    if isinstance(value, list):
        return [_canonical_ast(v) for v in value]
    if isinstance(value, tuple):
        return tuple(_canonical_ast(v) for v in value)
    return value


def _parse_for_equivalence(path: str, *, recursive_descent: bool):
    parser_mod = _equiv_rd_parser if recursive_descent else _equiv_lark_parser
    parser_mod.set_deduce_directory(str(REPO_ROOT))
    parser_mod.set_filename(path)
    parser_mod.init_parser()
    with open(path, encoding="utf-8") as f:
        return parser_mod.parse(f.read())


def run_parser_equivalence() -> list[tuple[str, str, str]]:
    """Compare RD and LALR ASTs for accepted syntax.

    This covers ``lib/`` and ``test/should-validate/``. ``test/parse`` remains
    RD-only because those fixtures intentionally lock down beginner-facing RD
    diagnostics, while the LALR parser is kept as an executable grammar spec.
    """
    # ``--site`` generates ``doc_*.pf`` files into ``test/should-validate``.
    # They are already validated with both parsers by the site mode itself;
    # keep this drift baseline focused on checked-in should-validate files.
    pass_files = [
        f for f in list_pf(PASS_DIR)
        if not Path(f).name.startswith("doc_")
    ]
    files = list_pf(LIB_DIR) + pass_files
    failures: list[tuple[str, str, str]] = []
    seen_divergences: set[str] = set()
    for path in files:
        try:
            rd_ast = _canonical_ast(
                _parse_for_equivalence(path, recursive_descent=True)
            )
            lalr_ast = _canonical_ast(
                _parse_for_equivalence(path, recursive_descent=False)
            )
        except Exception as exc:
            failures.append((path, "parser-equivalence",
                             f"{type(exc).__name__}: {exc}"))
            continue

        if rd_ast == lalr_ast:
            if path in PARSER_EQUIV_EXPECTED_DIVERGENCES:
                failures.append((path, "parser-equivalence",
                                 "listed as a divergence but now matches"))
            continue

        if path in PARSER_EQUIV_EXPECTED_DIVERGENCES:
            seen_divergences.add(path)
        else:
            failures.append((path, "parser-equivalence",
                             "RD and LALR ASTs differ"))

    stale = PARSER_EQUIV_EXPECTED_DIVERGENCES - seen_divergences - {
        f for f in files if f in PARSER_EQUIV_EXPECTED_DIVERGENCES
    }
    for path in sorted(stale):
        failures.append((path, "parser-equivalence",
                         "expected divergence path no longer exists"))
    return failures


def run_cli_test() -> list[tuple[str, str, str]]:
    """Sanity-check that ``python deduce.py example.pf`` works end-to-end.

    The in-process runner exercises ``lsp.library.check_file``; this
    one subprocess invocation makes sure the ``deduce.py`` CLI wrapper
    itself (arg parsing, ``init_import_directories``,
    ``print_theorems``, exit codes) hasn't drifted. One file is
    enough -- we're not re-checking ``example.pf``'s contents (the
    in-process sweep already does that), we're testing the CLI shape.
    """
    cp = subprocess.run(
        [sys.executable, "deduce.py", "./example.pf"],
        capture_output=True, text=True,
    )
    failures: list[tuple[str, str, str]] = []
    if cp.returncode != 0:
        failures.append((
            "./example.pf", "cli",
            f"exit {cp.returncode}\nstderr: {cp.stderr[:500]}\n"
            f"stdout: {cp.stdout[:500]}",
        ))
    elif "example.pf is valid" not in cp.stdout:
        failures.append((
            "./example.pf", "cli",
            f"unexpected stdout:\n{cp.stdout[:500]}",
        ))
    return failures


def run_site(workers: int) -> list[tuple[str, str, str]]:
    """Generate ``doc_*.pf`` from ``gh_pages/doc/`` and check them."""
    from gh_pages.scripts.convert import convert_dir
    convert_dir("./gh_pages/doc/", False)
    files: list[str] = []
    for name in sorted(os.listdir(PASS_DIR)):
        if name.startswith("doc_") and name.endswith(".pf"):
            files.append(f"./{PASS_DIR.as_posix()}/{name}")
    tasks = [(f, p) for f in files for p in (True, False)]
    failures: list[tuple[str, str, str]] = []
    for f, ok, label, msg in _map_or_serial(workers, _worker_validate, tasks, 2):
        if not ok:
            failures.append((f, label, msg))
    return failures


# ---------------------------------------------------------------------------
# Regeneration of .err fixtures.
# ---------------------------------------------------------------------------


def _capture_err_output(path: str) -> str:
    """Run ``check_file`` on ``path`` and return the captured stdout.

    Mirrors what ``deduce.py`` would have printed on a failing run:
    interleaved warnings emitted via ``print()`` followed by the
    final ``result.error_message`` line.
    """
    set_recursive_descent(True)
    set_quiet_mode(True)
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        result = check_file(path, prewarm_modules=_WORKER_PREWARM)
        if not result.ok:
            print(result.error_message)
    return buf.getvalue()


def regenerate_one(path: str) -> None:
    out = _capture_err_output(path)
    with open(path + ".err", "w", encoding="utf-8") as f:
        f.write(out)
    print(f"  wrote {path}.err")


def regenerate_dir(directory: Path) -> None:
    for f in list_pf(directory):
        regenerate_one(f)


# ---------------------------------------------------------------------------
# CLI.
# ---------------------------------------------------------------------------


def time_section(label: str, fn) -> tuple[float, list]:
    t0 = time.perf_counter()
    result = fn()
    dt = time.perf_counter() - t0
    print(f"  {label:32s}  {dt:6.2f}s")
    return dt, result


def parse_args(argv: list[str]) -> dict:
    """Return a dict of flag → value. Tolerates the legacy long-form
    arguments still in scripts / muscle memory."""
    flags = {
        "cli": False, "lib": False, "passable": False, "errors": False,
        "equiv": False, "site": False, "parser": False,
        "regen_all": False, "regen_files": [], "gen_parse": False,
        "workers": max(1, (os.cpu_count() or 4)),
    }
    standalone = {"site", "parser", "regen_all", "regen_files", "gen_parse"}
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == "--cli": flags["cli"] = True
        elif a == "--lib": flags["lib"] = True
        elif a == "--passable": flags["passable"] = True
        elif a == "--errors": flags["errors"] = True
        elif a == "--equiv": flags["equiv"] = True
        elif a == "--site": flags["site"] = True
        elif a == "--parser": flags["parser"] = True
        elif a == "--regenerate-errors": flags["regen_all"] = True
        elif a == "--generate-error":
            flags["regen_files"].append(argv[i + 1])
            i += 1
        elif a == "--gen-parse": flags["gen_parse"] = True
        elif a == "--serial": flags["workers"] = 1
        elif a in ("--workers", "--max-threads"):
            flags["workers"] = max(1, int(argv[i + 1]))
            i += 1
        else:
            print(f"unknown argument: {a}", file=sys.stderr)
            sys.exit(2)
        i += 1

    # If no flags at all, default to the per-PR regression sweep.
    if not any(flags[k] for k in
               ("cli", "lib", "passable", "errors", "site", "parser",
                "equiv", "regen_all", "gen_parse")) and not flags["regen_files"]:
        flags["cli"] = flags["lib"] = flags["passable"] = True
        flags["errors"] = flags["equiv"] = True

    # Standalone modes are mutually exclusive with everything else.
    if any(flags[k] or flags["regen_files"] for k in standalone):
        category_flags = ("cli", "lib", "passable", "errors", "equiv")
        active_categories = [k for k in category_flags if flags[k]]
        active_standalone = [k for k in standalone if flags[k] or
                             (k == "regen_files" and flags["regen_files"])]
        if active_categories and active_standalone:
            print(
                f"--{active_standalone[0]} is standalone; cannot combine with "
                f"--{active_categories[0]}", file=sys.stderr,
            )
            sys.exit(2)
        if len(active_standalone) > 1:
            print(
                f"these flags are mutually exclusive: "
                f"{', '.join('--' + s for s in active_standalone)}",
                file=sys.stderr,
            )
            sys.exit(2)

    return flags


def main(argv: list[str]) -> int:
    flags = parse_args(argv)
    setup_paths()
    lib_modules = discover_lib_modules()
    workers = flags["workers"]

    total_failures: list[tuple[str, str, str]] = []
    total_t0 = time.perf_counter()

    # Standalone: regen / site / parser. Each owns the run.
    if flags["regen_all"]:
        print(f"Regenerating ALL errors in {ERROR_DIR}")
        bootstrap_prewarm(lib_modules)
        regenerate_dir(ERROR_DIR)
        return 0
    if flags["regen_files"]:
        bootstrap_prewarm(lib_modules)
        for path in flags["regen_files"]:
            print(f"Generating error for: {path}")
            regenerate_one(path)
        return 0
    if flags["gen_parse"]:
        print(f"Regenerating ALL parser errors in {PARSE_DIR}")
        bootstrap_prewarm(lib_modules)
        regenerate_dir(PARSE_DIR)
        return 0
    if flags["site"]:
        print("=== --site: generate doc_*.pf and check (parallel) ===")
        bootstrap_prewarm(lib_modules)
        _, fails = time_section("site doc files × 2 parsers",
                                lambda: run_site(workers))
        total_failures.extend(fails)
        return _report(total_failures, total_t0)
    if flags["parser"]:
        print(f"=== --parser: {PARSE_DIR} (RD only, parallel) ===")
        bootstrap_prewarm(lib_modules)
        _, fails = time_section("test/parse",
                                lambda: run_err_diff_parallel(
                                    PARSE_DIR, "parser", workers))
        total_failures.extend(fails)
        return _report(total_failures, total_t0)

    # Combinable per-category sweep.
    print(f"Discovered {len(lib_modules)} lib modules; workers={workers}")

    if flags["cli"]:
        print("\n=== --cli: deduce.py CLI sanity check ===")
        _, fails = time_section("deduce.py ./example.pf", run_cli_test)
        total_failures.extend(fails)

    # Lib pool: clean state (no shared cache).
    if flags["lib"]:
        reset_prelude_cache()
        print("\n=== lib (both parsers, parallel) ===")
        _, fails = time_section("lib × 2 parsers",
                                lambda: run_lib_parallel(workers))
        total_failures.extend(fails)

    # Prelude pool: prelude-injection bootstrap.
    if flags["passable"]:
        reset_prelude_cache()
        t0 = time.perf_counter()
        bootstrap_prelude(lib_modules)
        print(f"\n  {'bootstrap prelude (parent)':32s}  "
              f"{time.perf_counter() - t0:6.2f}s")
        print("=== test/prelude (both parsers, parallel) ===")
        _, fails = time_section("test/prelude × 2 parsers",
                                lambda: run_prelude_parallel(workers))
        total_failures.extend(fails)

    # Combined pool: should-validate + should-error share a prewarm bootstrap.
    if flags["passable"] or flags["errors"]:
        reset_prelude_cache()
        t0 = time.perf_counter()
        bootstrap_prewarm(lib_modules)
        print(f"\n  {'bootstrap prewarm (parent)':32s}  "
              f"{time.perf_counter() - t0:6.2f}s")

    if flags["passable"]:
        print("=== should-validate (both parsers, parallel) ===")
        _, fails = time_section("should-validate × 2 parsers",
                                lambda: run_validate_parallel(workers))
        total_failures.extend(fails)

    if flags["errors"]:
        print("\n=== should-error (RD only, parallel) ===")
        _, fails = time_section("should-error",
                                lambda: run_err_diff_parallel(
                                    ERROR_DIR, "recursive-descent", workers))
        total_failures.extend(fails)

    if flags["equiv"]:
        print("\n=== parser equivalence (RD vs LALR ASTs) ===")
        _, fails = time_section("lib + should-validate",
                                run_parser_equivalence)
        total_failures.extend(fails)

    return _report(total_failures, total_t0)


def _report(failures: list[tuple[str, str, str]], t0: float) -> int:
    print(f"\nTotal wall time: {time.perf_counter() - t0:.2f}s")
    if failures:
        print(f"\n{len(failures)} FAILURE(s):")
        for fpath, label, msg in failures[:20]:
            print(f"  [{label}] {fpath}")
            for line in str(msg).splitlines()[:3]:
                print(f"      {line}")
        if len(failures) > 20:
            print(f"  ... and {len(failures) - 20} more")
        return 1
    print("\nAll tests passed.")
    return 0


if __name__ == "__main__":
    signal(SIGINT, handle_sigint)
    sys.exit(main(sys.argv[1:]))
