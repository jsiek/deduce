"""In-process test runner with multiprocessing.

Mirrors ``test-deduce.py``'s should-validate / should-error sweeps,
but runs every test in a worker pool forked from a parent process
that has already paid the ~2.3s prelude bootstrap. Each worker
inherits the populated ``uniquified_modules`` cache via copy-on-write
fork(), so per-file checks pay only the per-file work.

Cached lib ASTs are parser-agnostic (the cache key is the module
name, and both parsers produce the same AST), so a single bootstrap
serves both ``--recursive-descent`` and ``--lalr`` tasks. The worker
flips the per-process parser flag before each ``check_file`` call.

Usage:
    python tools/test_runner_inproc.py                    # everything
    python tools/test_runner_inproc.py --lib
    python tools/test_runner_inproc.py --passable
    python tools/test_runner_inproc.py --errors
    python tools/test_runner_inproc.py --workers 4        # explicit pool size
    python tools/test_runner_inproc.py --serial           # workers=1

Coverage matches ``test-deduce.py`` default mode (lib + should-validate
+ test/prelude + should-error with .err diff).
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
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

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
        # sandbox-denied sysconf. multiprocessing.Pool still works on
        # macOS in this regime; the check is the only blocker.
        pass


_ppmod._check_system_limits = _patched_check_system_limits

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT))

sys.argv = [str(REPO_ROOT / "deduce.py")] + sys.argv[1:]
sys.setrecursionlimit(10000)

from abstract_syntax import add_import_directory, init_import_directories
from flags import set_quiet_mode, set_recursive_descent
from lsp.library import check_file, reset_prelude_cache


# Keep these as relative paths -- ``deduce.py``'s error messages
# encode the filename as given to the checker, and the ``.err``
# fixtures were captured against relative-path invocations.
LIB_DIR = Path("lib")
PASS_DIR = Path("test/should-validate")
ERROR_DIR = Path("test/should-error")
PRELUDE_DIR = Path("test/prelude")
IMPORTS_DIR = Path("test/test-imports")
EXAMPLE_FILE = Path("example.pf")


# Module-level globals consumed by worker functions. The parent
# populates these before forking the pool; workers inherit them via
# copy-on-write. Avoids pickling a 32-entry tuple per task.
_WORKER_PREWARM: tuple[str, ...] = ()
# Same idea for the prelude-tests pool, which uses ``prelude=`` rather
# than ``prewarm=``. The two cache configurations can't share a
# bootstrap (different cache keys in ``_prepare_state``), so they get
# separate pools.
_WORKER_PRELUDE: tuple[str, ...] = ()


def discover_lib_modules() -> tuple[str, ...]:
    return tuple(sorted(p.stem for p in LIB_DIR.glob("*.pf")))


def setup_paths() -> None:
    # Run from the repo root so the relative paths above resolve and so
    # error messages match the existing ``.err`` fixtures. The import
    # directories must be ``./``-prefixed because ``test-deduce.py``
    # was invoking ``deduce.py --dir ./lib --dir ./test/test-imports``
    # and that prefix ends up in some error messages (the "declared as
    # `lemma` in module X (<file>:<line>)" hint, in particular).
    os.chdir(REPO_ROOT)
    init_import_directories()
    add_import_directory("./" + LIB_DIR.as_posix())
    add_import_directory("./" + IMPORTS_DIR.as_posix())


def list_pf(d: Path) -> list[str]:
    # Return ``./test/<...>/foo.pf``-style paths to match how the
    # ``.err`` fixtures were captured.
    return sorted(f"./{d.as_posix()}/{p.name}" for p in d.iterdir() if p.suffix == ".pf")


# ---------------------------------------------------------------------------
# Worker functions (must be picklable for multiprocessing).
# ---------------------------------------------------------------------------


def _worker_validate(task: tuple[str, bool]) -> tuple[str, bool, str, str]:
    """should-validate worker. ``task`` is (filename, recursive_descent).

    Returns ``(file, ok, parser_label, error_message)``. State
    (``_WORKER_PREWARM``, import dirs, cwd) is inherited from the
    forking parent.
    """
    f, recursive_descent = task
    set_recursive_descent(recursive_descent)
    label = "recursive-descent" if recursive_descent else "lalr"
    result = check_file(f, prewarm_modules=_WORKER_PREWARM)
    return (f, result.ok, label, result.error_message or "")


def _worker_lib(task: tuple[str, bool]) -> tuple[str, bool, str, str]:
    """lib worker. Each lib file is checked with no prewarm so the
    file (and its transitive imports of other lib modules) is freshly
    parsed -- otherwise we'd just typecheck a cached AST that was
    parsed once by the parent and never exercise the LALR parser on
    lib code.
    """
    f, recursive_descent = task
    set_recursive_descent(recursive_descent)
    label = "recursive-descent" if recursive_descent else "lalr"
    result = check_file(f)
    return (f, result.ok, label, result.error_message or "")


def _worker_prelude(task: tuple[str, bool]) -> tuple[str, bool, str, str]:
    """test/prelude worker. Uses ``prelude=`` (injected imports), not
    ``prewarm=``.  ``task`` is (filename, recursive_descent).
    """
    f, recursive_descent = task
    set_recursive_descent(recursive_descent)
    label = "recursive-descent" if recursive_descent else "lalr"
    result = check_file(f, prelude=_WORKER_PRELUDE)
    return (f, result.ok, label, result.error_message or "")


def _worker_error(f: str) -> tuple[str, bool, str]:
    """should-error worker. Returns ``(file, passed, message)``.

    Reproduces the CLI's full stdout (warnings + error_message) and
    diffs against the sibling ``.pf.err`` fixture using ``diff
    --ignore-space-change`` so the matching semantics are identical
    to the existing harness.
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
    """Create a fork-based ProcessPoolExecutor.

    fork() snapshots the parent's address space, so workers inherit
    the post-bootstrap ``uniquified_modules`` cache for free. On
    macOS Python 3.8+, ``spawn`` is the default; we override.
    """
    fork_ctx = mp.get_context("fork")
    return ProcessPoolExecutor(max_workers=workers, mp_context=fork_ctx)


def bootstrap_prewarm(lib_modules: tuple[str, ...]) -> None:
    """Pay the prelude bootstrap once in the parent (prewarm flavour).

    Subsequent ``check_file`` calls (here in the parent, or in any
    child forked off after this returns) hit the cache and skip the
    expensive ``uniquify_deduce`` of every lib module.
    """
    global _WORKER_PREWARM
    _WORKER_PREWARM = lib_modules
    # ``content=""`` runs the pipeline on an empty buffer, which is
    # enough to trip ``_prepare_state`` into building the prewarm
    # snapshot. Cheapest valid trigger.
    set_recursive_descent(True)
    check_file("__warmup__.pf", content="", prewarm_modules=lib_modules)


def bootstrap_prelude(lib_modules: tuple[str, ...]) -> None:
    """Bootstrap with ``prelude=`` (implicit imports) instead of prewarm.

    Workers forked after this will check files with the stdlib
    injected -- this is what ``test/prelude/`` needs to exercise the
    auto-prelude path.
    """
    global _WORKER_PRELUDE
    _WORKER_PRELUDE = lib_modules
    set_recursive_descent(True)
    check_file("__warmup__.pf", content="", prelude=lib_modules)


def run_lib_parallel(workers: int) -> list[tuple[str, str, str]]:
    """Run ``lib/*.pf`` × both parsers with no shared cache.

    Each task starts from a clean post-empty-bootstrap state, so lib
    parsing is exercised per task and per parser -- matching what
    ``python deduce.py --recursive-descent ./lib`` /
    ``python deduce.py --lalr ./lib`` cover.
    """
    files = list_pf(LIB_DIR)
    # Strip the ``./lib/`` prefix and re-add ``./`` so the path matches
    # how ``test_deduce.py`` invokes it (``./lib/Nat.pf``).
    tasks: list[tuple[str, bool]] = []
    for f in files:
        tasks.append((f, True))
        tasks.append((f, False))

    failures: list[tuple[str, str, str]] = []
    if workers <= 1:
        for t in tasks:
            f, ok, label, msg = _worker_lib(t)
            if not ok:
                failures.append((f, label, msg))
        return failures

    with _make_fork_pool(workers) as ex:
        for f, ok, label, msg in ex.map(_worker_lib, tasks, chunksize=2):
            if not ok:
                failures.append((f, label, msg))
    return failures


def run_validate_parallel(workers: int) -> list[tuple[str, str, str]]:
    """Run should-validate × both parsers in parallel.

    Returns a list of ``(file, parser_label, error_message)`` for
    every failure.
    """
    files = list_pf(PASS_DIR) + [f"./{EXAMPLE_FILE.as_posix()}"]
    tasks: list[tuple[str, bool]] = []
    for f in files:
        tasks.append((f, True))   # recursive-descent
        tasks.append((f, False))  # lalr

    failures: list[tuple[str, str, str]] = []
    if workers <= 1:
        for t in tasks:
            f, ok, label, msg = _worker_validate(t)
            if not ok:
                failures.append((f, label, msg))
        return failures

    with _make_fork_pool(workers) as ex:
        for f, ok, label, msg in ex.map(_worker_validate, tasks, chunksize=4):
            if not ok:
                failures.append((f, label, msg))
    return failures


def run_prelude_parallel(workers: int) -> list[tuple[str, str, str]]:
    """Run ``test/prelude/`` × both parsers in a prelude-bootstrapped pool.

    Only 14 files, but each runs against the stdlib-injected
    pipeline, which is ~1.3s/file. With 2 parsers and 12 workers
    that's a 7s phase reduced to ~3s.
    """
    files = list_pf(PRELUDE_DIR)
    tasks: list[tuple[str, bool]] = []
    for f in files:
        tasks.append((f, True))
        tasks.append((f, False))

    failures: list[tuple[str, str, str]] = []
    if workers <= 1:
        for t in tasks:
            f, ok, label, msg = _worker_prelude(t)
            if not ok:
                failures.append((f, label, msg))
        return failures

    with _make_fork_pool(workers) as ex:
        for f, ok, label, msg in ex.map(_worker_prelude, tasks, chunksize=2):
            if not ok:
                failures.append((f, label, msg))
    return failures


def run_errors_parallel(workers: int) -> list[tuple[str, str, str]]:
    """Run should-error in parallel. Recursive-descent parser only."""
    files = list_pf(ERROR_DIR)
    failures: list[tuple[str, str, str]] = []
    if workers <= 1:
        for f in files:
            f, ok, msg = _worker_error(f)
            if not ok:
                failures.append((f, "recursive-descent", msg))
        return failures

    with _make_fork_pool(workers) as ex:
        for f, ok, msg in ex.map(_worker_error, files, chunksize=4):
            if not ok:
                failures.append((f, "recursive-descent", msg))
    return failures


def time_section(label: str, fn) -> tuple[float, list]:
    t0 = time.perf_counter()
    result = fn()
    dt = time.perf_counter() - t0
    print(f"  {label:32s}  {dt:6.2f}s")
    return dt, result


def parse_args(argv: list[str]) -> tuple[bool, bool, bool, int]:
    run_lib = "--lib" in argv
    run_passable = "--passable" in argv
    run_errors = "--errors" in argv
    if not (run_lib or run_passable or run_errors):
        run_lib = run_passable = run_errors = True

    workers = max(1, (os.cpu_count() or 4))
    if "--serial" in argv:
        workers = 1
    for i, a in enumerate(argv):
        if a == "--workers" and i + 1 < len(argv):
            workers = max(1, int(argv[i + 1]))
    return run_lib, run_passable, run_errors, workers


def main(argv: list[str]) -> int:
    run_lib, run_passable, run_errors, workers = parse_args(argv)

    setup_paths()
    lib_modules = discover_lib_modules()
    print(f"Discovered {len(lib_modules)} lib modules; workers={workers}")

    total_failures: list[tuple[str, str, str]] = []
    total_t0 = time.perf_counter()

    # Phase 0: lib tests (clean state, no shared cache -- workers
    # freshly parse each lib file with the requested parser). Run
    # first so the empty-bootstrap state is what workers inherit.
    if run_lib:
        reset_prelude_cache()
        print(f"\n=== lib (both parsers, parallel) ===")
        _, fails = time_section(
            "lib × 2 parsers",
            lambda: run_lib_parallel(workers),
        )
        total_failures.extend(fails)

    # Phase 1: prelude tests (only 14 × 2 parsers, but each needs the
    # stdlib *injected* as imports, which is a different bootstrap from
    # everything else). Get them out of the way before the larger
    # prewarm-bootstrapped pool starts.
    if run_passable:
        reset_prelude_cache()
        t0 = time.perf_counter()
        bootstrap_prelude(lib_modules)
        print(f"\n  {'bootstrap prelude (parent)':32s}  {time.perf_counter() - t0:6.2f}s")
        print(f"=== test/prelude (both parsers, parallel) ===")
        _, fails = time_section(
            "test/prelude × 2 parsers",
            lambda: run_prelude_parallel(workers),
        )
        total_failures.extend(fails)

    # Phase 2: should-validate (both parsers) + should-error (RD only).
    # Both use ``prewarm_modules=lib_modules``, so one bootstrap and
    # one pool serves both. Reset the prelude-mode cache first.
    if run_passable or run_errors:
        reset_prelude_cache()
        t0 = time.perf_counter()
        bootstrap_prewarm(lib_modules)
        print(f"\n  {'bootstrap prewarm (parent)':32s}  {time.perf_counter() - t0:6.2f}s")

    if run_passable:
        print(f"=== should-validate (both parsers, parallel) ===")
        _, fails = time_section(
            "should-validate × 2 parsers",
            lambda: run_validate_parallel(workers),
        )
        total_failures.extend(fails)

    if run_errors:
        print(f"\n=== should-error (recursive-descent, parallel) ===")
        _, fails = time_section(
            "should-error",
            lambda: run_errors_parallel(workers),
        )
        total_failures.extend(fails)

    total_dt = time.perf_counter() - total_t0
    print(f"\nTotal wall time: {total_dt:.2f}s")

    if total_failures:
        print(f"\n{len(total_failures)} FAILURE(s):")
        for fpath, label, msg in total_failures[:20]:
            print(f"  [{label}] {fpath}")
            for line in str(msg).splitlines()[:3]:
                print(f"      {line}")
        if len(total_failures) > 20:
            print(f"  ... and {len(total_failures) - 20} more")
        return 1
    print("\nAll tests passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
