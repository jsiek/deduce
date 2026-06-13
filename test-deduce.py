#!/usr/bin/env python3
"""Deduce test harness.

Replaces the older subprocess-per-file harness with an in-process
multiprocessing runner. The parent pays the ~2.3s prelude bootstrap
once; workers fork from the populated ``uniquified_modules`` cache
via copy-on-write and run ``lsp.library.check_file`` directly.

Modes
-----
Default (no flags): runs ``--cli + --lib + --passable + --errors +
--warns + --equiv``.

Per-category flags (combinable):
    --cli          One subprocess invocation of ``deduce.py`` on a tiny
                   no-stdlib proof to sanity-check the CLI entry point
                   itself.
    --lib          ``lib/`` with both parsers, no shared cache.
    --passable     ``test/should-validate``, ``example.pf``,
                   ``test/prelude`` with both parsers.
    --errors       ``test/should-error`` (RD only, ``.err`` diff).
    --warns        ``test/should-warn`` (RD only, ``.warn`` diff): files
                   that must validate AND emit specific warning text.
    --equiv        Parse ``lib/``, ``test/should-validate/``, and most of
                   ``test/should-error/`` with both parsers and compare
                   structural ASTs. Known historical divergences and
                   parser-error fixtures are allowlisted so CI catches new
                   drift. Also round-trip representative ASTs through the
                   pretty-printer and both parsers.

Standalone modes (mutually exclusive with the above):
    --site             Generate ``doc_*.pf`` from ``gh_pages/doc/``
                       and check them with both parsers.
    --parser           ``test/parse`` parser-error fixtures (RD only).
                       These stay RD-only because RD diagnostics are the
                       user-facing diagnostics; LALR is checked for accepted
                       syntax and AST shape by ``--equiv`` instead.
    --examples         ``examples/`` worked-example proofs (RD only).
                       LALR/RD parity is already covered by ``--equiv`` for
                       ``lib/`` + ``should-validate/``; here we just need to
                       catch regressions in the examples themselves.
    --regenerate-errors      Regenerate every ``test/should-error/*.err``.
    --generate-error <path>  Regenerate one ``.err`` fixture.
    --regenerate-warns       Regenerate every ``test/should-warn/*.warn``.
    --generate-warn <path>   Regenerate one ``.warn`` fixture.
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
from typing import Callable, Iterable, TypeVar, TypedDict, cast
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
WARN_DIR = Path("test/should-warn")
PRELUDE_DIR = Path("test/prelude")
IMPORTS_DIR = Path("test/test-imports")
PARSE_DIR = Path("test/parse")
EXAMPLES_DIR = Path("examples")
EXAMPLE_FILE = Path("example.pf")


# Current parser-equivalence baseline. These files parse successfully with
# both parsers but produce structurally different ASTs today. Keeping the
# baseline explicit makes any new drift fail CI, and also fails when a listed
# file becomes equivalent so the list gets smaller over time.
PARSER_EQUIV_EXPECTED_DIVERGENCES: frozenset[str] = frozenset()


# Most ``test/should-error`` files fail in later phases (type-check,
# proof-check) and parse cleanly under both parsers; comparing their ASTs
# gives us 180+ extra surface-syntax samples for drift detection. The files
# below are excluded because at least one parser rejects them at parse time
# today -- either as an intentional parser-error fixture or because the two
# parsers diverge on a tolerated form (e.g. RD currently accepts ``conclude
# ... by`` with a hole where LALR does not). If a listed file ever starts to
# parse cleanly with both parsers, the staleness check downgrades it to a
# failure so the baseline shrinks over time.
SHOULD_ERROR_PARSER_EQUIV_SKIP = frozenset({
    "./test/should-error/all5.pf",
    "./test/should-error/apply_to_error.pf",
    "./test/should-error/cases_error.pf",
    "./test/should-error/conjunct.pf",
    "./test/should-error/deep_error.pf",
    "./test/should-error/define_missing_semi.pf",
    "./test/should-error/define_proof_missing_term.pf",
    "./test/should-error/define_type.pf",
    "./test/should-error/define_with_type_params.pf",
    "./test/should-error/double_private.pf",
    "./test/should-error/fn_missing_arrow.pf",
    "./test/should-error/function_case_missing_equal.pf",
    "./test/should-error/missing-colon-in-have.pf",
    "./test/should-error/paren_term.pf",
    "./test/should-error/private_opaque.pf",
    "./test/should-error/suffices_misspell.pf",
    "./test/should-error/switch_case_close.pf",
    "./test/should-error/switch_case_empty.pf",
    "./test/should-error/switch_case_open.pf",
    "./test/should-error/switch_case_pattern.pf",
    "./test/should-error/theorem_implies8.pf",
    "./test/should-error/theorem_misspelled.pf",
    "./test/should-error/unclosed_comment.pf",
    "./test/should-error/union_bad_constructor.pf",
    "./test/should-error/union_missing_name.pf",
})


# Pretty-printer/parser round-trip coverage for accepted syntax. Keep this
# curated until the existing pretty-printer is parse-preserving for the whole
# corpus; broad parser equivalence above still covers every checked-in lib and
# should-validate file.
PARSER_ROUND_TRIP_FILES = (
    "./test/should-validate/theorem_true.pf",
    "./test/should-validate/function1.pf",
    "./test/should-validate/generic-fun.pf",
    "./test/should-validate/bintree.pf",
    "./test/should-validate/uint_viewrec.pf",
    "./lib/Option.pf",
    # Broaden coverage to additional small files that already
    # round-trip cleanly under today's pretty-printer. Each one
    # exercises a distinct surface construct so a regression in
    # any of these forms is caught here too.
    "./test/should-validate/empty_file.pf",        # empty input
    "./test/should-validate/bicond1.pf",           # biconditional <=>
    "./test/should-validate/conditional1.pf",      # if-then-else term
    "./test/should-validate/array1.pf",            # array literal + indexing
    "./test/should-validate/some1.pf",             # existential + `choose`
    "./test/should-validate/inst1.pf",             # all-elim by application
    "./test/should-validate/switch_term.pf",       # switch in a term position
    "./test/should-validate/predicate_basic.pf",   # `predicate` declaration
    "./test/should-validate/relation_basic.pf",    # `relation` declaration
    "./test/should-validate/opaque_define.pf",     # `opaque` visibility
    "./test/should-validate/import_using.pf",      # `import ... using ...`
    "./test/should-validate/auto_conditional.pf",  # `auto` + `postulate` decl
    "./test/should-validate/recall1.pf",           # `recall` proof
    "./test/should-validate/simplify1.pf",         # `simplify` proof
    "./test/should-validate/trace_recursive.pf",   # `trace` decl + `print`
    "./test/should-validate/union_positive_nested.pf",  # nested generic union
    "./test/should-validate/mark2.pf",             # `#`-mark term + `expand a | b`
    "./test/should-validate/nat_literals.pf",      # `ℕn` Nat literals + `lit`
    "./test/should-validate/fun_zero_param.pf",    # zero-parameter `fun`
    "./test/should-validate/some-intro-tlet.pf",   # `define ... ; ...` term-let
    "./test/should-validate/int1.pf",              # Int negation / literals
    "./test/should-validate/theorem_let.pf",       # inline `apply ... to ...`
    # Coverage added with the issue #931 round of pretty-printer fixes.
    # Each one exercises a fix landed in that pass:
    "./test/should-validate/all1.pf",              # `arbitrary x:T` (no `;`)
    "./test/should-validate/all2.pf",              # multi-`arbitrary` list
    "./test/should-validate/all3.pf",              # arbitrary + apply chain
    "./test/should-validate/bicond3.pf",           # `switch ... case … assume`
    "./test/should-validate/bicond4.pf",           # nested case-assume
    "./test/should-validate/not_equal.pf",         # `x /= y` surface form
    "./test/should-validate/private_define.pf",    # `private define : T = …`
    "./test/should-validate/private_function.pf",  # `private fun …`
    "./test/should-validate/private_union.pf",     # `private union` + `/=`
    "./test/should-validate/simplify3.pf",         # `simplify with q.`
    "./test/should-validate/simplify4.pf",         # `simplify with` + body
    "./test/should-validate/TestUIntDiv.pf",       # numeric literal sugar
    "./test/should-validate/rewrite_with_all.pf",  # `replace x.` finishing form
    "./test/should-validate/type_alias.pf",        # `type Foo = Bar` round-trip
    "./test/should-validate/predicate_opaque.pf",  # `opaque predicate`
    # Coverage added with the follow-up pretty-printer round (#931 again):
    # `suffices ... by { ... }` block, `cases <subject> case ... { ... }`,
    # and `induction T case <pat> { ... }` (no induction-hypothesis clause).
    "./test/should-validate/suffices1.pf",         # `suffices ... by ...`
    "./test/should-validate/suffices_def.pf",      # `suffices` with `define`
    "./test/should-validate/suffices_omitted.pf",  # `suffices ... by` then proof
    "./test/should-validate/suffices_rewrite.pf",  # `suffices ... by replace ...`
    "./test/should-validate/cases-tlet.pf",        # `cases prem` with `case <l>: <t>`
    "./test/should-validate/induction-tlet.pf",    # `induction T case A { . }`
    "./test/should-validate/induction_auto_assume.pf",  # induction + suffices body
    "./test/should-validate/private_roundtrip.pf", # `private type` + `private fun`
    # `private theorem` / `private lemma` / `private postulate` visibility
    # round-trip (Theorem.__str__ / Postulate.__str__ visibility prefix).
    "./test/should-validate/private_theorem.pf",
    # `recfun ... measure n of T { body } terminates { proof }` — both
    # the `of <measure_ty>` clause and the `terminates` proof block were
    # silently dropped by `GenRecFun.pretty_print`; covers both shapes.
    "./test/should-validate/recfun_roundtrip.pf",
    # Coverage added with the issue #945 fix for `mkEqual` emitting
    # `Var('=')` from the parser (so `equations`-block `=` matches the
    # ordinary infix-`=` parsing shape):
    "./test/should-validate/assoc1.pf",            # `equations` + `replace`
    "./test/should-validate/assoc2.pf",            # `equations` chain
    "./test/should-validate/induction1.pf",        # `equations` under induction
    "./test/should-validate/postulate1.pf",        # `equations` + `postulate`
    "./test/should-validate/mark3.pf",             # `equations` + `#`-marks
    "./test/should-validate/ListTests.pf",         # operator-call rator: `(f ∘ g)(x)`
    "./test/should-validate/function_type_paren.pf",  # multi-arg `fn` types
    "./test/should-validate/relation_operator_name.pf",  # `relation operator <op>`
    # `Omitted.__str__` previously returned `--`, which neither parser
    # accepts; the surface form is `__` (or `─`). Covers `suffices __ by …`.
    "./test/should-validate/suffices_implies_omitted.pf",
    # RD parser now chains `(...)` and `[...]` postfix in any order
    # (matching LALR), so `array(l)[0]` and `f(a)[0]` re-parse the
    # same way the pretty-printer emits them.
    "./test/should-validate/array4.pf",            # `array(...)` + `[i]`
    "./test/should-validate/array5.pf",            # nested `(array(...))[i]`
    "./test/should-validate/postfix_chain_roundtrip.pf",  # synthetic chain
    # `opaque define name : T = body` — `Define.pretty_print` used to
    # short-circuit to header-only when `visibility == 'opaque'`, dropping
    # the `= body`. Covers both an annotated `opaque define : T = fun ...`
    # and the visibility coexisting with the broader Define pretty-print.
    "./test/should-validate/ImportTests.pf",
    # `op_arg_str` now parenthesizes `TAnnote` args of operator Calls --
    # `:` binds looser than every operator, so the printed
    # `subject:type ^ ...` previously reparsed as `subject : (type ^ ...)`
    # and the leftover operator tripped the next statement.
    "./test/should-validate/int_pow.pf",
    # LALR's `all_elim_types` transformer was passing the Lark `Tree`
    # instead of the loop index `i` as the first slot of `AllElimTypes.pos`,
    # so the canonical AST drifted (and `__str__` would `TypeError` on a
    # `Tree + 1` comparison). Each of these files exercises `proof<T>` /
    # `proof<T1, T2>` in some surface context.
    "./test/should-validate/inst3.pf",                # `prem<UInt>[...]`
    "./test/should-validate/bicond2.pf",              # `empty_iff_0<E>` inside `apply`
    "./test/should-validate/expand-repeat.pf",        # `reverse_append<U>` chain
    "./test/should-validate/all-elim-types-tlet.pf",  # `bleh<T>` term-let
    "./test/should-validate/map_append_cross_type.pf",  # multi-arg `proof<UInt, bool>`
    # TLet's `define ...; ...` binds looser than operators/connectives, so
    # term-let operands must be parenthesized when pretty-printed in those
    # contexts.
    "./test/should-validate/contradict-tlet.pf",      # term-let under `and`
    "./test/should-validate/define_cases.pf",         # term-let under `and`/`or`
    "./test/should-validate/extensionality-tlet.pf",  # term-let equality args
)


class ParsedFlags(TypedDict):
    cli: bool
    lib: bool
    passable: bool
    errors: bool
    warns: bool
    equiv: bool
    site: bool
    parser: bool
    examples: bool
    regen_all: bool
    regen_files: list[str]
    regen_all_warns: bool
    regen_warn_files: list[str]
    gen_parse: bool
    workers: int


T = TypeVar("T")
R = TypeVar("R")
S = TypeVar("S")


# Module-level globals consumed by worker functions. The parent
# populates these before forking the pool; workers inherit them via
# copy-on-write. Avoids pickling a 32-entry tuple per task.
_WORKER_PREWARM: tuple[str, ...] = ()
_WORKER_PRELUDE: tuple[str, ...] = ()


def handle_sigint(signum: int, frame: object) -> None:
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


def _check_against_warn(f: str) -> tuple[str, bool, str]:
    """Run ``f`` and diff its captured stdout against ``f + '.warn'``.

    Counterpart to ``_check_against_err`` for ``test/should-warn``:
    the file must validate (``result.ok``) AND the warnings printed
    via ``error.warning`` must match the ``.warn`` fixture line-for-
    line (modulo whitespace, like ``--errors``).
    """
    warn_file = f + ".warn"
    if not os.path.isfile(warn_file):
        return (f, False, "missing .pf.warn fixture")
    set_recursive_descent(True)
    set_quiet_mode(True)
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        result = check_file(f, prewarm_modules=_WORKER_PREWARM)
    if not result.ok:
        return (f, False, f"expected valid + warnings but file errored:\n"
                          f"{(result.error_message or '')[:500]}")
    actual = buf.getvalue()
    with tempfile.NamedTemporaryFile(
        "w", suffix=".tmp", delete=False, encoding="utf-8"
    ) as tf:
        tf.write(actual)
        tmp_path = tf.name
    try:
        cp = subprocess.run(
            ["diff", "--ignore-space-change", warn_file, tmp_path],
            capture_output=True, text=True,
        )
        if cp.returncode != 0:
            return (f, False, f"warning output diverged:\n{cp.stdout[:500]}")
        return (f, True, "")
    finally:
        os.unlink(tmp_path)


# ---------------------------------------------------------------------------
# Orchestration.
# ---------------------------------------------------------------------------


def _make_fork_pool(workers: int) -> ProcessPoolExecutor:
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


def _map_or_serial(
    workers: int,
    fn: Callable[[T], R],
    tasks: Iterable[T],
    chunksize: int = 4,
) -> list[R]:
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


def run_warn_diff_parallel(workers: int) -> list[tuple[str, str, str]]:
    """Run ``.warn``-fixture tests in ``test/should-warn`` (RD only)."""
    files = list_pf(WARN_DIR)
    failures: list[tuple[str, str, str]] = []
    for f, ok, msg in _map_or_serial(workers, _check_against_warn, files, 4):
        if not ok:
            failures.append((f, "recursive-descent", msg))
    return failures


def _canonical_ast(
    value: object,
    *,
    parent_class: str | None = None,
    field_name: str | None = None,
) -> object:
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


def _parse_for_equivalence(
    path: str, *, recursive_descent: bool
) -> list[object]:
    with open(path, encoding="utf-8") as f:
        return _parse_text_for_equivalence(
            path, f.read(), recursive_descent=recursive_descent
        )


def _parse_text_for_equivalence(path: str, source: str, *,
                                recursive_descent: bool) -> list[object]:
    parser_mod = _equiv_rd_parser if recursive_descent else _equiv_lark_parser
    parser_mod.set_deduce_directory(str(REPO_ROOT))
    parser_mod.set_filename(path)
    parser_mod.init_parser()
    return cast(list[object], parser_mod.parse(source))


def _pretty_print_program(ast: Iterable[object]) -> str:
    chunks = []
    for stmt in ast:
        printer = getattr(stmt, "pretty_print", None)
        text = (
            cast(Callable[[int], str], printer)(0)
            if callable(printer)
            else str(stmt)
        )
        chunks.append(text if text.endswith("\n") else text + "\n")
    return "".join(chunks)


def run_parser_equivalence() -> list[tuple[str, str, str]]:
    """Compare RD and LALR ASTs for accepted syntax.

    Covers ``lib/``, ``test/should-validate/``, ``test/should-warn/``,
    and most of ``test/should-error/``. ``should-error`` files fail in
    later phases, so their ASTs are still meaningful surface-syntax
    samples; the ``SHOULD_ERROR_PARSER_EQUIV_SKIP`` baseline excludes
    the fixtures where at least one parser rejects at parse time today.

    ``test/parse`` remains RD-only because those fixtures intentionally lock
    down beginner-facing RD diagnostics, while the LALR parser is kept as an
    executable grammar spec.
    """
    # ``--site`` generates ``doc_*.pf`` files into ``test/should-validate``.
    # They are already validated with both parsers by the site mode itself;
    # keep this drift baseline focused on checked-in should-validate files.
    pass_files = [
        f for f in list_pf(PASS_DIR)
        if not Path(f).name.startswith("doc_")
    ]
    should_error_files = [
        f for f in list_pf(ERROR_DIR)
        if f not in SHOULD_ERROR_PARSER_EQUIV_SKIP
    ]
    files = (list_pf(LIB_DIR) + pass_files + list_pf(WARN_DIR)
             + should_error_files)
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

    failures.extend(_check_should_error_skip_set())

    stale = PARSER_EQUIV_EXPECTED_DIVERGENCES - seen_divergences - {
        f for f in files if f in PARSER_EQUIV_EXPECTED_DIVERGENCES
    }
    for path in sorted(stale):
        failures.append((path, "parser-equivalence",
                         "expected divergence path no longer exists"))
    return failures


def _check_should_error_skip_set() -> list[tuple[str, str, str]]:
    """Verify each ``SHOULD_ERROR_PARSER_EQUIV_SKIP`` entry still needs skipping.

    A file belongs in the skip set only as long as at least one parser
    rejects it at parse time. Once both parsers accept it, it should be
    promoted into the main equivalence sweep so we get drift coverage there
    too.
    """
    failures: list[tuple[str, str, str]] = []
    existing_error_files = set(list_pf(ERROR_DIR))
    for path in sorted(SHOULD_ERROR_PARSER_EQUIV_SKIP):
        if path not in existing_error_files:
            failures.append((path, "parser-equivalence",
                             "skip-set path no longer exists"))
            continue
        try:
            _parse_for_equivalence(path, recursive_descent=True)
            rd_ok = True
        except Exception:
            rd_ok = False
        try:
            _parse_for_equivalence(path, recursive_descent=False)
            lalr_ok = True
        except Exception:
            lalr_ok = False
        if rd_ok and lalr_ok:
            failures.append((path, "parser-equivalence",
                             "skip-set entry now parses with both parsers; "
                             "remove from SHOULD_ERROR_PARSER_EQUIV_SKIP"))
    return failures


def run_parser_round_trip() -> list[tuple[str, str, str]]:
    """Pretty-print representative ASTs and re-parse with both parsers."""
    failures: list[tuple[str, str, str]] = []
    for path in PARSER_ROUND_TRIP_FILES:
        for source_rd in (True, False):
            source_label = "RD" if source_rd else "LALR"
            try:
                original = _parse_for_equivalence(
                    path, recursive_descent=source_rd
                )
                pretty_source = _pretty_print_program(original)
                original_ast = _canonical_ast(original)
            except Exception as exc:
                failures.append((path, "parser-roundtrip",
                                 f"{source_label} source parse/print: "
                                 f"{type(exc).__name__}: {exc}"))
                continue

            for roundtrip_rd in (True, False):
                roundtrip_label = "RD" if roundtrip_rd else "LALR"
                try:
                    reparsed = _parse_text_for_equivalence(
                        path + f"<{source_label}-roundtrip-{roundtrip_label}>",
                        pretty_source,
                        recursive_descent=roundtrip_rd,
                    )
                except Exception as exc:
                    failures.append((path, "parser-roundtrip",
                                     f"{source_label} pretty source failed "
                                     f"with {roundtrip_label}: "
                                     f"{type(exc).__name__}: {exc}"))
                    continue

                if _canonical_ast(reparsed) != original_ast:
                    failures.append((path, "parser-roundtrip",
                                     f"{source_label} pretty source changed "
                                     f"when parsed with {roundtrip_label}"))
    return failures


def run_cli_test() -> list[tuple[str, str, str]]:
    """Sanity-check that ``python deduce.py`` works end-to-end.

    The in-process runner exercises ``lsp.library.check_file``; this
    one subprocess invocation makes sure the ``deduce.py`` CLI wrapper
    itself (arg parsing, no-stdlib mode, exit codes, success output)
    hasn't drifted. A tiny no-stdlib file is enough -- we're testing
    the CLI shape without paying for a full stdlib bootstrap.
    """
    cli_path = "./test/should-validate/theorem_true.pf"
    cp = subprocess.run(
        [sys.executable, "deduce.py", "--no-stdlib", cli_path],
        capture_output=True, text=True,
    )
    failures: list[tuple[str, str, str]] = []
    if cp.returncode != 0:
        failures.append((
            cli_path, "cli",
            f"exit {cp.returncode}\nstderr: {cp.stderr[:500]}\n"
            f"stdout: {cp.stdout[:500]}",
        ))
    elif "theorem_true.pf is valid" not in cp.stdout:
        failures.append((
            cli_path, "cli",
            f"unexpected stdout:\n{cp.stdout[:500]}",
        ))
    return failures


def run_examples_parallel(workers: int) -> list[tuple[str, str, str]]:
    """``examples/*.pf`` × RD parser only.

    Examples are end-user-facing proofs that rely on the auto-prelude
    (``import UInt`` etc. is not written out); use the prelude-injection
    worker so the stdlib is implicitly available, the same way
    ``deduce.py`` runs them.
    """
    files = list_pf(EXAMPLES_DIR)
    tasks = [(f, True) for f in files]
    failures: list[tuple[str, str, str]] = []
    for f, ok, label, msg in _map_or_serial(workers, _worker_prelude, tasks, 4):
        if not ok:
            failures.append((f, label, msg))
    return failures


def run_site(workers: int) -> list[tuple[str, str, str]]:
    """Generate ``doc_*.pf`` from ``gh_pages/doc/`` and check them."""
    from gh_pages.scripts.convert import convert_dir as convert_dir_raw
    convert_dir = cast(Callable[[str, bool], None], convert_dir_raw)
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


def regenerate_one(path: str, suffix: str = ".err") -> None:
    out = _capture_err_output(path)
    with open(path + suffix, "w", encoding="utf-8") as f:
        f.write(out)
    print(f"  wrote {path}{suffix}")


def regenerate_dir(directory: Path, suffix: str = ".err") -> None:
    for f in list_pf(directory):
        regenerate_one(f, suffix)


# ---------------------------------------------------------------------------
# CLI.
# ---------------------------------------------------------------------------


def time_section(label: str, fn: Callable[[], S]) -> tuple[float, S]:
    t0 = time.perf_counter()
    result = fn()
    dt = time.perf_counter() - t0
    print(f"  {label:32s}  {dt:6.2f}s")
    return dt, result


def parse_args(argv: list[str]) -> ParsedFlags:
    """Return a dict of flag → value. Tolerates the legacy long-form
    arguments still in scripts / muscle memory."""
    flags: ParsedFlags = {
        "cli": False, "lib": False, "passable": False, "errors": False,
        "warns": False, "equiv": False, "site": False, "parser": False,
        "examples": False, "regen_all": False, "regen_files": [],
        "regen_all_warns": False, "regen_warn_files": [],
        "gen_parse": False, "workers": max(1, (os.cpu_count() or 4)),
    }
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == "--cli": flags["cli"] = True
        elif a == "--lib": flags["lib"] = True
        elif a == "--passable": flags["passable"] = True
        elif a == "--errors": flags["errors"] = True
        elif a == "--warns": flags["warns"] = True
        elif a == "--equiv": flags["equiv"] = True
        elif a == "--site": flags["site"] = True
        elif a == "--parser": flags["parser"] = True
        elif a == "--examples": flags["examples"] = True
        elif a == "--regenerate-errors": flags["regen_all"] = True
        elif a == "--generate-error":
            flags["regen_files"].append(argv[i + 1])
            i += 1
        elif a == "--regenerate-warns": flags["regen_all_warns"] = True
        elif a == "--generate-warn":
            flags["regen_warn_files"].append(argv[i + 1])
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
    if not (
        flags["cli"] or flags["lib"] or flags["passable"] or flags["errors"]
        or flags["warns"] or flags["site"] or flags["parser"]
        or flags["examples"] or flags["equiv"] or flags["regen_all"]
        or flags["regen_all_warns"] or flags["gen_parse"]
        or flags["regen_files"] or flags["regen_warn_files"]
    ):
        flags["cli"] = flags["lib"] = flags["passable"] = True
        flags["errors"] = flags["warns"] = flags["equiv"] = True

    # Standalone modes are mutually exclusive with everything else.
    category_flags = (
        ("cli", flags["cli"]),
        ("lib", flags["lib"]),
        ("passable", flags["passable"]),
        ("errors", flags["errors"]),
        ("warns", flags["warns"]),
        ("equiv", flags["equiv"]),
    )
    standalone_flags = (
        ("site", flags["site"]),
        ("parser", flags["parser"]),
        ("examples", flags["examples"]),
        ("regen_all", flags["regen_all"]),
        ("regen_files", bool(flags["regen_files"])),
        ("regen_all_warns", flags["regen_all_warns"]),
        ("regen_warn_files", bool(flags["regen_warn_files"])),
        ("gen_parse", flags["gen_parse"]),
    )
    if any(active for _, active in standalone_flags):
        active_categories = [name for name, active in category_flags if active]
        active_standalone = [
            name for name, active in standalone_flags if active
        ]
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
    if flags["regen_all_warns"]:
        print(f"Regenerating ALL warnings in {WARN_DIR}")
        bootstrap_prewarm(lib_modules)
        regenerate_dir(WARN_DIR, ".warn")
        return 0
    if flags["regen_warn_files"]:
        bootstrap_prewarm(lib_modules)
        for path in flags["regen_warn_files"]:
            print(f"Generating warning fixture for: {path}")
            regenerate_one(path, ".warn")
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
    if flags["examples"]:
        print(f"=== --examples: {EXAMPLES_DIR} (RD only, parallel) ===")
        bootstrap_prelude(lib_modules)
        _, fails = time_section("examples",
                                lambda: run_examples_parallel(workers))
        total_failures.extend(fails)
        return _report(total_failures, total_t0)

    # Combinable per-category sweep.
    print(f"Discovered {len(lib_modules)} lib modules; workers={workers}")

    if flags["cli"]:
        print("\n=== --cli: deduce.py CLI sanity check ===")
        _, fails = time_section(
            "deduce.py --no-stdlib theorem_true.pf", run_cli_test
        )
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

    # Combined pool: should-validate + should-error + should-warn share a
    # prewarm bootstrap.
    if flags["passable"] or flags["errors"] or flags["warns"]:
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

    if flags["warns"]:
        print("\n=== should-warn (RD only, parallel) ===")
        _, fails = time_section("should-warn",
                                lambda: run_warn_diff_parallel(workers))
        total_failures.extend(fails)

    if flags["equiv"]:
        print("\n=== parser equivalence (RD vs LALR ASTs) ===")
        _, fails = time_section("lib + should-validate + should-error",
                                run_parser_equivalence)
        total_failures.extend(fails)
        _, fails = time_section("pretty-print round trip",
                                run_parser_round_trip)
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
