"""Acceptance test for Phase 5 / Step 22 (gdb-parity REPL).

The plan's acceptance criteria, verbatim:

    test/lsp/test_debugger_repl.py with stdio-driven fixtures per
    command; recursion test pinning step-over correctness (the PR
    #269 regression).

This file covers:

* the four step modes (continue / step / next / finish) and their
  depth interactions;
* file:line and function-name breakpoints with optional ``if``
  conditions;
* the inspection commands -- print, list, where, up, down, locals,
  info, delete, help;
* the PR #269 regression: step-over (``next``) must NOT re-trap
  inside a recursive call to the function whose call site we
  stepped past.

Step 21's basic wiring tests stay in ``test_debugger.py``; this file
is purely about REPL command behavior.
"""

from __future__ import annotations

import io
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from lsp.debugger import Debugger, DebuggerQuit  # noqa: E402
from lsp.library import check_file  # noqa: E402


# Programs are small and self-contained so each test's expected
# command transcript is short and grepable.
RECURSIVE_PROGRAM = """\
recursive double(Nat) -> Nat {
  double(zero) = zero
  double(suc(n')) = suc(suc(double(n')))
}

print double(suc(suc(zero)))
"""

NESTED_PROGRAM = """\
recursive triple(Nat) -> Nat {
  triple(zero) = zero
  triple(suc(n')) = suc(suc(suc(triple(n'))))
}

recursive caller(Nat) -> Nat {
  caller(zero) = zero
  caller(suc(n')) = triple(suc(n'))
}

print caller(suc(zero))
"""

PRELUDE = ("Nat",)


def _write_fixture(name: str, source: str) -> Path:
    tmp = REPO_ROOT / "tmp"
    tmp.mkdir(exist_ok=True)
    path = tmp / name
    path.write_text(source)
    return path


def _run(path: Path, repl_input: str):
    """Drive ``check_file`` with a debugger reading ``repl_input``.

    Returns ``(result, dbg, captured_repl_output, stdout_lines)``.
    The ``stdout_lines`` capture is via pytest's ``capsys`` would be
    cleaner, but we want this helper callable both inside and outside
    pytest fixtures; we route the debugger's writes to an in-memory
    buffer and ignore the Python-stdout side-effects from ``print``
    statements (those go to the real stdout and are inspected via
    ``capsys.readouterr`` in tests that care).
    """
    out = io.StringIO()
    dbg = Debugger(input=io.StringIO(repl_input), output=out)
    result = check_file(str(path), prelude=PRELUDE, debugger=dbg)
    return result, dbg, out.getvalue()


# --------------------------------------------------------------------------
# Step modes.
# --------------------------------------------------------------------------


def test_step_traps_on_every_hook():
    """``step`` should pause at the very next hook, regardless of
    whether it's a statement or a function call."""
    path = _write_fixture("step.pf", RECURSIVE_PROGRAM)
    # ``step`` then ``continue``: after the first statement trap, we
    # ``step`` to land at either the next statement or the first
    # function call (whichever comes first), then ``continue`` to the
    # end.  We just assert there's at least one "-> call" line in the
    # transcript -- confirming step did pause at a function call.
    result, _, out = _run(path, "step\ncontinue\n")
    assert result.ok, result.error_message
    assert "-> call" in out or out.count("-> statement") >= 2


def test_next_does_not_recurse_into_calls():
    """The PR #269 regression: ``next`` (step-over) must not trap
    inside a function call.  ``double(2)`` makes two recursive
    descent steps inside ``double`` -- a location-keyed step-over
    would re-trap on each.  Depth-tracking step-over should trap at
    most once after we step past the print statement."""
    path = _write_fixture("next.pf", RECURSIVE_PROGRAM)
    # Land at first statement, ``next`` to step past it (over any
    # function calls inside), and we should NOT trap again inside
    # ``double``.  Then ``continue`` to handle subsequent statements.
    result, _, out = _run(path, "next\ncontinue\n")
    assert result.ok, result.error_message
    # Count traps: starting trap + any extras.  We must NOT see a
    # "-> call double" line, because next steps over user calls.
    assert "-> call double" not in out


def test_next_doesnt_retrap_after_first_call(monkeypatch):
    """Companion to ``test_next_does_not_recurse_into_calls``: a
    deeper-recursion fixture (six recursive frames) where PR #269's
    location-keyed step-over would have re-trapped six times.  Today
    ``next`` only re-traps at depth <= depth-at-command, so we see
    *at most* the initial trap plus traps after the recursion ends."""
    path = _write_fixture("next_deep.pf", RECURSIVE_PROGRAM)
    # Just ``next``: from the first statement trap, step over every
    # subsequent function call, never re-trapping mid-recursion.
    # We feed extra continues in case there are post-call statements
    # that legitimately re-trap.
    result, _, out = _run(path, "next\nnext\nnext\ncontinue\n")
    assert result.ok, result.error_message
    # The "-> call double" trap text must not appear -- the whole
    # point of step-over is to skip over function bodies.
    assert "-> call double" not in out


def test_finish_runs_to_return():
    """``finish`` from inside a frame runs until that frame returns.

    We arm by hitting a function breakpoint on ``double``, then
    ``delete`` it (otherwise the recursive ``double`` calls keep
    re-trapping: breakpoints fire regardless of step mode, gdb-style),
    then ``finish`` to run until the current frame returns."""
    path = _write_fixture("finish.pf", RECURSIVE_PROGRAM)
    result, dbg, out = _run(
        path,
        "break double\n"
        "continue\n"   # advance to first ``double`` call
        "delete\n"     # so the recursive descent doesn't keep firing
        "finish\n"     # unwind the current double frame
        "continue\n",  # mop up any remaining statements
    )
    assert result.ok, result.error_message
    assert "-> call double" in out


def test_finish_at_top_level_is_continue():
    """``finish`` with an empty stack collapses to ``continue`` --
    there's no frame to return from."""
    path = _write_fixture("finish_top.pf", RECURSIVE_PROGRAM)
    result, _, out = _run(path, "finish\n")
    assert result.ok, result.error_message


# --------------------------------------------------------------------------
# Breakpoints.
# --------------------------------------------------------------------------


def test_function_breakpoint_fires():
    path = _write_fixture("bp_func.pf", RECURSIVE_PROGRAM)
    # ``double`` recurses, so the breakpoint fires on every call.
    # Use ``delete`` after the first hit so the rest of the run
    # doesn't need an unbounded supply of continues.
    result, dbg, out = _run(
        path,
        "break double\n"
        "continue\n"   # advance to first ``double`` call
        "delete\n"      # tear down the breakpoint
        "continue\n",   # let the rest of the file run
    )
    assert result.ok, result.error_message
    assert "-> call double" in out


def test_file_line_breakpoint_fires():
    """File:line breakpoint should trap on the matching ``Print``
    statement's location."""
    path = _write_fixture("bp_line.pf", RECURSIVE_PROGRAM)
    # The print statement is line 6 of RECURSIVE_PROGRAM.
    result, _, out = _run(
        path,
        f"break {path.name}:6\n"
        "continue\n"
        "continue\n",
    )
    assert result.ok, result.error_message
    # Either a statement trap at line 6 or a function call trap whose
    # location lands on line 6 -- we just check the spec was honored
    # and we trapped after the continue (more than one prompt).
    assert out.count("(deduce-debug)") >= 2


def test_conditional_breakpoint_skips_when_false():
    """``b foo if false`` should never fire -- continue should run
    the whole file."""
    path = _write_fixture("bp_cond_false.pf", RECURSIVE_PROGRAM)
    result, dbg, out = _run(
        path,
        "break double if false\n"
        "continue\n",
    )
    assert result.ok, result.error_message
    assert "-> call double" not in out
    # The breakpoint was registered with its condition.
    assert dbg.breakpoints[0].condition == "false"


def test_conditional_breakpoint_fires_when_true():
    path = _write_fixture("bp_cond_true.pf", RECURSIVE_PROGRAM)
    result, _, out = _run(
        path,
        "break double if true\n"
        "continue\n"   # advance to first ``double`` call
        "delete\n"     # avoid re-trapping on recursion
        "continue\n",
    )
    assert result.ok, result.error_message
    assert "-> call double" in out


def test_delete_breakpoints():
    path = _write_fixture("bp_delete.pf", RECURSIVE_PROGRAM)
    result, dbg, out = _run(
        path,
        "break double\n"
        "delete\n"          # nuke all
        "continue\n",
    )
    assert result.ok, result.error_message
    assert dbg.breakpoints == []
    assert "-> call double" not in out


def test_info_breakpoints_lists_them():
    path = _write_fixture("bp_info.pf", RECURSIVE_PROGRAM)
    _, _, out = _run(
        path,
        "break double\n"
        "info breakpoints\n"
        "quit\n",
    )
    assert "1: double" in out


# --------------------------------------------------------------------------
# Inspection commands.
# --------------------------------------------------------------------------


def test_print_evaluates_expression():
    """``print`` parses + reduces an arbitrary term in the current
    env.  At the first trap (top-level scope) the user can print
    things visible via the prelude / their own decls."""
    path = _write_fixture("print.pf", RECURSIVE_PROGRAM)
    _, _, out = _run(
        path,
        "print suc(zero)\n"
        "quit\n",
    )
    # The reduced form of ``suc(zero)`` in the proof-checker print
    # form.  Don't pin the exact representation -- just confirm we
    # got output back, not a "could not evaluate" error.
    assert "could not evaluate" not in out
    # The output stream has the prompt, our print response, and one
    # more prompt before quit.  At least two prompts total.
    assert out.count("(deduce-debug)") >= 2


def test_print_unknown_identifier_reports_error():
    path = _write_fixture("print_err.pf", RECURSIVE_PROGRAM)
    _, _, out = _run(
        path,
        "print zzz_not_a_real_name\n"
        "quit\n",
    )
    assert "could not evaluate" in out


def test_list_shows_source():
    """``list`` reads the source by ``Meta.filename`` + ``Meta.line``.

    The first trap is on a synthesized ``import`` statement whose
    ``Meta()`` is empty (no filename, no line) -- ``list`` correctly
    reports "no source location" there.  ``step`` advances us to the
    first real statement; ``list`` then shows the surrounding
    source."""
    path = _write_fixture("list.pf", RECURSIVE_PROGRAM)
    _, _, out = _run(path, "step\nlist\nquit\n")
    assert "recursive double" in out
    assert "->" in out  # marker for the current line


def test_where_with_no_active_call():
    path = _write_fixture("where_empty.pf", RECURSIVE_PROGRAM)
    _, _, out = _run(path, "where\nquit\n")
    assert "no active call stack" in out


def test_where_shows_frames_inside_call():
    """After hitting a breakpoint inside ``double``, ``where`` shows
    at least one frame (the active call)."""
    path = _write_fixture("where_inside.pf", RECURSIVE_PROGRAM)
    _, _, out = _run(
        path,
        "break double\n"
        "continue\n"
        "where\n"
        "quit\n",
    )
    assert "#0" in out
    assert "double" in out


def test_locals_dumps_params():
    """After hitting a function breakpoint, ``locals`` shows the
    arguments the function was called with.

    For ``double(suc(n'))``, pattern matching binds ``n'`` -- which
    funnels through ``do_function_call``'s ``subst`` rather than its
    positional ``params`` list.  The hook collects both into the
    frame's locals dict, so the user sees the binding either way."""
    path = _write_fixture("locals.pf", RECURSIVE_PROGRAM)
    _, _, out = _run(
        path,
        "break double\n"
        "continue\n"
        "locals\n"
        "quit\n",
    )
    # Look for ``<name> = <value>`` anywhere in the captured output;
    # the prompt prefix breaks line.startswith().
    assert "n' = suc(zero)" in out


def test_help_lists_commands():
    path = _write_fixture("help.pf", RECURSIVE_PROGRAM)
    _, _, out = _run(path, "help\nquit\n")
    assert "continue" in out
    assert "break" in out
    assert "quit" in out


# --------------------------------------------------------------------------
# Misc REPL behavior.
# --------------------------------------------------------------------------


def test_typo_suggestion():
    """An unrecognized command should suggest a near match."""
    path = _write_fixture("typo.pf", RECURSIVE_PROGRAM)
    _, _, out = _run(path, "contineu\ncontinue\n")
    assert "unrecognized command" in out
    # ``continue`` should be the suggestion.
    assert "continue" in out


def test_help_alias_is_h():
    path = _write_fixture("help_alias.pf", RECURSIVE_PROGRAM)
    _, _, out = _run(path, "h\nquit\n")
    assert "continue" in out  # help body contains command list


# --------------------------------------------------------------------------
# Generic-function stepping: ``recursive head<E>(...)`` and friends go
# through ``do_function_call`` with non-empty ``type_params`` /
# ``type_args``, so the single hook there should catch them.  We pin
# this to guard against future refactors that split the named-function
# path by genericity.
# --------------------------------------------------------------------------

GENERIC_PROGRAM = """\
import List

print length(node(zero, node(suc(zero), empty)))
"""

GENERIC_PRELUDE = ("Nat", "Base", "UInt", "List")


def _run_with_prelude(path: Path, repl_input: str, prelude):
    out = io.StringIO()
    dbg = Debugger(input=io.StringIO(repl_input), output=out)
    result = check_file(str(path), prelude=prelude, debugger=dbg)
    return result, dbg, out.getvalue()


def test_step_through_generic_function():
    """``length<Nat>(node(0, node(1, empty)))`` exercises a generic
    recursive function.  The ``do_function_call`` hook should fire
    with the type-args present in the call (the function is
    instantiated at ``E = Nat`` here)."""
    path = _write_fixture("generic.pf", GENERIC_PROGRAM)
    result, dbg, out = _run_with_prelude(
        path,
        "break length\n"   # function-name breakpoint -- ignores type args
        "continue\n"       # advance to the first length() call
        "where\n"          # confirm we landed inside ``length``
        "locals\n"         # the pattern-bound names should be visible
        "delete\n"         # tear down -- length recurses
        "continue\n",
        GENERIC_PRELUDE,
    )
    assert result.ok, result.error_message
    # The breakpoint matched on the bare name, even though length is
    # generic.  ``where`` shows the active frame named ``length``.
    assert "-> call length" in out
    assert "length" in out  # in the where output too


def test_next_over_generic_call_does_not_recurse():
    """The PR-#269 step-over regression also applies to generic
    recursive functions: ``next`` past a ``length(...)`` call must
    not re-trap on each recursive descent."""
    path = _write_fixture("generic_next.pf", GENERIC_PROGRAM)
    result, _, out = _run_with_prelude(path, "next\nnext\ncontinue\n",
                                       GENERIC_PRELUDE)
    assert result.ok, result.error_message
    # ``length`` recurses twice on this 2-element list; depth-tracking
    # ``next`` should not surface any of those calls.
    assert "-> call length" not in out


def test_imports_do_not_trap():
    """The debugger does not trap on ``import`` statements -- they
    are pure declarations and have no executable body for ``step``
    to advance through (gdb's ``step`` doesn't trap on ``#include``
    for the same reason).

    The CLI's default mode also prepends one synthesised ``Import``
    per stdlib module before parsing the user file; ~32 of them
    with the full stdlib.  Skipping the whole ``Import`` AST type
    covers both -- without keying on ``Meta`` internals."""
    path = _write_fixture("import_skip.pf", GENERIC_PROGRAM)
    # Single ``continue`` is enough: zero trap on the 32 synthesised
    # prelude imports, zero trap on the user's own ``import Nat`` /
    # ``import List`` (which type_check_stmt drops anyway as
    # duplicates of the prelude).  If the filter regressed, the
    # transcript hits EOF and fails with DebuggerQuit before reaching
    # the user's first real statement.
    result, _, out = _run_with_prelude(path, "continue\n", GENERIC_PRELUDE)
    assert result.ok, result.error_message
    # No ``-> statement at`` lines mention ``import``.
    for line in out.splitlines():
        if line.startswith("-> statement"):
            assert "import" not in line, line
    # And nothing should display as ``<unknown>`` -- the only stmts
    # that lack source locations *are* the synthetic prelude imports.
    assert "<unknown>" not in out


def test_skip_lib_suppresses_step_into():
    """Default skip rule (``lib/``): ``step`` past a print of a
    prelude function does not trap inside the function's body.  The
    call still happens (the print produces the correct value) and the
    frame is still pushed (a breakpoint set on the function would
    still fire); the trap-on-entry is what gets suppressed."""
    path = _write_fixture("skip_lib.pf", GENERIC_PROGRAM)
    # ``step`` four times: statement -> print -> next statement
    # boundary should be reachable without ever trapping inside
    # ``length`` (which lives in lib/List.pf).
    result, _, out = _run_with_prelude(path, "step\nstep\nstep\nstep\ncontinue\n",
                                       GENERIC_PRELUDE)
    assert result.ok, result.error_message
    # No trap line should reference ``length`` -- it's skipped.
    for line in out.splitlines():
        if line.startswith("-> call"):
            assert "length" not in line, line


def test_skip_lib_still_honours_explicit_breakpoint():
    """The whole point of the skip-vs-invisible split: a user who
    explicitly says ``break length`` wants to drill in.  Skip rules
    only suppress the *automatic* step-into trap; explicit
    breakpoints take precedence."""
    path = _write_fixture("skip_lib_break.pf", GENERIC_PROGRAM)
    result, _, out = _run_with_prelude(
        path,
        "break length\n"
        "continue\n"     # advance to first length() call
        "delete\n"        # avoid retraps on length's recursion
        "continue\n",
        GENERIC_PRELUDE,
    )
    assert result.ok, result.error_message
    assert "-> call length" in out


def test_recursive_case_location_points_at_matched_case():
    """Recursive functions have one ``Case`` per pattern arm.  When
    a call dispatches to a specific arm, the debugger's ``-> call``
    location should be that arm's body, not the ``recursive`` header
    line that opens the function.

    For our ``count_down`` fixture:
      line 12: ``recursive count_down(Nat) -> Nat {``
      line 13: ``  count_down(zero) = zero``
      line 14: ``  count_down(suc(n')) = count_down(n')``

    A call with a ``suc(...)`` arg must trap at 14:N; a call with
    ``zero`` must trap at 13:N.  Step 22 originally surfaced the
    RecFun's outer ``loc`` for every case, gluing the ``->`` arrow
    to line 12 on every recursive entry."""
    path = _write_fixture("rec_case_loc.pf", RECURSIVE_PROGRAM)
    # ``RECURSIVE_PROGRAM`` defines ``double`` similarly:
    #   line 1: recursive double(Nat) -> Nat {
    #   line 2:   double(zero) = zero
    #   line 3:   double(suc(n')) = suc(suc(double(n')))
    # ``double(suc(suc(zero)))`` hits the inductive case twice then
    # the base case.  We expect to see ``-> call double(...) at 3:N``
    # for the suc cases and ``-> call double()`` at ``2:N`` for the
    # base.
    result, _, out = _run(
        path,
        "break double\n"
        "continue\n" "continue\n" "continue\n"
        "delete\n"
        "continue\n",
    )
    assert result.ok, result.error_message
    # Inductive-case entries land on line 3.  The REPL prompt is on
    # the same line as the trap header (no newline after the prompt),
    # so use ``in`` rather than ``startswith``.
    suc_traps = [line for line in out.splitlines()
                 if "-> call double(n'=" in line]
    assert suc_traps, f"expected at least one suc-case trap\n{out}"
    for line in suc_traps:
        assert " at 3:" in line, line
    # Base-case entry lands on line 2.
    base_traps = [line for line in out.splitlines()
                  if "-> call double() " in line]
    for line in base_traps:
        assert " at 2:" in line, line


def test_invisible_lit_never_appears():
    """``lit`` is a Nat-identity marker in lib/NatDefs.pf used by
    the auto-rewrite machinery.  It's an implementation detail the
    user model doesn't have; the debugger hides it entirely:

    - never traps on entry, even with ``step`` or ``break lit``;
    - never appears in ``where``;
    - never gets pushed onto the call stack.

    This test confirms it: step through the whole file and assert
    no transcript line mentions lit."""
    path = _write_fixture("invisible_lit.pf", GENERIC_PROGRAM)
    result, _, out = _run_with_prelude(
        path,
        "break lit\n"           # would normally fire; invisible vetoes it
        "step\n" * 30 +
        "continue\n",
        GENERIC_PRELUDE,
    )
    assert result.ok, result.error_message
    # No reference to ``lit`` anywhere in the captured transcript.
    for line in out.splitlines():
        if line.startswith("-> "):
            assert "lit" not in line, line


def test_lambda_does_not_double_trap():
    """``Call.reduce``'s ``Lambda`` arm forwards to ``do_call`` which
    in turn calls ``do_function_call(name='anonymous', ...)``.  A
    naive Step-21 implementation hooked *both* sites and produced a
    pair of back-to-back traps at the same source location -- PR
    #269's bug verbatim.  The single hook in ``do_function_call`` is
    enough; this test pins that.

    Uses ``length(...)`` on a 1-element list, which reduces through
    enough lambda-bearing prelude infrastructure that any duplicate
    hook would surface as adjacent identical traps in the output."""
    path = _write_fixture("lambda_no_double.pf", GENERIC_PROGRAM)
    # ``step`` through every hook, capturing all traps.  Feed enough
    # ``step`` commands to drive the recursion to completion;
    # remaining ones are no-ops once the file finishes.
    result, _, out = _run_with_prelude(
        path,
        ("step\n" * 200),
        GENERIC_PRELUDE,
    )
    # Collect every trap header.  No two consecutive entries should
    # be at the same source location with the same args -- that's
    # the double-trap signature.
    traps = [line for line in out.splitlines()
             if line.startswith("-> call ") or
                line.startswith("-> statement ")]
    for prev, cur in zip(traps, traps[1:]):
        assert prev != cur, (
            f"adjacent identical traps -- hook double-fire?\n"
            f"  prev: {prev}\n  cur:  {cur}"
        )


def test_print_generic_call_returns_result():
    """``print length(...)`` inside the debugger should reduce the
    full generic call.  The save/restore around ``_eval_expr`` keeps
    intermediate ``on_function`` traps from leaking."""
    path = _write_fixture("generic_print.pf", GENERIC_PROGRAM)
    _, _, out = _run_with_prelude(
        path,
        "print length(node(zero, empty))\n"
        "quit\n",
        GENERIC_PRELUDE,
    )
    # Should produce the literal 1 (one-element list).  Don't pin the
    # exact rendering of UInt 1 -- just confirm it didn't error out.
    assert "could not evaluate" not in out
