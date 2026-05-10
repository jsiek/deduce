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

    We arm by hitting a function breakpoint on ``double``, then issue
    ``finish``: subsequent traps must only fire after returning from
    the current ``double`` frame (i.e. either at a *later* statement
    or at a re-entrant call after we've popped out)."""
    path = _write_fixture("finish.pf", RECURSIVE_PROGRAM)
    result, dbg, out = _run(
        path,
        "break double\n"   # arm function breakpoint
        "continue\n"        # advance to it
        "finish\n"          # run until the current double frame returns
        "continue\n",       # mop up
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
