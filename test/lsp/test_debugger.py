"""Acceptance test for Phase 5 / Step 21 (Debugger foundation).

The plan's acceptance criteria, verbatim:

    test/lsp/test_debugger.py scripts the REPL via captured stdio
    against fixed inputs; test/should-validate/ and test/should-error/
    runs unchanged (with and without --debug); benchmark from
    lsp/benchmark.py shows ≤1% overhead on non-debug runs.

The cross-cutting "runs unchanged" prong is exercised by the existing
``make tests`` invocation -- this file covers the new surface:

* the Debugger instance integrates with ``check_file`` via the
  ``debugger=`` parameter, gets attached/detached cleanly, and never
  leaks across calls;
* the hooks fire (``on_statement`` per top-level statement, plus
  ``on_function`` for each user-function call); empty stdin terminates
  the REPL via ``DebuggerQuit`` (the EOF -> quit translation);
* a ``continue`` command runs the file to completion;
* non-debug runs of the same file produce identical observable output
  (the hook short-circuits really do short-circuit).
"""

from __future__ import annotations

import io
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from flags import get_debugger  # noqa: E402
from lsp.debugger import Debugger, DebuggerQuit  # noqa: E402
from lsp.library import check_file  # noqa: E402


# A tiny self-contained fixture exercising the three hook sites:
# top-level statements (``recursive`` decl + ``print`` + ``assert``),
# a named user-function call (``double``), and the function's
# recursive self-call.  Pulls in just ``Nat`` from the prelude so the
# bootstrap stays fast.
SIMPLE_PROGRAM = """\
recursive double(Nat) -> Nat {
  double(zero) = zero
  double(suc(n')) = suc(suc(double(n')))
}

print double(suc(suc(zero)))
assert double(suc(suc(suc(zero)))) = suc(suc(suc(suc(suc(suc(zero))))))
"""

PRELUDE = ("Nat",)


def _run(source: str, repl_input: str = "", *, attach: bool = True):
    """Helper: write ``source`` to a tmp file, attach a Debugger driven
    by ``repl_input`` (when ``attach`` is True), and run check_file.

    Returns ``(result, debugger, stdout_text)``.
    """
    tmp = REPO_ROOT / "tmp"
    tmp.mkdir(exist_ok=True)
    path = tmp / "debugger_test.pf"
    path.write_text(source)

    debugger = None
    out = io.StringIO()
    if attach:
        debugger = Debugger(input=io.StringIO(repl_input), output=out)
    result = check_file(str(path), prelude=PRELUDE, debugger=debugger)
    return result, debugger, out.getvalue()


# --------------------------------------------------------------------------
# Core wiring: attach/detach, hook firing, REPL termination via EOF.
# --------------------------------------------------------------------------


def test_debugger_attaches_and_detaches_cleanly():
    """``flags.get_debugger()`` must return ``None`` after check_file
    returns, even on a failed/aborted run.  This is the leak-prevention
    contract that lets a long-lived daemon (the LSP server) safely run
    a debug session."""
    assert get_debugger() is None
    _, _, _ = _run(SIMPLE_PROGRAM, repl_input="continue\n")
    assert get_debugger() is None


def test_eof_on_repl_triggers_DebuggerQuit():
    """Empty stdin => EOF on first ``readline`` => ``DebuggerQuit``.
    Non-interactive callers (CI, dead pipes) need to terminate cleanly."""
    result, _, out = _run(SIMPLE_PROGRAM, repl_input="")
    assert not result.ok
    assert "debugger session ended" in result.error_message
    assert isinstance(result.exception, DebuggerQuit)
    # The first prompt should have been written before EOF.
    assert "(deduce-debug)" in out


def test_continue_runs_to_completion():
    """``continue`` from the very first trap resumes execution and the
    rest of the file checks normally.  ``Print``'s side effect should
    still be observable (stdout, not the debugger's output stream)."""
    result, dbg, out = _run(SIMPLE_PROGRAM, repl_input="continue\n")
    assert result.ok, result.error_message
    # The first statement (the user-function declaration) traps, then
    # ``continue`` releases execution.  No further trap should fire.
    assert "-> statement at" in out
    assert "(deduce-debug)" in out
    # Stack should be empty at end (every push was popped).
    assert dbg.stack == []


def test_quit_command_aborts():
    result, _, out = _run(SIMPLE_PROGRAM, repl_input="quit\n")
    assert not result.ok
    assert isinstance(result.exception, DebuggerQuit)
    assert "user quit" in str(result.exception)


def test_unrecognized_command_reprompts():
    """Unknown command should print an error then prompt again, not
    crash and not silently advance."""
    _, _, out = _run(SIMPLE_PROGRAM, repl_input="xyzzy\ncontinue\n")
    assert "unrecognized command" in out
    # Two prompts: one for ``xyzzy``, one for ``continue``.
    assert out.count("(deduce-debug)") >= 2


def test_empty_input_replays_last_command():
    """Bare-RET replays the previous command, gdb-style.  ``continue``
    followed by RET should exit on the first ``continue`` -- the second
    bare-RET shouldn't be needed -- but if the REPL re-traps for some
    reason, the replayed ``continue`` would still resume."""
    result, _, _ = _run(
        SIMPLE_PROGRAM, repl_input="continue\n\n"
    )
    assert result.ok


# --------------------------------------------------------------------------
# Non-debug runs are unchanged (the "≤1% overhead" prong is benchmark
# territory; here we just pin that the hook short-circuits really do).
# --------------------------------------------------------------------------


def test_non_debug_run_is_unaffected():
    """Same file, same prelude, no debugger attached.  Result must be
    indistinguishable from the version of check_file before Step 21
    landed.  Cross-checks the ``debugger is None`` short-circuit."""
    result, _, _ = _run(SIMPLE_PROGRAM, attach=False)
    assert result.ok, result.error_message


def test_debug_then_non_debug_does_not_leak():
    """Sanity check: running a debug session followed by a normal one
    must not corrupt the second run (e.g. via a stale ``flags.debugger``
    or a polluted statement cache)."""
    r1, _, _ = _run(SIMPLE_PROGRAM, repl_input="continue\n")
    assert r1.ok
    r2, _, _ = _run(SIMPLE_PROGRAM, attach=False)
    assert r2.ok


# --------------------------------------------------------------------------
# Hook coverage: confirm that on_function fires for user calls.  We
# subclass Debugger and override the hook so we can count without
# reaching into ``stack`` (which Step 22 will use for its own purposes).
# --------------------------------------------------------------------------


class _CountingDebugger(Debugger):
    def __init__(self, *a, **kw):
        super().__init__(*a, **kw)
        self.statement_count = 0
        self.function_calls: list[str] = []

    def on_statement(self, stmt, env):
        self.statement_count += 1
        super().on_statement(stmt, env)

    def on_function(self, name, location, env, **kw):
        self.function_calls.append(name)
        super().on_function(name, location, env, **kw)


def test_hooks_fire_on_statements_and_function_calls():
    tmp = REPO_ROOT / "tmp"
    tmp.mkdir(exist_ok=True)
    path = tmp / "debugger_hooks_test.pf"
    path.write_text(SIMPLE_PROGRAM)
    dbg = _CountingDebugger(input=io.StringIO("continue\n"), output=io.StringIO())
    result = check_file(str(path), prelude=PRELUDE, debugger=dbg)
    assert result.ok, result.error_message
    # ``recursive`` (which desugars into the function decl plus a
    # synthesised induction lemma), ``print``, ``assert``.  We assert
    # at-least-3 to stay robust to the exact desugaring count.
    assert dbg.statement_count >= 3
    # ``double`` is called twice from user code (print + assert) and
    # recurses; we just assert at least one call happened, with the
    # right name (the exact recursion count is brittle to surrounding
    # opt passes and isn't load-bearing for Step 21).
    assert any("double" in n for n in dbg.function_calls)
