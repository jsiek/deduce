"""Acceptance tests for Phase 5 / Step 23 (REPL UX polish).

We can't drive readline directly from a test (it needs a real
terminal), so we hit the pure-function side of the completion
machinery via ``Debugger._complete(text, line, begidx)``.  That's
what the readline-facing ``_completer`` ultimately calls.
"""

from __future__ import annotations

import io
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from lsp.debugger import Debugger, _Breakpoint  # noqa: E402
from lsp.library import check_file  # noqa: E402


SIMPLE_PROGRAM = """\
recursive double(Nat) -> Nat {
  double(zero) = zero
  double(suc(n')) = suc(suc(double(n')))
}

print double(suc(zero))
"""

PRELUDE = ("Nat",)


def _fresh_dbg() -> Debugger:
    """A Debugger not yet driven by a real session.  ``_complete``
    is called directly; no env / stack is required for command-name
    completion."""
    return Debugger(input=io.StringIO(""), output=io.StringIO())


# --------------------------------------------------------------------------
# Command-name completion.  ``begidx == 0`` means we're at the start
# of the line.
# --------------------------------------------------------------------------


def test_complete_command_prefix_matches_unique():
    dbg = _fresh_dbg()
    opts = dbg._complete("contin", "contin", 0)
    assert opts == ["continue"]


def test_complete_command_prefix_matches_multiple():
    """``c`` is the prefix of both ``c`` (the alias) and ``continue``
    plus ``clear``.  All three should be returned, sorted."""
    dbg = _fresh_dbg()
    opts = dbg._complete("c", "c", 0)
    assert "c" in opts
    assert "continue" in opts
    assert "clear" in opts
    # Sorted for stable display.
    assert opts == sorted(opts)


def test_complete_empty_command_returns_everything():
    """Empty text returns all command verbs -- one tab-tab at the
    start of an empty line should show every command."""
    dbg = _fresh_dbg()
    opts = dbg._complete("", "", 0)
    # A handful of canonical verbs should be present.
    for verb in ("continue", "step", "next", "break", "clear",
                 "delete", "print", "list", "quit"):
        assert verb in opts


def test_complete_unknown_prefix_returns_empty():
    dbg = _fresh_dbg()
    assert dbg._complete("zzz", "zzz", 0) == []


# --------------------------------------------------------------------------
# Argument completion.  Requires a live debugger session so the env
# and the breakpoint list are populated.
# --------------------------------------------------------------------------


def _run_to_first_pause(source: str = SIMPLE_PROGRAM):
    """Drive ``check_file`` to its first pause and quit immediately,
    returning the Debugger instance with its session state filled in
    (current env, breakpoints, etc.)."""
    tmp = REPO_ROOT / "tmp"
    tmp.mkdir(exist_ok=True)
    path = tmp / "debugger_completion_test.pf"
    path.write_text(source)
    dbg = Debugger(input=io.StringIO("quit\n"), output=io.StringIO())
    check_file(str(path), prelude=PRELUDE, debugger=dbg)
    return dbg


def test_complete_print_completes_scope_names():
    """``print z<TAB>`` should propose names visible in scope, e.g.
    ``zero`` from the ``Nat`` prelude."""
    dbg = _run_to_first_pause()
    # After "print z" the cursor is just past z; begidx is 6 (the
    # space after "print" is at index 5; the z starts at index 6).
    opts = dbg._complete("z", "print z", 6)
    assert "zero" in opts


def test_complete_break_completes_function_names():
    """``b doub<TAB>`` should complete to ``double``."""
    dbg = _run_to_first_pause()
    opts = dbg._complete("doub", "b doub", 2)
    assert "double" in opts


def test_complete_clear_completes_breakpoint_specs():
    """``clear <TAB>`` should propose existing breakpoint specs so
    the user can finish what they typed to ``break``."""
    dbg = _run_to_first_pause()
    dbg.breakpoints = [
        _Breakpoint(id=1, spec="foo.pf:14"),
        _Breakpoint(id=2, spec="double"),
    ]
    opts = dbg._complete("doub", "clear doub", 6)
    assert "double" in opts


def test_complete_delete_completes_breakpoint_ids():
    """``d <TAB>`` should propose active breakpoint ids as strings."""
    dbg = _run_to_first_pause()
    dbg.breakpoints = [
        _Breakpoint(id=1, spec="foo.pf:14"),
        _Breakpoint(id=2, spec="double"),
    ]
    opts = dbg._complete("", "d ", 2)
    assert "1" in opts
    assert "2" in opts


def test_complete_unknown_command_returns_empty():
    """An argument position for a command we don't know about (e.g.
    ``locals foo``) returns no candidates."""
    dbg = _run_to_first_pause()
    opts = dbg._complete("foo", "locals foo", 7)
    assert opts == []


# --------------------------------------------------------------------------
# Persistent history.  We pass an explicit ``history_file`` and check
# that the file is created.  Skipped when readline is unavailable
# (the only environment where this matters).
# --------------------------------------------------------------------------


def test_history_file_is_optional(tmp_path):
    """A Debugger created with StringIO streams (the test path)
    should not touch the filesystem at all -- history writing is
    skipped because readline isn't attached."""
    histfile = tmp_path / "no_such_file"
    Debugger(input=io.StringIO(""), output=io.StringIO(),
             history_file=str(histfile))
    assert not histfile.exists()


def test_save_history_is_noop_without_readline(tmp_path):
    """Even called directly, ``_save_history`` should be a no-op
    when ``readline`` isn't attached (the StringIO/test case)."""
    histfile = tmp_path / "h"
    dbg = Debugger(input=io.StringIO(""), output=io.StringIO(),
                   history_file=str(histfile))
    dbg._save_history()
    assert not histfile.exists()
