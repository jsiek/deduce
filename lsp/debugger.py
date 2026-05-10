"""Step 21 (Phase 5): the ``Debugger`` core.

A gdb-style stepper for the *functional* fragment of Deduce: top-level
``Print`` / ``Assert`` statements and any user-function calls evaluated
during their reduction.  Stepping through proofs is out of scope (see
``docs/lsp-plan.md`` Phase 5 for the full plan).

This module contains only the foundation:

- ``Debugger`` owns all per-session state (no module-level globals).
- Hook callbacks (``on_statement`` / ``after_statement`` / ``on_function``
  / ``after_function``) are called from ``proof_checker.check_proofs`` and
  ``abstract_syntax.do_function_call`` / ``Call.reduce``.
- A bare-minimum text REPL: ``continue`` (resume) and ``quit`` (abort)
  are wired up so smoke tests can drive a session through stdio.

Step 22 adds step / next / finish / break / print / list / where; this
PR keeps the surface small so the wiring is independently reviewable.

The instance is one-shot: a fresh ``Debugger`` is created for each
``lsp.library.check_file`` call that opts in.  Hooks are no-ops unless a
debugger is attached to the active session via ``flags.set_debugger``.
PR #269's module-level globals are deliberately not carried forward --
they leaked across calls in a long-lived daemon (see
``docs/lsp-plan.md`` Phase 5 / Step 21 prelude-bootstrap rationale).
"""

from __future__ import annotations

import sys
from dataclasses import dataclass, field
from typing import IO, Optional


class DebuggerQuit(Exception):
    """Raised by the REPL when the user types ``quit``.

    ``lsp.library.check_file`` catches this and translates the run into
    a normal ``CheckResult`` with ``ok=False`` and a synthetic message,
    rather than letting the exception escape as a Python traceback.
    """


@dataclass
class _Frame:
    """One entry in the call stack maintained by ``on_function`` /
    ``after_function``.  Step 22's ``where`` / ``up`` / ``down`` will
    consume this; for Step 21 it just exists so the depth-tracking step
    modes (``next`` / ``finish``) have something to count.
    """

    name: str
    location: object  # lark Meta or "<unknown>"
    params: dict = field(default_factory=dict)


class Debugger:
    """A live debugger session.

    One instance per ``check_file`` call.  Constructed by the CLI
    (``deduce.py --debug``) or the DAP adapter (Step 25); attached via
    ``flags.set_debugger`` for the duration of one ``check_file`` and
    detached in a ``finally``.

    The hooks are intentionally tiny -- they're called from hot paths
    in the reducer and need to add no measurable overhead when the
    debugger is detached.  When attached, they delegate to ``_pause``,
    which prints the current location and reads a command from
    ``self.input``.

    Attributes:
        input:    REPL input stream (default ``sys.stdin``).
        output:   REPL output stream (default ``sys.stdout``).
        stack:    Call stack -- pushed by ``on_function``, popped by
                  ``after_function``.  Used by Step 22's depth-based
                  step modes; exposed here so tests can assert on it.
        stop_on_next_statement:  When True, the next ``on_statement``
                  call traps.  Set by the CLI just before handing off
                  to ``check_file`` so the user lands in the REPL on
                  the first user-file statement.
    """

    def __init__(
        self,
        input: Optional[IO[str]] = None,
        output: Optional[IO[str]] = None,
    ):
        self.input = input if input is not None else sys.stdin
        self.output = output if output is not None else sys.stdout
        self.stack: list[_Frame] = []
        self.stop_on_next_statement: bool = True
        self._last_command: str = ""
        # When True, every hook is a no-op -- the user typed ``continue``
        # and we should stay out of the way until either a breakpoint
        # is hit (Step 22) or the run finishes.  Step 21's REPL has no
        # breakpoints, so once continued, we don't trap again.
        self._running_to_end: bool = False

    # ------------------------------------------------------------------
    # Hook callbacks -- called from proof_checker / abstract_syntax.
    # Each is a one-line dispatch so non-debug runs (no debugger
    # attached) skip the work entirely; ``flags.get_debugger()`` returns
    # ``None`` and the caller never enters these methods.
    # ------------------------------------------------------------------

    def on_statement(self, stmt) -> None:
        """Called before evaluating each top-level statement in
        ``check_proofs``.  For Step 21, only ``Print`` and ``Assert``
        meaningfully execute user code -- but the hook fires for every
        statement so Step 24 (tactic stepping) can opt in without
        moving the call site.
        """
        if self._running_to_end:
            return
        if not self.stop_on_next_statement:
            return
        self.stop_on_next_statement = False
        loc = getattr(stmt, "location", None)
        self._print(f"-> statement at {self._format_loc(loc)}: {stmt}")
        self._repl()

    def after_statement(self, stmt) -> None:
        """Symmetric counterpart to ``on_statement``.  Step 22 uses this
        for depth-based ``next`` re-arming; Step 21's body is empty but
        the hook is wired so future steps don't have to re-touch the
        call sites.
        """
        return

    def on_function(
        self,
        name: str,
        location,
        params: Optional[list] = None,
        args: Optional[list] = None,
    ) -> None:
        """Called before reducing a user-function body.  Pushes a frame
        and -- in Step 22 -- pauses if the function is a breakpoint
        target.  Step 21 only maintains the stack.
        """
        params_dict: dict = {}
        if params is not None and args is not None:
            from abstract_syntax import base_name
            for p, a in zip(params, args):
                key = base_name(p) if isinstance(p, str) else str(p)
                params_dict[key] = a
        self.stack.append(_Frame(name=name, location=location, params=params_dict))

    def after_function(self, name: str, return_value=None) -> None:
        """Pops the matching frame.  Defensive against a mismatched
        push/pop (shouldn't happen in well-formed runs but a corrupted
        stack would silently break Step 22's depth tracking, so keep
        it simple and best-effort).
        """
        if self.stack:
            self.stack.pop()

    # ------------------------------------------------------------------
    # REPL -- Step 21 ships only ``continue`` and ``quit`` so the wiring
    # can be reviewed without dragging in command parsing.  Step 22
    # extends this with the full gdb-parity command set.
    # ------------------------------------------------------------------

    def _repl(self) -> None:
        """Read commands until one resumes execution.  Empty input
        replays the last command -- the gdb convention, kept from PR
        #269.  Unknown commands print an error and re-prompt.
        """
        while True:
            self._write("(deduce-debug) ")
            try:
                line = self.input.readline()
            except (EOFError, KeyboardInterrupt):
                line = ""
            if line == "":
                # EOF on stdin -- treat as quit so non-interactive
                # callers (CI, dead pipes) terminate cleanly instead
                # of looping forever.
                raise DebuggerQuit("EOF on debugger input")
            line = line.strip()
            if line == "":
                line = self._last_command
            else:
                self._last_command = line
            tokens = line.split()
            if not tokens:
                continue
            cmd, args = tokens[0], tokens[1:]
            if cmd in ("continue", "c"):
                self._running_to_end = True
                return
            if cmd in ("quit", "q"):
                raise DebuggerQuit("user quit")
            self._print(f"unrecognized command: {cmd!r} (Step 21 supports: continue, quit)")

    # ------------------------------------------------------------------
    # Output helpers -- one call site each so a future DAP adapter can
    # subclass and route to JSON-RPC events instead of writing to a
    # text stream.
    # ------------------------------------------------------------------

    def _print(self, msg: str) -> None:
        self._write(msg + "\n")

    def _write(self, s: str) -> None:
        self.output.write(s)
        self.output.flush()

    @staticmethod
    def _format_loc(loc) -> str:
        if loc is None:
            return "<unknown>"
        line = getattr(loc, "line", None)
        col = getattr(loc, "column", None)
        if line is not None and col is not None:
            return f"{line}:{col}"
        return "<unknown>"
