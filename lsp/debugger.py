"""Phase 5 / Steps 21-22 (debugger).

A gdb-style stepper for the *functional* fragment of Deduce: top-level
``Print`` / ``Assert`` statements and any user-function calls evaluated
during their reduction.  Stepping through proofs is out of scope (see
``docs/lsp-plan.md`` Phase 5).

This module is a single in-process ``Debugger`` class (no module
globals) plus its supporting types.  Created by
``deduce.py --debug`` or by the DAP adapter (Step 25, not yet built);
attached to one ``check_file`` call via ``flags.set_debugger`` and
detached in a ``finally``.

Step 21 stood up the foundation and a tiny ``continue`` / ``quit``
REPL.  Step 22 fills in the gdb-parity command set: step modes
keyed on call-stack depth (so ``next`` doesn't re-trap on recursion,
fixing PR #269's bug), file:line and function-name breakpoints with
optional ``if`` conditions, expression evaluation against the live
proof-checker env, source listing, stack navigation, and locals
inspection.
"""

from __future__ import annotations

import os
import sys
from dataclasses import dataclass, field
from os.path import basename
from typing import IO, Any, Callable, Optional, cast


DEFAULT_HISTORY_FILE = os.path.expanduser("~/.config/deduce/debug_history")


class DebuggerQuit(Exception):
    """Raised by the REPL when the user types ``quit`` or input EOFs.

    ``lsp.library.check_file`` catches this and translates the run into
    a normal failed ``CheckResult`` rather than letting the exception
    leak as a Python traceback.
    """


class _StepMode:
    """Marker constants for the step state machine.

    Plain strings (not enum.Enum) keep ``__repr__`` readable in
    test failure output and avoid a transitive import.
    """

    RUN = "RUN"        # only pause at breakpoints
    STEP = "STEP"      # pause at the very next hook
    NEXT = "NEXT"      # pause when depth <= depth_at_command
    FINISH = "FINISH"  # pause when depth < depth_at_command
    STOP = "STOP"      # initial: pause at the next ``on_statement``


@dataclass
class _Frame:
    """One entry in the call stack maintained by ``on_function`` /
    ``after_function``.

    ``env`` is the env at the call site; ``params`` is the {param ->
    arg} dict captured when we entered the frame.  Both are consumed
    by ``up`` / ``down`` / ``locals`` / ``print``.

    ``is_skipped`` records the skip-policy decision at push time so
    ``after_function`` can suppress the return-trap symmetrically:
    if we didn't trap on entry into a prelude function, we don't
    want to trap on its exit either.
    """

    name: str
    location: object
    env: object
    params: dict[str, Any] = field(default_factory=dict)
    is_skipped: bool = False
    # The call's positional arguments, as the user wrote them.
    # Used by both the entry trap header and the matching return
    # trap so the unwinding view is self-describing.
    display_args: list[Any] = field(default_factory=list)


@dataclass
class _Breakpoint:
    """A user-set breakpoint.

    ``spec`` is either ``"file:line"`` (e.g. ``"foo.pf:42"``) or a bare
    function name (matched against ``base_name(name)``).  ``condition``
    is the raw expression text from ``b ... if <expr>``; ``None`` means
    unconditional.
    """

    id: int
    spec: str
    condition: Optional[str] = None

    # --- pause-decision helpers ---

    def hits_at_statement(self, stmt: Any, env: Any, dbg: "Debugger") -> bool:
        if ":" not in self.spec:
            # function-name breakpoints fire in on_function, not here
            return False
        if not self._loc_matches(getattr(stmt, "location", None)):
            return False
        return self._condition_holds(env, dbg)

    def hits_at_function(
        self, name: str, location: Any, env: Any, dbg: "Debugger"
    ) -> bool:
        if ":" in self.spec:
            # file:line breakpoint -- match against the function's
            # source location.  Surfaces both as ``b foo.pf:42`` on a
            # definition site and as ``b foo.pf:42`` on a use site;
            # users don't have to know which.
            if not self._loc_matches(location):
                return False
            return self._condition_holds(env, dbg)
        # bare function name
        from abstract_syntax import base_name
        if name == self.spec or base_name(name) == self.spec:
            return self._condition_holds(env, dbg)
        return False

    # --- internals ---

    def _loc_matches(self, loc: Any) -> bool:
        if loc is None:
            return False
        file_part, _, line_part = self.spec.rpartition(":")
        try:
            target_line = int(line_part)
        except ValueError:
            return False
        if getattr(loc, "line", None) != target_line:
            return False
        loc_file = getattr(loc, "filename", None)
        if loc_file is None:
            return False
        if file_part in (loc_file, basename(loc_file)):
            return True
        return False

    def _condition_holds(self, env: Any, dbg: "Debugger") -> bool:
        if self.condition is None:
            return True
        try:
            result = dbg._eval_expr(self.condition, env)
        except Exception as e:  # pragma: no cover -- defensive
            dbg._print(f"breakpoint {self.id} condition error: {e}")
            return False
        # Truthy iff the reduced term is the literal ``true``.
        from abstract_syntax import Bool
        if isinstance(result, Bool):
            return bool(result.value)
        return False


class Debugger:
    """A live debugger session.

    One instance per ``check_file`` call.  ``flags.set_debugger`` makes
    it active; ``lsp.library.check_file`` is responsible for that
    attach/detach.
    """

    def __init__(
        self,
        input: Optional[IO[str]] = None,
        output: Optional[IO[str]] = None,
        history_file: Optional[str] = None,
    ):
        self.input = input if input is not None else sys.stdin
        self.output = output if output is not None else sys.stdout
        # Use GNU readline (line editing + tab completion + history)
        # only when the REPL is talking to a real terminal.  Tests
        # pass StringIO objects; for those we fall back to plain
        # ``readline()`` on the stream and skip the history file
        # entirely so unit tests don't poke the filesystem.
        self._readline: Optional[Any] = None
        self._history_file: Optional[str] = None
        if (self.input is sys.stdin and self.output is sys.stdout
                and sys.stdin.isatty()):
            try:
                import readline as _readline
                self._readline = _readline
                self._history_file = (
                    history_file if history_file is not None
                    else DEFAULT_HISTORY_FILE
                )
                self._setup_readline()
            except ImportError:  # pragma: no cover -- readline absent
                pass
        # Step 21 carried this name to mean "first statement traps";
        # Step 22 generalizes via ``_StepMode.STOP`` for the same effect.
        self.stack: list[_Frame] = []
        self.breakpoints: list[_Breakpoint] = []
        self._next_bp_id = 1
        self._step_mode = _StepMode.STOP
        # Depth at which ``next`` / ``finish`` was requested.  Compared
        # against ``len(self.stack)`` at later hook firings.  Resets on
        # every step-mode-changing command.
        self._step_depth = 0
        self._last_command = ""
        # ``_frame_cursor`` is a peek-only pointer used by ``up`` /
        # ``down`` / ``locals``.  ``-1`` means "the synthetic top
        # frame" (the statement currently trapped on -- not in
        # self.stack).  ``i >= 0`` indexes into ``self.stack`` from
        # the bottom; visually printed as gdb-style frame numbers
        # where 0 is the innermost.
        self._frame_cursor = -1
        # Filled by ``on_statement`` and ``on_function``; the REPL
        # consumes them for ``print`` (env) and ``list`` (location).
        self._current_stmt: Optional[Any] = None
        self._current_env: Optional[Any] = None
        self._current_loc: Optional[Any] = None
        # Mirror of ``_current_stmt`` for use by ``list`` -- the very
        # first ``on_statement`` is the only place we learn the user's
        # source path.  Subsequent hooks (function calls) preserve
        # this so ``list`` still works inside a call.
        self._source_path: Optional[str] = None
        # Two separate visibility policies (Step 22, refined after
        # smoke testing).  gdb conflates them; Deduce splits them
        # because the use cases differ:
        #
        # Skip (``_skip_file_substrs``): the gdb-style policy.
        # ``step`` treats a call into a skipped function as ``next``
        # -- skip into the body is suppressed -- but the frame
        # still gets pushed, so ``where`` shows the call, ``locals``
        # works inside it, and ``break <name>`` can drill in.  This
        # is what users want for the prelude: they care that they're
        # *inside* ``length`` even if they don't want to step
        # through 30 lines of UInt arithmetic.
        #
        # Invisible (``_invisible_function_names``): the stronger
        # policy.  No frame, no trap, no breakpoint match -- the
        # function might as well not exist.  Reserved for
        # implementation hacks the user model doesn't have, like
        # ``lit`` (the Nat-identity marker used to tag literal
        # numerals for auto-rewrite -- ``lib/NatDefs.pf``).
        #
        # Step 23 will add ``skip`` / ``unskip`` / ``hide`` /
        # ``unhide`` REPL commands; for now we ship defaults.
        self._skip_file_substrs: list[str] = ["lib/"]
        self._invisible_function_names: set[str] = {"lit"}

    # ------------------------------------------------------------------
    # Hook callbacks -- called from proof_checker / abstract_syntax.
    # ------------------------------------------------------------------

    def on_statement(self, stmt: Any, env: Any) -> None:
        # gdb doesn't trap on ``#include``; the debugger doesn't trap
        # on ``import``.  Imports are pure declarations -- no
        # user-visible side effect to step through, no body for
        # ``list`` to point at.  This rule applies uniformly: the
        # 32 prelude prepends synthesised by ``lsp.library`` *and*
        # any user-written ``import M`` that survives dedup.
        from abstract_syntax import Import
        if isinstance(stmt, Import):
            return
        self._current_stmt = stmt
        self._current_env = env
        self._current_loc = getattr(stmt, "location", None)
        sp = getattr(self._current_loc, "filename", None)
        if sp:
            self._source_path = sp
        if not self._should_pause_at_statement(stmt, env):
            return
        self._frame_cursor = -1  # snap focus back to here
        self._print(f"-> statement at {self._format_loc(self._current_loc)}: {stmt}")
        self._repl()

    def after_statement(self, stmt: Any, env: Any) -> None:
        return

    def on_function(
        self,
        name: str,
        location: Any,
        env: Any,
        params: Optional[list[Any]] = None,
        args: Optional[list[Any]] = None,
        subst: Optional[dict[Any, Any]] = None,
        defn_loc: Any = None,
        display_args: Optional[list[Any]] = None,
    ) -> None:
        # ``defn_loc`` is the function's *defining* site (from its
        # body's ``Meta``).  ``location`` is the call site.  For
        # generic calls in particular these differ: the TermInst
        # wrapping the RecFun keeps its synthesised location at the
        # user's call site, not at the prelude file where the
        # function actually lives.  Visibility decisions key on
        # ``defn_loc``.
        if self._is_invisible(name):
            # Invisible: no frame, no trap, no breakpoint match.
            # ``after_function`` will see nothing to pop.  Keeps the
            # depth-based step machinery honest (``next`` / ``finish``
            # measure visible frames only).
            return
        params_dict: dict[str, Any] = {}
        from abstract_syntax import base_name
        if params is not None and args is not None:
            for p, a in zip(params, args):
                key = base_name(p) if isinstance(p, str) else str(p)
                params_dict[key] = a
        # ``subst`` carries the bindings introduced by pattern matching
        # on the first arg of a recursive call -- the most common way
        # Deduce functions name their inputs.  Merging it into the
        # frame's locals lets ``locals`` and ``print n'`` work even
        # when the call site has no positional ``params``.
        if subst:
            for k, v in subst.items():
                key = base_name(k) if isinstance(k, str) else str(k)
                params_dict[key] = v
        skipped = self._is_skipped(defn_loc)
        args_for_display = list(display_args) if display_args else []
        frame = _Frame(
            name=name, location=location, env=env, params=params_dict,
            is_skipped=skipped, display_args=args_for_display,
        )
        self.stack.append(frame)
        self._current_env = env
        self._current_loc = location
        if not self._should_pause_at_function(name, location, env, defn_loc):
            return
        self._frame_cursor = -1
        pretty = ", ".join(str(a) for a in args_for_display)
        self._print(
            f"-> call {base_name(name)}({pretty}) at "
            f"{self._format_loc(location)}"
        )
        self._repl()

    def after_function(
        self, name: str, env: Any, return_value: Any = None
    ) -> None:
        # No matching frame iff ``on_function`` chose not to push
        # (invisible function).  Nothing to pop, nothing to trap.
        if not self.stack:
            return
        # Defensive: only pop if the top frame matches the name we're
        # leaving.  A mismatch can happen on the boundary if a hook
        # is added or removed without symmetry; popping unconditionally
        # would silently corrupt the depth count.
        if self.stack[-1].name != name:
            return
        popped = self.stack.pop()
        # Refresh ``_current_env`` / ``_current_loc`` to the caller's
        # frame so ``locals`` and ``print`` evaluated at the return
        # trap see the caller's scope, not the just-returned frame's.
        # When popping the *last* frame we're back at top-level --
        # fall back to the current statement's location so the
        # editor's UI shows where we actually are (the statement
        # whose reduction we're partway through), not the stale
        # location of the function we just returned from.
        if self.stack:
            top = self.stack[-1]
            self._current_env = top.env
            self._current_loc = top.location
        elif self._current_stmt is not None:
            stmt_loc = getattr(self._current_stmt, "location", None)
            if stmt_loc is not None:
                self._current_loc = stmt_loc
        # gdb-style: ``step`` at the last line of a function pops you
        # back to the caller.  Without trapping on returns, a ``step``
        # at a base-case body cascades through every unwinding frame
        # in one keystroke -- you blast past 5 nested ``count_down``
        # returns and land at the next top-level statement, losing the
        # "we returned from each frame" UX.  Trap here:
        # - STEP: every return is interesting (gdb's ``step``), EXCEPT
        #   skipped frames -- if we didn't trap on entry into the
        #   prelude function, don't trap on exit either.
        # - NEXT / FINISH: trap once when we cross below the depth at
        #   which the mode was armed.  Same skip exception.
        if self._should_pause_after_function(popped):
            from abstract_syntax import base_name
            self._frame_cursor = -1
            # Echo the call signature so the user can tell which
            # frame is unwinding -- five identical ``returned from
            # count_down`` lines are useless during a recursive
            # unwind.  Use the *original* call args (stored at push
            # time), not the pattern-bound names: that way the base
            # case shows ``count_down(zero)`` rather than the empty
            # ``count_down()`` (the pattern consumes the arg, so
            # ``params`` is empty for the base case).  Return value
            # goes on an indented second line so it's visually
            # distinct from the call header.
            pretty = ", ".join(str(a) for a in popped.display_args)
            self._print(f"<- returned from {base_name(name)}({pretty})")
            self._print(f"     = {return_value}")
            self._repl()

    def _should_pause_after_function(self, popped: _Frame) -> bool:
        if popped.is_skipped:
            return False
        if self._step_mode == _StepMode.STEP:
            return True
        if self._step_mode in (_StepMode.NEXT, _StepMode.FINISH):
            return len(self.stack) < self._step_depth
        return False

    def _is_invisible(self, name: str) -> bool:
        """The stronger policy: the function is hidden entirely --
        no frame, no trap, no breakpoint match.  See the
        ``_invisible_function_names`` doc in ``__init__``."""
        from abstract_syntax import base_name
        bn = base_name(name) if isinstance(name, str) else ""
        return bn in self._invisible_function_names

    def _is_skipped(self, defn_loc: Any) -> bool:
        """The gdb-style policy: ``step`` doesn't trap on entry, but
        the function still pushes a frame.  Keyed on the function's
        defining-file location (so generic calls don't slip past via
        the call-site location).  See the ``_skip_file_substrs`` doc
        in ``__init__``."""
        fn = getattr(defn_loc, "filename", None)
        if fn is None:
            return False
        return any(substr in fn for substr in self._skip_file_substrs)

    # ------------------------------------------------------------------
    # Pause-decision logic.  Single source of truth for every hook.
    # ------------------------------------------------------------------

    def _should_pause_at_statement(self, stmt: Any, env: Any) -> bool:
        if self._step_mode in (_StepMode.STEP, _StepMode.STOP):
            return True
        if self._step_mode == _StepMode.NEXT:
            if len(self.stack) <= self._step_depth:
                return True
        elif self._step_mode == _StepMode.FINISH:
            if len(self.stack) < self._step_depth:
                return True
        # RUN: only stop at a breakpoint
        return any(bp.hits_at_statement(stmt, env, self)
                   for bp in self.breakpoints)

    def _should_pause_at_function(
        self, name: str, location: Any, env: Any, defn_loc: Any = None
    ) -> bool:
        # Breakpoints always fire, regardless of step mode and
        # regardless of whether the file is in the skip list -- the
        # whole point of ``break length`` after ``skip lib/`` is to
        # drill *into* a skipped function deliberately.
        if any(bp.hits_at_function(name, location, env, self)
               for bp in self.breakpoints):
            return True
        # Skip rule: ``step`` into a function defined in a skipped
        # file becomes ``next`` -- the frame is pushed (so ``where``
        # / ``locals`` still work) but we don't trap on entry.
        if self._is_skipped(defn_loc):
            return False
        if self._step_mode == _StepMode.STEP:
            return True
        if self._step_mode == _StepMode.NEXT:
            # The frame for *this* call has already been pushed, so
            # ``len(self.stack)`` is depth-after-entry; ``next`` should
            # NOT pause inside the new call.  Hence the strict ``<=``
            # comparison: it's only true when we re-emerge at a depth
            # ≤ the depth at which the user typed ``next``.  PR #269
            # keyed step-over on the source location, which re-trapped
            # on recursion -- that bug is what this depth check fixes.
            return False
        if self._step_mode == _StepMode.FINISH:
            return False
        # STOP only triggers in on_statement; in on_function it's a no-op
        # so the first frame's call doesn't double-trap.
        return False

    # ------------------------------------------------------------------
    # REPL.
    # ------------------------------------------------------------------

    def _repl(self) -> None:
        """Read commands until one resumes execution.

        Empty input replays the last command (gdb convention, kept from
        PR #269).  Unknown commands print an error and re-prompt.  EOF
        on input raises ``DebuggerQuit`` so non-interactive callers
        (CI, dead pipes) terminate cleanly.
        """
        commands = self._command_table()
        try:
            while True:
                line = self._read_input()
                if line == "":
                    raise DebuggerQuit("EOF on debugger input")
                line = line.strip()
                if line == "":
                    line = self._last_command
                else:
                    self._last_command = line
                if line == "":
                    continue
                cmd, _, rest = line.partition(" ")
                handler = commands.get(cmd)
                if handler is None:
                    from edit_distance import closest_keyword
                    suggestion = closest_keyword(cmd, list(commands.keys()))
                    hint = f" (did you mean {suggestion!r}?)" if suggestion else ""
                    self._print(f"unrecognized command: {cmd!r}{hint}")
                    continue
                try:
                    resume = handler(rest.strip())
                except DebuggerQuit:
                    raise
                except Exception as e:
                    self._print(f"error running {cmd!r}: {e}")
                    continue
                if resume:
                    return
        finally:
            # Save history on every REPL exit (including via
            # ``DebuggerQuit``) so a session that crashes mid-flow
            # doesn't lose the user's typing.  Cheap when readline
            # isn't active (no-op).
            self._save_history()

    def _read_input(self) -> str:
        """One line of REPL input, ``""`` on EOF.  Routes through
        Python's ``input()`` when readline is active so line editing
        / completion / history all work; falls back to plain stream
        reads for the StringIO-driven test path."""
        if self._readline is not None:
            try:
                return input("(deduce-debug) ") + "\n"
            except (EOFError, KeyboardInterrupt):
                # Ctrl-D / Ctrl-C end the session cleanly.
                return ""
        self._write("(deduce-debug) ")
        try:
            return self.input.readline()
        except (EOFError, KeyboardInterrupt):
            return ""

    def _setup_readline(self) -> None:
        """Install the completer and load the history file.  Called
        once during ``__init__`` when readline is available."""
        r = self._readline
        history_file = self._history_file
        assert r is not None and history_file is not None
        r.set_completer(self._completer)
        r.parse_and_bind("tab: complete")
        # ``readline`` defaults its delimiters to include ``-``,
        # which breaks completion on names like ``operator-`` and
        # on anything else with a hyphen.  Restrict to whitespace --
        # that's the only thing that separates tokens in our REPL
        # syntax.
        r.set_completer_delims(" \t\n")
        try:
            os.makedirs(os.path.dirname(history_file), exist_ok=True)
        except OSError:  # pragma: no cover -- best-effort
            return
        if os.path.exists(history_file):
            try:
                r.read_history_file(history_file)
            except OSError:  # pragma: no cover -- defensive
                pass

    def _save_history(self) -> None:
        if self._readline is None or self._history_file is None:
            return
        try:
            self._readline.write_history_file(self._history_file)
        except OSError:  # pragma: no cover -- best-effort
            pass

    # ------------------------------------------------------------------
    # Tab completion.  ``_completer`` is the readline-facing entry
    # point; ``_complete`` is a pure function we test directly so
    # readline doesn't need to be in the loop.
    # ------------------------------------------------------------------

    def _completer(self, text: str, state: int) -> Optional[str]:
        """``readline`` calls this repeatedly with increasing
        ``state`` until it returns ``None``.  Each call returns one
        candidate."""
        if self._readline is None:
            return None
        line = self._readline.get_line_buffer()
        begidx = self._readline.get_begidx()
        opts = self._complete(text, line, begidx)
        return opts[state] if state < len(opts) else None

    def _complete(self, text: str, line: str, begidx: int) -> list[str]:
        """Pure-function completion.  ``text`` is the partial token
        under the cursor, ``line`` is the whole input buffer, and
        ``begidx`` is the start index of ``text`` within ``line``.

        Context rules:
        - When ``begidx == 0`` we're completing the command verb --
          return matching command names.
        - Otherwise the first token of ``line`` is the command;
          dispatch to ``_completion_options`` for argument hints.
        """
        if begidx == 0:
            verbs = sorted(self._command_table().keys())
            return [v for v in verbs if v.startswith(text)]
        prefix_tokens = line[:begidx].split()
        cmd = prefix_tokens[0] if prefix_tokens else ""
        return self._completion_options(cmd, text)

    def _completion_options(self, cmd: str, text: str) -> list[str]:
        """Candidate list for the argument position of ``cmd``."""
        if cmd in ("print", "p"):
            return self._sorted_matches(self._scope_names(), text)
        if cmd in ("break", "b"):
            return self._sorted_matches(self._scope_names(), text)
        if cmd == "clear":
            return self._sorted_matches(
                [bp.spec for bp in self.breakpoints] + self._scope_names(),
                text,
            )
        if cmd in ("delete", "d"):
            return self._sorted_matches(
                [str(bp.id) for bp in self.breakpoints], text,
            )
        return []

    def _scope_names(self) -> list[str]:
        """Identifiers visible at the current pause: the proof-checker
        env's bound names (base form, so the uniquified ``foo.s0_...``
        becomes ``foo``) plus the focused frame's pattern bindings."""
        if self._current_env is None:
            return []
        from abstract_syntax import base_name
        names: set[str] = set()
        for unique in self._current_env.dict.keys():
            names.add(base_name(unique))
        for k in self._focus_params().keys():
            names.add(k)
        return list(names)

    @staticmethod
    def _sorted_matches(seq: list[str], text: str) -> list[str]:
        return sorted(set(s for s in seq if s.startswith(text)))

    def _command_table(self) -> dict[str, Callable[[str], bool]]:
        """Map of command verb -> handler.  Aliases get their own
        entries so the typo-suggestion routine and tab-completion can
        treat them uniformly.

        Each handler returns ``True`` to resume execution (release the
        REPL) or ``False`` to re-prompt.
        """
        t: dict[str, Callable[[str], bool]] = {
            "continue": self._cmd_continue,
            "c":        self._cmd_continue,
            "step":     self._cmd_step,
            "s":        self._cmd_step,
            "next":     self._cmd_next,
            "n":        self._cmd_next,
            "finish":   self._cmd_finish,
            "fin":      self._cmd_finish,
            "break":    self._cmd_break,
            "b":        self._cmd_break,
            "delete":   self._cmd_delete,
            "d":        self._cmd_delete,
            "clear":    self._cmd_clear,
            "info":     self._cmd_info,
            "print":    self._cmd_print,
            "p":        self._cmd_print,
            "list":     self._cmd_list,
            "l":        self._cmd_list,
            "where":    self._cmd_where,
            "bt":       self._cmd_where,
            "up":       self._cmd_up,
            "down":     self._cmd_down,
            "locals":   self._cmd_locals,
            "quit":     self._cmd_quit,
            "q":        self._cmd_quit,
            "help":     self._cmd_help,
            "h":        self._cmd_help,
        }
        return t

    # ------------------------------------------------------------------
    # Command handlers.  Each takes the (already-stripped) arg string
    # and returns True to release the REPL, False to re-prompt.
    # ------------------------------------------------------------------

    def _cmd_continue(self, args: str) -> bool:
        self._step_mode = _StepMode.RUN
        return True

    def _cmd_step(self, args: str) -> bool:
        self._step_mode = _StepMode.STEP
        return True

    def _cmd_next(self, args: str) -> bool:
        # Re-trap at the same depth (or shallower) -- step *over* any
        # new function calls that happen between now and the next hook.
        self._step_mode = _StepMode.NEXT
        self._step_depth = len(self.stack)
        return True

    def _cmd_finish(self, args: str) -> bool:
        # Run until we return from the current frame.  If the stack is
        # empty we're at the top level; ``finish`` collapses to a
        # ``continue`` rather than running off the end.
        if not self.stack:
            self._step_mode = _StepMode.RUN
        else:
            self._step_mode = _StepMode.FINISH
            self._step_depth = len(self.stack)
        return True

    def _cmd_break(self, args: str) -> bool:
        """``break <spec>``  or  ``break <spec> if <expr>``.

        ``spec`` is one of:
          - a bare line number (defaults to the current source file)
          - ``file:line``
          - a function name

        No validation here -- a typo just produces a breakpoint that
        never fires, which is consistent with how gdb behaves on
        symbols not yet loaded.
        """
        if not args:
            self._print(
                "usage: break <line | file:line | function> [if <expr>]"
            )
            return False
        spec, condition = self._split_condition(args)
        # gdb-style convenience: bare line number means "the current
        # source file".  Requires we know the current source path --
        # ``on_statement`` sets ``_source_path`` on the very first
        # trap, so this is available by the time the REPL accepts
        # input.
        if spec.isdigit():
            if self._source_path is None:
                self._print(
                    "cannot resolve bare line number: no current "
                    "source file (try ``file:line`` form)"
                )
                return False
            spec = f"{self._source_path}:{spec}"
        bp = _Breakpoint(id=self._next_bp_id, spec=spec, condition=condition)
        self._next_bp_id += 1
        self.breakpoints.append(bp)
        cond_str = f" if {condition}" if condition else ""
        self._print(f"breakpoint {bp.id} set: {spec}{cond_str}")
        return False

    def _cmd_delete(self, args: str) -> bool:
        """``delete`` (all) or ``delete <id>...`` -- remove
        breakpoints by id (gdb convention).  Non-integer args error
        out -- use ``clear <line|file:line|name>`` for spec-based
        removal.
        """
        if not args:
            self.breakpoints.clear()
            self._print("all breakpoints deleted")
            return False
        ids_to_remove: set[int] = set()
        for piece in args.split():
            if not piece.isdigit():
                self._print(
                    f"delete expects breakpoint ids; "
                    f"use ``clear {piece}`` for spec-based removal"
                )
                return False
            ids_to_remove.add(int(piece))
        before = len(self.breakpoints)
        self.breakpoints = [
            bp for bp in self.breakpoints if bp.id not in ids_to_remove
        ]
        self._print(f"deleted {before - len(self.breakpoints)} breakpoint(s)")
        return False

    def _cmd_clear(self, args: str) -> bool:
        """``clear <spec>`` -- remove the breakpoint(s) at the given
        location.  ``spec`` is one of:
          - a bare line number (defaults to the current source file)
          - ``file:line``
          - a function name
        Bare line numbers resolve against the current source file,
        mirroring ``break``'s convenience.  Multiple breakpoints at
        the same spec are all removed.
        """
        if not args:
            self._print(
                "usage: clear <line | file:line | name>"
            )
            return False
        # Same bare-line rewrite as ``_cmd_break`` so ``clear 13`` is
        # symmetric with ``break 13``.
        spec = args.strip()
        if spec.isdigit():
            if self._source_path is None:
                self._print(
                    "cannot resolve bare line number: no current "
                    "source file (try ``file:line`` form)"
                )
                return False
            spec = f"{self._source_path}:{spec}"
        matches = [bp.id for bp in self.breakpoints if bp.spec == spec]
        if not matches:
            self._print(f"no breakpoint at {spec!r}")
            return False
        before = len(self.breakpoints)
        match_set = set(matches)
        self.breakpoints = [
            bp for bp in self.breakpoints if bp.id not in match_set
        ]
        self._print(f"cleared {before - len(self.breakpoints)} breakpoint(s)")
        return False

    def _cmd_info(self, args: str) -> bool:
        """``info breakpoints`` (or ``info b``) -- list active bps.

        Other ``info`` subcommands are out of scope for Step 22; the
        ``info args`` request from the plan is covered by ``locals``.
        """
        sub = args.split()[0] if args else ""
        if sub in ("breakpoints", "break", "b", ""):
            if not self.breakpoints:
                self._print("no breakpoints")
            else:
                for bp in self.breakpoints:
                    cond = f" if {bp.condition}" if bp.condition else ""
                    self._print(f"  {bp.id}: {bp.spec}{cond}")
            return False
        self._print(f"unknown info subcommand: {sub!r}")
        return False

    def _cmd_print(self, args: str) -> bool:
        if not args:
            self._print("usage: print <expr>")
            return False
        env = self._focus_env()
        params = self._focus_params()
        # Shortcut: if the user typed a bare param name, look it up
        # directly.  Avoids the parser+reduce round-trip for the
        # 90%-common case and dodges the ``rec_desc_parser``'s
        # module-level state.  PR #269 also did this.
        if args in params:
            self._print(str(params[args]))
            return False
        try:
            result = self._eval_expr(args, env)
        except Exception as e:
            self._print(f"could not evaluate {args!r}: {e}")
            return False
        self._print(str(result))
        return False

    def _cmd_list(self, args: str) -> bool:
        path = self._source_path
        if path is None or self._current_loc is None:
            self._print("(no source location)")
            return False
        line = getattr(self._current_loc, "line", None)
        if line is None:
            self._print("(no source location)")
            return False
        try:
            lines = open(path, "r", encoding="utf-8").read().splitlines()
        except OSError as e:
            self._print(f"could not read {path}: {e}")
            return False
        lo = max(1, line - 5)
        hi = min(len(lines), line + 5)
        width = len(str(hi))
        for n in range(lo, hi + 1):
            marker = "->" if n == line else "  "
            self._print(f"{marker} {n:>{width}}  {lines[n - 1]}")
        return False

    def _cmd_where(self, args: str) -> bool:
        """gdb-style: frame 0 is the innermost (top of the stack)."""
        if not self.stack:
            self._print("(no active call stack)")
            return False
        # Print bottom (outermost) to top (innermost) so the most
        # recent frame is at the bottom of the output -- the format a
        # reader expects to read top-down chronologically.  Frame
        # numbers go 0..N-1 from innermost outward, which is the gdb
        # convention; ``up`` increases the number, ``down`` decreases.
        from abstract_syntax import base_name
        for i in range(len(self.stack) - 1, -1, -1):
            frame = self.stack[i]
            depth = len(self.stack) - 1 - i
            cursor = " *" if (
                (self._frame_cursor == -1 and depth == 0) or
                (self._frame_cursor == depth)
            ) else "  "
            self._print(
                f"{cursor}#{depth}  {base_name(frame.name)} at "
                f"{self._format_loc(frame.location)}"
            )
        return False

    def _cmd_up(self, args: str) -> bool:
        if not self.stack:
            self._print("(no active call stack)")
            return False
        current = max(self._frame_cursor, 0)
        new = current + 1
        if new >= len(self.stack):
            self._print("already at the outermost frame")
            return False
        self._frame_cursor = new
        return self._cmd_where("")

    def _cmd_down(self, args: str) -> bool:
        if not self.stack or self._frame_cursor <= 0:
            self._print("already at the innermost frame")
            return False
        self._frame_cursor -= 1
        return self._cmd_where("")

    def _cmd_locals(self, args: str) -> bool:
        params = self._focus_params()
        if not params:
            self._print("(no locals in this frame)")
            return False
        for k, v in params.items():
            self._print(f"  {k} = {v}")
        return False

    def _cmd_quit(self, args: str) -> bool:
        raise DebuggerQuit("user quit")

    def _cmd_help(self, args: str) -> bool:
        self._print(
            "commands:\n"
            "  continue/c, step/s, next/n, finish/fin, quit/q\n"
            "  break/b <line | file:line | name>[ if <expr>]   -- set breakpoint\n"
            "  delete/d [id...]                                 -- remove breakpoints by id (all if no arg)\n"
            "  clear <line | file:line | name>                  -- remove breakpoint(s) at a location\n"
            "  info breakpoints                                 -- list breakpoints with ids\n"
            "  print/p <expr>                                   -- evaluate expression\n"
            "  list/l                                           -- show source around current line\n"
            "  where/bt, up, down                               -- call stack navigation\n"
            "  locals                                           -- show bindings in current frame"
        )
        return False

    # ------------------------------------------------------------------
    # Helpers.
    # ------------------------------------------------------------------

    def _focus_env(self) -> Optional[Any]:
        """Env to use for ``print`` / ``locals`` based on ``up``/``down``.
        Defaults to the most recent hook env (the focused / innermost
        frame), but the user can navigate."""
        if self._frame_cursor == -1:
            return self._current_env
        idx = len(self.stack) - 1 - self._frame_cursor
        if 0 <= idx < len(self.stack):
            return self.stack[idx].env
        return self._current_env

    def _focus_params(self) -> dict[str, Any]:
        if self._frame_cursor == -1:
            if not self.stack:
                return {}
            return self.stack[-1].params
        idx = len(self.stack) - 1 - self._frame_cursor
        if 0 <= idx < len(self.stack):
            return self.stack[idx].params
        return {}

    @staticmethod
    def _split_condition(args: str) -> tuple[str, Optional[str]]:
        """Split ``"foo:42 if x > 0"`` into ``("foo:42", "x > 0")``.

        ``" if "`` (with surrounding spaces) is the delimiter -- this
        is brittle if the user writes ``if`` without spaces, but the
        gdb convention is the same and it keeps parsing free.
        """
        marker = " if "
        idx = args.find(marker)
        if idx < 0:
            return args.strip(), None
        return args[:idx].strip(), args[idx + len(marker):].strip()

    def _eval_expr(self, expr_text: str, env: Any) -> Any:
        """Parse ``expr_text`` as a term, uniquify it against the
        proof-checker env's bindings, and reduce.

        ``rec_desc_parser`` keeps the token stream and current
        position in module-level globals -- snapshot and restore
        around the parse so we don't corrupt a parser state the proof
        checker still owns.  Same idea for ``filename``.

        Uniquify normally takes a ``dict[base_name -> [unique_names]]``
        (see ``abstract_syntax.Var.uniquify``); the proof-checker env
        stores the inverse (``unique_name -> Binding``), so we invert
        it here.  We also fold in the current frame's params, since
        they're what the user most often wants to print.
        """
        import rec_desc_parser as _p
        from abstract_syntax import UniquifyContext, base_name

        saved = (
            _p.token_list, _p.current_position,
            _p.filename, _p.check_closest_kwd,
        )
        try:
            _p.set_filename("<debugger>")
            _p.init_parser()
            assert _p.lark_parser is not None
            _p.token_list = list(_p.lark_parser.lex(expr_text))
            _p.current_position = 0
            _p.check_closest_kwd = False
            parse_term: Callable[[], Any] = getattr(_p, "parse_term")
            term = parse_term()
        finally:
            (_p.token_list, _p.current_position,
             _p.filename, _p.check_closest_kwd) = saved

        # Build a uniquify env from the proof-checker env.  Each base
        # name maps to a list of the uniquified candidates -- which
        # is exactly what overload resolution at uniquify-time uses.
        u_env: dict[str, list[str]] = {"≠": ["≠"], "=": ["="]}
        for unique in env.dict.keys():
            b = base_name(unique)
            u_env.setdefault(b, []).append(unique)
        # Also expose the current frame's params under their base
        # names so ``print x`` works inside a function call.  PR #269
        # only supported bare identifiers via this path; here it
        # composes with the parser, so ``print x + 1`` works too.
        params = self._focus_params()
        for k in params.keys():
            u_env.setdefault(k, []).append(k)

        ctx = UniquifyContext()
        term = term.uniquify(u_env, ctx)
        # Force full reduction so the printed value matches what
        # ``print`` / ``assert`` would compute in the proof checker.
        from abstract_syntax import set_eval_all, set_reduce_all
        set_reduce = cast(Callable[[bool], None], set_reduce_all)
        set_eval = cast(Callable[[bool], None], set_eval_all)
        set_reduce(True)
        set_eval(True)
        # Suppress traps while evaluating the user's debugger
        # expression: the reduction will fire the same hooks the
        # surrounding session uses, and re-trapping inside ``print``
        # would force the user to ``continue`` through every
        # recursive call of the function they wanted printed.
        # Breakpoints would still fire if RUN (gdb does this too),
        # but the hooks also mutate ``_current_*`` and ``stack`` --
        # save/restore those so the surrounding session resumes
        # with the same "where am I" state.
        saved_state = (
            self._step_mode, self._step_depth,
            self._current_env, self._current_loc, self._current_stmt,
            list(self.stack),
        )
        self._step_mode = _StepMode.RUN
        try:
            return term.reduce(env)
        finally:
            (self._step_mode, self._step_depth,
             self._current_env, self._current_loc, self._current_stmt,
             self.stack) = saved_state
            set_eval(False)
            set_reduce(False)

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
    def _format_loc(loc: Any) -> str:
        if loc is None:
            return "<unknown>"
        line = getattr(loc, "line", None)
        col = getattr(loc, "column", None)
        if line is not None and col is not None:
            return f"{line}:{col}"
        return "<unknown>"
