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

import sys
from dataclasses import dataclass, field
from os.path import basename
from typing import IO, Optional


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
    """

    name: str
    location: object
    env: object
    params: dict = field(default_factory=dict)


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

    def hits_at_statement(self, stmt, env, dbg: "Debugger") -> bool:
        if ":" not in self.spec:
            # function-name breakpoints fire in on_function, not here
            return False
        if not self._loc_matches(getattr(stmt, "location", None)):
            return False
        return self._condition_holds(env, dbg)

    def hits_at_function(
        self, name: str, location, env, dbg: "Debugger"
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

    def _loc_matches(self, loc) -> bool:
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

    def _condition_holds(self, env, dbg: "Debugger") -> bool:
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
    ):
        self.input = input if input is not None else sys.stdin
        self.output = output if output is not None else sys.stdout
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
        self._current_stmt = None
        self._current_env = None
        self._current_loc = None
        # Mirror of ``_current_stmt`` for use by ``list`` -- the very
        # first ``on_statement`` is the only place we learn the user's
        # source path.  Subsequent hooks (function calls) preserve
        # this so ``list`` still works inside a call.
        self._source_path: Optional[str] = None

    # ------------------------------------------------------------------
    # Hook callbacks -- called from proof_checker / abstract_syntax.
    # ------------------------------------------------------------------

    def on_statement(self, stmt, env) -> None:
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

    def after_statement(self, stmt, env) -> None:
        return

    def on_function(
        self,
        name: str,
        location,
        env,
        params: Optional[list] = None,
        args: Optional[list] = None,
        subst: Optional[dict] = None,
    ) -> None:
        params_dict: dict = {}
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
        frame = _Frame(
            name=name, location=location, env=env, params=params_dict,
        )
        self.stack.append(frame)
        self._current_env = env
        self._current_loc = location
        if not self._should_pause_at_function(name, location, env):
            return
        self._frame_cursor = -1
        from abstract_syntax import base_name
        pretty = ", ".join(
            f"{k}={v}" for k, v in params_dict.items()
        ) if params_dict else ""
        self._print(
            f"-> call {base_name(name)}({pretty}) at "
            f"{self._format_loc(location)}"
        )
        self._repl()

    def after_function(self, name: str, env, return_value=None) -> None:
        if self.stack:
            self.stack.pop()

    # ------------------------------------------------------------------
    # Pause-decision logic.  Single source of truth for every hook.
    # ------------------------------------------------------------------

    def _should_pause_at_statement(self, stmt, env) -> bool:
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

    def _should_pause_at_function(self, name, location, env) -> bool:
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
        if self._step_mode == _StepMode.STOP:
            return False
        return any(bp.hits_at_function(name, location, env, self)
                   for bp in self.breakpoints)

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
        while True:
            self._write("(deduce-debug) ")
            try:
                line = self.input.readline()
            except (EOFError, KeyboardInterrupt):
                line = ""
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

    def _command_table(self) -> dict:
        """Map of command verb -> handler.  Aliases get their own
        entries so the typo-suggestion routine and tab-completion can
        treat them uniformly.

        Each handler returns ``True`` to resume execution (release the
        REPL) or ``False`` to re-prompt.
        """
        t = {
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

        ``spec`` is either ``file:line`` or a bare function name.  No
        validation here -- a typo just produces a breakpoint that
        never fires, which is consistent with how gdb behaves on
        symbols not yet loaded.
        """
        if not args:
            self._print("usage: break <file:line | function> [if <expr>]")
            return False
        spec, condition = self._split_condition(args)
        bp = _Breakpoint(id=self._next_bp_id, spec=spec, condition=condition)
        self._next_bp_id += 1
        self.breakpoints.append(bp)
        cond_str = f" if {condition}" if condition else ""
        self._print(f"breakpoint {bp.id} set: {spec}{cond_str}")
        return False

    def _cmd_delete(self, args: str) -> bool:
        """``delete``  or  ``delete <id>...`` -- remove breakpoints."""
        if not args:
            self.breakpoints.clear()
            self._print("all breakpoints deleted")
            return False
        ids_to_remove = set()
        for piece in args.split():
            try:
                ids_to_remove.add(int(piece))
            except ValueError:
                self._print(f"not a breakpoint id: {piece!r}")
                return False
        before = len(self.breakpoints)
        self.breakpoints = [
            bp for bp in self.breakpoints if bp.id not in ids_to_remove
        ]
        self._print(f"deleted {before - len(self.breakpoints)} breakpoint(s)")
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
            "commands: continue/c, step/s, next/n, finish/fin,\n"
            "          break/b <spec>[ if <expr>], delete/d [id...],\n"
            "          info breakpoints, print/p <expr>, list/l,\n"
            "          where/bt, up, down, locals, quit/q"
        )
        return False

    # ------------------------------------------------------------------
    # Helpers.
    # ------------------------------------------------------------------

    def _focus_env(self):
        """Env to use for ``print`` / ``locals`` based on ``up``/``down``.
        Defaults to the most recent hook env (the focused / innermost
        frame), but the user can navigate."""
        if self._frame_cursor == -1:
            return self._current_env
        idx = len(self.stack) - 1 - self._frame_cursor
        if 0 <= idx < len(self.stack):
            return self.stack[idx].env
        return self._current_env

    def _focus_params(self) -> dict:
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

    def _eval_expr(self, expr_text: str, env):
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
            _p.token_list = list(_p.lark_parser.lex(expr_text))
            _p.current_position = 0
            _p.check_closest_kwd = False
            term = _p.parse_term()
        finally:
            (_p.token_list, _p.current_position,
             _p.filename, _p.check_closest_kwd) = saved

        # Build a uniquify env from the proof-checker env.  Each base
        # name maps to a list of the uniquified candidates -- which
        # is exactly what overload resolution at uniquify-time uses.
        u_env: dict = {"≠": ["≠"], "=": ["="]}
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
        set_reduce_all(True)
        set_eval_all(True)
        # Suppress traps while evaluating the user's debugger
        # expression: the reduction will fire the same hooks the
        # surrounding session uses, and re-trapping inside ``print``
        # would force the user to ``continue`` through every
        # recursive call of the function they wanted printed.
        # Breakpoints would still fire if RUN (gdb does this too),
        # but the hooks also mutate ``_current_*`` and ``stack`` --
        # save/restore those so the surrounding session resumes
        # with the same "where am I" state.
        saved = (
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
             self.stack) = saved
            set_eval_all(False)
            set_reduce_all(False)

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

