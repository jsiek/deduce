"""Phase 5 / Step 25: Debug Adapter Protocol server for Deduce.

Speaks DAP over stdio.  Each editor launch spawns its own process;
there is no shared daemon -- a debug session blocks on user input
at every trap, so a daemon would have to serialize requests across
sessions for no benefit.  The cost of spinning up Python+lark per
launch (~3s with the .thm cache warm) is dwarfed by interactive
time.

Module entry point:

    python -m lsp.dap_server

The editor (VS Code via the ``debuggers`` contribution in Step 26,
or Emacs ``dap-mode``) speaks DAP to the process's stdin/stdout.
DAP messages are Content-Length-framed JSON; see the protocol spec
at https://microsoft.github.io/debug-adapter-protocol/ for the
canonical request/response/event shapes.

Supported request set (Step 25 minimum, per ``docs/lsp-plan.md``):

- lifecycle: ``initialize``, ``launch``, ``configurationDone``,
  ``disconnect``, ``terminate``
- breakpoints: ``setBreakpoints``, ``setFunctionBreakpoints``
- stepping: ``continue``, ``next``, ``stepIn``, ``stepOut``,
  ``pause``
- inspection: ``threads``, ``stackTrace``, ``scopes``,
  ``variables``, ``evaluate``

Out of scope: ``setExceptionBreakpoints`` (Deduce's static errors
aren't user-throwable), ``restart`` (just relaunch),
``goto`` (no jump-to-line semantics).
"""

from __future__ import annotations

import contextlib
import json
import os
import queue
import sys
import threading
import traceback as _traceback
from pathlib import Path
from typing import IO, Any, Optional, TypeAlias, cast


# ---------------------------------------------------------------------------
# Deduce environment bootstrap (mirrors lsp.lsp_server / lsp.mcp_server).
# ---------------------------------------------------------------------------


def _resolve_deduce_root() -> Path:
    env_root = os.environ.get("DEDUCE_ROOT")
    if env_root:
        return Path(env_root).resolve()
    return Path(__file__).resolve().parent.parent


_DEDUCE_ROOT = _resolve_deduce_root()
_LIB_DIR = _DEDUCE_ROOT / "lib"
_PSEUDO_ENTRY = str(_DEDUCE_ROOT / "deduce.py")
sys.argv = [_PSEUDO_ENTRY] + sys.argv[1:]
sys.setrecursionlimit(10000)
if str(_DEDUCE_ROOT) not in sys.path:
    sys.path.insert(0, str(_DEDUCE_ROOT))

from abstract_syntax import (  # noqa: E402
    add_import_directory,
    base_name,
    init_import_directories,
)
from flags import set_quiet_mode  # noqa: E402

set_quiet_mode(True)
init_import_directories()
add_import_directory(str(_LIB_DIR))

from lsp.debugger import (  # noqa: E402
    Debugger,
    DebuggerQuit,
    _Breakpoint,
    _StepMode,
)
from lsp.library import check_file  # noqa: E402

JSONDict: TypeAlias = dict[str, Any]


def _compute_default_prelude() -> tuple[str, ...]:
    if os.environ.get("DEDUCE_NO_STDLIB") == "1":
        return ()
    if not _LIB_DIR.is_dir():
        return ()
    return tuple(sorted(p.stem for p in _LIB_DIR.glob("*.pf")))


# Captured at module-load time so a later test (or downstream code)
# flipping ``DEDUCE_NO_STDLIB`` mid-process can't drop the prelude
# out from under us.  Mirrors ``lsp.lsp_server``'s pattern.
_PRELUDE: tuple[str, ...] = _compute_default_prelude()


def _default_prelude() -> tuple[str, ...]:
    return _PRELUDE


# ---------------------------------------------------------------------------
# DAP message framing.  Content-Length-prefixed JSON; CRLF separator
# between the header block and the body.
# ---------------------------------------------------------------------------


def read_message(stream: IO[bytes]) -> Optional[JSONDict]:
    """Read one DAP message from ``stream``.  Returns ``None`` on
    EOF (the editor closed the connection)."""
    headers: dict[str, str] = {}
    while True:
        raw = stream.readline()
        if not raw:
            return None
        line = raw.rstrip(b"\r\n").decode("ascii", errors="replace")
        if not line:
            break
        key, _, val = line.partition(":")
        headers[key.strip().lower()] = val.strip()
    n = int(headers.get("content-length", "0"))
    if n <= 0:
        return None
    body = stream.read(n)
    if len(body) < n:
        return None
    return cast(JSONDict, json.loads(body.decode("utf-8")))


def write_message(stream: IO[bytes], msg: JSONDict, lock: threading.Lock) -> None:
    """Send a DAP message.  ``lock`` serialises writes -- the
    program thread can emit ``stopped`` / ``output`` events while
    the reader thread is sending responses."""
    data = json.dumps(msg).encode("utf-8")
    header = f"Content-Length: {len(data)}\r\n\r\n".encode("ascii")
    with lock:
        stream.write(header + data)
        stream.flush()


# ---------------------------------------------------------------------------
# DAP-aware debugger.  Subclasses the text-mode ``Debugger`` so the
# hook machinery (step modes, breakpoints, skip rules, the
# pattern-bound locals, etc.) is shared verbatim.  Only the REPL
# turns into a stopped-event + step-request handshake.
# ---------------------------------------------------------------------------


class _DAPDebugger(Debugger):
    """A ``Debugger`` whose ``_repl`` blocks on a queue of step
    requests from the DAP server instead of reading text commands.

    The DAP server owns this instance and pokes its state from the
    reader thread (``set_file_breakpoints``, ``set_function_breakpoints``,
    ``step_trace``, etc.).  Concurrency is constrained by design:
    the program thread is paused inside ``_repl`` while DAP requests
    are processed, so reads of ``stack`` / ``_current_env`` from the
    reader thread happen against a quiescent debugger.
    """

    def __init__(self, server: "DAPServer"):
        # Bypass the readline-init in ``Debugger.__init__`` by passing
        # in-memory stream stand-ins.  We never read from ``input``;
        # ``output`` is unused except by base-class defensive prints
        # (which we don't expect to trigger during a DAP session).
        import io
        super().__init__(input=io.StringIO(""), output=io.StringIO())
        self._server = server
        # Reason to report on the next ``stopped`` event.  Updated
        # by ``on_statement`` / ``on_function`` / ``after_function``
        # so the editor sees ``breakpoint`` vs ``step`` vs ``pause``.
        self._stop_reason: str = "entry"

    # Override the trap entry points so we can label the stop reason
    # before delegating to the base-class pause machinery.

    def on_statement(self, stmt: Any, env: Any) -> None:
        # If the upcoming pause is breakpoint-driven, the base class
        # decides that via ``_should_pause_at_statement``.  Pick the
        # reason here based on which decision will fire.
        from abstract_syntax import Import
        if isinstance(stmt, Import):
            return
        self._stop_reason = self._reason_for_statement(stmt, env)
        super().on_statement(stmt, env)

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
        self._stop_reason = self._reason_for_function(name, location, defn_loc)
        super().on_function(
            name, location, env,
            params=params, args=args, subst=subst,
            defn_loc=defn_loc, display_args=display_args,
        )

    def after_function(self, name: Any, env: Any, return_value: Any = None) -> None:
        # The return-trap (Step 22) is always a step event from the
        # DAP point of view; no breakpoint fires on returns.
        self._stop_reason = "step"
        super().after_function(name, env, return_value=return_value)

    def _print(self, msg: str) -> None:
        """Override the text-mode helper so debugger-emitted messages
        (``-> call ...``, ``-> statement ...``, ``<- returned ...``,
        REPL output) reach the editor as DAP ``output`` events
        instead of disappearing into the per-instance ``StringIO``."""
        text = msg if msg.endswith("\n") else msg + "\n"
        self._server._send_event("output", {
            "category": "console",
            "output": text,
        })

    def _reason_for_statement(self, stmt: Any, env: Any) -> str:
        if any(bp.hits_at_statement(stmt, env, self) for bp in self.breakpoints):
            return "breakpoint"
        return "step"

    def _reason_for_function(self, name: str, location: Any, defn_loc: Any) -> str:
        if any(bp.hits_at_function(name, location, None, self)
               for bp in self.breakpoints):
            return "breakpoint"
        return "step"

    # The base class calls ``_repl`` whenever a trap fires; this is
    # the substitution point.

    def _repl(self) -> None:
        # Notify the editor that we're paused.  The reader thread
        # will respond with one of the step commands, which is fed
        # to us via the server's queue.
        self._server.notify_stopped(self._stop_reason)
        while True:
            cmd = self._server.wait_for_step()
            if cmd == "continue":
                self._step_mode = _StepMode.RUN
                return
            if cmd == "next":
                self._step_mode = _StepMode.NEXT
                self._step_depth = len(self.stack)
                return
            if cmd == "stepIn":
                self._step_mode = _StepMode.STEP
                return
            if cmd == "stepOut":
                if not self.stack:
                    self._step_mode = _StepMode.RUN
                else:
                    self._step_mode = _StepMode.FINISH
                    self._step_depth = len(self.stack)
                return
            if cmd == "pause":
                # Already paused -- ignore and wait for the next
                # real step command.
                continue
            if cmd == "disconnect":
                raise DebuggerQuit("disconnect")

    # Accessors used by the DAP server when answering DAP requests
    # while the program is paused inside ``_repl``.

    def stack_trace(self) -> list[JSONDict]:
        """Convert ``self.stack`` to DAP stack frames.  Frame 0 is
        the innermost call -- gdb / DAP convention.

        When ``self.stack`` is empty (we're paused at a top-level
        statement, not inside a function call) DAP still needs a
        frame to anchor the editor's UI on -- otherwise the
        ``stackTrace`` response is an empty array and the editor
        silently resumes.  Synthesize a single ``<top-level>`` frame
        pointing at ``_current_loc``."""
        frames: list[JSONDict] = []
        for i in range(len(self.stack) - 1, -1, -1):
            f = self.stack[i]
            depth = len(self.stack) - 1 - i
            loc = f.location
            entry: JSONDict = {
                "id": depth,
                "name": base_name(f.name) if isinstance(f.name, str) else str(f.name),
                "line": getattr(loc, "line", 0) or 0,
                "column": getattr(loc, "column", 0) or 0,
            }
            src_path = getattr(loc, "filename", None)
            if src_path:
                entry["source"] = {
                    "name": Path(src_path).name,
                    "path": src_path,
                }
            frames.append(entry)
        if not frames and self._current_loc is not None:
            top_entry: JSONDict = {
                "id": 0,
                "name": "<top-level>",
                "line": getattr(self._current_loc, "line", 0) or 0,
                "column": getattr(self._current_loc, "column", 0) or 0,
            }
            src_path = getattr(self._current_loc, "filename", None)
            if src_path:
                top_entry["source"] = {
                    "name": Path(src_path).name,
                    "path": src_path,
                }
            frames.append(top_entry)
        return frames

    def variables_for_frame(self, frame_id: int) -> list[JSONDict]:
        """Locals visible in the frame numbered ``frame_id`` (gdb
        convention, 0 = innermost)."""
        if frame_id < 0 or frame_id >= len(self.stack):
            return []
        frame = self.stack[len(self.stack) - 1 - frame_id]
        return [
            {"name": k, "value": str(v), "variablesReference": 0}
            for k, v in frame.params.items()
        ]

    def evaluate(self, expr: str) -> str:
        """``evaluate`` reuses the same machinery as the text
        REPL's ``print`` command."""
        if self._current_env is None:
            raise RuntimeError("no current scope")
        return str(self._eval_expr(expr, self._current_env))

    def set_file_breakpoints(
        self, path: str, dap_bps: list[JSONDict],
    ) -> list[JSONDict]:
        """Replace existing file:line breakpoints for ``path`` with
        the new set.  Returns a list of ``{verified, line}`` dicts
        in the same order as the input.
        """
        # Strip previous breakpoints whose spec started with this
        # file path -- DAP's contract is that ``setBreakpoints`` is
        # the canonical set for the given source.
        from os.path import basename as _bn
        keep: list[_Breakpoint] = []
        target_basename = _bn(path)
        for bp in self.breakpoints:
            if ":" in bp.spec:
                bp_file, _, _ = bp.spec.rpartition(":")
                if bp_file == path or bp_file == target_basename:
                    continue
            keep.append(bp)
        self.breakpoints = keep
        result: list[JSONDict] = []
        for entry in dap_bps:
            line = entry.get("line")
            if line is None:
                result.append({"verified": False})
                continue
            spec = f"{path}:{line}"
            condition = entry.get("condition") or None
            bp = _Breakpoint(id=self._next_bp_id, spec=spec, condition=condition)
            self._next_bp_id += 1
            self.breakpoints.append(bp)
            result.append({
                "verified": True,
                "id": bp.id,
                "line": line,
            })
        return result

    def set_function_breakpoints(self, dap_bps: list[JSONDict]) -> list[JSONDict]:
        """Replace existing function-name breakpoints with the new
        set.  Returns one ``{verified}`` entry per input."""
        # Drop existing bare-name breakpoints; line ones stay.
        self.breakpoints = [bp for bp in self.breakpoints if ":" in bp.spec]
        result: list[JSONDict] = []
        for entry in dap_bps:
            name = entry.get("name")
            if not name:
                result.append({"verified": False})
                continue
            condition = entry.get("condition") or None
            bp = _Breakpoint(id=self._next_bp_id, spec=name, condition=condition)
            self._next_bp_id += 1
            self.breakpoints.append(bp)
            result.append({"verified": True, "id": bp.id})
        return result


# ---------------------------------------------------------------------------
# DAP server: reads requests on a single thread, runs the user
# program on another, and exchanges signals via two queues.
# ---------------------------------------------------------------------------


class _DAPOutputCapture:
    """Stand-in for ``sys.stdout`` that forwards each line to a DAP
    ``output`` event.

    In CLI mode, Deduce's ``print`` statement writes the reduced
    value to ``sys.stdout`` and the user sees it in the terminal.
    In DAP mode, ``sys.stdout`` is the protocol wire; letting
    ``print`` write to it directly would corrupt JSON-RPC framing.
    Wrap the program's stdout in this capture so each output line
    becomes a DAP event the editor surfaces in its Debug Console /
    output panel.

    Lines are buffered until a newline arrives, so we don't fire
    one event per character.  ``flush()`` emits any partial line.
    """

    def __init__(self, server: "DAPServer", category: str = "stdout"):
        self._server = server
        self._category = category
        self._buf = ""

    def write(self, s: str) -> int:
        if not s:
            return 0
        self._buf += s
        while "\n" in self._buf:
            line, self._buf = self._buf.split("\n", 1)
            self._server._send_event("output", {
                "category": self._category,
                "output": line + "\n",
            })
        return len(s)

    def flush(self) -> None:
        if self._buf:
            self._server._send_event("output", {
                "category": self._category,
                "output": self._buf,
            })
            self._buf = ""

    def isatty(self) -> bool:
        return False

    def writable(self) -> bool:
        return True


class DAPServer:
    def __init__(
        self,
        instream: Optional[IO[bytes]] = None,
        outstream: Optional[IO[bytes]] = None,
    ):
        self._in = instream if instream is not None else sys.stdin.buffer
        self._out = outstream if outstream is not None else sys.stdout.buffer
        self._seq = 0
        self._write_lock = threading.Lock()
        # ``configurationDone`` releases this so the program thread
        # can start running.
        self._config_done = threading.Event()
        # Pending step commands from the reader thread to the
        # program thread.  ``_DAPDebugger._repl`` consumes one per
        # pause.  Capacity 16 is plenty -- the editor doesn't
        # double-queue under normal use.
        self._steps: queue.Queue[str] = queue.Queue(maxsize=16)
        # The debugger and program thread are created on ``launch``.
        self.debugger: Optional[_DAPDebugger] = None
        self._program_thread: Optional[threading.Thread] = None
        self._program_path: Optional[str] = None
        # Set once the program either finishes or quits.  The reader
        # loop checks this so a ``disconnect`` arriving after the
        # program ended still gets a response.
        self._program_done = threading.Event()
        self._terminated = False

    # --- protocol I/O ---

    def _next_seq(self) -> int:
        self._seq += 1
        return self._seq

    def _send_response(
        self, req: JSONDict, body: Optional[JSONDict] = None,
        success: bool = True, message: Optional[str] = None,
    ) -> None:
        resp: JSONDict = {
            "type": "response",
            "seq": self._next_seq(),
            "request_seq": req.get("seq", 0),
            "command": req.get("command", ""),
            "success": success,
        }
        if message:
            resp["message"] = message
        if body is not None:
            resp["body"] = body
        write_message(self._out, resp, self._write_lock)

    def _send_event(self, event: str, body: Optional[JSONDict] = None) -> None:
        msg: JSONDict = {
            "type": "event",
            "seq": self._next_seq(),
            "event": event,
        }
        if body is not None:
            msg["body"] = body
        write_message(self._out, msg, self._write_lock)

    # --- public callbacks from _DAPDebugger ---

    def notify_stopped(self, reason: str) -> None:
        self._send_event("stopped", {
            "reason": reason,
            "threadId": 1,
            "allThreadsStopped": True,
        })

    def wait_for_step(self) -> str:
        """Block the program thread until the reader thread feeds
        in a step command."""
        return self._steps.get()

    # --- main loop ---

    def run(self) -> None:
        try:
            while not self._terminated:
                msg = read_message(self._in)
                if msg is None:
                    break
                if msg.get("type") != "request":
                    continue
                self._dispatch(msg)
        finally:
            # Best-effort: wake any blocked _repl so the program
            # thread can unwind.
            try:
                self._steps.put_nowait("disconnect")
            except queue.Full:
                pass

    def _dispatch(self, req: JSONDict) -> None:
        cmd = req.get("command", "")
        handler = getattr(self, f"_h_{cmd}", None)
        if handler is None:
            self._send_response(
                req, success=False, message=f"unknown DAP request: {cmd}",
            )
            return
        try:
            handler(req)
        except Exception as e:
            self._send_response(
                req, success=False,
                message=f"{type(e).__name__}: {e}\n{_traceback.format_exc()}",
            )

    # --- request handlers ---

    def _h_initialize(self, req: JSONDict) -> None:
        body = {
            "supportsConditionalBreakpoints": True,
            "supportsFunctionBreakpoints": True,
            "supportsEvaluateForHovers": True,
            "supportsConfigurationDoneRequest": True,
        }
        self._send_response(req, body=body)
        # ``initialized`` tells the editor it can now send
        # setBreakpoints / setFunctionBreakpoints / configurationDone.
        self._send_event("initialized")

    def _h_launch(self, req: JSONDict) -> None:
        args = req.get("arguments", {}) or {}
        program = args.get("program")
        if not program:
            self._send_response(
                req, success=False, message="launch requires 'program'",
            )
            return
        self._program_path = program
        self.debugger = _DAPDebugger(self)
        self._send_response(req)
        self._program_thread = threading.Thread(
            target=self._run_program, name="deduce-debugger", daemon=True,
        )
        self._program_thread.start()

    def _h_setBreakpoints(self, req: JSONDict) -> None:
        args = req.get("arguments", {}) or {}
        source = args.get("source", {}) or {}
        path = source.get("path", "")
        bps = args.get("breakpoints", []) or []
        if self.debugger is None:
            self._send_response(req, success=False, message="not launched")
            return
        result = self.debugger.set_file_breakpoints(path, bps)
        self._send_response(req, body={"breakpoints": result})

    def _h_setFunctionBreakpoints(self, req: JSONDict) -> None:
        args = req.get("arguments", {}) or {}
        bps = args.get("breakpoints", []) or []
        if self.debugger is None:
            self._send_response(req, success=False, message="not launched")
            return
        result = self.debugger.set_function_breakpoints(bps)
        self._send_response(req, body={"breakpoints": result})

    def _h_configurationDone(self, req: JSONDict) -> None:
        self._send_response(req)
        self._config_done.set()

    def _h_continue(self, req: JSONDict) -> None:
        self._steps.put("continue")
        self._send_response(req, body={"allThreadsContinued": True})

    def _h_next(self, req: JSONDict) -> None:
        self._steps.put("next")
        self._send_response(req)

    def _h_stepIn(self, req: JSONDict) -> None:
        self._steps.put("stepIn")
        self._send_response(req)

    def _h_stepOut(self, req: JSONDict) -> None:
        self._steps.put("stepOut")
        self._send_response(req)

    def _h_pause(self, req: JSONDict) -> None:
        self._steps.put("pause")
        self._send_response(req)

    def _h_threads(self, req: JSONDict) -> None:
        self._send_response(req, body={
            "threads": [{"id": 1, "name": "main"}],
        })

    def _h_stackTrace(self, req: JSONDict) -> None:
        frames = self.debugger.stack_trace() if self.debugger else []
        self._send_response(req, body={
            "stackFrames": frames,
            "totalFrames": len(frames),
        })

    def _h_scopes(self, req: JSONDict) -> None:
        # One "Locals" scope per frame.  ``variablesReference`` ==
        # ``frameId`` so the editor's follow-up ``variables`` request
        # arrives with enough info to look up the right frame.
        args = req.get("arguments", {}) or {}
        frame_id = args.get("frameId", 0)
        self._send_response(req, body={
            "scopes": [{
                "name": "Locals",
                "variablesReference": frame_id + 1,
                "expensive": False,
            }],
        })

    def _h_variables(self, req: JSONDict) -> None:
        args = req.get("arguments", {}) or {}
        var_ref = args.get("variablesReference", 0)
        if self.debugger is None or var_ref == 0:
            self._send_response(req, body={"variables": []})
            return
        # We encoded frame_id as variablesReference + 1.
        vars_ = self.debugger.variables_for_frame(var_ref - 1)
        self._send_response(req, body={"variables": vars_})

    def _h_evaluate(self, req: JSONDict) -> None:
        args = req.get("arguments", {}) or {}
        expr = args.get("expression", "")
        if self.debugger is None:
            self._send_response(req, success=False, message="not launched")
            return
        try:
            value = self.debugger.evaluate(expr)
        except Exception as e:
            self._send_response(req, success=False, message=str(e))
            return
        self._send_response(req, body={
            "result": value,
            "variablesReference": 0,
        })

    def _h_disconnect(self, req: JSONDict) -> None:
        self._send_response(req)
        self._terminated = True
        # Wake the program thread if it's blocked in ``_repl``.
        try:
            self._steps.put_nowait("disconnect")
        except queue.Full:
            pass

    def _h_terminate(self, req: JSONDict) -> None:
        self._h_disconnect(req)

    # --- program thread ---

    def _run_program(self) -> None:
        # Block until the editor has finished configuration
        # (setBreakpoints + configurationDone).
        self._config_done.wait()
        if self._terminated or self._program_path is None:
            return
        prelude = _default_prelude()
        # Route the user program's ``print`` output -- and any
        # incidental ``print``s from inside the proof checker -- to
        # DAP ``output`` events.  Without this redirect, Deduce's
        # ``print`` statement writes the reduced value to
        # ``sys.stdout``, which in DAP mode IS the protocol wire;
        # the editor never displays it and at worst the editor's
        # JSON-RPC parser chokes on the unframed bytes.
        capture = _DAPOutputCapture(self)
        try:
            with contextlib.redirect_stdout(capture):
                try:
                    result = check_file(
                        self._program_path, prelude=prelude, debugger=self.debugger,
                    )
                    # A failed CheckResult (parse/type/proof error)
                    # doesn't raise from ``check_file`` -- surface it
                    # as a DAP ``output`` event so the editor (and
                    # our tests) can see what went wrong instead of
                    # mysteriously not producing a ``stopped`` event.
                    if not result.ok and not isinstance(result.exception, DebuggerQuit):
                        self._send_event("output", {
                            "category": "stderr",
                            "output": f"{result.error_message}\n",
                        })
                except DebuggerQuit:
                    pass
                except Exception as e:
                    self._send_event("output", {
                        "category": "stderr",
                        "output": f"{type(e).__name__}: {e}\n{_traceback.format_exc()}",
                    })
                finally:
                    capture.flush()
        finally:
            self._program_done.set()
            self._send_event("terminated")


def main() -> None:
    DAPServer().run()


if __name__ == "__main__":
    main()
