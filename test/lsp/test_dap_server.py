"""Acceptance test for Phase 5 / Step 25 (DAP adapter).

Drives ``lsp.dap_server.DAPServer`` over in-memory pipes with a
small DAP client harness.  No real terminal, no subprocesses --
``os.pipe`` plus a fake-client thread is enough to exercise the
full request/response/event protocol.
"""

from __future__ import annotations

import io
import json
import os
import queue
import sys
import threading
import time
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from lsp.dap_server import DAPServer  # noqa: E402


# --------------------------------------------------------------------------
# In-memory DAP client.  Connects a pair of ``os.pipe()`` file
# descriptors to the server's stdin/stdout, then exposes a
# request/response/event API over the protocol framing.
# --------------------------------------------------------------------------


class _Client:
    """A minimal DAP client used by tests.  Sends framed JSON via a
    pipe, reads framed JSON back, and routes responses to the
    waiting caller while events go onto a queue for assertions."""

    def __init__(self, to_server: int, from_server: int):
        self._send = os.fdopen(to_server, "wb", buffering=0)
        self._recv = os.fdopen(from_server, "rb", buffering=0)
        self._seq = 0
        self._pending: dict = {}      # request_seq -> threading.Event
        self._responses: dict = {}    # request_seq -> response body
        self.events: queue.Queue = queue.Queue()
        self._stop = False
        self._reader = threading.Thread(
            target=self._read_loop, daemon=True, name="dap-test-client",
        )
        self._reader.start()

    def _read_loop(self) -> None:
        while not self._stop:
            headers: dict = {}
            while True:
                line = self._recv.readline()
                if not line:
                    return
                line = line.rstrip(b"\r\n").decode("ascii", errors="replace")
                if not line:
                    break
                key, _, val = line.partition(":")
                headers[key.strip().lower()] = val.strip()
            n = int(headers.get("content-length", "0"))
            body_bytes = self._recv.read(n)
            if len(body_bytes) < n:
                return
            msg = json.loads(body_bytes.decode("utf-8"))
            if msg.get("type") == "response":
                rseq = msg.get("request_seq")
                self._responses[rseq] = msg
                ev = self._pending.pop(rseq, None)
                if ev is not None:
                    ev.set()
            elif msg.get("type") == "event":
                self.events.put(msg)

    def request(self, command: str, arguments=None, timeout: float = 5.0) -> dict:
        self._seq += 1
        seq = self._seq
        msg = {
            "seq": seq,
            "type": "request",
            "command": command,
        }
        if arguments is not None:
            msg["arguments"] = arguments
        ev = threading.Event()
        self._pending[seq] = ev
        data = json.dumps(msg).encode("utf-8")
        header = f"Content-Length: {len(data)}\r\n\r\n".encode("ascii")
        self._send.write(header + data)
        if not ev.wait(timeout):
            raise TimeoutError(f"no response to {command}")
        return self._responses.pop(seq)

    def wait_for_event(self, event_name: str, timeout: float = 5.0) -> dict:
        deadline = time.monotonic() + timeout
        # Collect intermediate events so a timeout error can name
        # them -- otherwise diagnosing a flaky DAP test is awful.
        seen: list = []
        while time.monotonic() < deadline:
            try:
                evt = self.events.get(timeout=0.1)
            except queue.Empty:
                continue
            if evt.get("event") == event_name:
                return evt
            seen.append(evt)
        raise TimeoutError(
            f"no '{event_name}' event in {timeout}s; "
            f"saw {[e.get('event') for e in seen]} bodies={[e.get('body') for e in seen]}"
        )

    def close(self) -> None:
        self._stop = True
        try:
            self._send.close()
        except OSError:
            pass
        try:
            self._recv.close()
        except OSError:
            pass


# --------------------------------------------------------------------------
# Test fixture: a running DAPServer wired to an in-memory client.
# --------------------------------------------------------------------------


@pytest.fixture
def dap_session(tmp_path):
    client_to_server_r, client_to_server_w = os.pipe()
    server_to_client_r, server_to_client_w = os.pipe()
    server_in = os.fdopen(client_to_server_r, "rb", buffering=0)
    server_out = os.fdopen(server_to_client_w, "wb", buffering=0)
    server = DAPServer(instream=server_in, outstream=server_out)
    server_thread = threading.Thread(
        target=server.run, name="dap-test-server", daemon=True,
    )
    server_thread.start()
    client = _Client(client_to_server_w, server_to_client_r)
    try:
        yield server, client, tmp_path
    finally:
        # Drain the session deterministically.  The program thread
        # is daemon=True; if we just close the pipes and move on,
        # a thread blocked mid-``check_file`` (e.g. inside the
        # prelude bootstrap) keeps mutating shared module state
        # (prelude caches, name counters, ``flags.debugger``) while
        # the next test runs -- producing flaky failures with no
        # visible owner.  Send ``disconnect``, wait for the program
        # thread to actually finish, then close pipes.
        try:
            client.request("disconnect", timeout=2.0)
        except (TimeoutError, OSError):
            pass
        prog_thread = server._program_thread
        if prog_thread is not None:
            prog_thread.join(timeout=10.0)
        client.close()
        try:
            server_in.close()
        except OSError:
            pass
        try:
            server_out.close()
        except OSError:
            pass
        server_thread.join(timeout=2.0)
        # Belt-and-suspenders: if the program thread somehow didn't
        # unwind through check_file's finally, detach explicitly.
        from flags import set_debugger
        set_debugger(None)


def _write_fixture(tmp_path: Path, name: str, content: str) -> str:
    """Write a fixture .pf into the per-test tmp dir.  Use absolute
    paths so DAP's ``source.path`` matches the file's ``Meta``."""
    p = tmp_path / name
    p.write_text(content)
    return str(p.resolve())


# Smallest useful program: one print + one user-defined function.
SIMPLE_PROGRAM = """\
recursive double(Nat) -> Nat {
  double(zero) = zero
  double(suc(n')) = suc(suc(double(n')))
}

print double(suc(zero))
"""


# --------------------------------------------------------------------------
# Tests.
# --------------------------------------------------------------------------


def test_initialize_returns_capabilities(dap_session):
    _, client, _ = dap_session
    resp = client.request("initialize", {"clientID": "pytest"})
    assert resp["success"], resp
    body = resp["body"]
    assert body["supportsConditionalBreakpoints"] is True
    assert body["supportsFunctionBreakpoints"] is True
    # The server should also emit an 'initialized' event so the
    # client knows it can send configuration requests.
    evt = client.wait_for_event("initialized", timeout=2.0)
    assert evt["event"] == "initialized"


def test_unknown_request_fails_gracefully(dap_session):
    _, client, _ = dap_session
    resp = client.request("noSuchCommand")
    assert resp["success"] is False
    assert "unknown DAP request" in resp.get("message", "")


def test_full_session_continue_to_end(dap_session, tmp_path):
    """Minimum viable session: initialize -> launch -> wait for
    the first stopped event -> continue -> terminated."""
    server, client, _ = dap_session
    fixture = _write_fixture(tmp_path, "simple.pf", SIMPLE_PROGRAM)
    assert client.request("initialize", {})["success"]
    client.wait_for_event("initialized")
    assert client.request("launch", {"program": fixture})["success"]
    # No breakpoints, just signal configuration done.
    assert client.request("configurationDone")["success"]
    stopped = client.wait_for_event("stopped", timeout=10.0)
    assert stopped["body"]["threadId"] == 1
    # Resume; the program should finish.
    assert client.request("continue")["success"]
    client.wait_for_event("terminated", timeout=10.0)


def test_stack_trace_synthesizes_top_level_frame(dap_session, tmp_path):
    """At the first pause we're at a top-level statement, not inside
    a function call -- ``self.stack`` is empty.  DAP still needs a
    frame in the trace for the editor's UI to anchor on; otherwise
    the editor silently resumes (this is exactly what happened in
    Jeremy's first emacs smoke run).  The server synthesises a
    single ``<top-level>`` frame pointing at the current location."""
    server, client, _ = dap_session
    fixture = _write_fixture(tmp_path, "toplevel.pf", SIMPLE_PROGRAM)
    client.request("initialize", {})
    client.wait_for_event("initialized")
    client.request("launch", {"program": fixture})
    client.request("configurationDone")
    client.wait_for_event("stopped", timeout=10.0)
    resp = client.request("stackTrace", {"threadId": 1})
    assert resp["success"], resp
    frames = resp["body"]["stackFrames"]
    assert len(frames) == 1, f"expected exactly one top-level frame, got {frames}"
    assert frames[0]["name"] == "<top-level>"
    assert frames[0]["source"]["path"] == fixture
    client.request("continue")
    try:
        client.wait_for_event("terminated", timeout=5.0)
    except TimeoutError:
        pass


def test_stack_trace_inside_function(dap_session, tmp_path):
    """After setting a function breakpoint and continuing into the
    call, ``stackTrace`` should report one frame named ``double``."""
    server, client, _ = dap_session
    fixture = _write_fixture(tmp_path, "stack.pf", SIMPLE_PROGRAM)
    client.request("initialize", {})
    client.wait_for_event("initialized")
    client.request("launch", {"program": fixture})
    # Drop a function breakpoint on ``double``.
    client.request("setFunctionBreakpoints", {
        "breakpoints": [{"name": "double"}],
    })
    client.request("configurationDone")
    # First stop: the initial-statement trap (Step 21 leftover).
    client.wait_for_event("stopped", timeout=10.0)
    client.request("continue")
    # Second stop: the function breakpoint on ``double``.
    client.wait_for_event("stopped", timeout=10.0)
    resp = client.request("stackTrace", {"threadId": 1})
    assert resp["success"], resp
    frames = resp["body"]["stackFrames"]
    assert frames, "expected at least one frame"
    assert frames[0]["name"] == "double"
    # And ``scopes`` -> ``variables`` should surface the
    # pattern-bound ``n'``.
    scopes = client.request("scopes", {"frameId": frames[0]["id"]})
    var_ref = scopes["body"]["scopes"][0]["variablesReference"]
    variables = client.request("variables", {
        "variablesReference": var_ref,
    })
    names = [v["name"] for v in variables["body"]["variables"]]
    assert "n'" in names
    # Drain so the program can finish.
    client.request("continue")
    while True:
        try:
            evt = client.wait_for_event("stopped", timeout=2.0)
        except TimeoutError:
            break
        client.request("continue")
    # Wait for terminated -- a few residual stops are fine.
    try:
        client.wait_for_event("terminated", timeout=5.0)
    except TimeoutError:
        pass


def test_evaluate_reduces_expression(dap_session, tmp_path):
    """``evaluate`` should drive the same parser+reducer the text
    REPL's ``print`` uses, returning the reduced value as a string."""
    server, client, _ = dap_session
    fixture = _write_fixture(tmp_path, "eval.pf", SIMPLE_PROGRAM)
    client.request("initialize", {})
    client.wait_for_event("initialized")
    client.request("launch", {"program": fixture})
    client.request("configurationDone")
    client.wait_for_event("stopped", timeout=10.0)
    # ``zero`` is in scope; the evaluator should produce ``zero``.
    resp = client.request("evaluate", {"expression": "zero"})
    assert resp["success"], resp
    assert resp["body"]["result"] == "zero"
    # An unknown identifier surfaces as an error response.
    err = client.request("evaluate", {"expression": "totally_undefined_name"})
    assert err["success"] is False
    client.request("continue")
    try:
        client.wait_for_event("terminated", timeout=5.0)
    except TimeoutError:
        pass


def test_set_file_breakpoint_fires_at_line(dap_session, tmp_path):
    """``setBreakpoints`` on a source path / line should produce a
    ``stopped`` event with reason ``breakpoint`` when the line is
    reached."""
    server, client, _ = dap_session
    fixture = _write_fixture(tmp_path, "lineBp.pf", SIMPLE_PROGRAM)
    client.request("initialize", {})
    client.wait_for_event("initialized")
    client.request("launch", {"program": fixture})
    # Line 6 is the ``print double(suc(zero))`` statement.
    bp_resp = client.request("setBreakpoints", {
        "source": {"path": fixture},
        "breakpoints": [{"line": 6}],
    })
    assert bp_resp["success"], bp_resp
    assert bp_resp["body"]["breakpoints"][0]["verified"] is True
    client.request("configurationDone")
    # First stop is the initial pause; continue past it.
    client.wait_for_event("stopped", timeout=10.0)
    client.request("continue")
    # Second stop should be the line-6 breakpoint.
    stopped = client.wait_for_event("stopped", timeout=10.0)
    assert stopped["body"]["reason"] == "breakpoint"
    client.request("continue")
    try:
        client.wait_for_event("terminated", timeout=5.0)
    except TimeoutError:
        pass


def test_print_routed_to_output_event(dap_session, tmp_path):
    """``print double(...)`` runs during ``check_file``; in DAP mode
    its stdout has to be forwarded as an ``output`` event so the
    editor's Debug Console / output panel surfaces it (and so the
    bytes don't corrupt the protocol stream)."""
    server, client, _ = dap_session
    fixture = _write_fixture(tmp_path, "print.pf", SIMPLE_PROGRAM)
    client.request("initialize", {})
    client.wait_for_event("initialized")
    client.request("launch", {"program": fixture})
    client.request("configurationDone")
    client.wait_for_event("stopped", timeout=10.0)
    client.request("continue")
    # The program runs ``print double(suc(zero))`` -> ``suc(suc(zero))``.
    # Drain events until we see an output one with stdout category,
    # then confirm the body contains the expected value.
    output_lines: list[str] = []
    while True:
        try:
            evt = client.wait_for_event("output", timeout=5.0)
        except TimeoutError:
            break
        body = evt.get("body") or {}
        if body.get("category") == "stdout":
            output_lines.append(body.get("output", ""))
    assert any("suc(suc(zero))" in line for line in output_lines), (
        f"expected print output in stdout events; got {output_lines}"
    )
    try:
        client.wait_for_event("terminated", timeout=5.0)
    except TimeoutError:
        pass


def test_disconnect_terminates(dap_session, tmp_path):
    server, client, _ = dap_session
    fixture = _write_fixture(tmp_path, "disc.pf", SIMPLE_PROGRAM)
    client.request("initialize", {})
    client.wait_for_event("initialized")
    client.request("launch", {"program": fixture})
    client.request("configurationDone")
    client.wait_for_event("stopped", timeout=10.0)
    resp = client.request("disconnect")
    assert resp["success"]
