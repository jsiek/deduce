"""The LSP server's worker thread (#1218): checks and requests run off the
I/O loop, a newer version of a document supersedes its check, and a
request can be cancelled while it runs."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import threading
import time
from concurrent.futures import CancelledError
from pathlib import Path
from typing import Any, Iterator

import pytest

from lsp.worker import CheckCancelled, CheckSuperseded, Worker

REPO_ROOT = Path(__file__).resolve().parents[2]


def _spin(started: threading.Event) -> None:
    started.set()
    while True:
        pass


def test_jobs_run_in_order() -> None:
    worker = Worker()
    order: list[int] = []
    futures = [worker.submit(order.append, i) for i in range(5)]
    for f in futures:
        f.result(timeout=10)
    assert order == [0, 1, 2, 3, 4]


def test_a_keyed_job_supersedes_the_queued_and_the_running_one() -> None:
    worker = Worker()
    started = threading.Event()
    running = worker.submit(_spin, started, key="doc")
    assert started.wait(10)
    queued = worker.submit(_spin, threading.Event(), key="doc")
    other = worker.submit(lambda: "other")
    final = worker.submit(lambda: "final", key="doc")
    with pytest.raises(CheckSuperseded):
        running.result(timeout=10)
    assert queued.cancelled()
    assert other.result(timeout=10) == "other"
    assert final.result(timeout=10) == "final"


def test_cancel_drops_a_queued_job_and_interrupts_a_running_one() -> None:
    worker = Worker()
    started = threading.Event()
    running = worker.submit(_spin, started)
    queued = worker.submit(lambda: "never")
    assert started.wait(10)
    worker.cancel(queued)
    assert queued.cancelled()
    worker.cancel(running)
    with pytest.raises(CheckCancelled):
        running.result(timeout=10)
    assert worker.submit(lambda: "after").result(timeout=10) == "after"


def test_interrupt() -> None:
    worker = Worker()
    assert not worker.interrupt()
    started = threading.Event()
    running = worker.submit(_spin, started)
    assert started.wait(10)
    assert worker.interrupt()
    with pytest.raises(CheckCancelled):
        running.result(timeout=10)
    with pytest.raises(CancelledError):
        cancelled = worker.submit(lambda: None)
        cancelled.cancel()
        cancelled.result(timeout=10)


# --- The server over stdio -------------------------------------------------

# Checking the assert takes ~14 s; a variant differs only in a comment.
_SLOW = """union N { z  s(N) }
recursive add(N, N) -> N {
  add(z, m) = m
  add(s(n), m) = s(add(n, m))
}
recursive mul(N, N) -> N {
  mul(z, m) = z
  mul(s(n), m) = add(m, mul(n, m))
}
define ten : N = s(s(s(s(s(s(s(s(s(s(z))))))))))
assert mul(mul(ten, ten), mul(ten, s(s(s(z))))) = mul(mul(ten, ten), mul(ten, s(s(s(z)))))
"""
_FAST = "theorem t: true\nproof\n  ?\nend\n"


class _Client:
    def __init__(self, tmp_path: Path) -> None:
        env = dict(os.environ, DEDUCE_NO_STDLIB="1", DEDUCE_SNAPSHOT_DIR="")
        self.proc = subprocess.Popen(
            [sys.executable, "-m", "lsp.lsp_server"], cwd=REPO_ROOT, env=env,
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
        self.uri = (tmp_path / "doc.pf").as_uri()
        self.next_id = 1
        self.send("initialize", {"processId": None, "rootUri": None, "capabilities": {}},
                  request=True)
        self.receive_response(1)
        self.send("initialized", {})

    def send(self, method: str, params: Any, request: bool = False) -> int:
        message: dict[str, Any] = {"jsonrpc": "2.0", "method": method, "params": params}
        if request:
            message["id"] = self.next_id
            self.next_id += 1
        body = json.dumps(message).encode()
        assert self.proc.stdin is not None
        self.proc.stdin.write(b"Content-Length: %d\r\n\r\n" % len(body) + body)
        self.proc.stdin.flush()
        return message.get("id", 0)

    def receive(self) -> dict[str, Any]:
        assert self.proc.stdout is not None
        length = 0
        while (line := self.proc.stdout.readline().strip()):
            if line.lower().startswith(b"content-length:"):
                length = int(line.split(b":")[1])
        message: dict[str, Any] = json.loads(self.proc.stdout.read(length))
        return message

    def receive_response(self, msg_id: int) -> tuple[dict[str, Any], list[dict[str, Any]]]:
        """The response to ``msg_id`` and the notifications before it."""
        notifications = []
        while (message := self.receive()).get("id") != msg_id:
            notifications.append(message)
        return message, notifications

    def symbols(self) -> int:
        return self.send("textDocument/documentSymbol",
                         {"textDocument": {"uri": self.uri}}, request=True)


@pytest.fixture
def client(tmp_path: Path) -> Iterator[_Client]:
    c = _Client(tmp_path)
    yield c
    c.proc.kill()
    c.proc.wait()


def test_a_burst_of_edits_publishes_one_check_of_the_final_text(client: _Client) -> None:
    start = time.monotonic()
    client.send("textDocument/didOpen", {"textDocument": {
        "uri": client.uri, "languageId": "deduce", "version": 1, "text": _SLOW}})
    for version in range(2, 6):
        text = _FAST if version == 5 else _SLOW + "// %d\n" % version
        client.send("textDocument/didChange", {
            "textDocument": {"uri": client.uri, "version": version},
            "contentChanges": [{"text": text}]})
    # Requests run after the checks queued before them.
    _, notifications = client.receive_response(client.symbols())
    published = [n for n in notifications if n.get("method") == "textDocument/publishDiagnostics"]
    assert len(published) == 1, published
    [diagnostic] = published[0]["params"]["diagnostics"]
    assert diagnostic["range"]["start"]["line"] == 2  # the `?` of _FAST
    # Without interrupting the running check, this would take ~14 s.
    assert time.monotonic() - start < 10


def test_cancel_request_interrupts_a_running_request(client: _Client) -> None:
    client.send("textDocument/didOpen", {"textDocument": {
        "uri": client.uri, "languageId": "deduce", "version": 1, "text": _SLOW}})
    client.send("textDocument/didChange", {
        "textDocument": {"uri": client.uri, "version": 2},
        "contentChanges": [{"text": _SLOW + "// 2\n"}]})
    start = time.monotonic()
    slow = client.symbols()  # checks the slow text: waits, then runs ~14 s
    time.sleep(1)
    client.send("$/cancelRequest", {"id": slow})
    response, _ = client.receive_response(slow)
    assert response["error"]["code"] == -32800  # RequestCancelled
    # The check of version 2 is still to finish, but not the request.
    client.send("textDocument/didChange", {
        "textDocument": {"uri": client.uri, "version": 3},
        "contentChanges": [{"text": _FAST}]})
    response, _ = client.receive_response(client.symbols())
    assert [s["name"] for s in response["result"]] == ["t"]
    assert time.monotonic() - start < 10
