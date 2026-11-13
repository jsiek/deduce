"""The thread that runs the Deduce pipeline for the LSP server (#1218).

The pipeline keeps module-level state (see ``lsp/library.py``), so it
runs on one thread at a time. The server hands every check and every
request to a single ``Worker`` thread, which leaves pygls's I/O loop
free to read new edits and ``$/cancelRequest`` notifications while a
check runs.

A job is interrupted inside a statement, not just between statements:
``PyThreadState_SetAsyncExc`` raises ``CheckCancelled`` in the worker at
its next bytecode boundary, and the checker is pure Python. Nothing is
left half done, because ``lsp/library.py`` restores the post-prelude
state before each check and the statement cache records a verdict only
after a statement passes (see "Cancellation and limits" in
``docs/ipad-app-design.md``).
"""

from __future__ import annotations

import ctypes
import threading
from collections import deque
from concurrent.futures import Future
from dataclasses import dataclass, field
from typing import Any, Callable, Optional


class CheckCancelled(BaseException):
    """Raised in the worker to interrupt its job. A ``BaseException`` so
    the checker's ``except Exception`` handlers don't turn a cancellation
    into a diagnostic."""


class CheckSuperseded(CheckCancelled):
    """Interrupts a check because a newer one of the same document was
    submitted."""


@dataclass
class _Job:
    fn: Callable[..., Any]
    args: tuple[Any, ...]
    key: Optional[object]
    future: Future[Any] = field(default_factory=Future)


class Worker:
    """Runs submitted jobs in order on one thread with a large stack (the
    checker recurses deeply; see ``RECURSION_LIMIT``)."""

    def __init__(self, stack_size: int = 256 << 20) -> None:
        self._stack_size = stack_size
        self._lock = threading.Condition()
        self._queue: deque[_Job] = deque()
        self._running: Optional[_Job] = None
        self._thread: Optional[threading.Thread] = None

    def submit(self, fn: Callable[..., Any], *args: Any,
               key: Optional[object] = None) -> Future[Any]:
        """Queue ``fn(*args)``. A ``key`` makes the job supersede the
        earlier ones with that key: a queued one is dropped (its future
        cancelled) and a running one is interrupted with
        ``CheckSuperseded``."""
        job = _Job(fn, args, key)
        with self._lock:
            if key is not None:
                for old in [j for j in self._queue if j.key == key]:
                    self._queue.remove(old)
                    old.future.cancel()
                if self._running is not None and self._running.key == key:
                    self._raise_in_worker(CheckSuperseded)
            self._queue.append(job)
            if self._thread is None:
                previous = threading.stack_size(self._stack_size)
                try:
                    self._thread = threading.Thread(
                        target=self._loop, name="deduce-worker", daemon=True)
                    self._thread.start()
                finally:
                    threading.stack_size(previous)
            self._lock.notify()
        return job.future

    def cancel(self, future: Future[Any]) -> None:
        """Drop the job of ``future`` if it is queued, or interrupt it
        with ``CheckCancelled`` if it is running."""
        with self._lock:
            if self._running is not None and self._running.future is future:
                self._raise_in_worker(CheckCancelled)
            elif future.cancel():
                self._queue = deque(j for j in self._queue if j.future is not future)

    def interrupt(self) -> bool:
        """Interrupt the running job, if any, with ``CheckCancelled``.
        Returns whether there was one."""
        with self._lock:
            if self._running is None:
                return False
            self._raise_in_worker(CheckCancelled)
            return True

    def _raise_in_worker(self, exc: type[CheckCancelled]) -> None:
        # Called holding the lock, with a job running.
        assert self._thread is not None and self._thread.ident is not None
        ctypes.pythonapi.PyThreadState_SetAsyncExc(
            ctypes.c_ulong(self._thread.ident), ctypes.py_object(exc))

    def _loop(self) -> None:
        while True:
            with self._lock:
                while not self._queue:
                    self._lock.wait()
                job = self._queue.popleft()
                if not job.future.set_running_or_notify_cancel():
                    continue
                self._running = job
            # An interrupt is only sent while ``job`` is ``_running``, and
            # is raised at the next bytecode boundary: inside ``fn``, or at
            # the latest while clearing ``_running``. Either way it ends up
            # as the job's outcome, never outside this ``try``.
            try:
                try:
                    result = job.fn(*job.args)
                finally:
                    with self._lock:
                        self._running = None
                job.future.set_result(result)
            except BaseException as exc:
                if not job.future.done():
                    job.future.set_exception(exc)
