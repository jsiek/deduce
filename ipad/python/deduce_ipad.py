"""Entry point for the iPad app's embedded interpreter.

``serve`` runs the Deduce LSP server over the pipe pair the app passes
in. ``interrupt`` is called from the app (on another thread, holding the
GIL) to cancel the check in progress: it raises ``CheckCancelled`` in the
serving thread via ``PyThreadState_SetAsyncExc``. Spike scaffolding for
#1220; the real worker-thread design is #1218.
"""

import ctypes
import os
import threading
from typing import Callable

from lsprotocol import types as lsp_types
from pygls.lsp.server import LanguageServer


class CheckCancelled(BaseException):
    """BaseException so the checker's ``except Exception`` handlers don't
    turn a cancellation into a diagnostic."""


_checking_thread: int | None = None


def _cancellable(
    publish: Callable[[LanguageServer, str], None],
) -> Callable[[LanguageServer, str], None]:
    def wrapper(ls: LanguageServer, uri: str) -> None:
        global _checking_thread
        _checking_thread = threading.get_ident()
        try:
            publish(ls, uri)
        except CheckCancelled:
            ls.window_log_message(lsp_types.LogMessageParams(
                type=lsp_types.MessageType.Info, message="check cancelled: " + uri))
        finally:
            _checking_thread = None
    return wrapper


def interrupt() -> bool:
    """Cancel the check in progress, if any. Returns whether one was."""
    if _checking_thread is None:
        return False
    ctypes.pythonapi.PyThreadState_SetAsyncExc(
        ctypes.c_ulong(_checking_thread), ctypes.py_object(CheckCancelled))
    return True


def serve(read_fd: int, write_fd: int) -> None:
    from lsp import lsp_server

    setattr(lsp_server, "_publish_diagnostics", _cancellable(lsp_server._publish_diagnostics))
    lsp_server.server.start_io(os.fdopen(read_fd, "rb"), os.fdopen(write_fd, "wb"))
