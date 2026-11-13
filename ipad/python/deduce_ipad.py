"""Entry point for the iPad app's embedded interpreter.

``serve`` runs the Deduce LSP server over the pipe pair the app passes
in. ``interrupt`` is called from the app (on another thread, holding the
GIL) to cancel the check or request in progress: the server's worker
thread then raises ``CheckCancelled`` (see ``lsp/worker.py``, #1218).
"""

import os


def interrupt() -> bool:
    """Cancel the check or request in progress, if any. Returns whether
    there was one."""
    from lsp import lsp_server

    return lsp_server.interrupt()


def serve(read_fd: int, write_fd: int, snapshot_dir: str) -> None:
    from lsp import lsp_server
    from lsp.library import set_snapshot_dir

    # Load the post-prelude state from the app's caches instead of
    # re-checking the stdlib on every launch (#1217).
    set_snapshot_dir(snapshot_dir)
    lsp_server.server.start_io(os.fdopen(read_fd, "rb"), os.fdopen(write_fd, "wb"))
