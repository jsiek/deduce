"""MCP adapter for the Deduce query API (Phase 1 / Step 7).

Exposes ``lsp.query``'s four functions as MCP tools over stdio. Each
tool is a thin wrapper that reads the file from disk, calls the
underlying query helper, and serializes the result to JSON-friendly
dicts.

Run directly to start the stdio server::

    python3 -m lsp.mcp_server

Wire it into Claude Code via ``.mcp.json`` (or the user-level
equivalent)::

    {
      "mcpServers": {
        "deduce": {
          "command": "python3",
          "args": ["-m", "lsp.mcp_server"]
        }
      }
    }

The standard library at ``lib/`` is auto-prepended as the default
prelude unless ``DEDUCE_NO_STDLIB=1`` is set in the environment;
that mirrors ``deduce.py``'s ``--no-stdlib`` flag. Set
``DEDUCE_ROOT`` to override where the server looks for ``lib/`` and
``test/test-imports/``; otherwise it falls back to the parent
directory of this module.

The MCP boundary stays protocol-specific: the only consumer of
``mcp`` lives here. Everything reachable from tests and the LSP
adapter (Step 9) goes through ``lsp.query``.
"""

from __future__ import annotations

import os
import sys
from dataclasses import asdict, is_dataclass
from pathlib import Path
from typing import Any, Optional


# ---------------------------------------------------------------------------
# Bootstrap: configure the Deduce environment exactly once at import.
# ---------------------------------------------------------------------------


def _resolve_deduce_root() -> Path:
    env_root = os.environ.get("DEDUCE_ROOT")
    if env_root:
        return Path(env_root).resolve()
    # ``lsp/mcp_server.py`` lives one directory below the repo root.
    return Path(__file__).resolve().parent.parent


_DEDUCE_ROOT = _resolve_deduce_root()
_LIB_DIR = _DEDUCE_ROOT / "lib"
_TEST_IMPORTS_DIR = _DEDUCE_ROOT / "test" / "test-imports"

# ``set_deduce_directory`` -- called by the parsers -- reads
# ``os.path.dirname(sys.argv[0])`` to find ``Deduce.lark``. Make
# sure it points at the repo root regardless of how the server
# was launched.
_PSEUDO_ENTRY = str(_DEDUCE_ROOT / "deduce.py")
sys.argv = [_PSEUDO_ENTRY] + sys.argv[1:]
sys.setrecursionlimit(10000)

# Repo root needs to be on sys.path for ``import abstract_syntax`` etc.
if str(_DEDUCE_ROOT) not in sys.path:
    sys.path.insert(0, str(_DEDUCE_ROOT))

from abstract_syntax import (  # noqa: E402
    add_import_directory,
    init_import_directories,
)
from flags import set_quiet_mode  # noqa: E402

set_quiet_mode(True)
init_import_directories()
add_import_directory(str(_LIB_DIR))
if _TEST_IMPORTS_DIR.is_dir():
    add_import_directory(str(_TEST_IMPORTS_DIR))


def _default_prelude() -> tuple[str, ...]:
    """Module names for every ``.pf`` in ``lib/`` -- the standard
    library prelude, mirroring ``deduce.py`` without ``--no-stdlib``.
    Returns ``()`` when ``DEDUCE_NO_STDLIB=1`` or ``lib/`` is missing.
    """
    if os.environ.get("DEDUCE_NO_STDLIB") == "1":
        return ()
    if not _LIB_DIR.is_dir():
        return ()
    return tuple(
        sorted(p.stem for p in _LIB_DIR.glob("*.pf"))
    )


_PRELUDE = _default_prelude()


def _path_is_in_lib(path: str) -> bool:
    """True iff ``path`` lives inside the standard library directory.

    Files inside ``lib/`` are part of the prelude themselves; checking
    one with the prelude prepended would import the file twice and
    trip ``theorem names may not be overloaded`` (mirrors the
    ``check_in_prelude`` logic in ``deduce.py``)."""
    try:
        Path(path).resolve().relative_to(_LIB_DIR.resolve())
    except (OSError, ValueError):
        return False
    return True


def _prelude_for(path: str) -> tuple[str, ...]:
    """Empty prelude for files in ``lib/``, otherwise the default."""
    return () if _path_is_in_lib(path) else _PRELUDE


# ---------------------------------------------------------------------------
# Server definition
# ---------------------------------------------------------------------------


from lsp import query  # noqa: E402
from mcp.server.fastmcp import FastMCP  # noqa: E402


mcp = FastMCP("deduce-lsp")


def _to_serializable(obj: Any) -> Any:
    """Convert frozen dataclasses (and tuples/enums of them) into
    plain dicts/lists for the MCP JSON wire format."""
    if obj is None:
        return None
    if is_dataclass(obj):
        return {k: _to_serializable(v) for k, v in asdict(obj).items()}
    if isinstance(obj, (list, tuple)):
        return [_to_serializable(x) for x in obj]
    if hasattr(obj, "value") and hasattr(obj, "name"):
        # Enum-ish: surface the .value (e.g. "error" for Severity).
        return obj.value
    return obj


def _read_file(path: str) -> str:
    """Read a file with the same encoding ``check_file`` uses."""
    with open(path, "r", encoding="utf-8") as f:
        return f.read()


@mcp.tool()
def check_file(path: str) -> dict:
    """Run the Deduce pipeline on ``path`` and return diagnostics.

    The standard library at ``lib/`` is auto-prepended unless the
    server was started with ``DEDUCE_NO_STDLIB=1``. Returns a dict
    with a ``diagnostics`` list; an empty list means the file is
    valid. Diagnostic entries have ``severity``, ``range`` (with
    1-indexed line/column positions), ``message``, and an optional
    ``code``.
    """
    content = _read_file(path)
    diagnostics = query.check(path, content, prelude=_prelude_for(path))
    return {"diagnostics": _to_serializable(diagnostics)}


@mcp.tool()
def goal_at(path: str, line: int, column: int) -> Optional[dict]:
    """Return the proof obligation visible at ``line``:``column``.

    Lines and columns are 1-indexed (matching the location text in
    Deduce error messages). Returns ``None`` when the cursor is
    outside any active proof or the file does not parse. The result
    has ``formula`` (a rendered string), ``givens`` (a list of
    ``{label, formula}`` pairs in scope), and ``range``.
    """
    content = _read_file(path)
    pos = query.Position(line=line, column=column)
    goal = query.goal_at(path, content, pos, prelude=_prelude_for(path))
    return _to_serializable(goal)


@mcp.tool()
def definition_of(path: str, line: int, column: int) -> Optional[dict]:
    """Return the source location of the symbol at ``line``:``column``.

    Returns ``None`` when the cursor isn't on a resolvable symbol or
    when the definition lives outside the file (an imported module,
    a built-in). The result has ``path`` and ``range``.
    """
    content = _read_file(path)
    pos = query.Position(line=line, column=column)
    loc = query.definition_of(path, content, pos, prelude=_prelude_for(path))
    return _to_serializable(loc)


@mcp.tool()
def list_symbols(path: str) -> list[dict]:
    """Return all top-level declarations in ``path``.

    Includes theorems, lemmas, postulates, defines, recursive
    functions, unions, predicates, and explicit imports. Auto-
    prepended prelude imports are filtered out so the outline shows
    only what the user wrote. Each entry has ``name``, ``kind``
    (e.g. ``"theorem"``), ``location``, and an optional
    ``signature``.
    """
    content = _read_file(path)
    syms = query.list_symbols(path, content, prelude=_prelude_for(path))
    return _to_serializable(syms)


def main() -> None:
    """Run the server over stdio. Used as the ``__main__`` entry."""
    mcp.run()


if __name__ == "__main__":
    main()
