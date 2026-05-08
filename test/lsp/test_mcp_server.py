"""End-to-end tests for the MCP adapter (Phase 1 / Step 7).

Each MCP tool is exercised through the SDK's in-memory test client so
we cover the full path -- input schema, JSON serialization,
``query.*`` plumbing -- without spawning a stdio subprocess. The
underlying ``query`` functions are already exhaustively tested in
``test_check.py`` / ``test_goal_at.py`` / ``test_symbols.py``; the
job here is to verify the wrapper.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

# Skip if mcp isn't installed -- it's an optional dependency and the
# rest of the LSP suite stays runnable without it.
mcp = pytest.importorskip("mcp")
from mcp.shared.memory import (  # noqa: E402
    create_connected_server_and_client_session,
)

# Importing the server triggers Deduce environment setup. Ensure no
# stdlib auto-prepend so test fixtures don't depend on it.
import os  # noqa: E402

os.environ["DEDUCE_NO_STDLIB"] = "1"

from lsp import mcp_server as _server_module  # noqa: E402


VALID_FILE = REPO_ROOT / "test" / "should-validate" / "after.pf"
ERROR_FILE = REPO_ROOT / "test" / "should-error" / "advice_and.pf"


@pytest.fixture
def server():
    """The configured FastMCP instance under test."""
    return _server_module.mcp


def _parse_response(result) -> Any:
    """Decode whatever FastMCP returned for our tool.

    FastMCP picks one of three encodings depending on the tool's return
    annotation:

    * ``dict`` returns -- one ``TextContent`` holding a JSON object,
      ``structuredContent`` is ``None``;
    * ``list[...]`` and ``None`` returns -- ``structuredContent`` is
      ``{"result": ...}`` (and ``content`` mirrors each list element);
    * primitives -- similar to lists.

    Prefer structured content when present, fall back to parsing the
    text body otherwise.
    """
    sc = getattr(result, "structuredContent", None)
    if sc is not None and "result" in sc:
        return sc["result"]
    if not result.content:
        return None
    return json.loads(result.content[0].text)


async def _call(server, name: str, arguments: dict) -> Any:
    async with create_connected_server_and_client_session(
        server._mcp_server
    ) as session:
        await session.initialize()
        result = await session.call_tool(name, arguments)
        assert not result.isError, f"{name} returned error: {result.content}"
        return _parse_response(result)


# --------------------------------------------------------------------------
# Tool registration
# --------------------------------------------------------------------------


@pytest.mark.anyio
async def test_all_tools_are_registered(server):
    async with create_connected_server_and_client_session(
        server._mcp_server
    ) as session:
        await session.initialize()
        listing = await session.list_tools()
        names = {t.name for t in listing.tools}
        assert names == {
            "check_file",
            "goal_at",
            "definition_of",
            "list_symbols",
            "refine_at",
            "case_split_at",
            "splittable_vars_at",
            "induction_skeleton_at",
            "eliminate_at",
            "eliminable_vars_at",
        }


# --------------------------------------------------------------------------
# check_file
# --------------------------------------------------------------------------


@pytest.mark.anyio
async def test_check_file_on_valid_file_returns_no_diagnostics(server):
    payload = await _call(server, "check_file", {"path": str(VALID_FILE)})
    assert payload == {"diagnostics": []}


@pytest.mark.anyio
async def test_check_file_on_error_file_returns_one_diagnostic(server):
    payload = await _call(server, "check_file", {"path": str(ERROR_FILE)})
    assert "diagnostics" in payload
    diags = payload["diagnostics"]
    assert len(diags) == 1
    diag = diags[0]
    assert diag["severity"] == "error"
    assert "range" in diag
    assert diag["range"]["start"]["line"] == 6
    assert "incomplete proof" in diag["message"]


# --------------------------------------------------------------------------
# goal_at
# --------------------------------------------------------------------------


@pytest.mark.anyio
async def test_goal_at_returns_goal_dict(server, tmp_path):
    # Self-contained bool-only fixture so we don't need the prelude.
    src = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  reflexive\n"
        "end\n"
    )
    fp = tmp_path / "goal.pf"
    fp.write_text(src)
    payload = await _call(
        server,
        "goal_at",
        {"path": str(fp), "line": 4, "column": 1},
    )
    assert payload is not None
    assert payload["formula"] == "P = P"
    assert payload["givens"] == []


@pytest.mark.anyio
async def test_goal_at_returns_null_outside_proof(server, tmp_path):
    src = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  reflexive\n"
        "end\n"
        "\n"
        "-- here, after end\n"
    )
    fp = tmp_path / "outside.pf"
    fp.write_text(src)
    payload = await _call(
        server,
        "goal_at",
        {"path": str(fp), "line": 7, "column": 1},
    )
    assert payload is None


# --------------------------------------------------------------------------
# definition_of
# --------------------------------------------------------------------------


@pytest.mark.anyio
async def test_definition_of_finds_theorem(server, tmp_path):
    src = (
        "theorem t1: true\n"
        "proof\n"
        "  .\n"
        "end\n"
        "\n"
        "theorem t2: true\n"
        "proof\n"
        "  t1\n"
        "end\n"
    )
    fp = tmp_path / "defn.pf"
    fp.write_text(src)
    payload = await _call(
        server,
        "definition_of",
        {"path": str(fp), "line": 8, "column": 3},
    )
    assert payload is not None
    assert payload["path"] == str(fp)
    assert payload["range"]["start"]["line"] == 1


@pytest.mark.anyio
async def test_definition_of_returns_null_for_whitespace(server, tmp_path):
    src = (
        "theorem t1: true\n"
        "proof\n"
        "  .\n"
        "end\n"
    )
    fp = tmp_path / "ws.pf"
    fp.write_text(src)
    payload = await _call(
        server,
        "definition_of",
        {"path": str(fp), "line": 3, "column": 1},
    )
    assert payload is None


# --------------------------------------------------------------------------
# list_symbols
# --------------------------------------------------------------------------


@pytest.mark.anyio
async def test_list_symbols_returns_each_top_level_decl(server, tmp_path):
    src = (
        "theorem t1: true\n"
        "proof\n"
        "  .\n"
        "end\n"
        "\n"
        "define X: bool = true\n"
        "\n"
        "union Color {\n"
        "  Red\n"
        "  Blue\n"
        "}\n"
    )
    fp = tmp_path / "outline.pf"
    fp.write_text(src)
    payload = await _call(server, "list_symbols", {"path": str(fp)})
    assert isinstance(payload, list)
    by_name = {s["name"]: s for s in payload}
    assert set(by_name) == {"t1", "X", "Color"}
    assert by_name["t1"]["kind"] == "theorem"
    assert by_name["X"]["kind"] == "define"
    assert by_name["Color"]["kind"] == "union"


# --------------------------------------------------------------------------
# refine_at
# --------------------------------------------------------------------------


@pytest.mark.anyio
async def test_refine_at_returns_workspace_edit(server, tmp_path):
    """Cursor on a `?` whose goal is `P = P` -> reflexive template."""
    src = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  ?\n"
        "end\n"
    )
    fp = tmp_path / "refine.pf"
    fp.write_text(src)
    payload = await _call(
        server,
        "refine_at",
        {"path": str(fp), "line": 4, "column": 3},
    )
    assert payload is not None
    assert payload["path"] == str(fp)
    assert payload["new_text"] == "reflexive"
    assert payload["range"]["start"] == {"line": 4, "column": 3}
    assert payload["range"]["end"] == {"line": 4, "column": 4}


@pytest.mark.anyio
async def test_refine_at_returns_null_when_cursor_not_on_hole(
    server, tmp_path
):
    src = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  reflexive\n"
        "end\n"
    )
    fp = tmp_path / "complete.pf"
    fp.write_text(src)
    payload = await _call(
        server,
        "refine_at",
        {"path": str(fp), "line": 4, "column": 3},
    )
    assert payload is None


# --------------------------------------------------------------------------
# case_split_at and splittable_vars_at
# --------------------------------------------------------------------------


@pytest.mark.anyio
async def test_case_split_at_returns_switch_workspace_edit(server, tmp_path):
    """Cursor on `?` + variable=`x` -> switch skeleton edit."""
    src = (
        "union N {\n"
        "  z\n"
        "  s(N)\n"
        "}\n"
        "\n"
        "theorem t: all x:N. x = x\n"
        "proof\n"
        "  arbitrary x:N\n"
        "  ?\n"
        "end\n"
    )
    fp = tmp_path / "case_split.pf"
    fp.write_text(src)
    payload = await _call(
        server,
        "case_split_at",
        {"path": str(fp), "line": 9, "column": 3, "variable": "x"},
    )
    assert payload is not None
    assert payload["path"] == str(fp)
    assert "switch x" in payload["new_text"]
    assert "case z {" in payload["new_text"]
    assert "case s(n1) {" in payload["new_text"]
    assert payload["range"]["start"] == {"line": 9, "column": 3}
    assert payload["range"]["end"] == {"line": 9, "column": 4}


@pytest.mark.anyio
async def test_case_split_at_returns_null_when_cursor_not_on_hole(
    server, tmp_path
):
    src = (
        "union N {\n"
        "  z\n"
        "  s(N)\n"
        "}\n"
        "\n"
        "theorem t: all x:N. x = x\n"
        "proof\n"
        "  arbitrary x:N\n"
        "  ?\n"
        "end\n"
    )
    fp = tmp_path / "no_split.pf"
    fp.write_text(src)
    # Cursor on the `x` of `arbitrary x:N` -- not on the ?.
    payload = await _call(
        server,
        "case_split_at",
        {"path": str(fp), "line": 8, "column": 13, "variable": "x"},
    )
    assert payload is None


@pytest.mark.anyio
async def test_splittable_vars_at_returns_candidates(server, tmp_path):
    src = (
        "union N {\n"
        "  z\n"
        "  s(N)\n"
        "}\n"
        "\n"
        "theorem t: all P:bool, x:N. if P or P then x = x\n"
        "proof\n"
        "  arbitrary P:bool, x:N\n"
        "  assume H: P or P\n"
        "  ?\n"
        "end\n"
    )
    fp = tmp_path / "candidates.pf"
    fp.write_text(src)
    payload = await _call(
        server,
        "splittable_vars_at",
        {"path": str(fp), "line": 10, "column": 3},
    )
    # Constructors (z, s) excluded; bool var (P) excluded; only the
    # Union-typed term var and the Or-formula proof var.
    assert payload == ["H", "x"]


@pytest.mark.anyio
async def test_splittable_vars_at_returns_empty_off_hole(server, tmp_path):
    src = (
        "union N {\n"
        "  z\n"
        "  s(N)\n"
        "}\n"
        "\n"
        "theorem t: all x:N. x = x\n"
        "proof\n"
        "  arbitrary x:N\n"
        "  ?\n"
        "end\n"
    )
    fp = tmp_path / "off.pf"
    fp.write_text(src)
    # Cursor on `x` of arbitrary -- not on ?.
    payload = await _call(
        server,
        "splittable_vars_at",
        {"path": str(fp), "line": 8, "column": 13},
    )
    assert payload == []


# --------------------------------------------------------------------------
# induction_skeleton_at
# --------------------------------------------------------------------------


@pytest.mark.anyio
async def test_induction_skeleton_at_returns_workspace_edit(
    server, tmp_path
):
    """Cursor on `?` whose goal is `all x:N. x = x` -> induction
    skeleton with one case per Nat constructor."""
    src = (
        "union N {\n"
        "  z\n"
        "  s(N)\n"
        "}\n"
        "\n"
        "theorem t: all x:N. x = x\n"
        "proof\n"
        "  ?\n"
        "end\n"
    )
    fp = tmp_path / "induction.pf"
    fp.write_text(src)
    payload = await _call(
        server,
        "induction_skeleton_at",
        {"path": str(fp), "line": 8, "column": 3},
    )
    assert payload is not None
    assert payload["path"] == str(fp)
    assert "induction N" in payload["new_text"]
    assert "case z {" in payload["new_text"]
    assert "case s(n1) assume IH1: n1 = n1 {" in payload["new_text"]
    assert payload["range"]["start"] == {"line": 8, "column": 3}
    assert payload["range"]["end"] == {"line": 8, "column": 4}


@pytest.mark.anyio
async def test_induction_skeleton_at_returns_null_for_non_forall(
    server, tmp_path
):
    """A goal that isn't `all x:T. ...` -> null."""
    src = (
        "theorem t: all P:bool. P or not P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  ?\n"
        "end\n"
    )
    fp = tmp_path / "no_induction.pf"
    fp.write_text(src)
    payload = await _call(
        server,
        "induction_skeleton_at",
        {"path": str(fp), "line": 4, "column": 3},
    )
    assert payload is None


# --------------------------------------------------------------------------
# eliminate_at and eliminable_vars_at
# --------------------------------------------------------------------------


@pytest.mark.anyio
async def test_eliminate_at_returns_workspace_edit(server, tmp_path):
    """Cursor on `?` + label='H' (Or-shaped) -> cases skeleton edit."""
    src = (
        "theorem t: all P:bool, Q:bool. if P or Q then Q or P\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume H: P or Q\n"
        "  ?\n"
        "end\n"
    )
    fp = tmp_path / "eliminate.pf"
    fp.write_text(src)
    payload = await _call(
        server,
        "eliminate_at",
        {"path": str(fp), "line": 5, "column": 3, "label": "H"},
    )
    assert payload is not None
    assert payload["path"] == str(fp)
    assert "cases H" in payload["new_text"]
    assert payload["range"]["start"] == {"line": 5, "column": 3}
    assert payload["range"]["end"] == {"line": 5, "column": 4}


@pytest.mark.anyio
async def test_eliminable_vars_at_returns_candidates(server, tmp_path):
    src = (
        "theorem t: all P:bool, Q:bool. if P or Q then Q or P\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume H: P or Q\n"
        "  ?\n"
        "end\n"
    )
    fp = tmp_path / "candidates.pf"
    fp.write_text(src)
    payload = await _call(
        server,
        "eliminable_vars_at",
        {"path": str(fp), "line": 5, "column": 3},
    )
    assert "H" in payload


# --------------------------------------------------------------------------
# pytest-anyio plumbing -- pytest.mark.anyio needs an event-loop fixture
# --------------------------------------------------------------------------


@pytest.fixture
def anyio_backend():
    return "asyncio"
