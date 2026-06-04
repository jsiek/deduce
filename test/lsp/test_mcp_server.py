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
            "fill_from_given_at",
            "matching_givens_at",
            "preview_conclude_at",
            "apply_at",
            "preview_replace_at",
            "preview_expand_at",
            "available_lemmas_at",
            "auto_rules_at",
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


@pytest.mark.anyio
async def test_check_file_accepts_inline_content(server, tmp_path):
    disk_src = (
        "theorem from_disk: true\n"
        "proof\n"
        "  .\n"
        "end\n"
    )
    inline_src = (
        "theorem from_inline: true\n"
        "proof\n"
        "  ?\n"
        "end\n"
    )
    fp = tmp_path / "inline-content.pf"
    fp.write_text(disk_src)

    payload = await _call(
        server,
        "check_file",
        {"path": str(fp), "content": inline_src},
    )

    assert "diagnostics" in payload
    diags = payload["diagnostics"]
    assert len(diags) == 1
    diag = diags[0]
    assert diag["severity"] == "error"
    assert diag["range"]["start"]["line"] == 3
    assert "incomplete proof" in diag["message"]


@pytest.mark.anyio
@pytest.mark.parametrize("parser", ["recursive-descent", "lalr"])
async def test_check_file_accepts_parser_argument(server, parser):
    """The MCP wrapper plumbs ``parser`` through to ``query.check`` and
    each parser accepts a known-valid file."""
    payload = await _call(
        server, "check_file", {"path": str(VALID_FILE), "parser": parser}
    )
    assert payload == {"diagnostics": []}


@pytest.mark.anyio
async def test_check_file_parser_both_labels_each_diagnostic(server):
    """With ``parser="both"`` the wrapper runs RD and LALR and tags
    every returned diagnostic with which parser produced it. For a
    valid file the merged list is empty but the call still succeeds."""
    payload = await _call(
        server, "check_file", {"path": str(VALID_FILE), "parser": "both"}
    )
    assert payload == {"diagnostics": []}


@pytest.mark.anyio
async def test_check_file_parser_both_merges_error_diagnostics(server):
    """``parser="both"`` returns one entry per parser per problem, each
    tagged with the parser that produced it."""
    payload = await _call(
        server, "check_file", {"path": str(ERROR_FILE), "parser": "both"}
    )
    diags = payload["diagnostics"]
    parsers_seen = sorted({d["parser"] for d in diags})
    assert parsers_seen == ["lalr", "recursive-descent"]
    # Both parsers agree on the same incomplete-proof hole.
    rd = next(d for d in diags if d["parser"] == "recursive-descent")
    lalr = next(d for d in diags if d["parser"] == "lalr")
    assert "incomplete proof" in rd["message"]
    assert "incomplete proof" in lalr["message"]


@pytest.mark.anyio
async def test_check_file_rejects_unknown_parser(server):
    """An unknown ``parser`` value must surface as a tool error rather
    than silently defaulting."""
    async with create_connected_server_and_client_session(
        server._mcp_server
    ) as session:
        await session.initialize()
        result = await session.call_tool(
            "check_file", {"path": str(VALID_FILE), "parser": "bogus"}
        )
        assert result.isError


@pytest.mark.anyio
async def test_check_file_on_stdlib_file_does_not_prepend_stdlib(
    server, monkeypatch
):
    lib_file = REPO_ROOT / "lib" / "UIntDiv.pf"
    if not lib_file.exists():
        pytest.skip(f"{lib_file} not present in this checkout")

    # Simulate a normally configured MCP server with a non-empty
    # stdlib prelude. A lib/* target must still run with an empty
    # prelude, or the target file is imported twice and reports
    # duplicate theorem declarations.
    monkeypatch.setattr(_server_module, "_PRELUDE", ("UIntDiv",))

    payload = await _call(server, "check_file", {"path": str(lib_file)})

    assert payload == {"diagnostics": []}


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


@pytest.mark.anyio
async def test_goal_at_returns_stdlib_hole_goal(server, monkeypatch):
    base = (REPO_ROOT / "lib" / "UIntDiv.pf").read_text()
    src = base + (
        "\n\n"
        "theorem uint_mult_mod_tmp: all a:UInt, b:UInt, m:UInt.\n"
        "  if 0 < m then (a * b) % m = ((a % m) * (b % m)) % m\n"
        "proof\n"
        "  arbitrary a:UInt, b:UInt, m:UInt\n"
        "  assume m_pos: 0 < m\n"
        "  ?\n"
        "end\n"
    )
    hole_line = src[: src.index("  ?\n", len(base))].count("\n") + 1
    stdlib_path = REPO_ROOT / "lib" / "UIntDiv.pf"

    monkeypatch.setattr(_server_module, "_read_file", lambda path: src)

    payload = await _call(
        server,
        "goal_at",
        {"path": str(stdlib_path), "line": hole_line, "column": 3},
    )
    assert payload is not None
    assert payload["formula"] == "(a * b) % m = ((a % m) * (b % m)) % m"
    assert payload["givens"] == [
        {"label": "m_pos", "formula": "0 < m", "formula_normalized": None}
    ]


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


@pytest.mark.anyio
async def test_refine_at_returns_unsupported_shape_dict(server, tmp_path):
    """Cursor on a real `?` whose goal is a bare bool atom: no
    template applies, so the tool returns an explanatory dict
    (``outcome``/``goal``/``supported_shapes``) rather than ``None``.
    Distinguishes "no template" from "no hole here" for callers."""
    src = (
        "theorem t: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  suppose pP: P\n"
        "  ?\n"
        "end\n"
    )
    fp = tmp_path / "unsupported.pf"
    fp.write_text(src)
    payload = await _call(
        server,
        "refine_at",
        {"path": str(fp), "line": 5, "column": 3},
    )
    assert payload is not None
    assert payload["outcome"] == "unsupported_shape"
    assert payload["goal"] == "P"
    assert "if _ then _" in payload["supported_shapes"]
    assert "all _. _" in payload["supported_shapes"]


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
# apply_at
# --------------------------------------------------------------------------


@pytest.mark.anyio
async def test_apply_at_returns_ok_dict(server, tmp_path):
    """Cursor on ``?`` + ``theorem='H'`` for an in-scope ``if P then Q``
    -> ``ok`` outcome with the premise as a remaining obligation."""
    src = (
        "theorem t: all P:bool, Q:bool. if (if P then Q) and P then Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume H: (if P then Q) and P\n"
        "  have Hpq: if P then Q by conjunct 0 of H\n"
        "  ?\n"
        "end\n"
    )
    fp = tmp_path / "apply_ok.pf"
    fp.write_text(src)
    payload = await _call(
        server,
        "apply_at",
        {"path": str(fp), "line": 6, "column": 3, "theorem": "Hpq"},
    )
    assert payload == {
        "outcome": "ok",
        "conclusion": "Q",
        "remaining_premises": ["P"],
    }


@pytest.mark.anyio
async def test_apply_at_unbound_returns_unbound_dict(server, tmp_path):
    src = (
        "theorem t: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume H: P\n"
        "  ?\n"
        "end\n"
    )
    fp = tmp_path / "apply_unbound.pf"
    fp.write_text(src)
    payload = await _call(
        server,
        "apply_at",
        {"path": str(fp), "line": 5, "column": 3, "theorem": "no_such"},
    )
    assert payload == {"outcome": "unbound", "theorem": "no_such"}


@pytest.mark.anyio
async def test_apply_at_with_args_instantiates_quantifier(
    server, tmp_path
):
    """Explicit ``[Q]`` instantiates the outer ``all P`` so the
    conclusion ``Q`` matches the goal."""
    src = (
        "theorem identity: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume H: P\n"
        "  H\n"
        "end\n"
        "\n"
        "theorem t: all Q:bool. if Q then Q\n"
        "proof\n"
        "  arbitrary Q:bool\n"
        "  assume H: Q\n"
        "  ?\n"
        "end\n"
    )
    fp = tmp_path / "apply_args.pf"
    fp.write_text(src)
    payload = await _call(
        server,
        "apply_at",
        {
            "path": str(fp),
            "line": 12,
            "column": 3,
            "theorem": "identity",
            "args": ["Q"],
        },
    )
    assert payload == {
        "outcome": "ok",
        "conclusion": "Q",
        "remaining_premises": ["Q"],
    }


# --------------------------------------------------------------------------
# preview_replace_at and preview_expand_at
# --------------------------------------------------------------------------


@pytest.mark.anyio
async def test_preview_replace_at_returns_ok_outcome(server, tmp_path):
    """``replace H`` rewrites the goal's LHS to the RHS; preview shows
    both forms."""
    src = (
        "theorem t: all P:bool, Q:bool. if P = Q then P\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume H: P = Q\n"
        "  ?\n"
        "end\n"
    )
    fp = tmp_path / "preview_replace.pf"
    fp.write_text(src)
    payload = await _call(
        server,
        "preview_replace_at",
        {"path": str(fp), "line": 5, "column": 3, "equation": "H"},
    )
    assert payload is not None
    assert payload["outcome"] == "ok"
    assert payload["before"] == "P"
    assert payload["after"] == "Q"


@pytest.mark.anyio
async def test_preview_replace_at_returns_unbound(server, tmp_path):
    src = (
        "theorem t: all P:bool. P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  ?\n"
        "end\n"
    )
    fp = tmp_path / "preview_replace_unbound.pf"
    fp.write_text(src)
    payload = await _call(
        server,
        "preview_replace_at",
        {"path": str(fp), "line": 4, "column": 3, "equation": "no_such"},
    )
    assert payload is not None
    assert payload["outcome"] == "unbound"
    assert payload["name"] == "no_such"


@pytest.mark.anyio
async def test_preview_expand_at_unfolds_and_returns_ok(server, tmp_path):
    src = (
        "define my_and : fn bool, bool -> bool = λ a, b { a and b }\n"
        "theorem t: all P:bool, Q:bool. my_and(P, Q) = my_and(Q, P)\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  ?\n"
        "end\n"
    )
    fp = tmp_path / "preview_expand.pf"
    fp.write_text(src)
    payload = await _call(
        server,
        "preview_expand_at",
        {"path": str(fp), "line": 5, "column": 3, "names": ["my_and"]},
    )
    assert payload is not None
    assert payload["outcome"] == "ok"
    assert "my_and" in payload["before"]
    assert "my_and" not in payload["after"]


@pytest.mark.anyio
async def test_preview_expand_at_returns_unknown(server, tmp_path):
    src = (
        "theorem t: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume H: P\n"
        "  ?\n"
        "end\n"
    )
    fp = tmp_path / "preview_expand_unknown.pf"
    fp.write_text(src)
    payload = await _call(
        server,
        "preview_expand_at",
        {"path": str(fp), "line": 5, "column": 3, "names": ["nope"]},
    )
    assert payload is not None
    assert payload["outcome"] == "unknown"
    assert payload["name"] == "nope"


# --------------------------------------------------------------------------
# available_lemmas_at
# --------------------------------------------------------------------------


@pytest.mark.anyio
async def test_available_lemmas_at_query_pattern(server, tmp_path):
    """Goal-shape pattern with `_` placeholders surfaces matching lemmas."""
    fp = tmp_path / "lemmas.pf"
    fp.write_text(
        "theorem helper_le_zero: all x:bool. x = x\n"
        "proof\n"
        "  arbitrary x:bool\n"
        "  reflexive\n"
        "end\n"
    )
    payload = await _call(
        server,
        "available_lemmas_at",
        {
            "path": str(fp),
            "line": 1,
            "column": 1,
            "query": "helper_le",
        },
    )
    assert isinstance(payload, list)
    names = [m["name"] for m in payload]
    assert "helper_le_zero" in names
    entry = next(m for m in payload if m["name"] == "helper_le_zero")
    assert entry["kind"] == "theorem"
    assert entry["module"] == "lemmas"
    assert 0.0 <= entry["relevance"] <= 1.0


@pytest.mark.anyio
async def test_available_lemmas_at_no_signal_browses(server, tmp_path):
    """No `?` and no `query`: browse mode surfaces every in-scope
    lemma so off-hole exploration works (issue #418)."""
    fp = tmp_path / "browse.pf"
    fp.write_text(
        "theorem alpha: true\nproof\n  .\nend\n"
        "\n"
        "theorem beta: true\nproof\n  .\nend\n"
        "\n"
        "theorem gamma: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  reflexive\n"
        "end\n"
    )
    payload = await _call(
        server,
        "available_lemmas_at",
        {"path": str(fp), "line": 9, "column": 3},
    )
    assert isinstance(payload, list)
    names = {m["name"] for m in payload}
    assert {"alpha", "beta", "gamma"} <= names


# --------------------------------------------------------------------------
# auto_rules_at
# --------------------------------------------------------------------------


@pytest.mark.anyio
async def test_auto_rules_at_returns_each_in_scope_rule(server, tmp_path):
    """Two ``auto`` declarations, cursor past both -> both surfaced
    in declaration order with their rendered equations."""
    src = (
        "union Foo {\n"
        "  fzero\n"
        "  fsucc(Foo)\n"
        "}\n"
        "\n"
        "recursive fadd(Foo, Foo) -> Foo {\n"
        "  fadd(fzero, y) = y\n"
        "  fadd(fsucc(x), y) = fsucc(fadd(x, y))\n"
        "}\n"
        "\n"
        "theorem fadd_zero_left: all y:Foo. fadd(fzero, y) = y\n"
        "proof\n"
        "  arbitrary y:Foo\n"
        "  conclude fadd(fzero, y) = y by expand fadd.\n"
        "end\n"
        "auto fadd_zero_left\n"
        "\n"
        "theorem fadd_succ:\n"
        "  all x:Foo, y:Foo. fadd(fsucc(x), y) = fsucc(fadd(x, y))\n"
        "proof\n"
        "  arbitrary x:Foo, y:Foo\n"
        "  conclude fadd(fsucc(x), y) = fsucc(fadd(x, y))\n"
        "    by expand fadd.\n"
        "end\n"
        "auto fadd_succ\n"
        "\n"
        "theorem use_them: all z:Foo. z = z\n"
        "proof\n"
        "  arbitrary z:Foo\n"
        "  ?\n"
        "end\n"
    )
    fp = tmp_path / "auto.pf"
    fp.write_text(src)
    payload = await _call(
        server,
        "auto_rules_at",
        {"path": str(fp), "line": 30, "column": 3},
    )
    assert isinstance(payload, list)
    names = [r["name"] for r in payload]
    assert names == ["fadd_zero_left", "fadd_succ"]
    assert all(r["module"] == "auto" for r in payload)
    assert "fadd(fzero, y) = y" in payload[0]["equation"]
    assert "fadd(fsucc(x), y)" in payload[1]["equation"]


@pytest.mark.anyio
async def test_auto_rules_at_returns_empty_when_no_rules_in_scope(
    server, tmp_path
):
    src = (
        "theorem t: true\n"
        "proof\n"
        "  .\n"
        "end\n"
    )
    fp = tmp_path / "empty.pf"
    fp.write_text(src)
    payload = await _call(
        server,
        "auto_rules_at",
        {"path": str(fp), "line": 3, "column": 3},
    )
    assert payload == []


# --------------------------------------------------------------------------
# pytest-anyio plumbing -- pytest.mark.anyio needs an event-loop fixture
# --------------------------------------------------------------------------


@pytest.fixture
def anyio_backend():
    return "asyncio"
