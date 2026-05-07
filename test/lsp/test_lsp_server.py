"""End-to-end tests for the LSP adapter (Phase 2 / Step 9).

The protocol-level transport (``initialize`` / message framing /
JSON-RPC) is covered by ``pygls`` itself. What we own here is the
*translation* layer: LSP 0-indexed positions <-> query-API 1-indexed,
``textDocument/...`` parameter shapes <-> ``lsp.query`` calls,
diagnostics being routed to the right URI.

Tests call the registered feature handlers as plain Python callables,
passing a fake server that just exposes ``workspace`` and
``publish_diagnostics`` -- the surface the handlers actually touch.
That keeps the tests fast (no JSON-RPC subprocess) and pinned on the
mapping logic that's specific to this PR.
"""

from __future__ import annotations

import sys
from pathlib import Path
from types import SimpleNamespace
from typing import Optional

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

# Skip if pygls isn't installed -- it's optional.
pygls = pytest.importorskip("pygls")
lsprotocol = pytest.importorskip("lsprotocol")

# Configure no-prelude before import: the lsp_server module captures
# the prelude at module-load time, so this has to land first.
import os  # noqa: E402

os.environ["DEDUCE_NO_STDLIB"] = "1"

from lsprotocol import types as lsp_types  # noqa: E402

from lsp import lsp_server  # noqa: E402


# --------------------------------------------------------------------------
# Fake server used in place of the real LanguageServer
# --------------------------------------------------------------------------


class _FakeWorkspace:
    def __init__(self) -> None:
        self._docs: dict[str, SimpleNamespace] = {}

    def add_document(self, uri: str, content: str) -> None:
        self._docs[uri] = SimpleNamespace(source=content, uri=uri)

    def update_document(self, uri: str, content: str) -> None:
        """Simulate pygls's `update_text_document` for the Full
        TextDocumentSyncKind: replace the document's source."""
        if uri not in self._docs:
            raise KeyError(uri)
        self._docs[uri].source = content

    def get_text_document(self, uri: str) -> SimpleNamespace:
        if uri not in self._docs:
            raise KeyError(uri)
        return self._docs[uri]


class FakeServer:
    """Just enough of ``LanguageServer`` to drive the handlers.

    Mirrors pygls 2.x's API: ``text_document_publish_diagnostics``
    takes a ``PublishDiagnosticsParams`` rather than the pre-2.x
    ``publish_diagnostics(uri, list)`` shape.
    """

    def __init__(self) -> None:
        self.workspace = _FakeWorkspace()
        self.published: dict[str, list[lsp_types.Diagnostic]] = {}

    def text_document_publish_diagnostics(
        self, params: lsp_types.PublishDiagnosticsParams
    ) -> None:
        self.published[params.uri] = list(params.diagnostics)


def _file_uri(path: Path) -> str:
    return path.absolute().as_uri()


@pytest.fixture
def server() -> FakeServer:
    return FakeServer()


@pytest.fixture
def open_doc(server: FakeServer, tmp_path: Path):
    """Helper: write source to a temp .pf, register it with the
    workspace, and return ``(path, uri)``."""

    def _open(name: str, source: str) -> tuple[Path, str]:
        fp = tmp_path / name
        fp.write_text(source)
        uri = _file_uri(fp)
        server.workspace.add_document(uri, source)
        return fp, uri

    return _open


# --------------------------------------------------------------------------
# Feature registration
# --------------------------------------------------------------------------


def test_all_expected_features_are_registered():
    fm = lsp_server.server.protocol.fm
    expected = {
        lsp_types.TEXT_DOCUMENT_DID_OPEN,
        lsp_types.TEXT_DOCUMENT_DID_SAVE,
        lsp_types.TEXT_DOCUMENT_DID_CHANGE,
        lsp_types.TEXT_DOCUMENT_DID_CLOSE,
        lsp_types.TEXT_DOCUMENT_DEFINITION,
        lsp_types.TEXT_DOCUMENT_DOCUMENT_SYMBOL,
        lsp_types.TEXT_DOCUMENT_CODE_ACTION,
        lsp_server.GOAL_AT_REQUEST,
        lsp_server.CASE_SPLIT_REQUEST,
        lsp_server.SPLITTABLE_VARS_REQUEST,
    }
    assert expected.issubset(set(fm.features))


# --------------------------------------------------------------------------
# Position translation helpers
# --------------------------------------------------------------------------


def test_query_position_is_one_indexed_from_lsp():
    """LSP (0,0) becomes query (1,1)."""
    p = lsp_server._query_pos_from_lsp(lsp_types.Position(line=0, character=0))
    assert p.line == 1
    assert p.column == 1


def test_lsp_range_is_zero_indexed_from_query():
    """Query 1.1-1.5 becomes LSP 0.0-0.4."""
    from lsp.query import Position, Range

    rng = Range(
        start=Position(line=1, column=1),
        end=Position(line=1, column=5),
    )
    out = lsp_server._lsp_range_from_query(rng)
    assert out.start.line == 0
    assert out.start.character == 0
    assert out.end.line == 0
    assert out.end.character == 4


# --------------------------------------------------------------------------
# Diagnostics on didOpen / didSave
# --------------------------------------------------------------------------


def test_did_open_publishes_no_diagnostics_for_valid_file(
    server, open_doc
):
    fp, uri = open_doc(
        "valid.pf",
        "theorem t: true\nproof\n  .\nend\n",
    )
    params = lsp_types.DidOpenTextDocumentParams(
        text_document=lsp_types.TextDocumentItem(
            uri=uri,
            language_id="deduce",
            version=1,
            text=fp.read_text(),
        )
    )
    lsp_server.on_did_open(server, params)
    assert server.published[uri] == []


def test_did_open_publishes_error_diagnostic_for_broken_file(
    server, open_doc
):
    fp, uri = open_doc(
        "broken.pf",
        # Try to prove `false` by reflexive -- type-check fails.
        "theorem broken: false\nproof\n  .\nend\n",
    )
    params = lsp_types.DidOpenTextDocumentParams(
        text_document=lsp_types.TextDocumentItem(
            uri=uri,
            language_id="deduce",
            version=1,
            text=fp.read_text(),
        )
    )
    lsp_server.on_did_open(server, params)
    diags = server.published[uri]
    assert len(diags) == 1
    diag = diags[0]
    assert diag.severity == lsp_types.DiagnosticSeverity.Error
    assert diag.source == lsp_server.SERVER_NAME
    # Diagnostic is on a line within the file (LSP is 0-indexed; the
    # error fires inside the proof body or signature, lines 0..3).
    assert 0 <= diag.range.start.line <= 3


def test_did_save_re_runs_diagnostics(server, open_doc):
    fp, uri = open_doc(
        "save.pf",
        "theorem t: true\nproof\n  .\nend\n",
    )
    save_params = lsp_types.DidSaveTextDocumentParams(
        text_document=lsp_types.TextDocumentIdentifier(uri=uri),
    )
    lsp_server.on_did_save(server, save_params)
    assert server.published[uri] == []


def test_did_change_re_runs_diagnostics(server, open_doc):
    """`on_did_change' republishes diagnostics so the underline
    tracks the buffer's `?` location after a refactor edit."""
    # Open with a hole present -> diagnostic published on didOpen.
    src1 = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  ?\n"
        "end\n"
    )
    _, uri = open_doc("didchange.pf", src1)
    open_params = lsp_types.DidOpenTextDocumentParams(
        text_document=lsp_types.TextDocumentItem(
            uri=uri,
            language_id="deduce",
            version=1,
            text=src1,
        )
    )
    lsp_server.on_did_open(server, open_params)
    assert len(server.published[uri]) == 1
    initial_line = server.published[uri][0].range.start.line  # `?` on
    #  0-indexed line 2.
    assert initial_line == 2

    # Simulate a refactor edit: replace the `?` with an
    # `arbitrary P:bool\n  ?` skeleton.  The new `?` is now on line
    # 4 (0-indexed line 3).
    src2 = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  ?\n"
        "end\n"
    )
    server.workspace.update_document(uri, src2)

    change_params = lsp_types.DidChangeTextDocumentParams(
        text_document=lsp_types.VersionedTextDocumentIdentifier(
            uri=uri, version=2
        ),
        content_changes=[],  # pygls already applied; we drive the handler
    )
    lsp_server.on_did_change(server, change_params)

    # Diagnostic re-published; the new range follows the new `?`.
    assert len(server.published[uri]) == 1
    new_line = server.published[uri][0].range.start.line
    assert new_line == 3, (
        f"diagnostic line should follow the new `?` (line 3, 0-indexed); "
        f"got {new_line}"
    )


def test_did_change_clears_diagnostics_when_proof_completes(
    server, open_doc
):
    """If the buffer change makes the proof valid, the
    `on_did_change' re-publish clears the previously-published
    diagnostic."""
    src_with_hole = "theorem t: true\nproof\n  ?\nend\n"
    _, uri = open_doc("complete.pf", src_with_hole)
    open_params = lsp_types.DidOpenTextDocumentParams(
        text_document=lsp_types.TextDocumentItem(
            uri=uri,
            language_id="deduce",
            version=1,
            text=src_with_hole,
        )
    )
    lsp_server.on_did_open(server, open_params)
    assert len(server.published[uri]) == 1

    # Replace `?` with `.` -- now the proof validates.
    server.workspace.update_document(
        uri, "theorem t: true\nproof\n  .\nend\n"
    )
    change_params = lsp_types.DidChangeTextDocumentParams(
        text_document=lsp_types.VersionedTextDocumentIdentifier(
            uri=uri, version=2
        ),
        content_changes=[],
    )
    lsp_server.on_did_change(server, change_params)

    assert server.published[uri] == []


def test_did_close_clears_diagnostics(server, open_doc):
    _, uri = open_doc("close.pf", "theorem t: true\nproof\n  .\nend\n")
    # Pretend a previous run had stored some diagnostics.
    server.published[uri] = [
        lsp_types.Diagnostic(
            range=lsp_types.Range(
                start=lsp_types.Position(line=0, character=0),
                end=lsp_types.Position(line=0, character=1),
            ),
            severity=lsp_types.DiagnosticSeverity.Error,
            message="stale",
        )
    ]
    close_params = lsp_types.DidCloseTextDocumentParams(
        text_document=lsp_types.TextDocumentIdentifier(uri=uri),
    )
    lsp_server.on_did_close(server, close_params)
    assert server.published[uri] == []


# --------------------------------------------------------------------------
# Definition
# --------------------------------------------------------------------------


def test_definition_resolves_theorem_reference(server, open_doc):
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
    _, uri = open_doc("defn.pf", src)
    # LSP coords: line 7, character 2 (the `t1` reference inside t2's proof).
    params = lsp_types.DefinitionParams(
        text_document=lsp_types.TextDocumentIdentifier(uri=uri),
        position=lsp_types.Position(line=7, character=2),
    )
    loc = lsp_server.on_definition(server, params)
    assert loc is not None
    assert loc.uri == uri
    # ``theorem t1`` starts at LSP line 0 (1-indexed query line 1 minus 1).
    assert loc.range.start.line == 0


def test_definition_returns_none_on_whitespace(server, open_doc):
    src = "theorem t1: true\nproof\n  .\nend\n"
    _, uri = open_doc("ws.pf", src)
    params = lsp_types.DefinitionParams(
        text_document=lsp_types.TextDocumentIdentifier(uri=uri),
        # LSP line 2, character 0 -- whitespace at the start of `  .`.
        position=lsp_types.Position(line=2, character=0),
    )
    assert lsp_server.on_definition(server, params) is None


# --------------------------------------------------------------------------
# Document symbols
# --------------------------------------------------------------------------


def test_document_symbol_lists_each_top_level_decl(server, open_doc):
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
    _, uri = open_doc("outline.pf", src)
    params = lsp_types.DocumentSymbolParams(
        text_document=lsp_types.TextDocumentIdentifier(uri=uri),
    )
    syms = lsp_server.on_document_symbol(server, params)
    by_name = {s.name: s for s in syms}
    assert set(by_name) == {"t1", "X", "Color"}
    assert by_name["t1"].kind == lsp_types.SymbolKind.Function
    assert by_name["X"].kind == lsp_types.SymbolKind.Constant
    assert by_name["Color"].kind == lsp_types.SymbolKind.Enum
    # Ranges echo the declaration spans (0-indexed LSP).
    assert by_name["t1"].range.start.line == 0
    assert by_name["X"].range.start.line == 5
    assert by_name["Color"].range.start.line == 7


# --------------------------------------------------------------------------
# Custom deduce/goalAt request
# --------------------------------------------------------------------------


def test_goal_at_returns_goal_dict(server, open_doc):
    src = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  reflexive\n"
        "end\n"
    )
    _, uri = open_doc("goal.pf", src)
    # LSP coords: line 3, character 0 (the start of the line holding
    # `reflexive`, before any non-whitespace) -- 1-indexed query
    # equivalent is line 4, column 1.
    params = {
        "textDocument": {"uri": uri},
        "position": {"line": 3, "character": 0},
    }
    goal = lsp_server.on_goal_at(server, params)
    assert goal is not None
    assert goal["formula"] == "P = P"
    assert goal["givens"] == []
    # Range is echoed back at the cursor.
    assert goal["range"]["start"]["line"] == 3
    assert goal["range"]["start"]["character"] == 0


def test_goal_at_returns_none_outside_proof(server, open_doc):
    src = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  reflexive\n"
        "end\n"
        "\n"
        "-- after end\n"
    )
    _, uri = open_doc("none.pf", src)
    params = {
        "textDocument": {"uri": uri},
        "position": {"line": 6, "character": 0},
    }
    assert lsp_server.on_goal_at(server, params) is None


# --------------------------------------------------------------------------
# Defensive paths: missing document, missing URI
# --------------------------------------------------------------------------


def test_definition_with_unknown_uri_returns_none(server):
    params = lsp_types.DefinitionParams(
        text_document=lsp_types.TextDocumentIdentifier(uri="file:///nope.pf"),
        position=lsp_types.Position(line=0, character=0),
    )
    assert lsp_server.on_definition(server, params) is None


def test_goal_at_without_uri_returns_none(server):
    assert lsp_server.on_goal_at(server, {}) is None


# --------------------------------------------------------------------------
# Prelude scoping (regression for the lib/* self-import bug)
# --------------------------------------------------------------------------


def test_prelude_for_lib_file_is_empty():
    """Files inside ``lib/`` are themselves part of the prelude;
    auto-prepending the prelude when checking one would import
    the file twice and trip ``theorem names may not be overloaded``.
    Mirrors ``deduce.py``'s ``check_in_prelude`` logic."""
    lib_file = REPO_ROOT / "lib" / "Nat.pf"
    if not lib_file.exists():
        pytest.skip(f"{lib_file} not present in this checkout")
    assert lsp_server._prelude_for(str(lib_file)) == ()


def test_prelude_for_user_file_is_default():
    """A file outside ``lib/`` gets the configured prelude."""
    # `_PRELUDE` is captured at import time; it could be `()` if the
    # test process set DEDUCE_NO_STDLIB=1 (as test_mcp_server.py
    # does). Either way, a user-file path should match `_PRELUDE`
    # exactly, while a lib-path returns `()`.
    user_file = REPO_ROOT / "test" / "should-validate" / "after.pf"
    if not user_file.exists():
        pytest.skip(f"{user_file} not present")
    assert lsp_server._prelude_for(str(user_file)) == lsp_server._PRELUDE


def test_path_is_in_lib_helper():
    lib_file = REPO_ROOT / "lib" / "Nat.pf"
    if lib_file.exists():
        assert lsp_server._path_is_in_lib(str(lib_file)) is True
    user_file = REPO_ROOT / "test" / "should-validate" / "after.pf"
    if user_file.exists():
        assert lsp_server._path_is_in_lib(str(user_file)) is False
    # Nonexistent path: the resolve() walks the parents that do exist;
    # if its lexical prefix matches lib/, it counts as in lib.
    assert lsp_server._path_is_in_lib("/nope/not-a-path.pf") is False


# --------------------------------------------------------------------------
# Code actions: refine_at (Phase 4 / Step 15)
# --------------------------------------------------------------------------


def test_code_action_offers_refine_when_cursor_on_hole(server, open_doc):
    """Cursor on a `?` whose goal is a recognised shape -> one
    RefactorRewrite action carrying a single-file WorkspaceEdit."""
    src = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  ?\n"
        "end\n"
    )
    fp, uri = open_doc("refine.pf", src)
    # LSP coords for the `?` at line 4 col 3 (1-indexed) -- that's
    # line=3, character=2 in LSP-space.
    params = lsp_types.CodeActionParams(
        text_document=lsp_types.TextDocumentIdentifier(uri=uri),
        range=lsp_types.Range(
            start=lsp_types.Position(line=3, character=2),
            end=lsp_types.Position(line=3, character=2),
        ),
        context=lsp_types.CodeActionContext(diagnostics=[]),
    )
    actions = lsp_server.on_code_action(server, params)
    assert len(actions) == 1
    action = actions[0]
    assert action.title == "Refine hole"
    assert action.kind == lsp_types.CodeActionKind.RefactorRewrite
    # The edit has one TextEdit in the file's URI bucket.
    assert action.edit is not None
    assert list(action.edit.changes.keys()) == [uri]
    edits = action.edit.changes[uri]
    assert len(edits) == 1
    text_edit = edits[0]
    assert text_edit.new_text == "reflexive"
    # Range covers exactly the `?` (LSP 0-indexed: line 3, col 2-3).
    assert text_edit.range.start == lsp_types.Position(line=3, character=2)
    assert text_edit.range.end == lsp_types.Position(line=3, character=3)


def test_code_action_returns_empty_when_cursor_not_on_hole(server, open_doc):
    """No `?` near the cursor -> no actions offered."""
    src = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  reflexive\n"
        "end\n"
    )
    _, uri = open_doc("complete.pf", src)
    params = lsp_types.CodeActionParams(
        text_document=lsp_types.TextDocumentIdentifier(uri=uri),
        range=lsp_types.Range(
            start=lsp_types.Position(line=3, character=2),
            end=lsp_types.Position(line=3, character=2),
        ),
        context=lsp_types.CodeActionContext(diagnostics=[]),
    )
    assert lsp_server.on_code_action(server, params) == []


def test_code_action_with_unknown_uri_returns_empty(server):
    """Defensive: the workspace doesn't know about this URI."""
    params = lsp_types.CodeActionParams(
        text_document=lsp_types.TextDocumentIdentifier(uri="file:///nope.pf"),
        range=lsp_types.Range(
            start=lsp_types.Position(line=0, character=0),
            end=lsp_types.Position(line=0, character=0),
        ),
        context=lsp_types.CodeActionContext(diagnostics=[]),
    )
    assert lsp_server.on_code_action(server, params) == []


def test_chained_refine_after_workspace_update(server, open_doc):
    """End-to-end transport simulation for issue #339.

    Sequence:
    1. didOpen with `?` at line 3 col 3.
    2. codeAction at the `?` -> returns refine action.
    3. Simulate the client applying the edit + sending didChange:
       update the workspace document with the new content.
    4. codeAction at the new `?` (line 4 col 3) -> should ALSO
       return a refine action, against the UPDATED workspace.

    Step 4 is what failed in the user's manual test before the
    fix shipped: the second codeAction saw stale buffer content
    because eglot's didChange hadn't gone out yet.  The
    server-side handler is correct; this test pins the contract
    that pygls' workspace update + our handler do the right
    thing when the didChange DOES arrive.
    """
    src = (
        "theorem t: all P:bool. if P then P\n"
        "proof\n"
        "  ?\n"
        "end\n"
    )
    _, uri = open_doc("chain.pf", src)

    # Round 1: codeAction at the `?` (LSP line 2, col 2).
    params1 = lsp_types.CodeActionParams(
        text_document=lsp_types.TextDocumentIdentifier(uri=uri),
        range=lsp_types.Range(
            start=lsp_types.Position(line=2, character=2),
            end=lsp_types.Position(line=2, character=2),
        ),
        context=lsp_types.CodeActionContext(diagnostics=[]),
    )
    actions1 = lsp_server.on_code_action(server, params1)
    assert len(actions1) == 1, (
        f"first codeAction should return one refine action; got {actions1!r}"
    )
    assert actions1[0].title == "Refine hole"
    edit1 = actions1[0].edit.changes[uri][0]
    # Eglot would apply this edit locally and then send didChange.
    # Simulate the post-edit content here.
    new_text = "arbitrary P:bool\n  ?"
    src_after = src.replace("  ?", "  " + new_text, 1)
    server.workspace.update_document(uri, src_after)

    # Round 2: codeAction at the NEW `?` (now at LSP line 3 col 2).
    params2 = lsp_types.CodeActionParams(
        text_document=lsp_types.TextDocumentIdentifier(uri=uri),
        range=lsp_types.Range(
            start=lsp_types.Position(line=3, character=2),
            end=lsp_types.Position(line=3, character=2),
        ),
        context=lsp_types.CodeActionContext(diagnostics=[]),
    )
    actions2 = lsp_server.on_code_action(server, params2)
    assert len(actions2) == 1, (
        f"second codeAction should return another refine action; "
        f"got {actions2!r}.  This is the issue-#339 regression: if the "
        f"workspace update isn't visible to the handler, the second "
        f"refine fails."
    )
    assert actions2[0].title == "Refine hole"


# --------------------------------------------------------------------------
# Custom requests: deduce/splittableVarsAt and deduce/caseSplitAt
# (Phase 4 / Step 16)
# --------------------------------------------------------------------------


def test_splittable_vars_at_returns_in_scope_variables(server, open_doc):
    """Cursor on a `?`; the response lists splittable variables in
    scope at that hole."""
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
    _, uri = open_doc("splittable.pf", src)
    # `?` at line 10 col 3 (1-indexed) -> LSP line 9, char 2.
    params = {
        "textDocument": {"uri": uri},
        "position": {"line": 9, "character": 2},
    }
    result = lsp_server.on_splittable_vars_at(server, params)
    assert result == ["H", "x"]


def test_splittable_vars_at_returns_empty_off_hole(server, open_doc):
    """Cursor not on a `?` -> empty list."""
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
    _, uri = open_doc("splittable_off.pf", src)
    # On `arbitrary` keyword, line 8 col 3 -> LSP line 7, char 2.
    params = {
        "textDocument": {"uri": uri},
        "position": {"line": 7, "character": 2},
    }
    assert lsp_server.on_splittable_vars_at(server, params) == []


def test_case_split_at_returns_workspace_edit_for_union_variable(
    server, open_doc
):
    """Cursor on `?`, variable=`x` (Union-typed) -> WorkspaceEdit
    with switch skeleton."""
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
    _, uri = open_doc("split.pf", src)
    # `?` at line 9 col 3 -> LSP line 8, char 2.
    params = {
        "textDocument": {"uri": uri},
        "position": {"line": 8, "character": 2},
        "variable": "x",
    }
    result = lsp_server.on_case_split_at(server, params)
    assert result is not None
    assert "changes" in result
    edits = result["changes"][uri]
    assert len(edits) == 1
    assert "switch x" in edits[0]["newText"]
    assert "case z {" in edits[0]["newText"]
    assert "case s(n1) {" in edits[0]["newText"]
    assert edits[0]["range"]["start"] == {"line": 8, "character": 2}
    assert edits[0]["range"]["end"] == {"line": 8, "character": 3}


def test_case_split_at_returns_null_for_unknown_variable(server, open_doc):
    """The variable name doesn't match any in-scope binding -> null."""
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
    _, uri = open_doc("split_bad.pf", src)
    params = {
        "textDocument": {"uri": uri},
        "position": {"line": 8, "character": 2},
        "variable": "no_such_var",
    }
    assert lsp_server.on_case_split_at(server, params) is None


def test_case_split_at_returns_null_when_variable_omitted(server, open_doc):
    """Missing `variable` field -> null (defensive)."""
    src = "x"
    _, uri = open_doc("noop.pf", src)
    params = {
        "textDocument": {"uri": uri},
        "position": {"line": 0, "character": 0},
    }
    assert lsp_server.on_case_split_at(server, params) is None
