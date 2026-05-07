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

    def get_text_document(self, uri: str) -> SimpleNamespace:
        if uri not in self._docs:
            raise KeyError(uri)
        return self._docs[uri]


class FakeServer:
    """Just enough of ``LanguageServer`` to drive the handlers."""

    def __init__(self) -> None:
        self.workspace = _FakeWorkspace()
        self.published: dict[str, list[lsp_types.Diagnostic]] = {}

    def publish_diagnostics(
        self, uri: str, diagnostics: list[lsp_types.Diagnostic]
    ) -> None:
        self.published[uri] = list(diagnostics)


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
        lsp_server.GOAL_AT_REQUEST,
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
