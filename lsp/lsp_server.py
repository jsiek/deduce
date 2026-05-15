"""LSP adapter for the Deduce query API (Phase 2 / Step 9).

Wraps the four ``lsp.query`` functions in standard Language Server
Protocol features, plus a custom ``deduce/goalAt`` request for proof
goals (LSP has no built-in for "what proof obligation is at this
cursor"). Document content is taken from pygls's open-buffer
workspace, so the queries see unsaved edits.

Run directly to start the stdio server::

    python3 -m lsp.lsp_server

Wire it into VS Code by pointing an LSP client at that command --
the existing ``deduce-mode`` extensions could grow a client
configuration that does so. See :mod:`lsp.mcp_server` for the MCP
sibling that exposes the same query helpers as tools.

Coordinate conventions
----------------------

LSP uses 0-indexed lines and 0-indexed UTF-16 characters; ``lsp.query``
uses 1-indexed lines and 1-indexed columns to match Deduce's existing
error messages. The translation is a simple ``+1`` / ``-1`` per
coordinate, performed at the boundary in the helpers below.

The LSP boundary stays protocol-specific: the only consumer of
``pygls`` and ``lsprotocol`` lives here. The query API itself is
unchanged.
"""

from __future__ import annotations

import os
import sys
from collections.abc import Mapping
from pathlib import Path
from typing import Optional, cast


# ---------------------------------------------------------------------------
# Bootstrap: configure the Deduce environment once at import.
# Mirrors lsp.mcp_server -- see that module's docstring for the
# DEDUCE_ROOT / DEDUCE_NO_STDLIB knobs.
# ---------------------------------------------------------------------------


def _resolve_deduce_root() -> Path:
    env_root = os.environ.get("DEDUCE_ROOT")
    if env_root:
        return Path(env_root).resolve()
    return Path(__file__).resolve().parent.parent


_DEDUCE_ROOT = _resolve_deduce_root()
_LIB_DIR = _DEDUCE_ROOT / "lib"
_TEST_IMPORTS_DIR = _DEDUCE_ROOT / "test" / "test-imports"

_PSEUDO_ENTRY = str(_DEDUCE_ROOT / "deduce.py")
sys.argv = [_PSEUDO_ENTRY] + sys.argv[1:]
sys.setrecursionlimit(10000)

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
    if os.environ.get("DEDUCE_NO_STDLIB") == "1":
        return ()
    if not _LIB_DIR.is_dir():
        return ()
    return tuple(sorted(p.stem for p in _LIB_DIR.glob("*.pf")))


_PRELUDE = _default_prelude()


def _path_is_in_lib(path: str) -> bool:
    """True iff ``path`` lives inside the standard library directory.

    Files inside ``lib/`` are themselves part of the prelude, so when
    we check one we must NOT auto-prepend the prelude -- otherwise
    the file gets imported twice (once via the prelude, once as the
    user file) and every theorem in it triggers
    ``theorem names may not be overloaded``.
    """
    try:
        Path(path).resolve().relative_to(_LIB_DIR.resolve())
    except (OSError, ValueError):
        return False
    return True


def _prelude_for(path: str) -> tuple[str, ...]:
    """Return the prelude appropriate for checking ``path``.

    Mirrors ``deduce.py``'s ``check_in_prelude`` logic: empty prelude
    for files that are themselves part of the standard library, the
    full default prelude otherwise.
    """
    return () if _path_is_in_lib(path) else _PRELUDE


# ---------------------------------------------------------------------------
# Server definition
# ---------------------------------------------------------------------------


from lsprotocol import types as lsp_types  # noqa: E402
from pygls.lsp.server import LanguageServer  # noqa: E402

from lsp import query as _query  # noqa: E402


SERVER_NAME = "deduce-lsp"
SERVER_VERSION = "0.1.0"

# Custom request method name for "what's the goal at this cursor".
# LSP has no built-in for this; downstream clients can issue a
# raw request with this method.
GOAL_AT_REQUEST = "deduce/goalAt"

# Custom requests for Step 16 (case split). ``deduce/caseSplitAt``
# carries the user-supplied variable name in its params, which
# ``textDocument/codeAction`` can't do; ``deduce/splittableVarsAt``
# returns the candidate variable names so editor clients can offer
# completion before prompting.
CASE_SPLIT_REQUEST = "deduce/caseSplitAt"
SPLITTABLE_VARS_REQUEST = "deduce/splittableVarsAt"

# Custom requests for Step 18 (eliminate / use-fact).  Same shape as
# the case-split pair: the editor fetches candidate labels via
# ``deduce/eliminableVarsAt`` for completion, then issues
# ``deduce/eliminateAt`` with the user's chosen label.
ELIMINATE_REQUEST = "deduce/eliminateAt"
ELIMINABLE_VARS_REQUEST = "deduce/eliminableVarsAt"

# Custom requests for issue #353 (fill hole with a given).  Same shape
# as the eliminate pair: the editor fetches matching-given labels via
# ``deduce/matchingGivensAt`` for completion, then issues
# ``deduce/fillFromGivenAt`` with the user's chosen label.
FILL_FROM_GIVEN_REQUEST = "deduce/fillFromGivenAt"
MATCHING_GIVENS_REQUEST = "deduce/matchingGivensAt"

# Custom request for the Claude hole-fill sidecar (hole-fill-plan
# Phase 1 / Step 2). Returns goal + givens + lemmas-in-scope +
# fingerprint for the ``?`` token at the cursor. Sibling to
# ``deduce/goalAt``; richer payload, doesn't disturb that contract.
HOLE_CONTEXT_AT_REQUEST = "deduce/holeContextAt"

# Custom request for the Claude hole-fill sidecar (hole-fill-plan
# Phase 1 / Step 4). Splices a candidate proof into the open buffer
# at a hole range and runs the checker, returning {ok, error}. The
# sidecar calls this on each candidate Claude generates.
VALIDATE_PROOF_REQUEST = "deduce/validateProof"

server = LanguageServer(
    SERVER_NAME,
    SERVER_VERSION,
    text_document_sync_kind=lsp_types.TextDocumentSyncKind.Full,
)


# --- Position / Range translation (LSP <-> query) -------------------------


def _query_pos_from_lsp(pos: lsp_types.Position) -> _query.Position:
    """LSP is 0-indexed line/character; query API is 1-indexed."""
    return _query.Position(line=pos.line + 1, column=pos.character + 1)


def _query_range_from_lsp(rng: lsp_types.Range) -> _query.Range:
    """Inverse of :func:`_lsp_range_from_query`: LSP-shaped Range to
    query-shaped Range, 0->1 indexed."""
    return _query.Range(
        start=_query_pos_from_lsp(rng.start),
        end=_query_pos_from_lsp(rng.end),
    )


def _lsp_range_from_query(rng: _query.Range) -> lsp_types.Range:
    return lsp_types.Range(
        start=lsp_types.Position(
            line=max(rng.start.line - 1, 0),
            character=max(rng.start.column - 1, 0),
        ),
        end=lsp_types.Position(
            line=max(rng.end.line - 1, 0),
            character=max(rng.end.column - 1, 0),
        ),
    )


def _severity_to_lsp(sev: _query.Severity) -> lsp_types.DiagnosticSeverity:
    return {
        _query.Severity.ERROR: lsp_types.DiagnosticSeverity.Error,
        _query.Severity.WARNING: lsp_types.DiagnosticSeverity.Warning,
        _query.Severity.INFO: lsp_types.DiagnosticSeverity.Information,
        _query.Severity.HINT: lsp_types.DiagnosticSeverity.Hint,
    }[sev]


_SYMBOL_KIND_MAP: dict[_query.SymbolKind, lsp_types.SymbolKind] = {
    _query.SymbolKind.THEOREM: lsp_types.SymbolKind.Function,
    _query.SymbolKind.LEMMA: lsp_types.SymbolKind.Function,
    _query.SymbolKind.FUNCTION: lsp_types.SymbolKind.Function,
    _query.SymbolKind.DEFINE: lsp_types.SymbolKind.Constant,
    _query.SymbolKind.UNION: lsp_types.SymbolKind.Enum,
    _query.SymbolKind.PREDICATE: lsp_types.SymbolKind.Function,
    _query.SymbolKind.POSTULATE: lsp_types.SymbolKind.Function,
    _query.SymbolKind.IMPORT: lsp_types.SymbolKind.Module,
    _query.SymbolKind.OTHER: lsp_types.SymbolKind.Variable,
}


# --- Helpers --------------------------------------------------------------


def _path_from_uri(uri: str) -> str:
    """Extract a filesystem path from an LSP ``file://`` URI."""
    if uri.startswith("file://"):
        from urllib.parse import unquote, urlparse

        parsed = urlparse(uri)
        return unquote(parsed.path)
    return uri


def _uri_from_path(path: str) -> str:
    """Inverse of :func:`_path_from_uri`: build an LSP ``file://`` URI
    from a (possibly relative) filesystem path.  Used by the
    ``textDocument/definition`` handler when a match lives in an
    imported module rather than the request URI's file."""
    return Path(os.path.abspath(path)).as_uri()


def _document_content(ls: LanguageServer, uri: str) -> Optional[str]:
    """Read open-buffer contents from pygls's workspace."""
    try:
        doc = ls.workspace.get_text_document(uri)
    except KeyError:
        return None
    source: object = doc.source
    return source if isinstance(source, str) else None


def _publish_diagnostics(ls: LanguageServer, uri: str) -> None:
    content = _document_content(ls, uri)
    if content is None:
        return
    path = _path_from_uri(uri)
    diags = _query.check(path, content, prelude=_prelude_for(path))
    # pygls 2.x exposes the publish-diagnostics notification as
    # ``text_document_publish_diagnostics(params)``. The pre-2.x
    # ``publish_diagnostics(uri, list)`` shape was removed; calling
    # it raises ``AttributeError: 'LanguageServer' object has no
    # attribute 'publish_diagnostics'`` at runtime, which is what
    # eglot users hit on first connect.
    ls.text_document_publish_diagnostics(
        lsp_types.PublishDiagnosticsParams(
            uri=uri,
            diagnostics=[
                lsp_types.Diagnostic(
                    range=_lsp_range_from_query(d.range),
                    severity=_severity_to_lsp(d.severity),
                    message=d.message,
                    source=SERVER_NAME,
                    code=d.code,
                )
                for d in diags
            ],
        )
    )


# --- Document sync features ----------------------------------------------


@server.feature(lsp_types.TEXT_DOCUMENT_DID_OPEN)
def on_did_open(
    ls: LanguageServer, params: lsp_types.DidOpenTextDocumentParams
) -> None:
    """Run diagnostics when a file is opened."""
    _publish_diagnostics(ls, params.text_document.uri)


@server.feature(lsp_types.TEXT_DOCUMENT_DID_SAVE)
def on_did_save(
    ls: LanguageServer, params: lsp_types.DidSaveTextDocumentParams
) -> None:
    """Re-run diagnostics on save."""
    _publish_diagnostics(ls, params.text_document.uri)


@server.feature(lsp_types.TEXT_DOCUMENT_DID_CHANGE)
def on_did_change(
    ls: LanguageServer, params: lsp_types.DidChangeTextDocumentParams
) -> None:
    """Re-publish diagnostics so the underline tracks the buffer.

    pygls updates the workspace document content automatically before
    invoking this handler.  We then re-run ``check`` and republish so
    the editor's flymake/diagnostic underline moves to the new
    location of any ``?`` (or clears if the proof is now complete) --
    otherwise the underline stays pinned to the pre-edit `?` position
    and the user can't tell at a glance which hole still needs work.

    Trade-off: this fires on every didChange, including ones from
    ordinary typing.  Eglot debounces typing-driven didChanges via
    ``eglot-send-changes-idle-time`` (default 0.5s), so the cost is
    one ``check`` per pause-while-typing rather than per-keystroke.
    For typical proof files that's tolerable.  Step 12 of
    ``docs/lsp-plan.md`` (per-statement caching) is the proper
    long-term answer if this turns out to be too slow.
    """
    _publish_diagnostics(ls, params.text_document.uri)


@server.feature(lsp_types.TEXT_DOCUMENT_DID_CLOSE)
def on_did_close(
    ls: LanguageServer, params: lsp_types.DidCloseTextDocumentParams
) -> None:
    """Clear diagnostics when the editor closes the buffer."""
    ls.text_document_publish_diagnostics(
        lsp_types.PublishDiagnosticsParams(
            uri=params.text_document.uri,
            diagnostics=[],
        )
    )


# --- Query features ------------------------------------------------------


@server.feature(lsp_types.TEXT_DOCUMENT_DEFINITION)
def on_definition(
    ls: LanguageServer, params: lsp_types.DefinitionParams
) -> Optional[lsp_types.Location]:
    """Resolve a reference to its definition.

    ``definition_of`` follows imports, so the matched declaration may
    live in a different file from the request URI.  When that happens
    we build a fresh ``file://`` URI from the matched ``Location``'s
    ``path``; same-file matches reuse the incoming URI verbatim to
    avoid unnecessary path normalisation round-trips.
    """
    uri = params.text_document.uri
    content = _document_content(ls, uri)
    if content is None:
        return None
    path = _path_from_uri(uri)
    pos = _query_pos_from_lsp(params.position)
    loc = _query.definition_of(path, content, pos, prelude=_prelude_for(path))
    if loc is None:
        return None
    if os.path.abspath(loc.path) == os.path.abspath(path):
        target_uri = uri
    else:
        target_uri = _uri_from_path(loc.path)
    return lsp_types.Location(
        uri=target_uri,
        range=_lsp_range_from_query(loc.range),
    )


@server.feature(lsp_types.TEXT_DOCUMENT_DOCUMENT_SYMBOL)
def on_document_symbol(
    ls: LanguageServer, params: lsp_types.DocumentSymbolParams
) -> list[lsp_types.DocumentSymbol]:
    """Outline view: one entry per top-level declaration."""
    uri = params.text_document.uri
    content = _document_content(ls, uri)
    if content is None:
        return []
    path = _path_from_uri(uri)
    syms = _query.list_symbols(path, content, prelude=_prelude_for(path))
    return [
        lsp_types.DocumentSymbol(
            name=s.name,
            kind=_SYMBOL_KIND_MAP.get(s.kind, lsp_types.SymbolKind.Variable),
            range=_lsp_range_from_query(s.location.range),
            # ``selection_range`` is what the editor highlights when
            # navigating to the symbol. We don't have a separate "name
            # range" today, so reuse the full declaration range.
            selection_range=_lsp_range_from_query(s.location.range),
            detail=s.signature,
        )
        for s in syms
    ]


# Map ``CompletionCandidate.kind`` strings to LSP ``CompletionItemKind``
# enum values.  Defaults to ``Text`` for anything not in the table so
# unknown kinds don't crash the client.
_COMPLETION_KIND_MAP = {
    "keyword": lsp_types.CompletionItemKind.Keyword,
    "constant": lsp_types.CompletionItemKind.Constant,
    "type": lsp_types.CompletionItemKind.Class,
    "theorem": lsp_types.CompletionItemKind.Function,
    "lemma": lsp_types.CompletionItemKind.Function,
    "postulate": lsp_types.CompletionItemKind.Function,
    "predicate": lsp_types.CompletionItemKind.Function,
    "function": lsp_types.CompletionItemKind.Function,
    "rule": lsp_types.CompletionItemKind.Function,
    "define": lsp_types.CompletionItemKind.Variable,
    "union": lsp_types.CompletionItemKind.Class,
    "constructor": lsp_types.CompletionItemKind.Constructor,
    "label": lsp_types.CompletionItemKind.Variable,
    "variable": lsp_types.CompletionItemKind.Variable,
}


@server.feature(
    lsp_types.TEXT_DOCUMENT_COMPLETION,
    lsp_types.CompletionOptions(),
)
def on_completion(
    ls: LanguageServer, params: lsp_types.CompletionParams
) -> Optional[lsp_types.CompletionList]:
    """In-buffer completion.  Returns keywords + every top-level name
    reachable from the file (own declarations + transitive imports) +
    in-scope local bindings (proof labels and term variables visible
    at the cursor), letting the client filter by the typed prefix.

    When the cursor sits on an existing ``?`` and a goal is visible,
    labels whose formula equals or implies the goal sort first via
    ``sortText`` (priority 0); everything else sorts at priority 1.
    """
    uri = params.text_document.uri
    content = _document_content(ls, uri)
    if content is None:
        return None
    path = _path_from_uri(uri)
    pos = _query_pos_from_lsp(params.position)
    candidates = _query.completions_at(
        path, content, pos, prelude=_prelude_for(path)
    )
    items = [
        lsp_types.CompletionItem(
            label=c.label,
            kind=_COMPLETION_KIND_MAP.get(c.kind, lsp_types.CompletionItemKind.Text),
            detail=c.detail,
            # Encode the query-side priority as the LSP ``sortText''
            # field.  Clients sort lexicographically by it, so priority
            # 0 (matching-goal labels) come before priority 1 (everyone
            # else).  Appending the label keeps within-priority order
            # alphabetical.
            sort_text=f"{c.priority}{c.label}",
        )
        for c in candidates
    ]
    # ``is_incomplete=False`` tells the client our candidate set is
    # complete for this position -- it can cache and filter locally
    # rather than re-issuing ``textDocument/completion`` on every
    # keystroke.
    return lsp_types.CompletionList(is_incomplete=False, items=items)


def _get_field(obj: object | None, name: str) -> object | None:
    """Read a named field from a custom-request param value.

    pygls 2.x converts the JSON params for *known* LSP methods into
    typed dataclasses, but for custom methods (like ``deduce/goalAt'')
    it produces a generic ``LSPObject`` whose JSON keys become
    Python attributes.  Older pygls / direct test invocations may
    pass a plain ``dict`` instead.  Handle both shapes."""
    if obj is None:
        return None
    if isinstance(obj, Mapping):
        return obj.get(name)
    return cast(object | None, getattr(obj, name, None))


def _field_as_str(obj: object | None, name: str) -> Optional[str]:
    value = _get_field(obj, name)
    return value if isinstance(value, str) else None


def _field_as_int(obj: object | None, name: str) -> int:
    value = _get_field(obj, name)
    if isinstance(value, int):
        return value
    if isinstance(value, str):
        try:
            return int(value)
        except ValueError:
            return 0
    return 0


def _field_as_bool(obj: object | None, name: str, default: bool) -> bool:
    value = _get_field(obj, name)
    return value if isinstance(value, bool) else default


def _position_from_param(pos_obj: object | None) -> lsp_types.Position:
    return lsp_types.Position(
        line=_field_as_int(pos_obj, "line"),
        character=_field_as_int(pos_obj, "character"),
    )


def _range_payload_from_query(rng: _query.Range) -> dict[str, object]:
    return {
        "start": {
            "line": max(rng.start.line - 1, 0),
            "character": max(rng.start.column - 1, 0),
        },
        "end": {
            "line": max(rng.end.line - 1, 0),
            "character": max(rng.end.column - 1, 0),
        },
    }


def _workspace_edit_payload(
    uri: str, edit: _query.WorkspaceEdit
) -> dict[str, object]:
    return {
        "changes": {
            uri: [
                {
                    "range": _range_payload_from_query(edit.range),
                    "newText": edit.new_text,
                }
            ]
        }
    }


@server.feature(
    lsp_types.TEXT_DOCUMENT_CODE_ACTION,
    lsp_types.CodeActionOptions(
        code_action_kinds=[lsp_types.CodeActionKind.RefactorRewrite],
    ),
)
def on_code_action(
    ls: LanguageServer, params: lsp_types.CodeActionParams
) -> list[lsp_types.CodeAction]:
    """Surface Phase-4 structured edits as refactor.rewrite actions.

    Today's actions:

    - **Refine hole** (Step 15) -- offered when the cursor sits on a
      ``?`` whose goal has a recognised shape.
    - **Induction** (Step 17) -- offered when the cursor sits on a
      ``?`` whose goal is ``all x:T. P(x)`` with T a Union of two
      or more constructors.

    Step 16 (case split) takes a user-supplied variable name, which
    ``textDocument/codeAction`` can't carry, so it lives behind the
    custom ``deduce/caseSplitAt`` request instead. The Emacs binding
    prompts for the variable (with completion against
    ``deduce/splittableVarsAt``) before issuing the request.
    """
    uri = params.text_document.uri
    content = _document_content(ls, uri)
    if content is None:
        return []
    path = _path_from_uri(uri)
    pos = _query_pos_from_lsp(params.range.start)
    prelude = _prelude_for(path)

    actions: list[lsp_types.CodeAction] = []

    refine_edit = _query.refine_at(path, content, pos, prelude=prelude)
    if isinstance(refine_edit, _query.WorkspaceEdit):
        actions.append(
            _code_action_from_edit(uri, "Refine hole", refine_edit)
        )

    induction_edit = _query.induction_skeleton_at(
        path, content, pos, prelude=prelude
    )
    if induction_edit is not None:
        actions.append(
            _code_action_from_edit(uri, "Induction", induction_edit)
        )

    return actions


def _code_action_from_edit(
    uri: str, title: str, edit: _query.WorkspaceEdit
) -> lsp_types.CodeAction:
    """Wrap a query-API ``WorkspaceEdit`` as an LSP ``CodeAction``."""
    text_edit = lsp_types.TextEdit(
        range=_lsp_range_from_query(edit.range),
        new_text=edit.new_text,
    )
    workspace_edit = lsp_types.WorkspaceEdit(changes={uri: [text_edit]})
    return lsp_types.CodeAction(
        title=title,
        kind=lsp_types.CodeActionKind.RefactorRewrite,
        edit=workspace_edit,
    )


@server.feature(GOAL_AT_REQUEST)
def on_goal_at(
    ls: LanguageServer, params: object
) -> Optional[dict[str, object]]:
    """Custom request: return the proof goal at a cursor position.

    Params: ``{"textDocument": {"uri": "..."}, "position": {"line":
    int, "character": int}}`` (LSP-shaped position; 0-indexed).

    Result: ``{"formula": str, "givens": [{"label": str | None,
    "formula": str}], "range": Range}`` or ``null``.
    """
    text_doc = _get_field(params, "textDocument")
    pos_obj = _get_field(params, "position")
    uri = _field_as_str(text_doc, "uri")
    if not uri:
        return None
    content = _document_content(ls, uri)
    if content is None:
        return None
    pos = _query_pos_from_lsp(
        _position_from_param(pos_obj)
    )
    path = _path_from_uri(uri)
    goal = _query.goal_at(path, content, pos, prelude=_prelude_for(path))
    if goal is None:
        return None
    return {
        "formula": goal.formula,
        "givens": [
            {"label": g.label, "formula": g.formula} for g in goal.givens
        ],
        "range": _range_payload_from_query(goal.range),
    }


@server.feature(HOLE_CONTEXT_AT_REQUEST)
def on_hole_context_at(
    ls: LanguageServer, params: object
) -> Optional[dict[str, object]]:
    """Custom request: return rich context for the ``?`` at a cursor.

    Sibling to ``deduce/goalAt``; the hole-fill sidecar uses this to
    pick up the goal + givens + lemmas in scope before asking Claude
    for a proof, plus a fingerprint to detect that the hole moved or
    its statement changed before the answer comes back.

    Params: ``{"textDocument": {"uri": "..."}, "position": {"line":
    int, "character": int}, "includeLemmas": bool?}``. ``includeLemmas``
    defaults to ``True``.

    Result: ``{"holeRange": Range, "goal": str, "givens":
    [{"label": str | None, "formula": str}], "lemmasInScope":
    [{"name": str, "kind": str, "signature": str}], "fingerprint":
    str}`` or ``null``.
    """
    text_doc = _get_field(params, "textDocument")
    pos_obj = _get_field(params, "position")
    uri = _field_as_str(text_doc, "uri")
    if not uri:
        return None
    content = _document_content(ls, uri)
    if content is None:
        return None
    pos = _query_pos_from_lsp(
        _position_from_param(pos_obj)
    )
    include_lemmas = _field_as_bool(params, "includeLemmas", True)
    path = _path_from_uri(uri)
    ctx = _query.hole_context_at(
        path,
        content,
        pos,
        prelude=_prelude_for(path),
        include_lemmas=include_lemmas,
    )
    if ctx is None:
        return None
    return {
        "holeRange": _range_payload_from_query(ctx.hole_range),
        "goal": ctx.goal,
        "givens": [
            {"label": g.label, "formula": g.formula} for g in ctx.givens
        ],
        "lemmasInScope": [
            {
                "name": lemma.name,
                "kind": lemma.kind.value,
                "signature": lemma.signature,
            }
            for lemma in ctx.lemmas_in_scope
        ],
        "fingerprint": ctx.fingerprint,
    }


@server.feature(VALIDATE_PROOF_REQUEST)
def on_validate_proof(
    ls: LanguageServer, params: object
) -> dict[str, object]:
    """Custom request: splice a proof into the open buffer at a hole
    range and report whether the resulting file checks.

    Wraps :func:`lsp.query.validate_proof_at`. The sidecar uses this
    on each candidate Claude generates; first valid wins.

    Params: ``{"textDocument": {"uri": "..."}, "holeRange": Range,
    "proofText": str}``. ``holeRange`` is LSP-shaped (0-indexed) and
    must cover exactly the ``?`` token at the hole.

    Result: ``{"ok": bool, "error": str | None}``. Unlike
    ``deduce/holeContextAt`` and ``deduce/goalAt``, this never
    returns ``null`` -- callers always get a structured outcome,
    even on malformed params (``ok=False`` with a helpful
    ``error``), so the sidecar has no separate "request failed"
    path to reason about.
    """
    text_doc = _get_field(params, "textDocument")
    uri = _field_as_str(text_doc, "uri")
    if not uri:
        return {"ok": False, "error": "missing textDocument.uri"}
    content = _document_content(ls, uri)
    if content is None:
        return {"ok": False, "error": f"no open document for {uri}"}

    range_obj = _get_field(params, "holeRange")
    if range_obj is None:
        return {"ok": False, "error": "missing holeRange"}
    start_obj = _get_field(range_obj, "start")
    end_obj = _get_field(range_obj, "end")
    if start_obj is None or end_obj is None:
        return {"ok": False, "error": "holeRange missing start/end"}
    hole_range = _query_range_from_lsp(
        lsp_types.Range(
            start=_position_from_param(start_obj),
            end=_position_from_param(end_obj),
        )
    )

    proof_text = _get_field(params, "proofText")
    if proof_text is None:
        return {"ok": False, "error": "missing proofText"}

    path = _path_from_uri(uri)
    result = _query.validate_proof_at(
        path, content, hole_range, str(proof_text), prelude=_prelude_for(path)
    )
    return {"ok": result.ok, "error": result.error}


@server.feature(SPLITTABLE_VARS_REQUEST)
def on_splittable_vars_at(ls: LanguageServer, params: object) -> list[str]:
    """Custom request: return variables at the cursor's hole that
    case-split can target.

    Params: ``{"textDocument": {"uri": "..."}, "position": {"line":
    int, "character": int}}``. Editor clients call this to populate
    completion candidates when prompting for the variable name.

    Result: a list of base names (sorted, deduplicated). Empty when
    the cursor isn't on a ``?`` or no splittable variable is in
    scope.
    """
    text_doc = _get_field(params, "textDocument")
    pos_obj = _get_field(params, "position")
    uri = _field_as_str(text_doc, "uri")
    if not uri:
        return []
    content = _document_content(ls, uri)
    if content is None:
        return []
    pos = _query_pos_from_lsp(
        _position_from_param(pos_obj)
    )
    path = _path_from_uri(uri)
    return list(
        _query.splittable_vars_at(path, content, pos, prelude=_prelude_for(path))
    )


@server.feature(CASE_SPLIT_REQUEST)
def on_case_split_at(
    ls: LanguageServer, params: object
) -> Optional[dict[str, object]]:
    """Custom request: return a WorkspaceEdit that case-splits the
    cursor's hole on a named variable.

    Params: ``{"textDocument": {"uri": "..."}, "position": {"line":
    int, "character": int}, "variable": str}``. The cursor must sit
    on a ``?``; the ``variable`` arg names which in-scope binding to
    split on.

    Result: ``{"changes": {<uri>: [{"range": Range, "newText":
    str}]}}`` (an LSP-shaped WorkspaceEdit) or ``null`` when the
    cursor isn't on a hole, the variable isn't in scope, or its
    shape isn't a Union / Or.
    """
    text_doc = _get_field(params, "textDocument")
    pos_obj = _get_field(params, "position")
    uri = _field_as_str(text_doc, "uri")
    variable = _field_as_str(params, "variable")
    if not uri or not variable:
        return None
    content = _document_content(ls, uri)
    if content is None:
        return None
    pos = _query_pos_from_lsp(
        _position_from_param(pos_obj)
    )
    path = _path_from_uri(uri)
    edit = _query.case_split_at(
        path, content, pos, str(variable), prelude=_prelude_for(path)
    )
    if edit is None:
        return None
    # Shape-shift to the LSP wire format: an LSP WorkspaceEdit with
    # `changes: {uri: [TextEdit]}`. Mirrors what the codeAction
    # handler emits for refine.
    return _workspace_edit_payload(uri, edit)


@server.feature(ELIMINABLE_VARS_REQUEST)
def on_eliminable_vars_at(ls: LanguageServer, params: object) -> list[str]:
    """Custom request: return labels of in-scope hypotheses that
    ``eliminate`` can target.

    Params: ``{"textDocument": {"uri": "..."}, "position": {"line":
    int, "character": int}}``.  Editor clients call this to populate
    completion candidates when prompting for the hypothesis label.

    Result: a list of base names (sorted, deduplicated).  Empty when
    the cursor isn't on a ``?`` or no eliminable hypothesis is in
    scope.
    """
    text_doc = _get_field(params, "textDocument")
    pos_obj = _get_field(params, "position")
    uri = _field_as_str(text_doc, "uri")
    if not uri:
        return []
    content = _document_content(ls, uri)
    if content is None:
        return []
    pos = _query_pos_from_lsp(
        _position_from_param(pos_obj)
    )
    path = _path_from_uri(uri)
    return list(
        _query.eliminable_vars_at(path, content, pos, prelude=_prelude_for(path))
    )


@server.feature(ELIMINATE_REQUEST)
def on_eliminate_at(
    ls: LanguageServer, params: object
) -> Optional[dict[str, object]]:
    """Custom request: return a WorkspaceEdit that uses the named
    hypothesis at the cursor's hole.

    Params: ``{"textDocument": {"uri": "..."}, "position": {"line":
    int, "character": int}, "label": str}``.  The cursor must sit on
    a ``?``; the ``label`` arg names which in-scope hypothesis to
    use.

    Result: ``{"changes": {<uri>: [{"range": Range, "newText":
    str}]}}`` (an LSP-shaped WorkspaceEdit) or ``null`` when the
    cursor isn't on a hole, the label isn't bound, or its formula's
    shape isn't in the supported template table (e.g. ``true``).
    """
    text_doc = _get_field(params, "textDocument")
    pos_obj = _get_field(params, "position")
    uri = _field_as_str(text_doc, "uri")
    label = _field_as_str(params, "label")
    if not uri or not label:
        return None
    content = _document_content(ls, uri)
    if content is None:
        return None
    pos = _query_pos_from_lsp(
        _position_from_param(pos_obj)
    )
    path = _path_from_uri(uri)
    edit = _query.eliminate_at(
        path, content, pos, str(label), prelude=_prelude_for(path)
    )
    if edit is None:
        return None
    return _workspace_edit_payload(uri, edit)


@server.feature(MATCHING_GIVENS_REQUEST)
def on_matching_givens_at(ls: LanguageServer, params: object) -> list[str]:
    """Custom request: return labels of in-scope local proof
    bindings whose formula equals the goal at the cursor's hole.

    Params: ``{"textDocument": {"uri": "..."}, "position": {"line":
    int, "character": int}}``.  Editor clients call this to populate
    completion candidates when prompting for the hypothesis label.

    Result: a list of base names (sorted, deduplicated).  Empty when
    the cursor isn't on a ``?`` or no local binding matches the goal.
    """
    text_doc = _get_field(params, "textDocument")
    pos_obj = _get_field(params, "position")
    uri = _field_as_str(text_doc, "uri")
    if not uri:
        return []
    content = _document_content(ls, uri)
    if content is None:
        return []
    pos = _query_pos_from_lsp(
        _position_from_param(pos_obj)
    )
    path = _path_from_uri(uri)
    return list(
        _query.matching_givens_at(path, content, pos, prelude=_prelude_for(path))
    )


@server.feature(FILL_FROM_GIVEN_REQUEST)
def on_fill_from_given_at(
    ls: LanguageServer, params: object
) -> Optional[dict[str, object]]:
    """Custom request: return a WorkspaceEdit that fills the cursor's
    hole with ``conclude <goal> by <label>``.

    Params: ``{"textDocument": {"uri": "..."}, "position": {"line":
    int, "character": int}, "label": str}``.  The cursor must sit on
    a ``?``; the ``label`` arg names which in-scope local hypothesis
    to use.

    Result: ``{"changes": {<uri>: [{"range": Range, "newText":
    str}]}}`` (an LSP-shaped WorkspaceEdit) or ``null`` when the
    cursor isn't on a hole, the label isn't bound, or the bound
    formula doesn't match the goal.
    """
    text_doc = _get_field(params, "textDocument")
    pos_obj = _get_field(params, "position")
    uri = _field_as_str(text_doc, "uri")
    label = _field_as_str(params, "label")
    if not uri or not label:
        return None
    content = _document_content(ls, uri)
    if content is None:
        return None
    pos = _query_pos_from_lsp(
        _position_from_param(pos_obj)
    )
    path = _path_from_uri(uri)
    edit = _query.fill_from_given_at(
        path, content, pos, str(label), prelude=_prelude_for(path)
    )
    if edit is None:
        return None
    return _workspace_edit_payload(uri, edit)


# --- Entry point ---------------------------------------------------------


def main() -> None:
    """Run the server over stdio. Used as the ``__main__`` entry."""
    server.start_io()


if __name__ == "__main__":
    main()
