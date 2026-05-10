"""Stub-level test that locks the protocol-neutral query API surface.

Phase 1 / Step 2 of the LSP/MCP plan. The implementations come in
Steps 3-5; this test pins the *signature* so an accidental edit to
``lsp/query.py`` shows up as a test failure rather than a quietly
broken adapter contract. It checks:

* every public function raises ``NotImplementedError`` until its
  dedicated step lands (the adapters can therefore be written against
  these signatures today)
* parameter names, return-type annotations, and ``__all__`` match
  what the plan documents
* the data types are frozen so adapters can't accidentally mutate
  returned values
* ``lsp/query.py`` imports nothing protocol-specific (no pygls, mcp,
  lsprotocol, anthropic) -- if it ever does, the boundary is broken
"""

import inspect
import sys
from pathlib import Path
from typing import Optional

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from lsp import query  # noqa: E402
from lsp.query import (  # noqa: E402
    Diagnostic,
    Given,
    Goal,
    HoleContext,
    LemmaInfo,
    Location,
    Position,
    Range,
    Severity,
    SymbolInfo,
    SymbolKind,
    ValidationResult,
    WorkspaceEdit,
    case_split_at,
    check,
    definition_of,
    eliminable_vars_at,
    eliminate_at,
    goal_at,
    hole_context_at,
    induction_skeleton_at,
    list_symbols,
    refine_at,
    splittable_vars_at,
    validate_proof_at,
)


# --------------------------------------------------------------------------
# Module surface
# --------------------------------------------------------------------------


EXPECTED_PUBLIC = {
    "Severity",
    "SymbolKind",
    "Position",
    "Range",
    "Location",
    "Diagnostic",
    "Given",
    "Goal",
    "SymbolInfo",
    "WorkspaceEdit",
    "LemmaInfo",
    "LemmaMatch",
    "HoleContext",
    "ValidationResult",
    "RewritePreview",
    "ExpandPreview",
    "check",
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
    "hole_context_at",
    "available_lemmas_at",
    "validate_proof_at",
    "preview_replace_at",
    "preview_expand_at",
}


def test_all_matches_expected():
    assert set(query.__all__) == EXPECTED_PUBLIC, (
        "lsp/query.py __all__ has drifted from the plan; if this is "
        "intentional, update docs/lsp-plan.md and the test together"
    )


def test_no_protocol_imports():
    forbidden = ("pygls", "mcp", "lsprotocol", "anthropic")
    source = Path(query.__file__).read_text()
    for name in forbidden:
        assert f"import {name}" not in source, (
            f"lsp/query.py imports {name!r} -- breaks protocol neutrality"
        )
        assert f"from {name}" not in source, (
            f"lsp/query.py imports from {name!r} -- breaks protocol neutrality"
        )


# --------------------------------------------------------------------------
# Data-type shape
# --------------------------------------------------------------------------


@pytest.mark.parametrize(
    "cls",
    [Position, Range, Location, Diagnostic, Given, Goal, SymbolInfo,
     WorkspaceEdit, LemmaInfo, HoleContext, ValidationResult],
)
def test_dataclasses_are_frozen(cls):
    """All public data types must be frozen so callers can't mutate
    returned values in place."""
    assert cls.__dataclass_params__.frozen, (
        f"{cls.__name__} is not frozen; the API contract requires it"
    )


def test_severity_values():
    # Strings rather than ints so MCP exposes a self-explanatory name.
    assert {s.value for s in Severity} == {"error", "warning", "info", "hint"}


def test_symbol_kinds_cover_top_level_forms():
    expected = {
        "theorem",
        "lemma",
        "function",
        "define",
        "union",
        "predicate",
        "postulate",
        "import",
        "other",
    }
    assert {k.value for k in SymbolKind} == expected


def test_position_is_one_indexed_by_construction():
    # Not enforced at runtime, but the docstring promises 1-indexed,
    # and Position(1, 1) (the smallest valid value) must construct.
    p = Position(1, 1)
    assert p.line == 1 and p.column == 1


def test_goal_givens_is_a_tuple():
    """``Goal`` is hashable -- givens must be a tuple, not a list."""
    g = Goal(formula="P", givens=(), range=Range(Position(1, 1), Position(1, 2)))
    hash(g)  # hashable iff all fields are hashable


# --------------------------------------------------------------------------
# Query function signatures
# --------------------------------------------------------------------------


def _check_sig(func, expected_params, expected_return):
    sig = inspect.signature(func)
    actual_params = [p.name for p in sig.parameters.values()]
    assert actual_params == expected_params, (
        f"{func.__name__} parameter names drifted: "
        f"expected {expected_params}, got {actual_params}"
    )
    assert sig.return_annotation == expected_return, (
        f"{func.__name__} return annotation drifted: "
        f"expected {expected_return!r}, got {sig.return_annotation!r}"
    )


def test_check_signature():
    _check_sig(check, ["path", "content", "prelude"], list[Diagnostic])


def test_goal_at_signature():
    _check_sig(
        goal_at, ["path", "content", "pos", "prelude"], Optional[Goal]
    )


def test_definition_of_signature():
    _check_sig(
        definition_of,
        ["path", "content", "pos", "prelude"],
        Optional[Location],
    )


def test_list_symbols_signature():
    _check_sig(
        list_symbols, ["path", "content", "prelude"], list[SymbolInfo]
    )


def test_refine_at_signature():
    _check_sig(
        refine_at,
        ["path", "content", "pos", "prelude"],
        Optional[WorkspaceEdit],
    )


def test_case_split_at_signature():
    _check_sig(
        case_split_at,
        ["path", "content", "pos", "variable", "prelude"],
        Optional[WorkspaceEdit],
    )


def test_splittable_vars_at_signature():
    _check_sig(
        splittable_vars_at,
        ["path", "content", "pos", "prelude"],
        tuple,
    )


def test_induction_skeleton_at_signature():
    _check_sig(
        induction_skeleton_at,
        ["path", "content", "pos", "prelude"],
        Optional[WorkspaceEdit],
    )


def test_eliminate_at_signature():
    _check_sig(
        eliminate_at,
        ["path", "content", "pos", "label", "prelude"],
        Optional[WorkspaceEdit],
    )


def test_eliminable_vars_at_signature():
    _check_sig(
        eliminable_vars_at,
        ["path", "content", "pos", "prelude"],
        tuple,
    )


def test_hole_context_at_signature():
    _check_sig(
        hole_context_at,
        ["path", "content", "pos", "prelude", "include_lemmas"],
        Optional[HoleContext],
    )


def test_hole_context_at_include_lemmas_default():
    """``include_lemmas`` defaults to True so the hole-fill sidecar's
    common case (wants lemmas) is the trivial call shape."""
    param = inspect.signature(hole_context_at).parameters["include_lemmas"]
    assert param.default is True


def test_validate_proof_at_signature():
    _check_sig(
        validate_proof_at,
        ["path", "content", "hole_range", "proof_text", "prelude"],
        ValidationResult,
    )


def test_prelude_param_has_default():
    """``prelude`` is optional on every query function so existing
    Step 3-5 callers (which pass ``path`` and ``content`` only)
    keep working."""
    for func in (
        check, goal_at, definition_of, list_symbols, refine_at,
        case_split_at, splittable_vars_at, induction_skeleton_at,
        eliminate_at, eliminable_vars_at, hole_context_at,
        validate_proof_at,
    ):
        prelude_param = inspect.signature(func).parameters["prelude"]
        assert prelude_param.default == (), (
            f"{func.__name__}.prelude default drifted: "
            f"got {prelude_param.default!r}"
        )


# All Phase 1 query functions are now implemented; their acceptance
# tests live in test_check.py (Step 3), test_goal_at.py (Step 4), and
# test_symbols.py (Step 5). The Phase 4 / Step 15 ``refine_at``
# acceptance tests live in test_refine.py.
