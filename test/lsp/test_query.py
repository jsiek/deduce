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
    Location,
    Position,
    Range,
    Severity,
    SymbolInfo,
    SymbolKind,
    check,
    definition_of,
    goal_at,
    list_symbols,
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
    "check",
    "goal_at",
    "definition_of",
    "list_symbols",
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
    [Position, Range, Location, Diagnostic, Given, Goal, SymbolInfo],
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
    _check_sig(check, ["path", "content"], list[Diagnostic])


def test_goal_at_signature():
    _check_sig(goal_at, ["path", "content", "pos"], Optional[Goal])


def test_definition_of_signature():
    _check_sig(definition_of, ["path", "content", "pos"], Optional[Location])


def test_list_symbols_signature():
    _check_sig(list_symbols, ["path", "content"], list[SymbolInfo])


# --------------------------------------------------------------------------
# Stubs raise NotImplementedError until the dedicated step lands.
# ``check`` is implemented (Step 3, see test_check.py).
# ``goal_at`` is implemented (Step 4, see test_goal_at.py).
# --------------------------------------------------------------------------


def test_definition_of_stub_raises():
    with pytest.raises(NotImplementedError):
        definition_of("file.pf", "", Position(1, 1))


def test_list_symbols_stub_raises():
    with pytest.raises(NotImplementedError):
        list_symbols("file.pf", "")
