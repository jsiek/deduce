"""Acceptance tests for ``lsp.query.available_lemmas_at`` (issue #403).

The function is the goal-shape-driven lemma search behind the MCP
``available_lemmas_at`` tool. It produces a ranked list of theorems
/ lemmas / postulates relevant at a cursor: either driven by the
goal at a ``?`` token or by an explicit ``query`` (substring or
goal-shape pattern with ``_`` placeholders).

Most tests stay inside ``bool`` territory so they don't depend on
the standard library. The "prelude" cases use the small
``HoleFillPrelude`` fixture from ``test/test-imports/`` -- the same
one ``test_hole_context.py`` uses.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from lsp.query import (  # noqa: E402
    LemmaMatch,
    Position,
    SymbolKind,
    available_lemmas_at,
)


# ---------------------------------------------------------------------------
# Goal-driven mode (cursor on a `?`)
# ---------------------------------------------------------------------------


def test_goal_drives_ranking_by_head_symbol() -> None:
    """Cursor on a `?` whose goal has shape ``P and Q``: an ``and``-
    headed user lemma outranks an unrelated equation lemma even
    though both are in scope."""
    source = (
        "theorem and_helper: all P:bool, Q:bool. if P then if Q then P and Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  suppose pP: P\n"
        "  suppose qQ: Q\n"
        "  pP, qQ\n"
        "end\n"
        "\n"
        "theorem eq_helper: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  reflexive\n"
        "end\n"
        "\n"
        "theorem with_hole: all P:bool, Q:bool. if P then if Q then P and Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  suppose pP: P\n"
        "  suppose qQ: Q\n"
        "  ?\n"
        "end\n"
    )
    matches = available_lemmas_at(
        "lemmas.pf",
        source,
        Position(line=20, column=3),
    )
    assert isinstance(matches, tuple)
    assert all(isinstance(m, LemmaMatch) for m in matches)

    by_name = {m.name: m for m in matches}
    assert "and_helper" in by_name
    assert "eq_helper" in by_name

    # Head match (``and``) plus symbol overlap pushes and_helper above
    # eq_helper.
    assert by_name["and_helper"].relevance > by_name["eq_helper"].relevance


def test_no_hole_no_query_returns_empty() -> None:
    """Cursor not on a `?` and no `query` -> nothing to match against."""
    source = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  reflexive\n"
        "end\n"
    )
    # Line 4 sits on `reflexive`, not a `?`.
    assert available_lemmas_at(
        "lemmas.pf", source, Position(line=4, column=3)
    ) == ()


def test_user_lemmas_get_module_set_to_file_stem() -> None:
    """Lemmas declared in the user file have ``module`` set to the
    path's stem (``"lemmas"`` for ``/tmp/lemmas.pf``)."""
    source = (
        "lemma helper: true\n"
        "proof\n"
        "  .\n"
        "end\n"
        "\n"
        "theorem with_hole: true\n"
        "proof\n"
        "  ?\n"
        "end\n"
    )
    matches = available_lemmas_at(
        "/tmp/lemmas.pf",
        source,
        Position(line=8, column=3),
    )
    by_name = {m.name: m for m in matches}
    assert "helper" in by_name
    assert by_name["helper"].module == "lemmas"
    assert by_name["helper"].kind == SymbolKind.LEMMA


# ---------------------------------------------------------------------------
# Query-only mode (no hole)
# ---------------------------------------------------------------------------


def test_substring_query_matches_name() -> None:
    """A bare-string ``query`` matches lemma names case-insensitively."""
    source = (
        "theorem foo_bar: true\n"
        "proof\n  .\nend\n"
        "\n"
        "theorem qux: true\n"
        "proof\n  .\nend\n"
    )
    matches = available_lemmas_at(
        "lemmas.pf",
        source,
        Position(line=1, column=1),
        query="foo",
    )
    names = {m.name for m in matches}
    assert "foo_bar" in names
    # qux doesn't contain "foo" -> filtered out by substring gate.
    assert "qux" not in names


def test_goal_shape_pattern_matches_signature() -> None:
    """A ``query`` containing ``_`` placeholders matches structurally
    against the rendered signature."""
    source = (
        "theorem and_intro: all P:bool, Q:bool. if P then if Q then P and Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  suppose pP: P\n"
        "  suppose qQ: Q\n"
        "  pP, qQ\n"
        "end\n"
        "\n"
        "theorem unrelated: true\n"
        "proof\n  .\nend\n"
    )
    # Pattern matches anything with ``_ and _``.
    matches = available_lemmas_at(
        "lemmas.pf",
        source,
        Position(line=1, column=1),
        query="_ and _",
    )
    names = {m.name for m in matches}
    assert "and_intro" in names
    assert "unrelated" not in names


# ---------------------------------------------------------------------------
# Visibility: prelude private lemmas are filtered, user-file private ones
# are kept.
# ---------------------------------------------------------------------------


def test_user_file_private_lemma_is_visible() -> None:
    """A ``lemma`` (i.e. private) declared in the user's file IS in
    scope at a hole and so appears in the result list."""
    source = (
        "lemma local_priv: true\n"
        "proof\n"
        "  .\n"
        "end\n"
        "\n"
        "theorem with_hole: true\n"
        "proof\n"
        "  ?\n"
        "end\n"
    )
    matches = available_lemmas_at(
        "lemmas.pf",
        source,
        Position(line=8, column=3),
    )
    names = {m.name for m in matches}
    assert "local_priv" in names


def test_prelude_postulate_is_surfaced() -> None:
    """Postulates and theorems imported via the prelude appear in
    results, with ``module`` set to the source module name."""
    source = (
        "theorem with_hole: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  ?\n"
        "end\n"
    )
    matches = available_lemmas_at(
        "user.pf",
        source,
        Position(line=4, column=3),
        prelude=("HoleFillPrelude",),
    )
    by_name = {m.name: m for m in matches}
    # ``hf_postulate`` is from HoleFillPrelude; ``hf_intro_and`` too.
    assert "hf_postulate" in by_name
    assert by_name["hf_postulate"].module == "HoleFillPrelude"
    assert by_name["hf_postulate"].kind == SymbolKind.POSTULATE


# ---------------------------------------------------------------------------
# Ranking signals: relevance is normalised; user-module lemmas outrank
# distant ones for the same head match.
# ---------------------------------------------------------------------------


def test_relevance_is_normalised_to_unit_interval() -> None:
    """The top-ranked match has ``relevance == 1.0`` and all others
    sit in ``[0.0, 1.0]``."""
    source = (
        "theorem foo_helper: true\n"
        "proof\n  .\nend\n"
        "\n"
        "theorem foo_other: true\n"
        "proof\n  .\nend\n"
    )
    matches = available_lemmas_at(
        "lemmas.pf",
        source,
        Position(line=1, column=1),
        query="foo",
    )
    assert matches
    assert matches[0].relevance == pytest.approx(1.0)
    for m in matches:
        assert 0.0 <= m.relevance <= 1.0


def test_module_proximity_breaks_tie_for_same_head() -> None:
    """Two lemmas with identical head symbols: the one in the user's
    own file (same module) outranks the one imported from a prelude
    module."""
    source = (
        "theorem local_intro_and: all P:bool, Q:bool. "
        "if P then if Q then P and Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  suppose pP: P\n"
        "  suppose qQ: Q\n"
        "  pP, qQ\n"
        "end\n"
        "\n"
        "theorem with_hole: all P:bool, Q:bool. "
        "if P then if Q then P and Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  suppose pP: P\n"
        "  suppose qQ: Q\n"
        "  ?\n"
        "end\n"
    )
    matches = available_lemmas_at(
        "user.pf",
        source,
        Position(line=14, column=3),
        prelude=("HoleFillPrelude",),
    )
    by_name = {m.name: m for m in matches}
    assert "local_intro_and" in by_name
    # ``hf_intro_and`` from the prelude has the same head shape but
    # is in a different module.
    if "hf_intro_and" in by_name:
        assert (
            by_name["local_intro_and"].relevance
            > by_name["hf_intro_and"].relevance
        )


def test_limit_caps_result_count() -> None:
    """``limit`` caps how many entries come back."""
    source = (
        "theorem t1: true\nproof\n  .\nend\n"
        "theorem t2: true\nproof\n  .\nend\n"
        "theorem t3: true\nproof\n  .\nend\n"
        "theorem t4: true\nproof\n  .\nend\n"
    )
    matches = available_lemmas_at(
        "lemmas.pf",
        source,
        Position(line=1, column=1),
        query="t",
        limit=2,
    )
    assert len(matches) == 2
