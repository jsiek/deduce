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
    LemmaInfo,
    Position,
    SymbolKind,
    _rank_lemmas,
    available_lemmas_at,
)
from lsp.library import check_file  # noqa: E402
from abstract_syntax import Theorem, base_name  # noqa: E402


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


def test_no_hole_no_query_returns_browse_results() -> None:
    """Cursor not on a `?` and no `query`: browse mode surfaces every
    in-scope lemma so off-hole exploration works without inserting a
    synthetic `?` (issue #418)."""
    source = (
        "theorem alpha: true\n"
        "proof\n  .\nend\n"
        "\n"
        "theorem beta: true\n"
        "proof\n  .\nend\n"
        "\n"
        "theorem gamma: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  reflexive\n"
        "end\n"
    )
    # Cursor on `reflexive` (line 12), not a `?`. Browse mode returns
    # every user-file lemma in scope at that point.
    matches = available_lemmas_at(
        "lemmas.pf", source, Position(line=12, column=3)
    )
    names = {m.name for m in matches}
    assert {"alpha", "beta", "gamma"} <= names


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


def test_explicit_import_substring_query_finds_lemma() -> None:
    """Issue #417: a substring ``query`` should match theorems that
    live in modules the user explicitly ``import``s, not just the
    user's file and the prelude.

    Mirrors the ``lib/`` reproducer: a file in ``lib/`` has an empty
    prelude (``_prelude_for`` returns ``()``) but still pulls in
    cross-module lemmas via ``import``. Without the fix the candidate
    set is empty, so the substring query returns nothing.
    """
    source = (
        "import HoleFillPrelude\n"
        "\n"
        "theorem t: true\n"
        "proof\n"
        "  .\n"
        "end\n"
    )
    matches = available_lemmas_at(
        "user.pf",
        source,
        Position(line=3, column=1),
        query="hf_intro_and",
    )
    by_name = {m.name: m for m in matches}
    assert "hf_intro_and" in by_name
    assert by_name["hf_intro_and"].module == "HoleFillPrelude"


def test_explicit_import_goal_shape_query_finds_lemma() -> None:
    """Issue #417: goal-shape patterns must also match lemmas from
    explicitly-imported modules, not just the user's file."""
    source = (
        "import HoleFillPrelude\n"
        "\n"
        "theorem t: true\n"
        "proof\n"
        "  .\n"
        "end\n"
    )
    matches = available_lemmas_at(
        "user.pf",
        source,
        Position(line=3, column=1),
        query="if _ then _ and _",
    )
    names = {m.name for m in matches}
    assert "hf_intro_and" in names


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


def test_rank_lemmas_dedupes_same_declaration_name() -> None:
    """Different import/prelude walks can reach the same declaration;
    only one recommendation should be returned for a theorem name."""
    source = "theorem helper: true\nproof\n  .\nend\n"
    result = check_file("lemmas.pf", content=source)
    assert result.ok
    helper = next(
        stmt
        for stmt in result.ast
        if isinstance(stmt, Theorem) and base_name(stmt.name) == "helper"
    )
    info = LemmaInfo("helper", SymbolKind.THEOREM, "helper: true")
    matches = _rank_lemmas(
        ((info, helper.what, "lemmas"), (info, helper.what, "lemmas")),
        goal_text=None,
        query=None,
        user_module="lemmas",
    )
    assert [m.name for m in matches] == ["helper"]


# ---------------------------------------------------------------------------
# Browse mode (no hole, no query): issue #418
# ---------------------------------------------------------------------------


def test_browse_mode_includes_prelude_lemmas() -> None:
    """Browse mode (no `?`, no `query`) also surfaces lemmas reached
    through ``prelude``, not just user-file declarations."""
    source = (
        "theorem local: true\n"
        "proof\n  .\nend\n"
    )
    matches = available_lemmas_at(
        "user.pf",
        source,
        Position(line=1, column=1),
        prelude=("HoleFillPrelude",),
    )
    by_name = {m.name: m for m in matches}
    # User-file lemma is present.
    assert "local" in by_name
    # Prelude lemma is also surfaced.
    assert "hf_intro_and" in by_name
    assert by_name["hf_intro_and"].module == "HoleFillPrelude"


def test_browse_mode_user_module_outranks_prelude() -> None:
    """Browse-mode ordering: same-file lemmas come before prelude
    lemmas, so the most-relevant scope shows up first."""
    source = (
        "theorem local: true\n"
        "proof\n  .\nend\n"
    )
    matches = available_lemmas_at(
        "user.pf",
        source,
        Position(line=1, column=1),
        prelude=("HoleFillPrelude",),
    )
    by_name = {m.name: m for m in matches}
    if "local" in by_name and "hf_intro_and" in by_name:
        assert (
            by_name["local"].relevance > by_name["hf_intro_and"].relevance
        )


def test_browse_mode_respects_limit() -> None:
    """``limit`` caps browse-mode results too."""
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
        limit=2,
    )
    assert len(matches) == 2


# ---------------------------------------------------------------------------
# Unify-score tier classifier (issue #690).
# ---------------------------------------------------------------------------


def test_unify_full_tier_when_all_premises_discharged() -> None:
    """A lemma whose conclusion unifies with the goal and whose
    premises are all discharged by local givens gets ``"full"``."""
    source = (
        "theorem and_intro: all P:bool, Q:bool. if P then if Q then P and Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  suppose pP: P\n"
        "  suppose qQ: Q\n"
        "  pP, qQ\n"
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
        "lemmas.pf", source, Position(line=14, column=3)
    )
    by_name = {m.name: m for m in matches}
    assert "and_intro" in by_name
    assert by_name["and_intro"].unify_tier == "full"
    # Discharged premises pair each instantiated premise with the
    # local-given label that satisfies it.
    labels = {label for _, label in by_name["and_intro"].discharged_premises}
    assert labels == {"pP", "qQ"}


def test_unify_premises_remain_when_no_givens_match() -> None:
    """The conclusion unifies but no local given satisfies the
    premise: tier collapses to ``"premises_remain"``."""
    source = (
        "theorem and_intro: all P:bool, Q:bool. if P then if Q then P and Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  suppose pP: P\n"
        "  suppose qQ: Q\n"
        "  pP, qQ\n"
        "end\n"
        "\n"
        "theorem with_hole: all P:bool, Q:bool. P and Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  ?\n"
        "end\n"
    )
    matches = available_lemmas_at(
        "lemmas.pf", source, Position(line=12, column=3)
    )
    by_name = {m.name: m for m in matches}
    assert "and_intro" in by_name
    assert by_name["and_intro"].unify_tier == "premises_remain"
    assert by_name["and_intro"].discharged_premises == ()


def test_unify_outranks_head_symbol_only_match() -> None:
    """A lemma whose conclusion actually unifies outranks one whose
    head is the same but whose conclusion shape doesn't unify."""
    source = (
        "theorem and_intro: all P:bool, Q:bool. if P then if Q then P and Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  suppose pP: P\n"
        "  suppose qQ: Q\n"
        "  pP, qQ\n"
        "end\n"
        "\n"
        "theorem head_match_only: true and true\n"
        "proof\n"
        "  .\n"
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
        "lemmas.pf", source, Position(line=19, column=3)
    )
    by_name = {m.name: m for m in matches}
    assert "and_intro" in by_name
    assert "head_match_only" in by_name
    # Both share the ``and`` head symbol, but only ``and_intro``
    # unifies against the goal.
    assert by_name["and_intro"].unify_tier == "full"
    assert by_name["head_match_only"].unify_tier != "full"
    assert (
        by_name["and_intro"].relevance
        > by_name["head_match_only"].relevance
    )


def test_browse_mode_leaves_unify_tier_unset() -> None:
    """Browse mode (no goal, no query) doesn't run the unifier, so
    ``unify_tier`` stays ``None`` on every result."""
    source = (
        "theorem alpha: true\nproof\n  .\nend\n"
        "theorem beta: all P:bool. P = P\n"
        "proof\n  arbitrary P:bool\n  reflexive\nend\n"
    )
    matches = available_lemmas_at(
        "lemmas.pf", source, Position(line=1, column=1)
    )
    assert matches  # browse mode surfaces everything
    assert all(m.unify_tier is None for m in matches)
    assert all(m.discharged_premises == () for m in matches)
