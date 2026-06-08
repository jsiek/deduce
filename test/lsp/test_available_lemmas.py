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
    synthetic `?` (issue #418). The enclosing theorem (the one the
    cursor sits inside) is excluded -- it can't be cited from its
    own proof (issue #903)."""
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
    # Cursor on the `reflexive` line (line 14), not a `?`. Browse
    # mode returns sibling user-file lemmas but not `gamma`, which
    # the cursor is inside.
    matches = available_lemmas_at(
        "lemmas.pf", source, Position(line=14, column=3)
    )
    names = {m.name for m in matches}
    assert {"alpha", "beta"} <= names
    assert "gamma" not in names


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


def test_unify_rewrite_subterm_tier_fires_for_equation_lemma() -> None:
    """An equation lemma whose LHS unifies with a subterm of the goal
    -- but whose whole-conclusion shape doesn't unify -- gets the
    ``rewrite_subterm`` tier.  Regression for the typo in Part 1 of
    issue #690 where ``conc.rands`` (instead of ``conc.args``) made
    the tier-3 branch silently dead code."""
    source = (
        "theorem not_not: all P:bool. P = not (not P)\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  switch P {\n"
        "    case true { . }\n"
        "    case false { . }\n"
        "  }\n"
        "end\n"
        "\n"
        "theorem with_hole: all P:bool, Q:bool."
        " if P and Q then not (not P) and Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  suppose h: P and Q\n"
        "  ?\n"
        "end\n"
    )
    matches = available_lemmas_at(
        "lemmas.pf", source, Position(line=14, column=3)
    )
    by_name = {m.name: m for m in matches}
    assert "not_not" in by_name
    assert by_name["not_not"].unify_tier == "rewrite_subterm"


def test_unify_uses_typed_lemma_overload_for_right_type_match() -> None:
    """A right-type lemma whose first lexically-resolved overload
    candidate does NOT alias the goal's resolved operator must still
    match as ``full``.

    Reproduces Bug 3 from issue #690: ``stmt.what`` (the parsed,
    pre-typecheck lemma AST) keeps :class:`OverloadedVar` with a
    candidate list whose first entry is just whatever uniquify saw
    first.  The matcher's name-equality check compares only that
    first candidate, so a lemma about ``A * A`` whose first ``*``
    overload happens to be the ``B * B`` one gets rejected even
    though it's the right answer.

    The fix is to look the lemma up in the proof environment (where
    overloads have been resolved during the prelude's type check)
    before unifying."""
    source = (
        "import OverloadShared\n"
        "\n"
        "theorem t: all a:A, c:A. a * c = c * a\n"
        "proof\n"
        "  arbitrary a:A, c:A\n"
        "  ?\n"
        "end\n"
    )
    matches = available_lemmas_at(
        "user.pf", source, Position(line=6, column=3),
        prelude=("OverloadShared",),
    )
    by_name = {m.name: m for m in matches}
    assert "aa_star_commute" in by_name, (
        "the right-type lemma should appear in the candidate list"
    )
    assert by_name["aa_star_commute"].unify_tier == "full", (
        "aa_star_commute applies to an A * A goal -- it should be "
        "the full-tier top match, not buried at None"
    )


def test_unify_rejects_wrong_type_overload_as_full_tier() -> None:
    """A wrong-type lemma whose first lexically-resolved overload
    candidate ALIASES the goal's resolved operator must not match as
    ``full``.

    Reproduces Bug 2 from issue #690: ``bb_star_commute`` and
    ``ab_star_refl`` both reference ``*`` with an :class:`OverloadedVar`
    candidate list that includes the A*A overload (because all three
    overloads are in scope where they were declared).  The matcher's
    first-candidate-only name-equality test mis-accepts the wrong-type
    lemma whenever that lexical first candidate happens to be the A*A
    one.

    The fix (looking up the typed formula in the proof environment)
    sees the resolved single overload and rejects the mismatch."""
    source = (
        "import OverloadShared\n"
        "\n"
        "theorem t: all a:A, c:A. a * c = c * a\n"
        "proof\n"
        "  arbitrary a:A, c:A\n"
        "  ?\n"
        "end\n"
    )
    matches = available_lemmas_at(
        "user.pf", source, Position(line=6, column=3),
        prelude=("OverloadShared",),
    )
    by_name = {m.name: m for m in matches}
    if "bb_star_commute" in by_name:
        assert by_name["bb_star_commute"].unify_tier != "full", (
            "bb_star_commute is about B * B; an A * A goal must not "
            "full-match it just because the first overload of `*` in "
            "the lemma's candidate list happens to be the A*A one"
        )
    if "ab_star_refl" in by_name:
        assert by_name["ab_star_refl"].unify_tier != "full", (
            "ab_star_refl is about A * B; an A * A goal must not "
            "full-match it"
        )


def test_specificity_pushes_clean_match_above_noisy_ties() -> None:
    """When many lemmas tie on head match + overlap, the Jaccard-like
    specificity signal must keep the lemma whose formula contains no
    extra operators above the noisy ones.

    Issue #690 Bug 1 (latency): ``_rank_lemmas`` only runs the
    expensive unifier on the top ``UNIFY_TOP_K`` cheap-ranked
    candidates.  Without specificity as a secondary signal, dozens of
    equation lemmas would tie on a ``a + b = b + a`` goal and the
    real ``uint_add_commute`` could be elbowed past the cutoff -- the
    user would never see the unify signal that earns it the top
    slot.

    Drives the ranker directly with synthetic ``LemmaInfo`` rows so
    the assertion lands on the cheap-signal path without needing a
    real stdlib import.
    """
    from lsp.query import _rank_lemmas

    # Two synthetic lemmas tying on head=``=`` and 100% overlap with
    # the goal tokens; ``noisy`` adds an unrelated ``-``.  Distinct
    # sentinel strings stand in for the formula AST so the patched
    # ``_formula_symbols`` can tell them apart.
    candidates = (
        (
            LemmaInfo(name="add_pure", kind=SymbolKind.THEOREM,
                      signature="add_pure: all a, b. a + b = b + a"),
            "FORMULA_PURE",
            "user",
        ),
        (
            LemmaInfo(name="add_noisy", kind=SymbolKind.THEOREM,
                      signature="add_noisy: all a, b, c. (a + b) - c = (b + a) - c"),
            "FORMULA_NOISY",
            "user",
        ),
    )
    # Patch ``_formula_symbols`` for this call -- the real one walks
    # an AST; we want to control symbol sets directly.
    import lsp.query as Q
    real = Q._formula_symbols
    Q._formula_symbols = lambda f: (
        frozenset({"+", "="}) if f == "FORMULA_PURE" else frozenset({"+", "-", "="})
    )
    try:
        ranked = _rank_lemmas(
            candidates,
            goal_text="all x, y. x + y = y + x",
            query=None,
            user_module="user",
        )
    finally:
        Q._formula_symbols = real

    by_name = {m.name: m for m in ranked}
    assert "add_pure" in by_name and "add_noisy" in by_name
    assert by_name["add_pure"].relevance > by_name["add_noisy"].relevance, (
        "Lemma with no extra operators must outrank one carrying "
        "irrelevant `-` on a `+=+` goal"
    )


def test_current_theorem_excluded_from_lemma_list() -> None:
    """The theorem currently being proved must not appear in the
    candidate list -- a proof can't cite itself (issue #690 Bug 5).

    User report: with cursor on the ``?`` inside ``theorem t``,
    `C-c C-l` listed ``t`` as one of the applicable lemmas.
    """
    source = (
        "theorem helper: true\nproof\n  .\nend\n"
        "\n"
        "theorem t: all a:UInt, b:UInt. a + b = b + a\n"
        "proof\n"
        "  arbitrary a:UInt, b:UInt\n"
        "  ?\n"
        "end\n"
    )
    # Hole sits on line 9 inside ``theorem t``.
    matches = available_lemmas_at(
        "user.pf", source, Position(line=9, column=3),
    )
    names = {m.name for m in matches}
    assert "t" not in names, (
        "The current theorem must not be offered as a lemma -- "
        "citing it from its own proof is circular"
    )
    # Sibling theorems remain visible.
    assert "helper" in names


# ---------------------------------------------------------------------------
# Disjunction / existential lemma discovery (issue #869)
# ---------------------------------------------------------------------------


_DISJUNCTION_SOURCE = (
    "define g : fn bool, bool -> bool"
    " = fun x:bool, y:bool { if x then x else y }\n"
    "\n"
    "theorem g_left_or_right: all x:bool, y:bool."
    " (g(x, y) = x) or (g(x, y) = y)\n"
    "proof\n"
    "  arbitrary x:bool, y:bool\n"
    "  switch x { case true { evaluate } case false { evaluate } }\n"
    "end\n"
    "\n"
    "theorem g_unrelated: all x:bool. not (not x) = x\n"
    "proof\n"
    "  arbitrary x:bool\n"
    "  switch x { case true { evaluate } case false { evaluate } }\n"
    "end\n"
)


def test_goal_shape_or_query_finds_disjunction_lemma() -> None:
    """A goal-shape ``query`` with a top-level ``or`` finds a lemma whose
    conclusion is a disjunction of equations, even though each equation
    is parenthesized in the rendered signature (issue #869). A single
    whitespace-flexible regex misses it because of the parens; splitting
    on ``or`` and searching each disjunct independently does not."""
    source = _DISJUNCTION_SOURCE + (
        "\ntheorem t: true\nproof\n  .\nend\n"
    )
    matches = available_lemmas_at(
        "lemmas.pf",
        source,
        Position(line=1, column=1),
        query="g(_, _) = _ or g(_, _) = _",
    )
    names = {m.name for m in matches}
    assert "g_left_or_right" in names
    assert "g_unrelated" not in names


def test_unify_disjunctive_split_tier_fires_for_disjunction_lemma() -> None:
    """A disjunction-of-equations lemma whose disjunct's LHS unifies with
    a subterm of the goal gets the ``disjunctive_split`` tier -- the
    high-value case-analysis lemma is surfaced rather than buried under
    rewrite-shaped lemmas with ``unify_tier: null`` (issue #869)."""
    source = _DISJUNCTION_SOURCE + (
        "\ntheorem with_hole: all a:bool, b:bool."
        " if g(a, b) = a then g(a, b) = a\n"
        "proof\n"
        "  arbitrary a:bool, b:bool\n"
        "  suppose h: g(a, b) = a\n"
        "  ?\n"
        "end\n"
    )
    hole_line = source.split("\n").index("  ?") + 1
    matches = available_lemmas_at(
        "lemmas.pf", source, Position(line=hole_line, column=3)
    )
    by_name = {m.name: m for m in matches}
    assert "g_left_or_right" in by_name
    assert by_name["g_left_or_right"].unify_tier == "disjunctive_split"


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


# ---------------------------------------------------------------------------
# Snap-to-hole (issue #903): an off-cursor (line, column) on the same line
# as a ``?`` token snaps to that hole rather than silently falling through
# to browse mode.
# ---------------------------------------------------------------------------


def test_off_cursor_same_line_snaps_to_hole() -> None:
    """Cursor a few columns to the left of a ``?`` on the same line
    drives goal-mode ranking, not browse mode -- the enclosing
    theorem doesn't surface at 1.0 and ranking remains goal-shape
    driven (issue #903)."""
    source = (
        "theorem and_helper: all P:bool, Q:bool."
        " if P then if Q then P and Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  suppose pP: P\n"
        "  suppose qQ: Q\n"
        "  pP, qQ\n"
        "end\n"
        "\n"
        "theorem with_hole: all P:bool, Q:bool."
        " if P then if Q then P and Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  suppose pP: P\n"
        "  suppose qQ: Q\n"
        "  ?\n"
        "end\n"
    )
    # The `?` sits at (line=14, column=3).
    on_hole = available_lemmas_at(
        "lemmas.pf", source, Position(line=14, column=3)
    )
    # A few columns to the left of the `?`, same line.
    off_cursor = available_lemmas_at(
        "lemmas.pf", source, Position(line=14, column=1)
    )
    on_names = [m.name for m in on_hole]
    off_names = [m.name for m in off_cursor]
    # Snap brings the off-cursor call back to the goal-driven result
    # set: same names, same order.
    assert on_names == off_names
    # And it does NOT include the enclosing theorem (with_hole).
    assert "with_hole" not in off_names


def test_off_cursor_closest_hole_wins() -> None:
    """When multiple ``?`` sit on the same line, snap to the one
    whose start column is closest to the cursor (issue #903)."""
    # Two `?` holes on the same line; the cursor is closer to the
    # first one's start column.
    source = (
        "theorem with_two_holes: all P:bool, Q:bool. P or Q or true\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  ?       ?\n"
        "end\n"
    )
    # The two `?` are at columns 3 and 11 on line 4. The cursor sits
    # at column 4 (between them but closer to the first).
    near_first = available_lemmas_at(
        "lemmas.pf", source, Position(line=4, column=4)
    )
    # Compare against an exact-hit call at column 3.
    exact = available_lemmas_at(
        "lemmas.pf", source, Position(line=4, column=3)
    )
    assert [m.name for m in near_first] == [m.name for m in exact]


def test_off_cursor_no_hole_on_line_stays_browse_mode() -> None:
    """Cursor on a line without any ``?`` token doesn't snap -- the
    call still falls through to browse mode, just like before issue
    #903. This preserves the off-hole exploration contract."""
    source = (
        "theorem alpha: true\nproof\n  .\nend\n"
        "\n"
        "theorem beta: all P:bool. P = P\n"
        "proof\n  arbitrary P:bool\n  reflexive\nend\n"
        "\n"
        "theorem with_hole: true\nproof\n  ?\nend\n"
    )
    # Cursor at line=8 sits on `arbitrary P:bool` -- inside `beta`,
    # nowhere near the `?` in `with_hole`. Browse mode applies.
    matches = available_lemmas_at(
        "lemmas.pf", source, Position(line=8, column=3)
    )
    names = {m.name for m in matches}
    # Sibling theorems still appear; `beta` (enclosing) is dropped.
    assert "alpha" in names
    assert "with_hole" in names
    assert "beta" not in names


# ---------------------------------------------------------------------------
# Enclosing theorem exclusion in browse mode (issue #903 part 4).
# ---------------------------------------------------------------------------


def test_enclosing_theorem_excluded_in_browse_mode() -> None:
    """Browse mode also drops the enclosing theorem from candidates
    -- a proof can't cite the theorem it's editing, even when no
    hole is present at the cursor (issue #903)."""
    source = (
        "theorem helper: true\nproof\n  .\nend\n"
        "\n"
        "theorem reverse_involutive: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  reflexive\n"
        "end\n"
    )
    # Cursor on the `reflexive` line (line 8), no `?` on that line,
    # so browse mode applies via the no-snap fallback.
    matches = available_lemmas_at(
        "lemmas.pf", source, Position(line=8, column=3)
    )
    names = {m.name for m in matches}
    assert "helper" in names
    assert "reverse_involutive" not in names
