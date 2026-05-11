"""Acceptance test for ``lsp.query.goal_at`` (Phase 1 / Step 4).

Hand-crafted fixtures embedded inline -- one per scenario worth pinning.
Each case supplies a snippet of Deduce source, a 1-indexed cursor
position, and the goal we expect ``goal_at`` to surface there.

Each fixture stays inside ``bool``-only territory so the test runs
without the standard library prelude (Step 6 introduces a daemon mode
where the prelude is preloaded; until then, ``goal_at`` runs each
check from scratch and we keep them small).
"""

from __future__ import annotations

import sys
from dataclasses import dataclass
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from lsp.query import Given, Goal, Position, goal_at  # noqa: E402


@dataclass(frozen=True)
class GoalCase:
    name: str
    source: str
    cursor: Position
    expected_formula: str
    expected_givens: tuple[Given, ...]


CASES = [
    GoalCase(
        name="simple_equality",
        # Cursor sits at the start of line 4, just after `arbitrary`.
        # Goal should be ``P = P`` with no givens (the binding for
        # ``P`` is a term variable, not a proof variable, so it does
        # not show up in Givens).
        source=(
            "theorem t: all P:bool. P = P\n"
            "proof\n"
            "  arbitrary P:bool\n"
            "  reflexive\n"
            "end\n"
        ),
        cursor=Position(line=4, column=1),
        expected_formula="P = P",
        expected_givens=(),
    ),
    GoalCase(
        name="implication_with_givens",
        # After ``suppose pP:P`` and ``suppose qQ:Q`` the goal is
        # ``P`` and both hypotheses are in scope.
        source=(
            "theorem t: all P:bool, Q:bool. if P then if Q then P\n"
            "proof\n"
            "  arbitrary P:bool, Q:bool\n"
            "  suppose pP: P\n"
            "  suppose qQ: Q\n"
            "  pP\n"
            "end\n"
        ),
        cursor=Position(line=6, column=1),
        expected_formula="P",
        expected_givens=(
            Given(label="qQ", formula="Q"),
            Given(label="pP", formula="P"),
        ),
    ),
    GoalCase(
        name="and_intro",
        # The goal at the top of a conjunction proof is the full
        # conjunction. We deliberately put the cursor on the line
        # holding the proof body so the test exercises mid-proof
        # cursor placement.
        source=(
            "theorem t: all P:bool, Q:bool. if P then if Q then P and Q\n"
            "proof\n"
            "  arbitrary P:bool, Q:bool\n"
            "  suppose pP: P\n"
            "  suppose qQ: Q\n"
            "  pP, qQ\n"
            "end\n"
        ),
        cursor=Position(line=6, column=1),
        expected_formula="(P and Q)",
        expected_givens=(
            Given(label="qQ", formula="Q"),
            Given(label="pP", formula="P"),
        ),
    ),
]


@pytest.mark.parametrize("case", CASES, ids=lambda c: c.name)
def test_goal_at(case: GoalCase) -> None:
    g = goal_at("test.pf", case.source, case.cursor)
    assert g is not None, f"{case.name}: goal_at returned None"
    assert isinstance(g, Goal)
    assert g.formula == case.expected_formula, (
        f"{case.name}: formula mismatch\n"
        f"  expected: {case.expected_formula!r}\n"
        f"  got:      {g.formula!r}"
    )
    assert g.givens == case.expected_givens, (
        f"{case.name}: givens mismatch\n"
        f"  expected: {case.expected_givens}\n"
        f"  got:      {g.givens}"
    )
    # The cursor position is echoed back as a degenerate range.
    assert g.range.start == case.cursor
    assert g.range.end == case.cursor


def test_goal_at_returns_none_after_proof_end() -> None:
    """Cursor outside any proof block has no obligation."""
    source = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  reflexive\n"
        "end\n"
        "\n"
        "-- top-level here, no proof in scope\n"
    )
    # Line 7, column 1 -- the comment line, after `end`.
    assert goal_at("test.pf", source, Position(line=7, column=1)) is None


def test_goal_at_returns_none_for_out_of_range_position() -> None:
    """Positions past EOF yield no goal."""
    source = "theorem t: bool = true\n"
    assert goal_at("test.pf", source, Position(line=99, column=1)) is None


def test_goal_at_returns_none_when_position_is_invalid() -> None:
    """Negative / zero coordinates are not 1-indexed positions."""
    source = "theorem t: bool = true\n"
    assert goal_at("test.pf", source, Position(line=0, column=1)) is None
    assert goal_at("test.pf", source, Position(line=1, column=0)) is None


def test_goal_at_works_inside_nested_case_block() -> None:
    """Regression: cursor inside a ``case ... { ... }`` block.

    The hole-insertion algorithm has to stop at the case body's own
    ``}`` rather than the proof body's ``end`` -- otherwise the ``}``
    gets consumed and the parser sees an unbalanced brace, which
    makes ``goal_at`` silently return ``None``.

    Mirrors the proof shape that surfaced this bug in ``lib/Nat.pf``::

        proof
          induction Nat
          case zero { ... }
          case suc(n') suppose IH {
            <cursor here>
            IH
          }
        end

    The exact reduced formula isn't asserted -- Deduce's reduction
    is implementation-detail-y for ``switch`` on bool. What matters
    is that ``goal_at`` doesn't trip over the nested ``}``.
    """
    source = (
        "theorem t: all x:bool. x = true or x = false\n"
        "proof\n"
        "  arbitrary x:bool\n"
        "  switch x {\n"
        "    case true {\n"
        "      .\n"
        "    }\n"
        "    case false {\n"
        "      .\n"
        "    }\n"
        "  }\n"
        "end\n"
    )
    # Line 6, column 1 -- the body of `case true { ... }`.
    g = goal_at("test.pf", source, Position(line=6, column=1))
    assert g is not None, (
        "goal_at returned None inside a case body -- the nested "
        "`}` likely confused the hole-insertion truncation."
    )
    assert isinstance(g, Goal)
    assert g.range.start == Position(line=6, column=1)


# --------------------------------------------------------------------------
# Cursor on or adjacent to an existing `?` (issue #341)
# --------------------------------------------------------------------------
#
# When the cursor sits on -- or one column past -- a `?` already in
# the source, the existing hole IS the goal site.  ``goal_at`` should
# *not* synthesise a second `?` (which would put two `?`s in a row in
# the modified source and trip the parser); it should run ``check``
# on the unmodified content and let the existing `?` raise.


def test_goal_at_cursor_on_existing_hole() -> None:
    """Cursor exactly on the `?` returns the goal at that hole, with
    a Range covering the `?` itself."""
    source = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  ?\n"
        "end\n"
    )
    g = goal_at("test.pf", source, Position(line=4, column=3))
    assert g is not None
    assert g.formula == "P = P"
    # Range covers exactly the `?` token, matching what refine_at
    # and case_split_at return.
    assert g.range.start == Position(line=4, column=3)
    assert g.range.end == Position(line=4, column=4)


def test_goal_at_cursor_immediately_after_existing_hole() -> None:
    """Cursor one column past the `?` (the natural cursor position
    just after typing `?`) still resolves to the existing hole.
    Without the fix this returned ``None`` because ``_insert_hole''
    produced an unparseable ``?\\n?`` sequence."""
    source = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  ?\n"
        "end\n"
    )
    # `?` is at line 4 col 3; cursor at col 4 sits just past it.
    g = goal_at("test.pf", source, Position(line=4, column=4))
    assert g is not None, (
        "goal_at returned None for cursor-just-past-`?` -- the "
        "regression for issue #341 has reappeared."
    )
    assert g.formula == "P = P"
    # Range still covers the `?`, not the cursor position.
    assert g.range.start == Position(line=4, column=3)
    assert g.range.end == Position(line=4, column=4)


def test_goal_at_cursor_on_hole_matches_synthetic_hole_path() -> None:
    """Sanity: the cursor-on-`?` path and the synthesise-a-hole path
    return the same formula and givens for matching positions.
    (Range differs: 1-char vs degenerate.)"""
    source_with_hole = (
        "theorem t: all P:bool, Q:bool. if P then if Q then P\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  suppose pP: P\n"
        "  suppose qQ: Q\n"
        "  ?\n"
        "end\n"
    )
    source_without_hole = source_with_hole.replace("?", "pP")
    # On the `?`: existing-hole path.
    g1 = goal_at("test.pf", source_with_hole, Position(line=6, column=3))
    # Synthesise-a-hole path: cursor on the same line, but the source
    # has `pP` instead of `?`.
    g2 = goal_at("test.pf", source_without_hole, Position(line=6, column=1))
    assert g1 is not None and g2 is not None
    assert g1.formula == g2.formula
    assert g1.givens == g2.givens


# ---------------------------------------------------------------------------
# Multi-hole files (issue #337)
# ---------------------------------------------------------------------------
#
# The proof checker raises IncompleteProof at the first `?` it
# encounters. Without the targeted-hole machinery in lsp/query.py,
# every cursor position in a multi-hole file would return the goal of
# the first hole. These tests pin the per-hole behaviour.


def test_goal_at_picks_second_of_two_holes_in_one_proof() -> None:
    """Two `have ... by ?` lines in one proof: cursor on the second `?`
    returns the second hole's goal, not the first."""
    source = (
        "theorem t: all P:bool, Q:bool. if P then if Q then P and Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  suppose pP: P\n"
        "  suppose qQ: Q\n"
        "  have h1: P by ?\n"
        "  have h2: Q by ?\n"
        "  h1, h2\n"
        "end\n"
    )
    # Cursor on the first `?` -> goal is `P`.
    g_first = goal_at("test.pf", source, Position(line=6, column=17))
    assert g_first is not None
    assert g_first.formula == "P"
    # Cursor on the second `?` -> goal is `Q`, with `h1: P` available
    # because the checker trusted the first hole.
    g_second = goal_at("test.pf", source, Position(line=7, column=17))
    assert g_second is not None
    assert g_second.formula == "Q"
    labels = {given.label for given in g_second.givens}
    assert "h1" in labels, (
        f"expected h1 in scope at second hole, got givens: {g_second.givens}"
    )


def test_goal_at_picks_hole_in_second_theorem() -> None:
    """Two theorems each with `?`: cursor on the second theorem's hole
    returns that theorem's goal, not the first theorem's."""
    source = (
        "theorem t1: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  ?\n"
        "end\n"
        "\n"
        "theorem t2: all Q:bool. Q = Q\n"
        "proof\n"
        "  arbitrary Q:bool\n"
        "  ?\n"
        "end\n"
    )
    g = goal_at("test.pf", source, Position(line=10, column=3))
    assert g is not None
    assert g.formula == "Q = Q"


# ---------------------------------------------------------------------------
# Post-auto-rule normalization (issue #421)
# ---------------------------------------------------------------------------
#
# When the goal or a given differs from the post-auto-reduction form
# that the proof checker compares against, ``goal_at`` surfaces the
# normalized form via ``formula_normalized``. When they coincide --
# the common case -- the field is ``None`` so callers can detect "no
# auto rule fired" by presence alone.


def test_goal_at_normalized_is_none_when_no_auto_rule_fires() -> None:
    """No auto rule in scope: ``formula_normalized`` stays ``None``
    on the goal and on each given, so callers don't have to compare
    strings to know the proof checker sees the same shape."""
    source = (
        "theorem t: all P:bool, Q:bool. if P then if Q then P\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  suppose pP: P\n"
        "  suppose qQ: Q\n"
        "  ?\n"
        "end\n"
    )
    g = goal_at("test.pf", source, Position(line=6, column=3))
    assert g is not None
    assert g.formula == "P"
    assert g.formula_normalized is None, (
        "expected no normalized form when no auto rule fires; "
        f"got {g.formula_normalized!r}"
    )
    for given in g.givens:
        assert given.formula_normalized is None, (
            f"given {given.label!r} unexpectedly normalized "
            f"from {given.formula!r} to {given.formula_normalized!r}"
        )


def test_goal_at_exposes_normalized_goal_under_auto_rule() -> None:
    """An ``auto`` rewrite turns ``id_bool(Q)`` into ``Q``. The
    pre-auto form stays in ``formula`` (matching the rendered
    ``Goal:`` text in the error message), and the post-auto form
    appears in ``formula_normalized`` -- the shape ``check_implies``
    actually sees."""
    source = (
        "fun id_bool(x : bool) { x }\n"
        "\n"
        "theorem id_bool_id: all x:bool. id_bool(x) = x\n"
        "proof\n"
        "  arbitrary x:bool\n"
        "  expand id_bool.\n"
        "end\n"
        "\n"
        "auto id_bool_id\n"
        "\n"
        "theorem t: all P:bool, Q:bool. if id_bool(P) then id_bool(Q)\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  suppose hp: id_bool(P)\n"
        "  ?\n"
        "end\n"
    )
    g = goal_at("test.pf", source, Position(line=15, column=3))
    assert g is not None
    assert g.formula == "id_bool(Q)"
    assert g.formula_normalized == "Q", (
        f"expected normalized goal 'Q'; got {g.formula_normalized!r}"
    )


def test_goal_at_exposes_normalized_given_under_auto_rule() -> None:
    """Same auto rule as the goal test, but cursor is on a hole where
    the given ``hp: id_bool(P)`` should expose ``formula_normalized
    = 'P'`` -- so an agent can match the given against a goal of
    shape ``P`` without writing a probe edit."""
    source = (
        "fun id_bool(x : bool) { x }\n"
        "\n"
        "theorem id_bool_id: all x:bool. id_bool(x) = x\n"
        "proof\n"
        "  arbitrary x:bool\n"
        "  expand id_bool.\n"
        "end\n"
        "\n"
        "auto id_bool_id\n"
        "\n"
        "theorem t: all P:bool, Q:bool. if id_bool(P) then id_bool(Q)\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  suppose hp: id_bool(P)\n"
        "  ?\n"
        "end\n"
    )
    g = goal_at("test.pf", source, Position(line=15, column=3))
    assert g is not None
    by_label = {given.label: given for given in g.givens}
    assert "hp" in by_label, f"expected hp in givens; got {g.givens}"
    assert by_label["hp"].formula == "id_bool(P)"
    assert by_label["hp"].formula_normalized == "P", (
        f"expected normalized given 'P'; got "
        f"{by_label['hp'].formula_normalized!r}"
    )


def test_goal_at_synthetic_hole_skips_earlier_existing_hole() -> None:
    """A `?` already exists earlier in the proof; cursor sits on a
    blank line later. The synthetic `?` inserted at the cursor must
    drive the goal report -- the earlier `?` should be skipped."""
    source = (
        "theorem t: all P:bool, Q:bool. if P then if Q then P and Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  suppose pP: P\n"
        "  suppose qQ: Q\n"
        "  have h1: P by ?\n"
        "  \n"
        "end\n"
    )
    # Cursor on the blank line 7 (no `?` there) -> should report the
    # local goal at that point, not the first hole's goal `P`.
    g = goal_at("test.pf", source, Position(line=7, column=3))
    assert g is not None
    # The remaining goal after `have h1: P` is the conjunction.
    assert g.formula == "(P and Q)"
    labels = {given.label for given in g.givens}
    assert "h1" in labels, (
        f"expected h1 in scope at synthetic hole, got givens: {g.givens}"
    )
