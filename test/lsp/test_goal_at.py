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
