"""Acceptance tests for ``lsp.query.induction_skeleton_at`` (Phase 4 / Step 17).

Each fixture supplies a snippet of Deduce source (with a custom
union and a forall-quantified theorem), the cursor position of the
``?``, and the literal ``new_text`` we expect
``induction_skeleton_at`` to produce.

Coverage matches the plan's three-case acceptance:

(a) splitting a Nat-shape union (zero/suc, IH on suc),
(b) splitting a parameterised List-shape union (empty/cons, IH on cons),
(c) splitting a custom union whose constructors mix recursive and
    non-recursive parameters,
plus boundary cases:
(d) a single-alternative union (no induction possible),
(e) a non-forall goal (no quantifier to induct over),
(f) cursor not on a ``?`` (no replacement target).

All fixtures define their own union so the tests run without the
standard library prelude.
"""

from __future__ import annotations

import sys
from dataclasses import dataclass
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from lsp.query import (  # noqa: E402
    Position,
    Range,
    Severity,
    WorkspaceEdit,
    check,
    induction_skeleton_at,
)


@dataclass(frozen=True)
class InductionCase:
    name: str
    source: str
    cursor: Position  # Cursor on a ?
    expected_text: str
    expected_range: Range  # Range of the ? being replaced


CASES = [
    InductionCase(
        name="nat_like_union",
        # Forall over a Nat-like union; recursive constructor `s(N)'
        # gets an IH binding.
        source=(
            "union N {\n"
            "  z\n"
            "  s(N)\n"
            "}\n"
            "\n"
            "theorem t: all x:N. x = x\n"
            "proof\n"
            "  ?\n"
            "end\n"
        ),
        cursor=Position(line=8, column=3),
        expected_text=(
            "induction N\n"
            "    case z { ? }\n"
            "    case s(n1) assume IH1: n1 = n1 { ? }"
        ),
        expected_range=Range(
            start=Position(line=8, column=3),
            end=Position(line=8, column=4),
        ),
    ),
    InductionCase(
        name="parameterised_list_union",
        # Forall over `L<bool>'; the recursive `cons' tail is an
        # `L<bool>' too, so it gets an IH.
        source=(
            "union L<T> {\n"
            "  e\n"
            "  cons(T, L<T>)\n"
            "}\n"
            "\n"
            "theorem t: all xs:L<bool>. xs = xs\n"
            "proof\n"
            "  ?\n"
            "end\n"
        ),
        cursor=Position(line=8, column=3),
        expected_text=(
            "induction L<bool>\n"
            "    case e { ? }\n"
            "    case cons(t1, l2) assume IH1: l2 = l2 { ? }"
        ),
        expected_range=Range(
            start=Position(line=8, column=3),
            end=Position(line=8, column=4),
        ),
    ),
    InductionCase(
        name="multi_recursive_constructor",
        # `node' takes two recursive parameters and one non-recursive
        # `bool' parameter -> two IHs (IH1, IH2), one per recursive
        # param, in declaration order.
        source=(
            "union Tree {\n"
            "  leaf\n"
            "  node(Tree, bool, Tree)\n"
            "}\n"
            "\n"
            "theorem t: all tr:Tree. tr = tr\n"
            "proof\n"
            "  ?\n"
            "end\n"
        ),
        cursor=Position(line=8, column=3),
        expected_text=(
            "induction Tree\n"
            "    case leaf { ? }\n"
            "    case node(t1, b2, t3) assume IH1: t1 = t1, IH2: t3 = t3 { ? }"
        ),
        expected_range=Range(
            start=Position(line=8, column=3),
            end=Position(line=8, column=4),
        ),
    ),
]


@pytest.mark.parametrize("case", CASES, ids=lambda c: c.name)
def test_induction_skeleton_template(case: InductionCase) -> None:
    edit = induction_skeleton_at("test.pf", case.source, case.cursor)
    assert edit is not None, f"{case.name}: induction_skeleton_at returned None"
    assert isinstance(edit, WorkspaceEdit)
    assert edit.path == "test.pf"
    assert edit.range == case.expected_range, (
        f"{case.name}: range mismatch\n"
        f"  expected: {case.expected_range}\n"
        f"  got:      {edit.range}"
    )
    assert edit.new_text == case.expected_text, (
        f"{case.name}: new_text mismatch\n"
        f"  expected: {case.expected_text!r}\n"
        f"  got:      {edit.new_text!r}"
    )


@pytest.mark.parametrize("case", CASES, ids=lambda c: c.name)
def test_post_edit_check_raises_at_first_case_body(
    case: InductionCase,
) -> None:
    """Plan acceptance: re-running ``check`` on the post-edit content
    must surface a fresh hole *inside the first case body*. After
    Step 11's depth-2 collection (sibling-loop catch in
    ``check_proof_of``), every case-body hole is reported, not just
    the first — so we assert the first-case hole is in the list, not
    that it's the only one."""
    edit = induction_skeleton_at("test.pf", case.source, case.cursor)
    assert edit is not None

    lines = case.source.splitlines(keepends=True)
    line_idx = edit.range.start.line - 1
    start_col = edit.range.start.column - 1
    end_col = edit.range.end.column - 1
    new_line = (
        lines[line_idx][:start_col]
        + edit.new_text
        + lines[line_idx][end_col:]
    )
    post = "".join(lines[:line_idx] + [new_line] + lines[line_idx + 1:])

    diags = check("test.pf", post, prelude=())
    assert len(diags) >= 1, (
        f"{case.name}: expected at least one diagnostic on post-edit "
        f"content, got 0"
    )
    for diag in diags:
        assert diag.severity == Severity.ERROR
        assert "incomplete proof" in diag.message
    # The first case body's `?' is on the line right after the
    # `induction T' header.
    first_case_line = edit.range.start.line + 1
    assert any(d.range.start.line == first_case_line for d in diags), (
        f"{case.name}: expected a diagnostic on line "
        f"{first_case_line} (first case body), got lines "
        f"{[d.range.start.line for d in diags]}"
    )


def test_returns_none_for_single_alternative_union() -> None:
    """Single-constructor unions don't have an inductive split to
    do -- there's no second case to make ``induction'' meaningful."""
    source = (
        "union Singleton {\n"
        "  only\n"
        "}\n"
        "\n"
        "theorem t: all x:Singleton. x = x\n"
        "proof\n"
        "  ?\n"
        "end\n"
    )
    edit = induction_skeleton_at(
        "test.pf", source, Position(line=7, column=3)
    )
    assert edit is None


def test_returns_none_for_non_forall_goal() -> None:
    """Goal must be ``all x:T. P(x)'' for induction; a non-forall
    goal has no quantifier to induct over."""
    source = (
        "theorem t: all P:bool. P or not P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  ?\n"
        "end\n"
    )
    # Goal at the hole is `P or not P', not a forall.
    edit = induction_skeleton_at(
        "test.pf", source, Position(line=4, column=3)
    )
    assert edit is None


def test_returns_none_when_cursor_not_on_hole() -> None:
    """Cursor not on a ``?'' -> no replacement target -> None."""
    source = (
        "union N {\n"
        "  z\n"
        "  s(N)\n"
        "}\n"
        "\n"
        "theorem t: all x:N. x = x\n"
        "proof\n"
        "  ?\n"
        "end\n"
    )
    # Cursor on the `theorem' keyword, line 6 col 3.
    edit = induction_skeleton_at(
        "test.pf", source, Position(line=6, column=3)
    )
    assert edit is None


def test_returns_none_when_quantifier_is_over_non_union_type() -> None:
    """``all P:bool. ...'' has no Union to induct over (bool is a
    primitive)."""
    source = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  ?\n"
        "end\n"
    )
    edit = induction_skeleton_at(
        "test.pf", source, Position(line=3, column=3)
    )
    assert edit is None


# --------------------------------------------------------------------------
# Multi-hole files (issue #337)
# --------------------------------------------------------------------------


def test_induction_skeleton_at_picks_second_of_two_holes() -> None:
    """Two `?`s in one proof: induction_skeleton_at on the second hole
    picks the goal at THAT hole, not the first hole's goal."""
    # First hole's goal: ``true``. Second hole's goal: ``all x:N. x = x``,
    # which the induction template can target. Without per-hole
    # targeting we'd see ``true`` and refuse to emit a template.
    source = (
        "union N {\n"
        "  z\n"
        "  s(N)\n"
        "}\n"
        "\n"
        "theorem t: all x:N. x = x\n"
        "proof\n"
        "  have triv: true by ?\n"
        "  ?\n"
        "end\n"
    )
    edit = induction_skeleton_at(
        "test.pf", source, Position(line=9, column=3)
    )
    assert edit is not None, (
        "induction_skeleton_at returned None -- per-hole targeting "
        "may have failed to reach the second hole"
    )
    assert "induction N" in edit.new_text
    assert edit.range.start == Position(line=9, column=3)
