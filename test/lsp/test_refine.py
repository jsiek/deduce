"""Acceptance tests for ``lsp.query.refine_at`` (Phase 4 / Step 15).

Hand-crafted fixtures embedded inline -- one per template shape worth
pinning. Each case supplies a snippet of Deduce source, the 1-indexed
cursor position of the ``?``, and the literal template text that
``refine_at`` should produce.

All fixtures stay inside ``bool``-only territory so the tests run
without the standard library prelude. The pipeline reaches the
cursor's ``?`` (each fixture has exactly one) and ``incomplete_error``
stashes the goal AST on the exception for ``_refine_template`` to
match against.
"""

from __future__ import annotations

import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from lsp.query import (  # noqa: E402
    Position,
    Range,
    WorkspaceEdit,
    refine_at,
)


@dataclass(frozen=True)
class RefineCase:
    name: str
    source: str
    cursor: Position
    expected_text: str
    # 1-indexed range covering exactly the `?` token in ``source``.
    expected_range: Range


CASES = [
    RefineCase(
        name="conjunction_two_args",
        # Goal at the hole: ``(P and Q)``. Template: ``?, ?``.
        source=(
            "theorem t: all P:bool, Q:bool. if P then if Q then P and Q\n"
            "proof\n"
            "  arbitrary P:bool, Q:bool\n"
            "  suppose pP: P\n"
            "  suppose qQ: Q\n"
            "  ?\n"
            "end\n"
        ),
        cursor=Position(line=6, column=3),
        expected_text="?, ?",
        expected_range=Range(
            start=Position(line=6, column=3),
            end=Position(line=6, column=4),
        ),
    ),
    RefineCase(
        name="conjunction_three_args",
        # Goal: ``(P and Q and R)``. Template: ``?, ?, ?``.
        source=(
            "theorem t: all P:bool, Q:bool, R:bool.\n"
            "  if P then if Q then if R then P and Q and R\n"
            "proof\n"
            "  arbitrary P:bool, Q:bool, R:bool\n"
            "  suppose pP: P\n"
            "  suppose qQ: Q\n"
            "  suppose rR: R\n"
            "  ?\n"
            "end\n"
        ),
        cursor=Position(line=8, column=3),
        expected_text="?, ?, ?",
        expected_range=Range(
            start=Position(line=8, column=3),
            end=Position(line=8, column=4),
        ),
    ),
    RefineCase(
        name="implication",
        # Goal: ``(if P then P)``. Template uses ``H1`` (no other
        # ``H<N>`` is in scope yet, so we start at 1). The ``?'' on
        # the second line picks up the surrounding proof body's
        # 2-space indent (issue #333).
        source=(
            "theorem t: all P:bool. if P then P\n"
            "proof\n"
            "  arbitrary P:bool\n"
            "  ?\n"
            "end\n"
        ),
        cursor=Position(line=4, column=3),
        expected_text="assume H1: P\n  ?",
        expected_range=Range(
            start=Position(line=4, column=3),
            end=Position(line=4, column=4),
        ),
    ),
    RefineCase(
        name="implication_picks_H2_when_H1_in_scope",
        # Regression for the label-collision bug: the user already
        # has ``H1`` in scope from a prior ``assume H1:``. The
        # template must pick the next free ``H<N>``, i.e. ``H2``,
        # rather than re-using ``H`` or ``H1``.
        source=(
            "theorem t: all P:bool, Q:bool. if P then if Q then P\n"
            "proof\n"
            "  arbitrary P:bool, Q:bool\n"
            "  assume H1: P\n"
            "  ?\n"
            "end\n"
        ),
        cursor=Position(line=5, column=3),
        expected_text="assume H2: Q\n  ?",
        expected_range=Range(
            start=Position(line=5, column=3),
            end=Position(line=5, column=4),
        ),
    ),
    RefineCase(
        name="implication_picks_H3_when_H1_and_H2_in_scope",
        # Two hypotheses already in scope -> next is H3.
        source=(
            "theorem t: all P:bool, Q:bool, R:bool.\n"
            "  if (if P and Q then R) then if Q then if P then R\n"
            "proof\n"
            "  arbitrary P:bool, Q:bool, R:bool\n"
            "  assume H1: (if (P and Q) then R)\n"
            "  assume H2: Q\n"
            "  ?\n"
            "end\n"
        ),
        cursor=Position(line=7, column=3),
        expected_text="assume H3: P\n  ?",
        expected_range=Range(
            start=Position(line=7, column=3),
            end=Position(line=7, column=4),
        ),
    ),
    RefineCase(
        name="forall",
        # Goal: ``(all P:bool. P = P)``. Template: ``arbitrary P:bool\n?``.
        # ``?`` picks up the proof body's 2-space indent.
        source=(
            "theorem t: all P:bool. P = P\n"
            "proof\n"
            "  ?\n"
            "end\n"
        ),
        cursor=Position(line=3, column=3),
        expected_text="arbitrary P:bool\n  ?",
        expected_range=Range(
            start=Position(line=3, column=3),
            end=Position(line=3, column=4),
        ),
    ),
    RefineCase(
        name="reflexive_equality",
        # Goal at hole (after `arbitrary`): ``P = P``. Both sides
        # already reduce to the same term, so template is
        # ``reflexive``.
        source=(
            "theorem t: all P:bool. P = P\n"
            "proof\n"
            "  arbitrary P:bool\n"
            "  ?\n"
            "end\n"
        ),
        cursor=Position(line=4, column=3),
        expected_text="reflexive",
        expected_range=Range(
            start=Position(line=4, column=3),
            end=Position(line=4, column=4),
        ),
    ),
]


@pytest.mark.parametrize("case", CASES, ids=lambda c: c.name)
def test_refine_at_template(case: RefineCase) -> None:
    edit = refine_at("test.pf", case.source, case.cursor)
    assert edit is not None, f"{case.name}: refine_at returned None"
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


def test_refine_at_returns_none_when_cursor_not_on_hole() -> None:
    """No `?` at or adjacent to the cursor -> no edit."""
    source = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  reflexive\n"
        "end\n"
    )
    # Cursor on the `r` of `reflexive` -- no hole anywhere near.
    assert refine_at("test.pf", source, Position(line=4, column=3)) is None


def test_refine_at_returns_none_for_unsupported_goal_shape() -> None:
    """A bare bool atom (no logical structure) has no template here."""
    # Goal at hole: ``P`` (a bool literal-shape variable). Not in the
    # template table, so refine_at returns None rather than guess.
    source = (
        "theorem t: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  suppose pP: P\n"
        "  ?\n"
        "end\n"
    )
    edit = refine_at("test.pf", source, Position(line=5, column=3))
    assert edit is None


def test_refine_at_returns_none_when_file_is_complete() -> None:
    """File without a hole -> nothing for refine_at to do."""
    source = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  reflexive\n"
        "end\n"
    )
    # Cursor wherever; there's no ? in the source.
    assert refine_at("test.pf", source, Position(line=3, column=3)) is None


def test_refine_at_cursor_one_position_after_hole() -> None:
    """Cursor immediately after the `?` should still match it.

    Eglot sends the cursor at the column past the character; this
    keeps the editor UX intuitive (`C-c C-r` while typing right after
    a hole).
    """
    source = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  ?\n"
        "end\n"
    )
    # Cursor at col 4, one past the `?` at col 3.
    edit = refine_at("test.pf", source, Position(line=4, column=4))
    assert edit is not None
    assert edit.new_text == "reflexive"
    assert edit.range.start == Position(line=4, column=3)


# --------------------------------------------------------------------------
# Indent preservation (issue #333)
# --------------------------------------------------------------------------


def test_indent_continuation_zero_indent_no_change() -> None:
    """Hole at column 1 -> no indent to add -> template unchanged."""
    # Cursor on `?' at line 4 col 1 -- no leading whitespace.
    # The `arbitrary P:bool` line is also unindented so the env at
    # the hole really has just ``P`` available; goal at hole is the
    # ``if P then P`` implication.
    source = (
        "theorem t: all P:bool. if P then P\n"
        "proof\n"
        "arbitrary P:bool\n"
        "?\n"
        "end\n"
    )
    edit = refine_at("test.pf", source, Position(line=4, column=1))
    assert edit is not None
    # No indent to add; the inner `?` stays at col 0.
    assert edit.new_text == "assume H1: P\n?"


def test_indent_continuation_tab_indent_preserved() -> None:
    """Hole on a tab-indented line -> continuation line gets the
    same tab prefix."""
    source = (
        "theorem t: all P:bool. if P then P\n"
        "proof\n"
        "\tarbitrary P:bool\n"
        "\t?\n"
        "end\n"
    )
    # Cursor on `?` at line 4 col 2 (the tab is 1 char).
    edit = refine_at("test.pf", source, Position(line=4, column=2))
    assert edit is not None
    assert edit.new_text == "assume H1: P\n\t?"


def test_indent_continuation_three_step_refine_stays_at_indent() -> None:
    """End-to-end: three successive refines on the issue #333 reproducer
    keep all the inserted lines at the same 2-space indent."""
    source = (
        "theorem ex_all_if_and: all P:bool, Q:bool, R:bool.\n"
        "  if (if P and Q then R) then (if Q then if P then R)\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  arbitrary Q:bool\n"
        "  arbitrary R:bool\n"
        "  ?\n"
        "end\n"
    )

    def apply(src: str, edit) -> str:
        lines = src.splitlines(keepends=True)
        i = edit.range.start.line - 1
        col = edit.range.start.column - 1
        ec = edit.range.end.column - 1
        new_line = lines[i][:col] + edit.new_text + lines[i][ec:]
        return "".join(lines[:i] + [new_line] + lines[i + 1:])

    # Three rounds of `assume H<N>: ...`
    for _ in range(3):
        # Find the next `?`
        for line_num, line in enumerate(source.split("\n"), 1):
            if "?" in line:
                col = line.index("?") + 1
                break
        edit = refine_at(
            "test.pf", source, Position(line=line_num, column=col)
        )
        assert edit is not None
        source = apply(source, edit)

    # Every `assume` line should be 2-space-indented; no line drops
    # to column 0 mid-staircase.
    for ln in source.splitlines():
        if ln.startswith("assume "):
            raise AssertionError(
                f"Line lost its indent (issue #333 regression):\n  {ln!r}"
            )
    assert "  assume H1:" in source
    assert "  assume H2: Q" in source
    assert "  assume H3: P" in source
