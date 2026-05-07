"""Acceptance tests for ``lsp.query.case_split_at`` and
``lsp.query.splittable_vars_at`` (Phase 4 / Step 16).

UX shape: cursor on a ``?``, plus an explicit ``variable`` argument
naming what to split on. The two functions are designed to be used
together by editor clients: ``splittable_vars_at`` populates
completion candidates, and ``case_split_at`` produces the edit once
the user picks one.

Coverage matches the plan's five-case acceptance:

(a) splitting a Nat-shape variable (a recursive constructor),
(b) splitting a parameterised List-shape variable (``List<T>``),
(c) splitting a custom union with multi-typed-parameter
    constructors,
(d) splitting a proof variable of ``P or Q``,
(e) cursor not on a ``?`` (returns ``None``).

All fixtures define their own union or rely on bool-only formulas so
the tests run without the standard library prelude.
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
    case_split_at,
    check,
    splittable_vars_at,
)


@dataclass(frozen=True)
class CaseSplitCase:
    name: str
    source: str
    cursor: Position  # Cursor on a ?
    variable: str
    expected_text: str
    expected_range: Range  # Range of the ? being replaced


CASES = [
    CaseSplitCase(
        name="nat_like_union",
        # Cursor on `?` at column 3 -> 2-space indent. Each line of
        # the switch skeleton picks up that indent so the inserted
        # block lines up with the surrounding proof body
        # (issue #333).
        source=(
            "union N {\n"
            "  z\n"
            "  s(N)\n"
            "}\n"
            "\n"
            "theorem t: all x:N. x = x\n"
            "proof\n"
            "  arbitrary x:N\n"
            "  ?\n"
            "end\n"
        ),
        cursor=Position(line=9, column=3),
        variable="x",
        expected_text=(
            "switch x {\n"
            "    case z { ? }\n"
            "    case s(n1) { ? }\n"
            "  }"
        ),
        expected_range=Range(
            start=Position(line=9, column=3),
            end=Position(line=9, column=4),
        ),
    ),
    CaseSplitCase(
        name="parameterised_list_union",
        source=(
            "union L<T> {\n"
            "  e\n"
            "  cons(T, L<T>)\n"
            "}\n"
            "\n"
            "theorem t: all xs:L<bool>. xs = xs\n"
            "proof\n"
            "  arbitrary xs:L<bool>\n"
            "  ?\n"
            "end\n"
        ),
        cursor=Position(line=9, column=3),
        variable="xs",
        expected_text=(
            "switch xs {\n"
            "    case e { ? }\n"
            "    case cons(t1, l2) { ? }\n"
            "  }"
        ),
        expected_range=Range(
            start=Position(line=9, column=3),
            end=Position(line=9, column=4),
        ),
    ),
    CaseSplitCase(
        name="custom_union_multi_typed_params",
        source=(
            "union Tag {\n"
            "  empty\n"
            "  flag(bool)\n"
            "  pair(bool, bool)\n"
            "}\n"
            "\n"
            "theorem t: all x:Tag. x = x\n"
            "proof\n"
            "  arbitrary x:Tag\n"
            "  ?\n"
            "end\n"
        ),
        cursor=Position(line=10, column=3),
        variable="x",
        expected_text=(
            "switch x {\n"
            "    case empty { ? }\n"
            "    case flag(b1) { ? }\n"
            "    case pair(b1, b2) { ? }\n"
            "  }"
        ),
        expected_range=Range(
            start=Position(line=10, column=3),
            end=Position(line=10, column=4),
        ),
    ),
    CaseSplitCase(
        name="proof_variable_of_or_formula",
        source=(
            "theorem t: all P:bool, Q:bool. if P or Q then Q or P\n"
            "proof\n"
            "  arbitrary P:bool, Q:bool\n"
            "  assume H: P or Q\n"
            "  ?\n"
            "end\n"
        ),
        cursor=Position(line=5, column=3),
        variable="H",
        expected_text=(
            "cases H\n"
            "    case h1: P { ? }\n"
            "    case h2: Q { ? }"
        ),
        expected_range=Range(
            start=Position(line=5, column=3),
            end=Position(line=5, column=4),
        ),
    ),
]


@pytest.mark.parametrize("case", CASES, ids=lambda c: c.name)
def test_case_split_at_template(case: CaseSplitCase) -> None:
    edit = case_split_at("test.pf", case.source, case.cursor, case.variable)
    assert edit is not None, f"{case.name}: case_split_at returned None"
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
    case: CaseSplitCase,
) -> None:
    """Plan acceptance: re-running ``check`` on the post-edit content
    must surface a fresh hole *inside the first case body*. This pins
    that the case skeleton parses and that the holes are reachable."""
    edit = case_split_at(
        "test.pf", case.source, case.cursor, case.variable
    )
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
    assert len(diags) == 1, (
        f"{case.name}: expected exactly one diagnostic on post-edit "
        f"content, got {len(diags)}"
    )
    diag = diags[0]
    assert diag.severity == Severity.ERROR
    assert "incomplete proof" in diag.message
    first_case_line = edit.range.start.line + 1
    assert diag.range.start.line == first_case_line, (
        f"{case.name}: expected diagnostic on line "
        f"{first_case_line} (first case body), got line "
        f"{diag.range.start.line}"
    )


def test_returns_none_when_cursor_not_on_hole() -> None:
    """Cursor not on a ``?`` -> no replacement target -> None."""
    source = (
        "union N {\n"
        "  z\n"
        "  s(N)\n"
        "}\n"
        "\n"
        "theorem t: all x:N. x = x\n"
        "proof\n"
        "  arbitrary x:N\n"
        "  ?\n"
        "end\n"
    )
    # Cursor on the `x` of `arbitrary x:N` -- no longer the right
    # input shape; case_split_at requires cursor on the ?.
    edit = case_split_at("test.pf", source, Position(line=8, column=13), "x")
    assert edit is None


def test_returns_none_for_unknown_variable() -> None:
    """``variable`` arg names something not in scope at the hole."""
    source = (
        "union N {\n"
        "  z\n"
        "  s(N)\n"
        "}\n"
        "\n"
        "theorem t: all x:N. x = x\n"
        "proof\n"
        "  arbitrary x:N\n"
        "  ?\n"
        "end\n"
    )
    edit = case_split_at(
        "test.pf", source, Position(line=9, column=3), "no_such_var"
    )
    assert edit is None


def test_returns_none_for_unsupported_variable_type() -> None:
    """``variable`` is in scope but its type isn't a Union / Or."""
    source = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  ?\n"
        "end\n"
    )
    # `P` is in scope at the hole but bool isn't a user Union.
    edit = case_split_at("test.pf", source, Position(line=4, column=3), "P")
    assert edit is None


# --------------------------------------------------------------------------
# splittable_vars_at
# --------------------------------------------------------------------------


def test_splittable_vars_includes_term_variable() -> None:
    """A Union-typed term variable shows up in the candidate list."""
    source = (
        "union N {\n"
        "  z\n"
        "  s(N)\n"
        "}\n"
        "\n"
        "theorem t: all x:N. x = x\n"
        "proof\n"
        "  arbitrary x:N\n"
        "  ?\n"
        "end\n"
    )
    candidates = splittable_vars_at(
        "test.pf", source, Position(line=9, column=3)
    )
    assert "x" in candidates


def test_splittable_vars_includes_or_proof_variable() -> None:
    """A proof variable of `P or Q` shows up in the candidate list."""
    source = (
        "theorem t: all P:bool, Q:bool. if P or Q then Q or P\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume H: P or Q\n"
        "  ?\n"
        "end\n"
    )
    candidates = splittable_vars_at(
        "test.pf", source, Position(line=5, column=3)
    )
    assert "H" in candidates


def test_splittable_vars_excludes_constructors() -> None:
    """Constructors are TermBindings of their union's type -- they
    must NOT show up as splittable variables."""
    source = (
        "union N {\n"
        "  z\n"
        "  s(N)\n"
        "}\n"
        "\n"
        "theorem t: all x:N. x = x\n"
        "proof\n"
        "  arbitrary x:N\n"
        "  ?\n"
        "end\n"
    )
    candidates = splittable_vars_at(
        "test.pf", source, Position(line=9, column=3)
    )
    assert "z" not in candidates
    assert "s" not in candidates


def test_splittable_vars_excludes_non_splittable_term_vars() -> None:
    """A `bool`-typed term variable isn't case-splittable."""
    source = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  ?\n"
        "end\n"
    )
    candidates = splittable_vars_at(
        "test.pf", source, Position(line=4, column=3)
    )
    assert "P" not in candidates


def test_splittable_vars_returns_empty_when_cursor_not_on_hole() -> None:
    """Cursor not on a ``?`` -> empty candidate list."""
    source = (
        "union N {\n"
        "  z\n"
        "  s(N)\n"
        "}\n"
        "\n"
        "theorem t: all x:N. x = x\n"
        "proof\n"
        "  arbitrary x:N\n"
        "  ?\n"
        "end\n"
    )
    # Cursor on the `x` of `arbitrary x:N`.
    candidates = splittable_vars_at(
        "test.pf", source, Position(line=8, column=13)
    )
    assert candidates == ()


def test_splittable_vars_returns_sorted_dedup_names() -> None:
    """The candidate list is sorted and deduplicated."""
    source = (
        "union N {\n"
        "  z\n"
        "  s(N)\n"
        "}\n"
        "\n"
        "theorem t: all P:bool, x:N. if P or P then x = x\n"
        "proof\n"
        "  arbitrary P:bool, x:N\n"
        "  assume H: P or P\n"
        "  ?\n"
        "end\n"
    )
    candidates = splittable_vars_at(
        "test.pf", source, Position(line=10, column=3)
    )
    # Both H (proof var of `P or P`) and x (Union-typed term var)
    # qualify; constructors and `P` (bool) don't.
    assert candidates == ("H", "x")
