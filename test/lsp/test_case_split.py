"""Acceptance tests for ``lsp.query.case_split_at`` (Phase 4 / Step 16).

Each fixture supplies a snippet of Deduce source, a 1-indexed cursor
position on a variable identifier, and the literal ``new_text`` we
expect ``case_split_at`` to produce when replacing the surrounding
``?``.

Coverage matches the plan's five-case acceptance:

(a) splitting a Nat-shape variable (a recursive constructor),
(b) splitting a parameterised List-shape variable (``List<T>``),
(c) splitting a custom union with multi-typed-parameter
    constructors,
(d) splitting a proof variable of ``P or Q``,
(e) cursor not on a variable (returns ``None``).

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
)


@dataclass(frozen=True)
class CaseSplitCase:
    name: str
    source: str
    cursor: Position
    expected_text: str
    expected_range: Range


CASES = [
    CaseSplitCase(
        name="nat_like_union",
        # ``z`` and ``s(N)`` -- the canonical shape. Cursor on the
        # `x` of ``arbitrary x:N``. Expected switch with one case
        # per constructor; recursive parameter gets a fresh `n1`
        # name.
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
        cursor=Position(line=8, column=13),  # the `x` after `arbitrary`
        expected_text=(
            "switch x {\n"
            "  case z { ? }\n"
            "  case s(n1) { ? }\n"
            "}"
        ),
        expected_range=Range(
            start=Position(line=9, column=3),
            end=Position(line=9, column=4),
        ),
    ),
    CaseSplitCase(
        name="parameterised_list_union",
        # ``L<T>`` with constructors ``e`` and ``cons(T, L<T>)``.
        # Tests that case-split works through TypeInst (the
        # variable's type is ``L<bool>``, an instantiation).
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
        cursor=Position(line=8, column=13),  # `xs` after `arbitrary`
        expected_text=(
            "switch xs {\n"
            "  case e { ? }\n"
            "  case cons(t1, l2) { ? }\n"
            "}"
        ),
        expected_range=Range(
            start=Position(line=9, column=3),
            end=Position(line=9, column=4),
        ),
    ),
    CaseSplitCase(
        name="custom_union_multi_typed_params",
        # Three constructors covering arity 0, 1, 2 -- exercises the
        # per-case scope reset for parameter naming (the second
        # ``flag``'s ``b1`` shouldn't collide with ``pair``'s ``b1``).
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
        cursor=Position(line=9, column=13),  # `x` after `arbitrary`
        expected_text=(
            "switch x {\n"
            "  case empty { ? }\n"
            "  case flag(b1) { ? }\n"
            "  case pair(b1, b2) { ? }\n"
            "}"
        ),
        expected_range=Range(
            start=Position(line=10, column=3),
            end=Position(line=10, column=4),
        ),
    ),
    CaseSplitCase(
        name="proof_variable_of_or_formula",
        # Proof binding ``H : P or Q`` -> ``cases H ...`` skeleton.
        # Each branch's hypothesis label is a fresh ``h<N>`` so
        # nested refines don't collide.
        source=(
            "theorem t: all P:bool, Q:bool. if P or Q then Q or P\n"
            "proof\n"
            "  arbitrary P:bool, Q:bool\n"
            "  assume H: P or Q\n"
            "  ?\n"
            "end\n"
        ),
        cursor=Position(line=4, column=10),  # the `H` of `assume H:`
        expected_text=(
            "cases H\n"
            "  case h1: P { ? }\n"
            "  case h2: Q { ? }"
        ),
        expected_range=Range(
            start=Position(line=5, column=3),
            end=Position(line=5, column=4),
        ),
    ),
]


@pytest.mark.parametrize("case", CASES, ids=lambda c: c.name)
def test_case_split_at_template(case: CaseSplitCase) -> None:
    edit = case_split_at("test.pf", case.source, case.cursor)
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
    edit = case_split_at("test.pf", case.source, case.cursor)
    assert edit is not None

    # Apply the single-line replacement.
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
    # The diagnostic should point at the first `?` inside the first
    # case body. That `?` is at the start of the second line of
    # ``edit.new_text`` (the body of `case ... {` ... `}`).
    first_case_line = edit.range.start.line + 1
    assert diag.range.start.line == first_case_line, (
        f"{case.name}: expected diagnostic on line "
        f"{first_case_line} (first case body), got line "
        f"{diag.range.start.line}"
    )


def test_returns_none_when_cursor_not_on_identifier() -> None:
    """Cursor on punctuation -> no identifier to split on."""
    source = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  ?\n"
        "end\n"
    )
    # Cursor on the `:` of `arbitrary P:bool`.
    edit = case_split_at("test.pf", source, Position(line=3, column=14))
    assert edit is None


def test_returns_none_when_no_hole_after_cursor() -> None:
    """Variable in scope but no `?` follows -> nothing to replace."""
    source = (
        "union N {\n"
        "  z\n"
        "  s(N)\n"
        "}\n"
        "\n"
        "theorem t: all x:N. x = x\n"
        "proof\n"
        "  arbitrary x:N\n"
        "  reflexive\n"
        "end\n"
    )
    # Cursor on `x`; the file has no `?` anywhere.
    edit = case_split_at("test.pf", source, Position(line=8, column=13))
    assert edit is None


def test_returns_none_for_unsupported_variable_type() -> None:
    """A bool variable has no constructors to split on -> None."""
    # ``bool`` is built-in and not a Union from the user's POV
    # (it's defined inside the prelude/builtins). Without prelude,
    # ``bool`` is just a primitive type and case_split_at returns
    # None rather than guess.
    source = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  ?\n"
        "end\n"
    )
    edit = case_split_at("test.pf", source, Position(line=3, column=13))
    assert edit is None


def test_returns_none_when_identifier_not_in_scope() -> None:
    """Cursor on text that lexes as an identifier but isn't a
    bound variable in the env at the hole."""
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
    # Cursor on the `theorem` keyword -- a token, but not a
    # variable bound in the env. The lookup fails -> None.
    edit = case_split_at("test.pf", source, Position(line=6, column=3))
    assert edit is None
