"""Acceptance tests for ``lsp.query.eliminate_at`` and
``lsp.query.eliminable_vars_at`` (Phase 4 / Step 18).

UX shape: cursor on a ``?`` plus an explicit ``label`` argument
naming the in-scope hypothesis to use.  Same shape as Step 16
(case split) -- editor clients fetch candidate labels via
``eliminable_vars_at`` and prompt with ``completing-read`` before
issuing ``eliminate_at``.

Coverage:

(a) ``H: P and Q`` -> destructure with ``have ... by conjunct N of H``
(b) ``H: P or Q``  -> ``cases H ...``
(c) ``H: if P then Q`` -> ``have h: Q by apply H to ?\\n?``
(d) ``H: all x:T. P`` -> ``H[?]`` (term arg) or ``H<?>`` (type arg)
(e) ``H: some x:T. P`` -> ``obtain ... where ... from H``
(f) ``H: e1 = e2`` -> ``replace H\\n?``
(g) ``H: false`` -> ``H``  (discharges any goal)
(h) ``H: true`` -> None    ("useless")

Plus boundary cases:
- cursor not on ``?``,
- label not in scope,
- hypothesis shape unsupported.

All fixtures stay inside ``bool``-only territory so the tests run
without the standard library prelude.
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
    WorkspaceEdit,
    eliminable_vars_at,
    eliminate_at,
)


@dataclass(frozen=True)
class EliminateCase:
    name: str
    source: str
    cursor: Position
    label: str
    expected_text: str
    expected_range: Range


CASES = [
    EliminateCase(
        name="and",
        # `H: P and Q' destructures into two `have' lines plus a `?'
        # for the original goal.
        source=(
            "theorem t: all P:bool, Q:bool. if P and Q then Q and P\n"
            "proof\n"
            "  arbitrary P:bool, Q:bool\n"
            "  assume H: P and Q\n"
            "  ?\n"
            "end\n"
        ),
        cursor=Position(line=5, column=3),
        label="H",
        expected_text=(
            "have H1: P by conjunct 1 of H\n"
            "  have H2: Q by conjunct 2 of H\n"
            "  ?"
        ),
        expected_range=Range(
            start=Position(line=5, column=3),
            end=Position(line=5, column=4),
        ),
    ),
    EliminateCase(
        name="or",
        source=(
            "theorem t: all P:bool, Q:bool. if P or Q then Q or P\n"
            "proof\n"
            "  arbitrary P:bool, Q:bool\n"
            "  assume H: P or Q\n"
            "  ?\n"
            "end\n"
        ),
        cursor=Position(line=5, column=3),
        label="H",
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
    EliminateCase(
        name="ifthen",
        source=(
            "theorem t: all P:bool, Q:bool.\n"
            "  if (if P then Q) then if P then Q\n"
            "proof\n"
            "  arbitrary P:bool, Q:bool\n"
            "  assume H: if P then Q\n"
            "  ?\n"
            "end\n"
        ),
        cursor=Position(line=6, column=3),
        label="H",
        expected_text=(
            "have H1: Q by apply H to ?\n"
            "  ?"
        ),
        expected_range=Range(
            start=Position(line=6, column=3),
            end=Position(line=6, column=4),
        ),
    ),
    EliminateCase(
        name="all_term_arg",
        # `H: all Q:bool. ...' instantiates as `H[?]'.
        source=(
            "theorem t: all P:bool.\n"
            "  if (all Q:bool. if Q then Q) then if P then P\n"
            "proof\n"
            "  arbitrary P:bool\n"
            "  assume H: all Q:bool. if Q then Q\n"
            "  ?\n"
            "end\n"
        ),
        cursor=Position(line=6, column=3),
        label="H",
        expected_text="H[?]",
        expected_range=Range(
            start=Position(line=6, column=3),
            end=Position(line=6, column=4),
        ),
    ),
    EliminateCase(
        name="some",
        source=(
            "theorem t: all P:bool, Q:bool.\n"
            "  if (some y:bool. P or Q) then true\n"
            "proof\n"
            "  arbitrary P:bool, Q:bool\n"
            "  assume H: some y:bool. P or Q\n"
            "  ?\n"
            "end\n"
        ),
        cursor=Position(line=6, column=3),
        label="H",
        expected_text=(
            "obtain b1 where H1: (P or Q) from H\n"
            "  ?"
        ),
        expected_range=Range(
            start=Position(line=6, column=3),
            end=Position(line=6, column=4),
        ),
    ),
    EliminateCase(
        name="equality",
        source=(
            "theorem t: all P:bool. if P = true then true = P\n"
            "proof\n"
            "  arbitrary P:bool\n"
            "  assume H: P = true\n"
            "  ?\n"
            "end\n"
        ),
        cursor=Position(line=5, column=3),
        label="H",
        expected_text=(
            "replace H\n"
            "  ?"
        ),
        expected_range=Range(
            start=Position(line=5, column=3),
            end=Position(line=5, column=4),
        ),
    ),
    EliminateCase(
        name="false",
        # `H: false' discharges any goal: replace `?` with `H`.
        source=(
            "theorem t: all P:bool. if false then P\n"
            "proof\n"
            "  arbitrary P:bool\n"
            "  assume H: false\n"
            "  ?\n"
            "end\n"
        ),
        cursor=Position(line=5, column=3),
        label="H",
        expected_text="H",
        expected_range=Range(
            start=Position(line=5, column=3),
            end=Position(line=5, column=4),
        ),
    ),
]


@pytest.mark.parametrize("case", CASES, ids=lambda c: c.name)
def test_eliminate_at_template(case: EliminateCase) -> None:
    edit = eliminate_at("test.pf", case.source, case.cursor, case.label)
    assert edit is not None, f"{case.name}: eliminate_at returned None"
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


def test_eliminate_at_returns_none_for_true_fact() -> None:
    """`H: true' has no useful template."""
    source = (
        "theorem t: all P:bool. if true then P or not P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume H: true\n"
        "  ?\n"
        "end\n"
    )
    edit = eliminate_at("test.pf", source, Position(line=5, column=3), "H")
    assert edit is None


def test_eliminate_at_returns_none_when_cursor_not_on_hole() -> None:
    """Cursor not on a ``?`` -> no replacement target."""
    source = (
        "theorem t: all P:bool, Q:bool. if P or Q then Q or P\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume H: P or Q\n"
        "  ?\n"
        "end\n"
    )
    # Cursor on `assume' keyword, line 4 col 3.
    edit = eliminate_at("test.pf", source, Position(line=4, column=3), "H")
    assert edit is None


def test_eliminate_at_returns_none_for_unknown_label() -> None:
    """Label doesn't match any in-scope binding."""
    source = (
        "theorem t: all P:bool, Q:bool. if P or Q then Q or P\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume H: P or Q\n"
        "  ?\n"
        "end\n"
    )
    edit = eliminate_at(
        "test.pf", source, Position(line=5, column=3), "nope"
    )
    assert edit is None


def test_eliminate_at_returns_none_for_term_variable() -> None:
    """Label refers to a term variable (`P:bool'), not a proof
    binding -> no template."""
    source = (
        "theorem t: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  ?\n"
        "end\n"
    )
    edit = eliminate_at("test.pf", source, Position(line=4, column=3), "P")
    assert edit is None


# --------------------------------------------------------------------------
# eliminable_vars_at
# --------------------------------------------------------------------------


def test_eliminable_vars_includes_local_proof_bindings() -> None:
    source = (
        "theorem t: all P:bool, Q:bool. if P or Q then P or Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume H: P or Q\n"
        "  ?\n"
        "end\n"
    )
    candidates = eliminable_vars_at(
        "test.pf", source, Position(line=5, column=3)
    )
    assert "H" in candidates


def test_eliminable_vars_excludes_term_variables() -> None:
    source = (
        "theorem t: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume pP: P\n"
        "  ?\n"
        "end\n"
    )
    candidates = eliminable_vars_at(
        "test.pf", source, Position(line=5, column=3)
    )
    # `P' is a bool term variable, not a proof binding -- excluded.
    assert "P" not in candidates
    # `pP' is a local proof binding (atom `P' though, no template
    # in v1 -- so it shouldn't show up either).
    assert "pP" not in candidates


def test_eliminable_vars_excludes_true_fact() -> None:
    """A `true'-shaped hypothesis has no useful template -> filtered
    out of the candidate list."""
    source = (
        "theorem t: all P:bool. if true then P or not P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume H: true\n"
        "  ?\n"
        "end\n"
    )
    candidates = eliminable_vars_at(
        "test.pf", source, Position(line=5, column=3)
    )
    assert "H" not in candidates


def test_eliminable_vars_returns_empty_off_hole() -> None:
    """Cursor not on a `?` -> empty list."""
    source = (
        "theorem t: all P:bool, Q:bool. if P or Q then Q or P\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume H: P or Q\n"
        "  ?\n"
        "end\n"
    )
    candidates = eliminable_vars_at(
        "test.pf", source, Position(line=4, column=3)
    )
    assert candidates == ()
