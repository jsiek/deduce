"""Acceptance tests for ``lsp.query.fill_from_given_at`` and
``lsp.query.matching_givens_at`` (issue #353).

UX shape: cursor on a ``?`` plus an explicit ``label`` argument
naming the in-scope local hypothesis whose formula equals the goal.
Same shape as Step 18 (eliminate) -- editor clients fetch candidate
labels via ``matching_givens_at`` and prompt with ``completing-read``
before issuing ``fill_from_given_at``.

Coverage:

(a) goal exactly matches a unique given -> bare ``<label>`` (the only
    shape valid in both statement and term positions);
(b) goal matches multiple givens -> all labels listed; either works;
(c) given strictly implies the goal -> ``conclude <goal> by <label>``
    (verbose form for auto-rule normalisation);
(d) goal matches no given -> empty list, ``None`` edit;
(e) cursor not on ``?`` -> empty list, ``None`` edit;
(f) label not in scope -> ``None``;
(g) label is a term variable (not a proof binding) -> ``None``;
(h) label is a theorem (not a local binding) -> ``None``.

All fixtures stay inside ``bool``-only territory so the tests run
without the standard library prelude.
"""

from __future__ import annotations

import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from lsp.query import (  # noqa: E402
    Position,
    Range,
    WorkspaceEdit,
    fill_from_given_at,
    matching_givens_at,
)


# --------------------------------------------------------------------------
# fill_from_given_at
# --------------------------------------------------------------------------


def test_fill_from_given_at_single_match() -> None:
    """Exact match (goal ``P or Q`` with given ``H: P or Q``) emits the
    bare label -- a proof term that's valid in both statement and term
    positions, unlike ``conclude ... by ...`` which is statement-only."""
    source = (
        "theorem t: all P:bool, Q:bool. if P or Q then P or Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume H: P or Q\n"
        "  ?\n"
        "end\n"
    )
    edit = fill_from_given_at(
        "test.pf", source, Position(line=5, column=3), "H"
    )
    assert edit is not None
    assert isinstance(edit, WorkspaceEdit)
    assert edit.path == "test.pf"
    assert edit.range == Range(
        start=Position(line=5, column=3),
        end=Position(line=5, column=4),
    )
    assert edit.new_text == "H"


def test_fill_from_given_at_atomic_goal() -> None:
    """Atomic-formula exact match: goal ``P`` with given ``pP: P``
    emits just the bare label."""
    source = (
        "theorem t: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume pP: P\n"
        "  ?\n"
        "end\n"
    )
    edit = fill_from_given_at(
        "test.pf", source, Position(line=5, column=3), "pP"
    )
    assert edit is not None
    assert edit.new_text == "pP"


def test_fill_from_given_at_picks_either_match() -> None:
    """Two matching givens: caller-chosen label both work, both as
    bare labels."""
    source = (
        "theorem t: all P:bool. if P then if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume H1: P\n"
        "  assume H2: P\n"
        "  ?\n"
        "end\n"
    )
    for label in ("H1", "H2"):
        edit = fill_from_given_at(
            "test.pf", source, Position(line=6, column=3), label
        )
        assert edit is not None, f"label {label} produced no edit"
        assert edit.new_text == label


def test_fill_from_given_at_implies_or_intro() -> None:
    """Implies-only match: goal ``P or Q`` with given ``H: P`` -- the
    given strictly implies the goal via ``Or`` introduction (issue
    #361).  Stays as ``conclude <goal> by <label>`` so the proof
    checker's auto-rule normalisation fires."""
    source = (
        "theorem t: all P:bool, Q:bool. if P then P or Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume H: P\n"
        "  ?\n"
        "end\n"
    )
    edit = fill_from_given_at(
        "test.pf", source, Position(line=5, column=3), "H"
    )
    assert edit is not None
    assert edit.new_text == "conclude (P or Q) by H"


def test_fill_from_given_at_in_conjunction_slot() -> None:
    """Regression for the term-position breakage.

    After refining ``? : P and Q`` into the conjunction shape
    ``?, ?``, the first hole is in *term* position (a slot of the
    conjunction proof), where ``conclude ... by ...'' is a syntax
    error.  Exact-match fill must therefore emit the bare label so
    the resulting ``H1, ?'' is a valid proof of ``P and Q''."""
    source = (
        "theorem t : all P:bool, Q:bool. if P then if Q then P and Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume H1: P\n"
        "  assume H2: Q\n"
        "  ?, ?\n"
        "end\n"
    )
    edit = fill_from_given_at(
        "test.pf", source, Position(line=6, column=3), "H1"
    )
    assert edit is not None
    # Critical: bare label, not ``conclude P by H1''.  The latter
    # would produce ``conclude P by H1, ?'' which the parser rejects
    # (``conclude'' is statement-level, not term-level).
    assert edit.new_text == "H1"


def test_fill_from_given_at_returns_none_when_unrelated() -> None:
    """Goal ``Q`` with an unrelated given ``H: P`` -- neither equals
    nor implies the goal."""
    source = (
        "theorem t: all P:bool, Q:bool. if Q then if P then Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume HQ: Q\n"
        "  assume H: P\n"
        "  ?\n"
        "end\n"
    )
    # Goal at the hole is `Q`; `H: P` does not imply it.
    edit = fill_from_given_at(
        "test.pf", source, Position(line=6, column=3), "H"
    )
    assert edit is None


def test_fill_from_given_at_returns_none_off_hole() -> None:
    """Cursor not on a ``?`` -> no replacement target."""
    source = (
        "theorem t: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume H: P\n"
        "  ?\n"
        "end\n"
    )
    # Cursor on `assume` keyword, line 4 col 3.
    edit = fill_from_given_at(
        "test.pf", source, Position(line=4, column=3), "H"
    )
    assert edit is None


def test_fill_from_given_at_returns_none_for_unknown_label() -> None:
    """Label doesn't match any in-scope binding."""
    source = (
        "theorem t: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume H: P\n"
        "  ?\n"
        "end\n"
    )
    edit = fill_from_given_at(
        "test.pf", source, Position(line=5, column=3), "nope"
    )
    assert edit is None


def test_fill_from_given_at_returns_none_for_term_variable() -> None:
    """Label refers to a term variable (`P:bool'), not a proof
    binding -- defensively returns None even though the formula
    doesn't make sense to compare."""
    source = (
        "theorem t: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume pP: P\n"
        "  ?\n"
        "end\n"
    )
    edit = fill_from_given_at(
        "test.pf", source, Position(line=5, column=3), "P"
    )
    assert edit is None


def test_fill_from_given_at_returns_none_for_non_local_binding() -> None:
    """A theorem in scope is a non-local proof binding -- excluded
    from the matching givens.  Users invoke theorems by name, not
    via this command."""
    source = (
        "theorem h: true\n"
        "proof . end\n"
        "theorem t: true\n"
        "proof\n"
        "  ?\n"
        "end\n"
    )
    # `h' has formula `true', which equals the goal `true', but `h'
    # is a theorem reference (non-local), so fill-from-given skips it.
    edit = fill_from_given_at(
        "test.pf", source, Position(line=5, column=3), "h"
    )
    assert edit is None


# --------------------------------------------------------------------------
# matching_givens_at
# --------------------------------------------------------------------------


def test_matching_givens_includes_unique_match() -> None:
    source = (
        "theorem t: all P:bool, Q:bool. if P or Q then P or Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume H: P or Q\n"
        "  ?\n"
        "end\n"
    )
    candidates = matching_givens_at(
        "test.pf", source, Position(line=5, column=3)
    )
    assert candidates == ("H",)


def test_matching_givens_lists_all_matches() -> None:
    source = (
        "theorem t: all P:bool. if P then if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume H1: P\n"
        "  assume H2: P\n"
        "  ?\n"
        "end\n"
    )
    candidates = matching_givens_at(
        "test.pf", source, Position(line=6, column=3)
    )
    assert candidates == ("H1", "H2")


def test_matching_givens_excludes_unrelated() -> None:
    """Givens that neither equal nor imply the goal aren't listed."""
    source = (
        "theorem t: all P:bool, Q:bool. if Q then if P then Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume HQ: Q\n"
        "  assume H: P\n"
        "  ?\n"
        "end\n"
    )
    # Goal is `Q`; only HQ matches (exactly). H is unrelated.
    candidates = matching_givens_at(
        "test.pf", source, Position(line=6, column=3)
    )
    assert candidates == ("HQ",)


def test_matching_givens_includes_implies_or_intro() -> None:
    """Given strictly implies the goal via ``Or`` introduction
    (issue #361): ``H: P`` should match goal ``P or Q``."""
    source = (
        "theorem t: all P:bool, Q:bool. if P then P or Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume H: P\n"
        "  ?\n"
        "end\n"
    )
    candidates = matching_givens_at(
        "test.pf", source, Position(line=5, column=3)
    )
    assert candidates == ("H",)


def test_matching_givens_includes_implies_and_elim() -> None:
    """Given strictly implies the goal via ``And`` elimination
    (issue #361): ``H: P and Q`` should match goal ``P``."""
    source = (
        "theorem t: all P:bool, Q:bool. if P and Q then P\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume H: P and Q\n"
        "  ?\n"
        "end\n"
    )
    candidates = matching_givens_at(
        "test.pf", source, Position(line=5, column=3)
    )
    assert candidates == ("H",)


def test_matching_givens_orders_exact_before_implies() -> None:
    """When both an exact match and an implies-only match are
    available, the exact match comes first (issue #361)."""
    source = (
        "theorem t: all P:bool, Q:bool. if P or Q then if P then P or Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume H1: P or Q\n"
        "  assume H2: P\n"
        "  ?\n"
        "end\n"
    )
    # H1: P or Q is exact; H2: P implies (P or Q) but isn't exact.
    candidates = matching_givens_at(
        "test.pf", source, Position(line=6, column=3)
    )
    assert candidates == ("H1", "H2")


def test_matching_givens_excludes_term_variables() -> None:
    """Term variables aren't proof bindings -- excluded."""
    source = (
        "theorem t: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume pP: P\n"
        "  ?\n"
        "end\n"
    )
    candidates = matching_givens_at(
        "test.pf", source, Position(line=5, column=3)
    )
    # `pP` matches the goal `P` and is local -> in.
    # `P` is a term variable -> out.
    assert "pP" in candidates
    assert "P" not in candidates


def test_matching_givens_excludes_non_local() -> None:
    """A theorem with the same formula as the goal isn't listed
    -- only local proof bindings count."""
    source = (
        "theorem h: true\n"
        "proof . end\n"
        "theorem t: true\n"
        "proof\n"
        "  ?\n"
        "end\n"
    )
    candidates = matching_givens_at(
        "test.pf", source, Position(line=5, column=3)
    )
    assert "h" not in candidates


def test_matching_givens_returns_empty_off_hole() -> None:
    """Cursor not on a `?` -> empty list."""
    source = (
        "theorem t: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume H: P\n"
        "  ?\n"
        "end\n"
    )
    candidates = matching_givens_at(
        "test.pf", source, Position(line=4, column=3)
    )
    assert candidates == ()
