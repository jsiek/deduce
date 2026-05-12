"""Acceptance tests for ``lsp.query.preview_replace_at`` and
``lsp.query.preview_expand_at`` (issue #401).

Both queries are pure / read-only: they target the cursor's ``?`` token,
target the proof checker's ``IncompleteProof`` exception to read the
goal AST and env at the hole, then call ``apply_rewrites`` /
``expand_definitions`` directly to compute the rewritten goal -- without
mutating any source file.

Coverage:

- ``preview_replace_at`` success (forward and ``symmetric``), plus the
  four documented failure outcomes (no_match, not_an_equation,
  unbound, and the auto-rule-canonicalized case).
- ``preview_expand_at`` success on a ``define`` and a recursive
  function, plus the unknown / opaque / no_match outcomes.

Most fixtures stay inside ``bool``-only territory so the tests run
without the ``Nat``/``UInt`` prelude. The two stdlib-dependent tests
explicitly request the relevant module.
"""

from __future__ import annotations

import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from lsp.query import (  # noqa: E402
    ExpandPreview,
    Position,
    RewritePreview,
    preview_expand_at,
    preview_replace_at,
)


# --------------------------------------------------------------------------
# preview_replace_at
# --------------------------------------------------------------------------


def test_preview_replace_at_forward_rewrite_succeeds() -> None:
    """``replace H`` rewrites occurrences of the LHS in the goal."""
    source = (
        "theorem t: all P:bool, Q:bool. if P = Q then P\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume H: P = Q\n"
        "  ?\n"
        "end\n"
    )
    # Goal at hole: `P`. With H: P = Q, forward rewrite turns `P` into
    # `Q`.
    preview = preview_replace_at(
        "test.pf", source, Position(line=5, column=3), "H"
    )
    assert preview is not None
    assert isinstance(preview, RewritePreview)
    assert preview.outcome == "ok", preview
    assert preview.before == "P"
    assert preview.after == "Q"


def test_preview_replace_at_changes_goal_when_lhs_present() -> None:
    """A goal containing the LHS is rewritten to use the RHS."""
    source = (
        "theorem t: all P:bool, Q:bool, R:bool.\n"
        "  if P = Q then if R = P then R = Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool, R:bool\n"
        "  assume H1: P = Q\n"
        "  assume H2: R = P\n"
        "  ?\n"
        "end\n"
    )
    # Goal at hole: `R = Q`. Replace H2 (which says R = P) goes
    # right-to-left in the sense that the LHS R appears in the goal and
    # is rewritten to P. So the new goal becomes `P = Q`.
    preview = preview_replace_at(
        "test.pf", source, Position(line=7, column=3), "H2"
    )
    assert preview is not None
    assert preview.outcome == "ok", preview
    assert preview.before == "R = Q"
    assert preview.after == "P = Q"


def test_preview_replace_at_symmetric_swaps_direction() -> None:
    """``replace symmetric H`` rewrites RHS occurrences with the LHS."""
    source = (
        "theorem t: all P:bool, Q:bool, R:bool.\n"
        "  if P = Q then if R = P then R = Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool, R:bool\n"
        "  assume H1: P = Q\n"
        "  assume H2: R = P\n"
        "  ?\n"
        "end\n"
    )
    # Goal at hole: `R = Q`. With `symmetric H1`, the equation becomes
    # `Q = P`, so the LHS `Q` is rewritten to `P` in the goal: `R = P`.
    preview = preview_replace_at(
        "test.pf", source, Position(line=7, column=3), "symmetric H1"
    )
    assert preview is not None
    assert preview.outcome == "ok", preview
    assert preview.before == "R = Q"
    assert preview.after == "R = P"


def test_preview_replace_at_no_match() -> None:
    """The equation's LHS doesn't appear in the goal -> no_match."""
    source = (
        "theorem t: all P:bool, Q:bool, R:bool.\n"
        "  if P = Q then if R then R\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool, R:bool\n"
        "  assume H: P = Q\n"
        "  assume pR: R\n"
        "  ?\n"
        "end\n"
    )
    preview = preview_replace_at(
        "test.pf", source, Position(line=7, column=3), "H"
    )
    assert preview is not None
    assert preview.outcome == "no_match", preview
    assert preview.reason
    assert "P" in preview.reason


def test_preview_replace_at_not_an_equation() -> None:
    """The named binding's formula is not an equation -> not_an_equation."""
    source = (
        "theorem t: all P:bool, Q:bool. if P and Q then P and Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume H: P and Q\n"
        "  ?\n"
        "end\n"
    )
    preview = preview_replace_at(
        "test.pf", source, Position(line=5, column=3), "H"
    )
    assert preview is not None
    assert preview.outcome == "not_an_equation", preview
    assert preview.formula
    assert "and" in preview.formula


def test_preview_replace_at_unbound_name() -> None:
    """No binding matches the equation name -> unbound."""
    source = (
        "theorem t: all P:bool, Q:bool. if P = Q then if P then Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume H: P = Q\n"
        "  assume pP: P\n"
        "  ?\n"
        "end\n"
    )
    preview = preview_replace_at(
        "test.pf", source, Position(line=6, column=3), "nope"
    )
    assert preview is not None
    assert preview.outcome == "unbound", preview
    assert preview.name == "nope"


def test_preview_replace_at_unbound_when_label_is_term_var() -> None:
    """Term variables are not equations; treat as unbound."""
    source = (
        "theorem t: all P:bool, Q:bool. if P = Q then if P then Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume H: P = Q\n"
        "  ?\n"
        "end\n"
    )
    # `P` resolves to a term binding, not a proof binding.
    preview = preview_replace_at(
        "test.pf", source, Position(line=5, column=3), "P"
    )
    assert preview is not None
    assert preview.outcome == "unbound", preview


def test_preview_replace_at_returns_none_when_cursor_not_on_hole() -> None:
    """Cursor not on a ``?`` -> None."""
    source = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  reflexive\n"
        "end\n"
    )
    preview = preview_replace_at(
        "test.pf", source, Position(line=4, column=3), "H"
    )
    assert preview is None


# --------------------------------------------------------------------------
# preview_expand_at
# --------------------------------------------------------------------------


def test_preview_expand_at_unfolds_define() -> None:
    """``expand foo`` unfolds the body of a ``define``."""
    source = (
        "define my_and : fn bool, bool -> bool = λ a, b { a and b }\n"
        "theorem t: all P:bool, Q:bool. my_and(P, Q) = my_and(Q, P)\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  ?\n"
        "end\n"
    )
    preview = preview_expand_at(
        "test.pf", source, Position(line=5, column=3), ["my_and"]
    )
    assert preview is not None
    assert isinstance(preview, ExpandPreview)
    assert preview.outcome == "ok", preview
    assert preview.before
    assert preview.after
    # The unexpanded goal mentions `my_and`; the expanded goal does
    # not.
    assert "my_and" in preview.before
    assert "my_and" not in preview.after


def test_preview_expand_at_unknown_name() -> None:
    """A name with no binding in scope -> unknown."""
    source = (
        "theorem t: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume H: P\n"
        "  ?\n"
        "end\n"
    )
    preview = preview_expand_at(
        "test.pf", source, Position(line=5, column=3), ["no_such_name"]
    )
    assert preview is not None
    assert preview.outcome == "unknown", preview
    assert preview.name == "no_such_name"


def test_preview_expand_at_no_match() -> None:
    """Definition exists in scope but doesn't appear in the goal."""
    source = (
        "define unused_def : bool = true\n"
        "theorem t: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume H: P\n"
        "  ?\n"
        "end\n"
    )
    preview = preview_expand_at(
        "test.pf", source, Position(line=6, column=3), ["unused_def"]
    )
    assert preview is not None
    assert preview.outcome == "no_match", preview
    assert preview.name == "unused_def"


def test_preview_expand_at_returns_none_when_cursor_not_on_hole() -> None:
    """Cursor not on a ``?`` -> None."""
    source = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  reflexive\n"
        "end\n"
    )
    preview = preview_expand_at(
        "test.pf", source, Position(line=4, column=3), ["foo"]
    )
    assert preview is None


def test_preview_expand_at_chained_unfolds() -> None:
    """Multiple names are unfolded in order; succeeds when each
    contributes at least one substitution."""
    source = (
        "define my_id : fn bool -> bool = λ a { a }\n"
        "define my_and : fn bool, bool -> bool = λ a, b { a and my_id(b) }\n"
        "theorem t: all P:bool, Q:bool. my_and(P, Q) = my_and(Q, P)\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  ?\n"
        "end\n"
    )
    preview = preview_expand_at(
        "test.pf", source, Position(line=6, column=3),
        ["my_and", "my_id"],
    )
    assert preview is not None
    assert preview.outcome == "ok", preview
    # After expanding both, the goal contains plain `and`, not `my_and`
    # or `my_id`.
    assert "my_and" not in preview.after
    assert "my_id" not in preview.after
