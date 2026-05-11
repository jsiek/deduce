"""Acceptance tests for ``lsp.query.preview_conclude_at`` (issue #420).

UX shape: cursor on a ``?`` plus an explicit ``label`` argument
naming the in-scope local hypothesis we want to check would
discharge the goal. Differs from ``fill_from_given_at`` /
``matching_givens_at`` by reducing both sides with ``.reduce(env)``
before the implication check -- so it matches what the proof checker
actually accepts in the catch-all branch of ``check_proof_of``.

Coverage:

(a) exact match (no auto needed)         -> ``discharges``
(b) implies-only match (Or-intro)        -> ``discharges``
(c) match via auto-rule normalization    -> ``discharges``
(d) unrelated label                      -> ``no_match``
(e) label not bound                      -> ``unbound``
(f) label refers to a theorem            -> ``not_local``
(g) cursor not on a ``?``                -> ``None``
(h) file has no incomplete proof         -> ``None``
"""

from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from lsp.query import (  # noqa: E402
    Position,
    preview_conclude_at,
)


def test_preview_conclude_at_exact_match() -> None:
    """``H: P or Q`` exactly matches goal ``P or Q``."""
    source = (
        "theorem t: all P:bool, Q:bool. if P or Q then P or Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume H: P or Q\n"
        "  ?\n"
        "end\n"
    )
    result = preview_conclude_at(
        "test.pf", source, Position(line=5, column=3), "H"
    )
    assert result is not None
    assert result["outcome"] == "discharges"
    # Renderer parenthesises top-level ``or`` expressions.
    assert result["given_normalized"] == "(P or Q)"
    assert result["goal_normalized"] == "(P or Q)"


def test_preview_conclude_at_implies_only_match() -> None:
    """``H: P`` strictly implies goal ``P or Q`` via Or introduction.
    ``check_implies`` covers this; no auto-rule needed."""
    source = (
        "theorem t: all P:bool, Q:bool. if P then P or Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume H: P\n"
        "  ?\n"
        "end\n"
    )
    result = preview_conclude_at(
        "test.pf", source, Position(line=5, column=3), "H"
    )
    assert result is not None
    assert result["outcome"] == "discharges"


def test_preview_conclude_at_match_modulo_auto_rule() -> None:
    """The motivating case from PR #413: ``H``'s formula reduces to
    the goal under an active ``auto`` rewrite, so the goal and H
    differ pre-reduce but equal post-reduce. ``matching_givens_at``
    would report no match here; ``preview_conclude_at`` reports
    ``discharges``, matching what ``conclude ... by H`` accepts.

    Setup uses ``fadd_zero_right: all x. fadd(x, fzero) = x`` as the
    auto rule -- a non-trivial theorem (needs induction on x), unlike
    a function-definition rewrite which ``reduce`` would apply even
    without the ``auto`` annotation. The goal ``z = fsucc(fzero)``
    does not collapse to ``true`` even after the auto rule fires,
    so we can assert on the post-reduce text without ambiguity."""
    source = (
        "union Foo {\n"                                                # 1
        "  fzero\n"                                                    # 2
        "  fsucc(Foo)\n"                                               # 3
        "}\n"                                                          # 4
        "recursive fadd(Foo, Foo) -> Foo {\n"                          # 5
        "  fadd(fzero, y) = y\n"                                       # 6
        "  fadd(fsucc(x), y) = fsucc(fadd(x, y))\n"                    # 7
        "}\n"                                                          # 8
        "postulate fadd_zero_right:\n"                                 # 9
        "  all x:Foo. fadd(x, fzero) = x\n"                            # 10
        "auto fadd_zero_right\n"                                       # 11
        "\n"                                                           # 12
        "theorem t: all z:Foo.\n"                                      # 13
        "  if fadd(z, fzero) = fsucc(fzero) then z = fsucc(fzero)\n"   # 14
        "proof\n"                                                      # 15
        "  arbitrary z:Foo\n"                                          # 16
        "  assume H: fadd(z, fzero) = fsucc(fzero)\n"                  # 17
        "  ?\n"                                                        # 18
        "end\n"                                                        # 19
    )
    result = preview_conclude_at(
        "test.pf", source, Position(line=18, column=3), "H"
    )
    assert result is not None, "preview_conclude_at returned None"
    assert result["outcome"] == "discharges", result
    # Both reduced sides equal ``z = fsucc(fzero)`` (the auto rule
    # rewrites ``fadd(z, fzero) -> z`` on the LHS of the equation).
    assert result["goal_normalized"] == "z = fsucc(fzero)"
    assert result["given_normalized"] == "z = fsucc(fzero)"


def test_preview_conclude_at_no_match_for_unrelated() -> None:
    """Goal ``Q`` with an unrelated given ``H: P`` -- doesn't discharge
    even modulo auto."""
    source = (
        "theorem t: all P:bool, Q:bool. if Q then if P then Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume HQ: Q\n"
        "  assume H: P\n"
        "  ?\n"
        "end\n"
    )
    result = preview_conclude_at(
        "test.pf", source, Position(line=6, column=3), "H"
    )
    assert result is not None
    assert result["outcome"] == "no_match"
    assert result["goal_normalized"] == "Q"
    assert result["given_normalized"] == "P"
    assert "does not imply" in result["reason"]


def test_preview_conclude_at_unbound_label() -> None:
    """Label not bound at the hole."""
    source = (
        "theorem t: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume H: P\n"
        "  ?\n"
        "end\n"
    )
    result = preview_conclude_at(
        "test.pf", source, Position(line=5, column=3), "nope"
    )
    assert result == {"outcome": "unbound", "label": "nope"}


def test_preview_conclude_at_label_is_term_variable() -> None:
    """Label refers to a term variable (``P:bool``), not a proof
    binding -- reported as ``unbound`` (no proof binding by that
    name)."""
    source = (
        "theorem t: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume pP: P\n"
        "  ?\n"
        "end\n"
    )
    result = preview_conclude_at(
        "test.pf", source, Position(line=5, column=3), "P"
    )
    assert result == {"outcome": "unbound", "label": "P"}


def test_preview_conclude_at_label_is_theorem_ref() -> None:
    """A theorem in scope is a non-local proof binding. Theorem
    references are invoked by name directly in proof position, not
    via ``conclude ... by``, so this preview reports ``not_local``."""
    source = (
        "theorem h: true\n"
        "proof . end\n"
        "theorem t: true\n"
        "proof\n"
        "  ?\n"
        "end\n"
    )
    result = preview_conclude_at(
        "test.pf", source, Position(line=5, column=3), "h"
    )
    assert result == {"outcome": "not_local", "label": "h"}


def test_preview_conclude_at_returns_none_off_hole() -> None:
    """Cursor not on a ``?`` -> ``None`` (this is a hole-driven tool)."""
    source = (
        "theorem t: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume H: P\n"
        "  ?\n"
        "end\n"
    )
    # Cursor on `assume` keyword.
    result = preview_conclude_at(
        "test.pf", source, Position(line=4, column=3), "H"
    )
    assert result is None


def test_preview_conclude_at_returns_none_when_complete() -> None:
    """File validates without ever raising IncompleteProof -- nothing
    to preview against."""
    source = (
        "theorem t: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume H: P\n"
        "  H\n"
        "end\n"
    )
    result = preview_conclude_at(
        "test.pf", source, Position(line=5, column=3), "H"
    )
    assert result is None
