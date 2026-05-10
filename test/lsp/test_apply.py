"""Acceptance tests for ``lsp.query.apply_at`` (issue #402).

UX shape: cursor on a ``?`` plus the name of an in-scope theorem
or hypothesis, plus an optional ordered list of explicit term
arguments instantiating outer ``all``-quantifiers (matching the
``theorem[arg, arg, ...]`` syntax).

Coverage:

(a) ``H: if P then C``, goal C ........... ok with [P]
(b) ``H: if P and Q then C``, goal C ..... ok with [P, Q] (split)
(c) ``T: all x. if P(x) then C(x)``, goal C(v) — no args, infer x ............... ok with [P(v)]
(d) ``T: all x. if P(x) then C(x)``, args [v] (explicit) ............... ok with [P(v)]
(e) Conclusion does not match goal ....... unifies_against
(f) Theorem name not in scope ............ unbound
(g) Theorem isn't an implication ......... arity_mismatch
(h) Too many ``[args]`` for outer alls ... arity_mismatch w/ expected,got
(i) Cursor not on ``?`` .................. None

All fixtures stay inside ``bool``-only territory so the tests run
without the standard library prelude.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from lsp.query import (  # noqa: E402
    Position,
    apply_at,
)


def test_apply_at_local_ifthen_hypothesis() -> None:
    """``H: if P then Q`` against goal ``Q`` -> ``ok`` with premise
    ``[P]``."""
    source = (
        "theorem t: all P:bool, Q:bool. if (if P then Q) and P then Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume H: (if P then Q) and P\n"
        "  have Hpq: if P then Q by conjunct 0 of H\n"
        "  have Hp: P by conjunct 1 of H\n"
        "  ?\n"
        "end\n"
    )
    result = apply_at(
        "test.pf", source, Position(line=7, column=3), "Hpq"
    )
    assert result == {
        "outcome": "ok",
        "conclusion": "Q",
        "remaining_premises": ["P"],
    }


def test_apply_at_conjunctive_premise_splits_on_and() -> None:
    """A premise of the shape ``P and Q`` is split into two entries
    so it maps to what the user would write after ``to``."""
    source = (
        "theorem multi: all P:bool, Q:bool. if P and Q then Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume H: P and Q\n"
        "  conjunct 1 of H\n"
        "end\n"
        "\n"
        "theorem t: all R:bool, S:bool. if R then if S then S\n"
        "proof\n"
        "  arbitrary R:bool, S:bool\n"
        "  assume HR: R\n"
        "  assume HS: S\n"
        "  ?\n"
        "end\n"
    )
    result = apply_at(
        "test.pf", source, Position(line=13, column=3),
        "multi", args=["R", "S"],
    )
    assert result == {
        "outcome": "ok",
        "conclusion": "S",
        "remaining_premises": ["R", "S"],
    }


def test_apply_at_quantified_no_args_infers_from_goal() -> None:
    """``identity: all P. if P then P`` against goal ``Q`` infers
    ``P := Q`` from unifying the conclusion with the goal."""
    source = (
        "theorem identity: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume H: P\n"
        "  H\n"
        "end\n"
        "\n"
        "theorem t: all Q:bool. if Q then Q\n"
        "proof\n"
        "  arbitrary Q:bool\n"
        "  assume H: Q\n"
        "  ?\n"
        "end\n"
    )
    result = apply_at(
        "test.pf", source, Position(line=12, column=3), "identity"
    )
    assert result == {
        "outcome": "ok",
        "conclusion": "Q",
        "remaining_premises": ["Q"],
    }


def test_apply_at_quantified_with_explicit_args() -> None:
    """Explicit ``[Q]`` instantiates the outer ``all P`` directly."""
    source = (
        "theorem identity: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume H: P\n"
        "  H\n"
        "end\n"
        "\n"
        "theorem t: all Q:bool. if Q then Q\n"
        "proof\n"
        "  arbitrary Q:bool\n"
        "  assume H: Q\n"
        "  ?\n"
        "end\n"
    )
    result = apply_at(
        "test.pf", source, Position(line=12, column=3),
        "identity", args=["Q"],
    )
    assert result == {
        "outcome": "ok",
        "conclusion": "Q",
        "remaining_premises": ["Q"],
    }


def test_apply_at_conclusion_does_not_match_goal() -> None:
    """``identity[Q]`` against goal ``R`` -> conclusion ``Q``
    doesn't match ``R``."""
    source = (
        "theorem identity: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume H: P\n"
        "  H\n"
        "end\n"
        "\n"
        "theorem t: all Q:bool, R:bool. if Q then R\n"
        "proof\n"
        "  arbitrary Q:bool, R:bool\n"
        "  assume H: Q\n"
        "  ?\n"
        "end\n"
    )
    result = apply_at(
        "test.pf", source, Position(line=12, column=3),
        "identity", args=["Q"],
    )
    assert result is not None
    assert result["outcome"] == "unifies_against"
    assert result["goal"] == "R"
    assert "Q" in result["reason"] and "R" in result["reason"]


def test_apply_at_unbound_theorem() -> None:
    source = (
        "theorem t: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume H: P\n"
        "  ?\n"
        "end\n"
    )
    result = apply_at(
        "test.pf", source, Position(line=5, column=3), "no_such_thing"
    )
    assert result == {
        "outcome": "unbound",
        "theorem": "no_such_thing",
    }


def test_apply_at_not_an_implication() -> None:
    """``H: P`` is a bare proposition, not an implication."""
    source = (
        "theorem t: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume H: P\n"
        "  ?\n"
        "end\n"
    )
    result = apply_at(
        "test.pf", source, Position(line=5, column=3), "H"
    )
    assert result is not None
    assert result["outcome"] == "arity_mismatch"
    assert "if-then" in result["reason"]


def test_apply_at_too_many_args() -> None:
    """``identity`` has one outer ``all``; passing two args is over."""
    source = (
        "theorem identity: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume H: P\n"
        "  H\n"
        "end\n"
        "\n"
        "theorem t: all Q:bool. if Q then Q\n"
        "proof\n"
        "  arbitrary Q:bool\n"
        "  assume H: Q\n"
        "  ?\n"
        "end\n"
    )
    result = apply_at(
        "test.pf", source, Position(line=12, column=3),
        "identity", args=["Q", "Q"],
    )
    assert result == {
        "outcome": "arity_mismatch",
        "expected": 1,
        "got": 2,
    }


def test_apply_at_arg_does_not_parse() -> None:
    """An arg referencing an undefined variable surfaces as
    ``unifies_against`` with a ``could not parse args`` reason."""
    source = (
        "theorem identity: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume H: P\n"
        "  H\n"
        "end\n"
        "\n"
        "theorem t: all Q:bool. if Q then Q\n"
        "proof\n"
        "  arbitrary Q:bool\n"
        "  assume H: Q\n"
        "  ?\n"
        "end\n"
    )
    result = apply_at(
        "test.pf", source, Position(line=12, column=3),
        "identity", args=["this_is_not_in_scope"],
    )
    assert result is not None
    assert result["outcome"] == "unifies_against"
    assert "could not parse args" in result["reason"]


def test_apply_at_returns_none_when_cursor_not_on_hole() -> None:
    """Cursor on the ``assume`` keyword, not on a ``?``."""
    source = (
        "theorem t: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume H: P\n"
        "  ?\n"
        "end\n"
    )
    result = apply_at(
        "test.pf", source, Position(line=4, column=3), "H"
    )
    assert result is None


def test_apply_at_no_args_and_local_premise_unifies() -> None:
    """Without ``args`` and a fully-instantiated implication, the
    premise comes through directly."""
    source = (
        "theorem t: all P:bool, Q:bool. if (if P then Q) and P then Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume H: (if P then Q) and P\n"
        "  have Hpq: if P then Q by conjunct 0 of H\n"
        "  ?\n"
        "end\n"
    )
    # Hpq has formula ``if P then Q`` with no Alls.
    result = apply_at(
        "test.pf", source, Position(line=6, column=3), "Hpq"
    )
    assert result == {
        "outcome": "ok",
        "conclusion": "Q",
        "remaining_premises": ["P"],
    }
