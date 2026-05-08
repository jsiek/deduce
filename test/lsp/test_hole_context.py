"""Acceptance tests for ``lsp.query.hole_context_at`` (Phase 5 / Step 1).

The function is the LSP-side context provider for the Claude hole-fill
sidecar (see docs/hole-fill-plan.md). It returns the goal, givens,
lemmas-in-scope, and a stable fingerprint for the ``?`` token at the
cursor.

Each fixture stays inside ``bool``-only territory so the tests run
without the standard library prelude. The one exception is the
"prelude lemmas appear" case, which uses the small
``test/test-imports/HoleFillPrelude.pf`` module the conftest already
makes available via ``add_import_directory``.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from lsp.query import (  # noqa: E402
    Given,
    HoleContext,
    LemmaInfo,
    Position,
    Range,
    SymbolKind,
    hole_context_at,
)


# ---------------------------------------------------------------------------
# Goal / givens / range
# ---------------------------------------------------------------------------


SIMPLE_HOLE = (
    "theorem t: all P:bool. P = P\n"
    "proof\n"
    "  arbitrary P:bool\n"
    "  ?\n"
    "end\n"
)


def test_returns_context_with_goal_and_givens() -> None:
    """Cursor on a `?`: HoleContext carries the goal text, the givens
    that were in scope, and a 1-char range covering the `?`."""
    source = (
        "theorem t: all P:bool, Q:bool. if P then if Q then P\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  suppose pP: P\n"
        "  suppose qQ: Q\n"
        "  ?\n"
        "end\n"
    )
    ctx = hole_context_at("test.pf", source, Position(line=6, column=3))
    assert ctx is not None
    assert isinstance(ctx, HoleContext)
    assert ctx.goal == "P"
    assert ctx.givens == (
        Given(label="qQ", formula="Q"),
        Given(label="pP", formula="P"),
    )
    assert ctx.hole_range == Range(
        start=Position(line=6, column=3),
        end=Position(line=6, column=4),
    )


def test_no_hole_returns_none() -> None:
    """Cursor not on a `?`: hole_context_at refuses to synthesise one."""
    source = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  reflexive\n"
        "end\n"
    )
    # Line 4 column 3 sits on `reflexive`, not a `?`.
    assert hole_context_at("test.pf", source, Position(line=4, column=3)) is None


def test_picks_cursor_hole_not_first() -> None:
    """Two-hole file, cursor on the second `?`: the returned goal is
    the second hole's goal, not the first.

    Regression check that hole_context_at uses ``_target_hole`` --
    without it the proof checker raises at the first `?` it sees and
    every cursor would resolve to the first hole's goal.
    """
    source = (
        "theorem t: all P:bool, Q:bool. if P then if Q then P and Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  suppose pP: P\n"
        "  suppose qQ: Q\n"
        "  have h1: P by ?\n"
        "  have h2: Q by ?\n"
        "  h1, h2\n"
        "end\n"
    )
    # First `?` at line 6 col 17, second at line 7 col 17.
    first = hole_context_at("test.pf", source, Position(line=6, column=17))
    second = hole_context_at("test.pf", source, Position(line=7, column=17))
    assert first is not None and second is not None
    assert first.goal == "P"
    assert second.goal == "Q"
    second_labels = {g.label for g in second.givens}
    assert "h1" in second_labels, (
        f"expected h1 in scope at second hole, got {second.givens}"
    )


# ---------------------------------------------------------------------------
# Lemma list
# ---------------------------------------------------------------------------


USER_FILE_WITH_LEMMAS = (
    "theorem outer: all P:bool. P = P\n"
    "proof\n"
    "  arbitrary P:bool\n"
    "  reflexive\n"
    "end\n"
    "\n"
    "lemma helper: true\n"
    "proof\n"
    "  .\n"
    "end\n"
    "\n"
    "theorem with_hole: all P:bool. P = P\n"
    "proof\n"
    "  arbitrary P:bool\n"
    "  ?\n"
    "end\n"
)


def test_lemmas_excluded_when_disabled() -> None:
    """include_lemmas=False yields an empty tuple."""
    ctx = hole_context_at(
        "test.pf",
        USER_FILE_WITH_LEMMAS,
        Position(line=15, column=3),
        include_lemmas=False,
    )
    assert ctx is not None
    assert ctx.lemmas_in_scope == ()


def test_lemmas_include_user_theorems() -> None:
    """Top-level theorems and lemmas in the user's file appear in
    ``lemmas_in_scope`` with the right kind."""
    ctx = hole_context_at(
        "test.pf",
        USER_FILE_WITH_LEMMAS,
        Position(line=15, column=3),
    )
    assert ctx is not None
    by_name = {lemma.name: lemma for lemma in ctx.lemmas_in_scope}

    assert "outer" in by_name, (
        f"expected 'outer' in lemmas, got {[l.name for l in ctx.lemmas_in_scope]}"
    )
    assert by_name["outer"].kind == SymbolKind.THEOREM

    assert "helper" in by_name
    assert by_name["helper"].kind == SymbolKind.LEMMA

    # The signature is the one-line "name: formula" form.
    assert by_name["outer"].signature.startswith("outer:")


def test_lemmas_include_prelude_when_loaded() -> None:
    """Theorems from a module passed in ``prelude`` appear in the list.

    Uses the small ``HoleFillPrelude`` fixture (in test/test-imports)
    so the test doesn't pull in the full standard library.
    """
    source = (
        "theorem with_hole: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  ?\n"
        "end\n"
    )
    ctx = hole_context_at(
        "test.pf",
        source,
        Position(line=4, column=3),
        prelude=("HoleFillPrelude",),
    )
    assert ctx is not None
    names = {lemma.name for lemma in ctx.lemmas_in_scope}
    # Theorems and postulates from the prelude module are surfaced.
    assert "hf_refl_true" in names, (
        f"prelude theorem missing from lemmas; got {sorted(names)}"
    )
    assert "hf_intro_and" in names
    assert "hf_postulate" in names
    by_name = {lemma.name: lemma for lemma in ctx.lemmas_in_scope}
    assert by_name["hf_postulate"].kind == SymbolKind.POSTULATE


# ---------------------------------------------------------------------------
# Fingerprint
# ---------------------------------------------------------------------------


def test_fingerprint_stable_under_unrelated_whitespace_edits() -> None:
    """Two source files that differ only in whitespace far from the
    hole produce equal fingerprints. The fingerprint hashes the
    rendered goal/givens, not the source text."""
    base = (
        "theorem t: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  suppose pP: P\n"
        "  ?\n"
        "end\n"
    )
    # Add a trailing comment line (doesn't affect parse or check).
    edited = base + "\n// a trailing comment, doesn't affect anything\n"
    a = hole_context_at("test.pf", base, Position(line=5, column=3))
    b = hole_context_at("test.pf", edited, Position(line=5, column=3))
    assert a is not None and b is not None
    assert a.fingerprint == b.fingerprint


def test_fingerprint_changes_when_goal_changes() -> None:
    """Two holes whose goals differ produce distinct fingerprints."""
    p_eq_p = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  ?\n"
        "end\n"
    )
    q_eq_q = (
        "theorem t: all Q:bool. Q = Q\n"
        "proof\n"
        "  arbitrary Q:bool\n"
        "  ?\n"
        "end\n"
    )
    a = hole_context_at("test.pf", p_eq_p, Position(line=4, column=3))
    b = hole_context_at("test.pf", q_eq_q, Position(line=4, column=3))
    assert a is not None and b is not None
    assert a.goal == "P = P"
    assert b.goal == "Q = Q"
    assert a.fingerprint != b.fingerprint


# ---------------------------------------------------------------------------
# Sanity: types are right
# ---------------------------------------------------------------------------


def test_lemma_info_shape() -> None:
    """Returned lemma entries are LemmaInfo instances (not dicts/tuples)."""
    ctx = hole_context_at(
        "test.pf",
        USER_FILE_WITH_LEMMAS,
        Position(line=15, column=3),
    )
    assert ctx is not None
    assert len(ctx.lemmas_in_scope) >= 1
    for lemma in ctx.lemmas_in_scope:
        assert isinstance(lemma, LemmaInfo)
        assert isinstance(lemma.kind, SymbolKind)
        assert isinstance(lemma.signature, str)
