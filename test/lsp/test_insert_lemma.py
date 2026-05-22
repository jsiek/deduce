"""Acceptance tests for ``lsp.query.insert_lemma_at`` (issue #690).

Companion to ``test_available_lemmas.py``. ``available_lemmas_at``
gives the editor a ranked picker of lemma candidates with a unify
tier on each entry; ``insert_lemma_at`` translates a chosen name
into a tier-aware ``WorkspaceEdit`` that splices the right Deduce
tactic shape into the buffer.

Coverage:

(a) ``full`` tier with 0 premises -> ``conclude <goal> by <name>``;
(b) ``full`` tier with 1 premise discharged by a given ->
    ``conclude <goal> by apply <name>[t1,...] to <label>``;
(c) ``full`` tier with N premises discharged ->
    ``conclude <goal> by apply <name>[t1,...] to <l1>, ..., <lN>``;
(d) ``premises_remain`` tier -> ``apply <name>[t1,...] to ?``;
(e) ``rewrite_subterm`` tier -> ``replace <name>`` (bare-var-pattern
    skips instantiation; structured patterns include it);
(f) no unify match (off-hole or browse) -> bare ``<name>`` at point;
(g) name not in scope -> ``None``;
(h) explicit forall-instantiation suffix when the unifier resolves
    every all-bound variable (issue #734) -- the splice writes
    ``name[t1, ..., tN]`` so ``apply ... to ?`` elaborates with a
    usable inner subgoal.

Fixtures stay inside ``bool``-only territory so tests run with no
prelude.
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
    insert_lemma_at,
)


# ---------------------------------------------------------------------------
# `full` tier: conclude ... by ...
# ---------------------------------------------------------------------------


def test_full_tier_no_premises_emits_conclude_by_name() -> None:
    """Zero-premise theorem unifies the goal directly -> the template
    is ``conclude <goal> by <name>`` (no ``apply``)."""
    source = (
        "theorem helper: true and true\n"
        "proof\n"
        "  .\n"
        "end\n"
        "\n"
        "theorem with_hole: true and true\n"
        "proof\n"
        "  ?\n"
        "end\n"
    )
    edit = insert_lemma_at(
        "lemmas.pf", source, Position(line=8, column=3), "helper"
    )
    assert edit is not None
    assert isinstance(edit, WorkspaceEdit)
    # Replaces the `?` 1-char span at line 8, col 3.
    assert edit.range == Range(
        start=Position(line=8, column=3),
        end=Position(line=8, column=4),
    )
    # Goal text is rendered with surrounding parens for ``and`` because
    # that's the canonical ``Goal`` formula spelling the goal-extractor
    # returns; the template embeds it verbatim.
    assert edit.new_text == "conclude (true and true) by helper"


def test_full_tier_one_premise_discharged_emits_apply_to_label() -> None:
    """Single-premise theorem whose only premise is discharged by a
    local given -> ``conclude <goal> by apply <name>[t] to <label>``.

    The unifier resolved ``P := P`` from the conclusion match, so the
    splice carries the explicit instantiation (issue #734)."""
    source = (
        "theorem dup: all P:bool. if P then P and P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume pP: P\n"
        "  pP, pP\n"
        "end\n"
        "\n"
        "theorem with_hole: all P:bool. if P then P and P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume h: P\n"
        "  ?\n"
        "end\n"
    )
    edit = insert_lemma_at(
        "lemmas.pf", source, Position(line=12, column=3), "dup"
    )
    assert edit is not None
    assert edit.new_text == "conclude (P and P) by apply dup[P] to h"


def test_full_tier_two_premises_discharged_emits_comma_labels() -> None:
    """Two-premise theorem whose premises are all discharged -> the
    label list is comma-separated in the ``apply ... to`` argument."""
    source = (
        "theorem and_intro: all P:bool, Q:bool. if P then if Q then P and Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  suppose pP: P\n"
        "  suppose qQ: Q\n"
        "  pP, qQ\n"
        "end\n"
        "\n"
        "theorem with_hole: all P:bool, Q:bool. if P then if Q then P and Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  suppose pP: P\n"
        "  suppose qQ: Q\n"
        "  ?\n"
        "end\n"
    )
    edit = insert_lemma_at(
        "lemmas.pf", source, Position(line=14, column=3), "and_intro"
    )
    assert edit is not None
    assert edit.new_text == (
        "conclude (P and Q) by apply and_intro[P, Q] to pP, qQ"
    )


# ---------------------------------------------------------------------------
# `premises_remain` tier: apply ... to ?
# ---------------------------------------------------------------------------


def test_premises_remain_tier_emits_apply_with_hole() -> None:
    """Conclusion unifies but no local given matches the premise ->
    template is ``apply <name>[t1, ..., tN] to ?``: explicit
    instantiations (issue #734) so the inner ``?`` displays the
    instantiated premise as its subgoal; one fresh hole for the
    user to fill."""
    source = (
        "theorem and_intro: all P:bool, Q:bool. if P then if Q then P and Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  suppose pP: P\n"
        "  suppose qQ: Q\n"
        "  pP, qQ\n"
        "end\n"
        "\n"
        "theorem with_hole: all P:bool, Q:bool. P and Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  ?\n"
        "end\n"
    )
    edit = insert_lemma_at(
        "lemmas.pf", source, Position(line=12, column=3), "and_intro"
    )
    assert edit is not None
    assert edit.new_text == "apply and_intro[P, Q] to ?"
    # Replaces the `?` 1-char span at line 12, col 3.
    assert edit.range == Range(
        start=Position(line=12, column=3),
        end=Position(line=12, column=4),
    )


# ---------------------------------------------------------------------------
# `rewrite_subterm` tier: replace ...
# ---------------------------------------------------------------------------


def test_rewrite_subterm_tier_emits_replace() -> None:
    """Equation lemma whose LHS unifies with a goal subterm ->
    template is ``replace <name>``.

    The lemma's LHS is a bare forall-var, so the auto-inferred
    "match" binds it to the whole goal -- a meaningless splice
    instantiation. The rewrite_subterm branch skips the
    ``[t1, ..., tN]`` suffix in that case so the rewrite engine
    can pattern-match across the goal as before (issue #734)."""
    # ``P = not (not P)`` -- the LHS ``P`` matches the subterm ``P``
    # in the goal ``P and Q``.
    source = (
        "theorem not_not: all P:bool. P = not (not P)\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  switch P {\n"
        "    case true { . }\n"
        "    case false { . }\n"
        "  }\n"
        "end\n"
        "\n"
        "theorem with_hole: all P:bool, Q:bool. if P and Q then not (not P) and Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  suppose h: P and Q\n"
        "  ?\n"
        "end\n"
    )
    edit = insert_lemma_at(
        "lemmas.pf", source, Position(line=14, column=3), "not_not"
    )
    assert edit is not None
    # The lemma's conclusion is an equation, and its LHS (``P``) matches
    # a subterm of the goal -> rewrite_subterm tier -> ``replace`` shape.
    assert edit.new_text == "replace not_not"


# ---------------------------------------------------------------------------
# No tier match: bare name
# ---------------------------------------------------------------------------


def test_off_hole_emits_bare_name_at_point() -> None:
    """Cursor off any ``?`` token (e.g. browse mode after picking a
    lemma to reference): inserts the bare ``<name>`` at the cursor as
    a zero-width edit."""
    source = (
        "theorem alpha: true\nproof\n  .\nend\n"
    )
    edit = insert_lemma_at(
        "lemmas.pf", source, Position(line=1, column=1), "alpha"
    )
    assert edit is not None
    assert edit.new_text == "alpha"
    # Zero-width edit at the cursor.
    assert edit.range == Range(
        start=Position(line=1, column=1),
        end=Position(line=1, column=1),
    )


def test_unrelated_lemma_at_hole_emits_bare_name() -> None:
    """Cursor on ``?`` but the named lemma's conclusion doesn't unify
    with the goal: tier is ``None`` so we just splice the bare name."""
    source = (
        "theorem alpha: true\nproof\n  .\nend\n"
        "\n"
        "theorem with_hole: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  ?\n"
        "end\n"
    )
    edit = insert_lemma_at(
        "lemmas.pf", source, Position(line=8, column=3), "alpha"
    )
    assert edit is not None
    # Replaces the `?` with the bare name; no `conclude` / `apply` /
    # `replace` wrapping because no tier matched.
    assert edit.new_text == "alpha"


# ---------------------------------------------------------------------------
# Failure mode: name not in scope
# ---------------------------------------------------------------------------


def test_unknown_name_returns_none() -> None:
    """Name not in scope as any theorem/lemma/postulate -> ``None``."""
    source = (
        "theorem t: true\n"
        "proof\n"
        "  ?\n"
        "end\n"
    )
    edit = insert_lemma_at(
        "lemmas.pf", source, Position(line=3, column=3), "no_such_lemma"
    )
    assert edit is None


# ---------------------------------------------------------------------------
# Issue #734: forall instantiations on splice
# ---------------------------------------------------------------------------
#
# The unifier may resolve substitutions for the lemma's outer
# all-bound variables when matching its conclusion against the goal.
# Before the fix, those substitutions were dropped on the floor and
# the splice emitted bare ``apply name to ?`` -- the inner ``?``
# could not elaborate because deduce had nothing to instantiate the
# implication's premise with, so editor "goal at point" lookups
# returned empty. The fix threads the substitution through into a
# ``name[t1, ..., tN]`` suffix on every shape (full / premises_remain
# / rewrite_subterm-with-structured-LHS) so the inner subgoal
# displays.


def test_premises_remain_emits_explicit_instantiation_when_resolved() -> None:
    """Issue #734 reproducer: every all-bound variable resolved by
    the conclusion match ends up in the ``[t1, ..., tN]`` splice
    suffix so the inner ``?`` elaborates with a usable subgoal.

    Postulate ``flip: all P:bool, Q:bool. if P and Q then Q and P``:
    matching the conclusion ``Q and P`` against the goal ``Q and P``
    binds ``P := P, Q := Q``. With both forall-vars resolved, the
    splice must read ``apply flip[P, Q] to ?`` -- without the
    instantiation, the bare ``apply flip to ?`` form leaves
    deduce unable to display a subgoal for the inner hole."""
    source = (
        "postulate flip: all P:bool, Q:bool. if P and Q then Q and P\n"
        "\n"
        "theorem with_hole: all P:bool, Q:bool. Q and P\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  ?\n"
        "end\n"
    )
    edit = insert_lemma_at(
        "lemmas.pf", source, Position(line=6, column=3), "flip"
    )
    assert edit is not None
    assert edit.new_text == "apply flip[P, Q] to ?"


def test_full_tier_emits_explicit_instantiation_when_resolved() -> None:
    """``full`` tier with one premise discharged: the apply splice
    carries the explicit instantiation alongside the given label.

    The fix applies uniformly across template shapes -- ``full``
    (this case), ``full`` with no premises, ``premises_remain``,
    and ``rewrite_subterm`` with a structured LHS -- so the
    instantiation suffix never gets dropped when the unifier knew
    it (issue #734).

    Postulate ``id_imp: all P:bool. if P then P``: matching the
    conclusion ``P`` against the goal ``P`` binds ``P := P``; the
    single premise ``P`` is discharged by the local given ``h: P``,
    so the tier is ``full``. Splice: ``conclude P by apply
    id_imp[P] to h``."""
    source = (
        "postulate id_imp: all P:bool. if P then P\n"
        "\n"
        "theorem with_hole: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume h: P\n"
        "  ?\n"
        "end\n"
    )
    edit = insert_lemma_at(
        "lemmas.pf", source, Position(line=7, column=3), "id_imp"
    )
    assert edit is not None
    assert edit.new_text == "conclude P by apply id_imp[P] to h"


def test_no_instantiation_suffix_when_lemma_has_no_forall() -> None:
    """A theorem without an outer ``all`` quantifier has no vars to
    instantiate -- ``instantiations`` is empty, so the splice omits
    the ``[]`` suffix entirely. Guards against an off-by-one that
    would emit ``apply name[] to ?`` (empty brackets, parse error
    in some grammars) when there are no forall-bound variables."""
    source = (
        "postulate refl_t: true = true\n"
        "\n"
        "theorem with_hole: true = true\n"
        "proof\n"
        "  ?\n"
        "end\n"
    )
    edit = insert_lemma_at(
        "lemmas.pf", source, Position(line=5, column=3), "refl_t"
    )
    assert edit is not None
    # No forall to peel -> instantiations are empty -> bare name
    # in the ``conclude ... by name`` template.
    assert edit.new_text == "conclude true = true by refl_t"
