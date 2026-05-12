"""Acceptance tests for ``lsp.query.completions_at`` (Phase 6 / Step 31).

Coverage:

(a) keyword + constant + type entries are always present;
(b) own-file declarations appear with the right ``kind``;
(c) ``Union.alternatives`` and ``Predicate.rules`` are yielded as their
    own candidates (so e.g. ``suc`` shows up alongside ``Nat``);
(d) ``Import.ast`` walking surfaces transitive names from the prelude
    (e.g. ``import Nat`` brings in constructors / operators reached
    through Nat -> NatDefs);
(e) duplicates reachable via multiple imports collapse to one entry;
(f) a parse-failing file still returns the keyword/constant/type set
    (the client's filtering surface stays useful when something
    minor is broken).
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from lsp.query import (  # noqa: E402
    COMPLETION_CONSTANT_KEYWORDS,
    COMPLETION_KEYWORDS,
    COMPLETION_TYPE_KEYWORDS,
    CompletionCandidate,
    Position,
    completions_at,
)


def _labels_by_kind(cands):
    out: dict[str, set[str]] = {}
    for c in cands:
        out.setdefault(c.kind, set()).add(c.label)
    return out


# --------------------------------------------------------------------------
# Keyword / constant / type entries
# --------------------------------------------------------------------------


def test_completions_includes_all_keywords() -> None:
    """Every entry in :data:`COMPLETION_KEYWORDS` is returned with
    ``kind == 'keyword'``.  Locks the static list against accidental
    truncation."""
    source = "theorem t: true\nproof\n  .\nend\n"
    cands = completions_at("test.pf", source, Position(line=3, column=3))
    by_kind = _labels_by_kind(cands)
    for kw in COMPLETION_KEYWORDS:
        assert kw in by_kind.get("keyword", set()), f"missing keyword: {kw}"


def test_completions_includes_constants_and_types() -> None:
    """``true`` / ``false`` come back as ``constant``; ``bool`` /
    ``type`` come back as ``type`` -- not keywords or generic
    identifiers."""
    source = "theorem t: true\nproof\n  .\nend\n"
    cands = completions_at("test.pf", source, Position(line=3, column=3))
    by_kind = _labels_by_kind(cands)
    assert set(COMPLETION_CONSTANT_KEYWORDS) <= by_kind.get("constant", set())
    assert set(COMPLETION_TYPE_KEYWORDS) <= by_kind.get("type", set())


# --------------------------------------------------------------------------
# Own-file declarations
# --------------------------------------------------------------------------


def test_completions_includes_own_file_decls() -> None:
    """A file's own theorems / defines / unions / constructors all
    show up in the candidate list, each with the right ``kind``."""
    source = (
        "theorem my_thm: true\n"             # line 1
        "proof . end\n"                       # line 2
        "\n"                                  # line 3
        "define my_const: bool = true\n"      # line 4
        "\n"                                  # line 5
        "union MyUnion {\n"                   # line 6
        "  AltA\n"                            # line 7
        "  AltB\n"                            # line 8
        "}\n"                                 # line 9
    )
    cands = completions_at("test.pf", source, Position(line=10, column=1))
    by_kind = _labels_by_kind(cands)
    assert "my_thm" in by_kind.get("theorem", set())
    assert "my_const" in by_kind.get("define", set())
    assert "MyUnion" in by_kind.get("union", set())
    assert "AltA" in by_kind.get("constructor", set())
    assert "AltB" in by_kind.get("constructor", set())


def test_completions_emits_lemma_kind_for_private_theorem() -> None:
    """``lemma`` (private theorem) gets ``kind == 'lemma'``, not
    ``'theorem'``, so the client can render it differently if it
    wants (e.g. dim-coloured for private decls)."""
    source = (
        "lemma my_priv: true\n"
        "proof . end\n"
    )
    cands = completions_at("test.pf", source, Position(line=3, column=1))
    by_kind = _labels_by_kind(cands)
    assert "my_priv" in by_kind.get("lemma", set())
    assert "my_priv" not in by_kind.get("theorem", set())


def test_completions_includes_predicate_rules() -> None:
    """Introduction rules inside a ``predicate`` are surfaced as their
    own ``kind == 'rule'`` candidates -- matching the descent
    ``_find_declaration`` does for cross-file F12 on rule labels."""
    source = (
        "import UInt\n"
        "\n"
        "predicate even : fn UInt -> bool {\n"
        "  ev0   : even(0)\n"
        "  ev_ss : all n : UInt. if even(n) then even(n + 2)\n"
        "}\n"
    )
    cands = completions_at("test.pf", source, Position(line=7, column=1))
    by_kind = _labels_by_kind(cands)
    assert "even" in by_kind.get("predicate", set())
    assert "ev0" in by_kind.get("rule", set())
    assert "ev_ss" in by_kind.get("rule", set())


# --------------------------------------------------------------------------
# Transitive imports
# --------------------------------------------------------------------------


def test_completions_pulls_names_from_imports() -> None:
    """``import Nat`` should bring in names defined in the lib, not
    just ``Nat`` itself.  ``suc`` (a constructor in NatDefs.pf,
    reached transitively through Nat's barrel chain) and ``+`` (the
    recursive operator) must show up."""
    source = (
        "import Nat\n"
        "\n"
        "define x : Nat = suc(zero)\n"
    )
    cands = completions_at("test.pf", source, Position(line=4, column=1))
    by_kind = _labels_by_kind(cands)
    assert "suc" in by_kind.get("constructor", set())
    assert "zero" in by_kind.get("constructor", set())
    assert "+" in by_kind.get("function", set())
    assert "Nat" in by_kind.get("union", set())


def test_completions_deduplicates_across_imports() -> None:
    """A name reachable through multiple imports appears only once in
    the candidate list.  ``Nat`` is in the user file's transitive
    closure through several paths, so it's a good probe."""
    source = (
        "import Nat\n"
        "import Nat\n"        # explicit duplicate import; still one Nat
        "\n"
        "theorem t: true\n"
        "proof . end\n"
    )
    cands = completions_at("test.pf", source, Position(line=6, column=1))
    nat_count = sum(1 for c in cands if c.label == "Nat" and c.kind == "union")
    assert nat_count == 1, f"expected Nat to appear once, got {nat_count}"


# --------------------------------------------------------------------------
# Robustness
# --------------------------------------------------------------------------


def test_completions_returns_keywords_on_parse_failure() -> None:
    """An unparseable file still gets keywords / constants / types --
    the client's filter surface stays useful while the user is mid-
    edit.  Own-file decls are necessarily absent (no AST to walk)."""
    source = "this is not deduce syntax\n"
    cands = completions_at("test.pf", source, Position(line=1, column=1))
    by_kind = _labels_by_kind(cands)
    assert "theorem" in by_kind.get("keyword", set())
    assert "true" in by_kind.get("constant", set())
    assert "bool" in by_kind.get("type", set())


def test_completions_returns_tuple_not_list() -> None:
    """``completions_at`` returns a ``tuple`` -- callers that want
    hashable candidate sets (for caching) can rely on it."""
    source = "theorem t: true\nproof . end\n"
    cands = completions_at("test.pf", source, Position(line=3, column=1))
    assert isinstance(cands, tuple)


def test_completion_candidate_is_frozen() -> None:
    """``CompletionCandidate`` is a frozen dataclass -- adapters
    can rely on instances being hashable / immutable."""
    c = CompletionCandidate(label="x", kind="define", detail=None)
    with pytest.raises((AttributeError, Exception)):
        c.label = "y"  # type: ignore[misc]


# --------------------------------------------------------------------------
# Local bindings in scope at the cursor
# --------------------------------------------------------------------------


def test_completions_surfaces_proof_label_in_scope() -> None:
    """``assume H: P`` introduces ``H`` as a proof label; completion
    on a blank line below should pick it up with ``kind='label'``.
    Pre-fix the env-walker didn't run at all and ``H`` was invisible."""
    source = (
        "theorem t : all P:bool. if P then P\n"  # line 1
        "proof\n"                                 # line 2
        "  arbitrary P:bool\n"                    # line 3
        "  assume H: P\n"                         # line 4
        "  \n"                                    # line 5: cursor here
        "end\n"                                   # line 6
    )
    cands = completions_at("test.pf", source, Position(line=5, column=3))
    by_kind = _labels_by_kind(cands)
    assert "H" in by_kind.get("label", set())


def test_completions_surfaces_term_variable_in_scope() -> None:
    """``arbitrary P:bool`` introduces ``P`` as a term variable.
    Deduce's ``local`` flag on ``TermBinding`` is module-visibility
    (not lexical scope), so the env-walker has to rely on the AST
    walker's ``seen`` set to distinguish ``P`` from top-level decls.
    Locks the dedup logic against a regression that would either
    drop ``P`` or surface ``Nat`` / ``+`` / ... as ``variable``."""
    source = (
        "theorem t : all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume H: P\n"
        "  \n"
        "end\n"
    )
    cands = completions_at("test.pf", source, Position(line=5, column=3))
    by_kind = _labels_by_kind(cands)
    assert "P" in by_kind.get("variable", set())
    # And it should NOT also show up as a constructor / type / etc.
    other_kinds_with_P = [
        k for k, names in by_kind.items()
        if "P" in names and k not in ("variable",)
    ]
    assert other_kinds_with_P == [], (
        f"P showed up in unexpected kinds: {other_kinds_with_P}"
    )


def test_completions_strips_partial_identifier_at_cursor() -> None:
    """When the cursor sits in the middle of (or just after) a
    partial identifier the user is typing, the env-walker still
    finds in-scope bindings.  Pre-fix, inserting ``?`` mid-identifier
    would produce a parse error and the env extraction would bail."""
    source = (
        "theorem t : all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume H: P\n"
        "  Hel\n"                                  # line 5: partial id
        "end\n"
    )
    # cursor sits after the `l` of `Hel`
    cands = completions_at("test.pf", source, Position(line=5, column=6))
    by_kind = _labels_by_kind(cands)
    assert "H" in by_kind.get("label", set()), (
        "env walker should still pick up H even when the cursor sits "
        "inside a partial identifier the user is typing"
    )


# --------------------------------------------------------------------------
# Hole-aware priority
# --------------------------------------------------------------------------


def test_completions_boosts_matching_label_at_existing_hole() -> None:
    """When the cursor sits on a literal ``?`` and a local label's
    formula equals the goal there, that label gets ``priority=0`` --
    floats to the top of the picker via ``sortText``.  Non-matching
    candidates keep the default priority ``1``."""
    source = (
        "theorem t : all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  assume H: P\n"
        "  ?\n"                                    # line 5: cursor on ?
        "end\n"
    )
    cands = completions_at("test.pf", source, Position(line=5, column=3))
    h = next((c for c in cands if c.label == "H" and c.kind == "label"), None)
    assert h is not None, "H should be in the candidate set"
    assert h.priority == 0, (
        "H's formula (P) matches the goal at the hole; expected "
        "priority=0 for the sortText boost"
    )
    # Sample a non-matching candidate (a keyword) and confirm it's at
    # the default priority.
    th = next((c for c in cands if c.label == "theorem"), None)
    assert th is not None and th.priority == 1


def test_completions_no_boost_when_no_match() -> None:
    """When the cursor sits on a ``?`` but no in-scope local label's
    formula equals/implies the goal, no candidate gets priority 0."""
    source = (
        "theorem t : all P:bool, Q:bool. if Q then if P then Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume HQ: Q\n"
        "  assume HP: P\n"
        "  ?\n"                                    # line 6: goal Q
        "end\n"
    )
    cands = completions_at("test.pf", source, Position(line=6, column=3))
    # HQ matches the goal; HP doesn't.
    hq = next((c for c in cands if c.label == "HQ"), None)
    hp = next((c for c in cands if c.label == "HP"), None)
    assert hq is not None and hq.priority == 0
    assert hp is not None and hp.priority == 1


# --------------------------------------------------------------------------
# Robustness of the env-walker
# --------------------------------------------------------------------------


def test_completions_works_when_env_extraction_fails() -> None:
    """Severely-broken file: even though env extraction can't recover
    a useful env, the keyword / constant / type / AST-derived top-
    level set should still come back.  This locks the contract that
    env failures degrade gracefully instead of erasing all
    completion."""
    source = "garbage garbage garbage\n"
    cands = completions_at("test.pf", source, Position(line=1, column=1))
    by_kind = _labels_by_kind(cands)
    assert "theorem" in by_kind.get("keyword", set())
    assert "true" in by_kind.get("constant", set())
