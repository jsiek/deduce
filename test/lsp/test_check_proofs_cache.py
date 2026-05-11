"""Acceptance tests for the per-statement ``check_proofs`` cache.

Phase 3 / Steps 13 and 14.  Plan acceptances:

- *Step 13:* ``edit one statement, recheck; instrumentation confirms
  untouched statements were cache hits``.
- *Step 14:* ``edit theorem T1; assert T2 (which uses T1) is
  invalidated and rechecked``.

The cache lives in ``proof_checker._stmt_cache`` and is keyed by
``(stmt_hash, deps_fingerprint, target, module_name)``.

- ``stmt_hash`` is a structural hash that skips ``location``
  (``Meta``) so adding/removing *other* statements doesn't perturb
  the hash of an unchanged one.  Per-statement scoping in
  ``uniquify_deduce`` (Step 14) keeps the structural hash stable
  even when an earlier statement's body changes size.
- ``deps_fingerprint`` folds in the structural hashes of just the
  prior statements *this* statement actually references (plus any
  global-barrier ``Import`` / ``Auto`` statements).  Editing an
  unrelated theorem leaves ``deps_fingerprint`` unchanged.
- ``target`` is the ``goal_at`` target-hole location (so a `?` that
  was previously treated as ``sorry`` doesn't reuse a stale
  verdict).
- ``module_name`` keeps two files in the same process from
  cross-contaminating each other.

What this file pins:

- a clean run populates the cache with all-misses,
- a re-run on the same content is all-hits,
- editing one statement leaves untouched prefix entries hit,
- editing a middle statement leaves later statements that don't
  reference it as hits (Step 14's deps-fingerprint kicking in),
- editing T1 invalidates T2 that uses it (Step 14 acceptance).

The earlier two loops (``process_declaration``, ``type_check_stmt``)
are deliberately *not* cached -- their AST output carries
``Meta`` locations that interact with the
``target_hole_location`` flag used by ``goal_at`` and friends, so
caching them across calls would surface as stale-location bugs.
``check_proofs`` is where the bulk of the time goes anyway.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

import proof_checker  # noqa: E402
from lsp.query import check  # noqa: E402


@pytest.fixture(autouse=True)
def _fresh_cache():
    """Each test starts with an empty cache and fresh stats."""
    proof_checker.reset_stmt_cache()
    yield
    proof_checker.reset_stmt_cache()


def _hits(loop_tag: str = "check_proofs") -> int:
    return proof_checker.get_cache_stats()["hits"].get(loop_tag, 0)


def _misses(loop_tag: str = "check_proofs") -> int:
    return proof_checker.get_cache_stats()["misses"].get(loop_tag, 0)


_THREE_THEOREMS = (
    "theorem t1: true\n"
    "proof\n"
    "  .\n"
    "end\n"
    "\n"
    "theorem t2: true = true\n"
    "proof\n"
    "  reflexive\n"
    "end\n"
    "\n"
    "theorem t3: all P:bool, Q:bool. if P then if Q then P\n"
    "proof\n"
    "  arbitrary P:bool, Q:bool\n"
    "  suppose pP: P\n"
    "  suppose qQ: Q\n"
    "  pP\n"
    "end\n"
)


def test_first_run_is_all_misses() -> None:
    """A clean cache + a fresh source means every statement is a
    miss the first time around."""
    diags = check("test.pf", _THREE_THEOREMS)
    assert diags == []
    assert _misses() == 3
    assert _hits() == 0


def test_second_run_on_same_content_is_all_hits() -> None:
    """Re-running ``check`` on the exact same content reuses the
    cache for every statement."""
    check("test.pf", _THREE_THEOREMS)
    proof_checker._cache_stats["hits"].clear()
    proof_checker._cache_stats["misses"].clear()
    diags = check("test.pf", _THREE_THEOREMS)
    assert diags == []
    assert _hits() == 3
    assert _misses() == 0


def test_editing_one_statement_keeps_others_cache_hits() -> None:
    """Plan acceptance: edit ONE statement, recheck.  The other
    two statements were not touched, so their cache entries hit;
    the modified statement misses."""
    # First run: populate cache for all three statements.
    check("test.pf", _THREE_THEOREMS)

    # Edit the *third* statement -- rewrite its proof body to use
    # an intermediate ``have``.  The first two theorems are
    # untouched.
    edited = _THREE_THEOREMS.replace(
        "  pP\n"
        "end\n",
        "  have h: P by pP\n"
        "  h\n"
        "end\n",
    )

    proof_checker._cache_stats["hits"].clear()
    proof_checker._cache_stats["misses"].clear()
    diags = check("test.pf", edited)
    assert diags == []
    # Two statements unchanged -> two hits.  One statement edited ->
    # one miss.
    assert _hits() == 2, (
        f"expected 2 hits (t1 and t2 unchanged), got {_hits()}; "
        f"misses={_misses()}"
    )
    assert _misses() == 1


def test_editing_a_middle_statement_leaves_unrelated_downstream_hits() -> None:
    """Step 14 acceptance, negative direction: editing a middle
    statement that nobody references leaves later, unrelated
    statements as cache hits.

    Under the old chain-hash invalidation, t3 would also miss --
    even though it doesn't use t2 -- because the running chain hash
    shifted.  Under Step 14's deps-fingerprint, t3 doesn't reference
    t2's name, so its dependency set is empty and its cache entry
    survives the edit."""
    check("test.pf", _THREE_THEOREMS)

    # Edit the *second* theorem.  Replace the proof body with an
    # intermediate ``have`` step -- AST changes structurally but
    # the proof still passes.  t1 (before t2) and t3 (after t2 but
    # not referencing it) should both stay cached.
    edited = _THREE_THEOREMS.replace(
        "theorem t2: true = true\n"
        "proof\n"
        "  reflexive\n"
        "end\n",
        "theorem t2: true = true\n"
        "proof\n"
        "  have h: true = true by reflexive\n"
        "  h\n"
        "end\n",
    )

    proof_checker._cache_stats["hits"].clear()
    proof_checker._cache_stats["misses"].clear()
    diags = check("test.pf", edited)
    assert diags == []
    # t1 unchanged, no deps -> hit.  t2 edited -> miss.  t3
    # unchanged and doesn't reference t2 -> hit.
    assert _hits() == 2, (
        f"expected 2 hits (t1 + t3 unchanged, neither references t2), "
        f"got {_hits()}; misses={_misses()}"
    )
    assert _misses() == 1


_T1_USED_BY_T2 = (
    "theorem t1: true\n"
    "proof\n"
    "  .\n"
    "end\n"
    "\n"
    "theorem t2: true and true\n"
    "proof\n"
    "  t1, t1\n"
    "end\n"
)


def test_editing_T1_invalidates_T2_that_uses_it() -> None:
    """Step 14 acceptance (verbatim from ``docs/lsp-plan.md``):
    ``edit theorem T1; assert T2 (which uses T1) is invalidated
    and rechecked``.

    t2 references t1 in its proof body (``t1, t1``).  Editing t1
    -- even just the proof body -- changes t1's stmt_hash, which
    in turn shifts t2's deps_fingerprint, so t2's cache entry is
    invalidated."""
    check("test.pf", _T1_USED_BY_T2)

    # Edit t1's proof body. Its statement type/conclusion is
    # unchanged so t2 still type-checks; what changes is t1's
    # post-uniquify structural hash, which is in t2's
    # deps_fingerprint.
    edited = _T1_USED_BY_T2.replace(
        "theorem t1: true\n"
        "proof\n"
        "  .\n"
        "end\n",
        "theorem t1: true\n"
        "proof\n"
        "  have h: true by .\n"
        "  h\n"
        "end\n",
    )

    proof_checker._cache_stats["hits"].clear()
    proof_checker._cache_stats["misses"].clear()
    diags = check("test.pf", edited)
    assert diags == []
    # t1 was edited -> miss.  t2 references t1, so t1's new
    # stmt_hash changes t2's deps_fingerprint -> miss.
    assert _hits() == 0, (
        f"expected 0 hits -- t1 edited and t2 depends on t1; "
        f"got hits={_hits()}, misses={_misses()}"
    )
    assert _misses() == 2


_T1_AUTO_T2 = (
    "theorem t1: true = true\n"
    "proof\n"
    "  reflexive\n"
    "end\n"
    "\n"
    "auto t1\n"
    "\n"
    "theorem t2: true = true\n"
    "proof\n"
    "  reflexive\n"
    "end\n"
)


def test_editing_an_autod_theorem_invalidates_later_proofs() -> None:
    """``auto`` registers a theorem as an implicit rewrite rule;
    a later proof can rely on it without ever mentioning the
    theorem's name.  Editing the auto'd theorem must therefore
    invalidate every subsequent proof, even ones that don't
    textually reference it.

    Without the auto-aware deps machinery, t2's
    ``deps_fingerprint`` would only include the ``Auto`` barrier's
    own ``stmt_hash`` -- and the ``Auto`` stmt's hash doesn't
    change when the theorem it points to changes (the reference
    is by uniquified name, which stays the same).  The fix folds
    each prior ``Auto``'s referenced names into the current
    statement's dependency set."""
    check("test.pf", _T1_AUTO_T2)

    # Edit t1's body. Its statement type is still ``true = true``
    # -- so ``auto t1`` and ``t2`` both still type-check -- but
    # t1's stmt_hash changes.
    edited = _T1_AUTO_T2.replace(
        "theorem t1: true = true\n"
        "proof\n"
        "  reflexive\n"
        "end\n",
        "theorem t1: true = true\n"
        "proof\n"
        "  have h: true = true by reflexive\n"
        "  h\n"
        "end\n",
    )

    proof_checker._cache_stats["hits"].clear()
    proof_checker._cache_stats["misses"].clear()
    diags = check("test.pf", edited)
    assert diags == []
    # t1 edited -> miss.  ``auto t1`` references t1 directly so
    # picks up t1 as a dep -> miss.  t2 doesn't reference t1
    # textually but transitively depends on it via the prior
    # ``auto`` -> miss.
    #
    # The key thing this pins is t2 missing.  Without the
    # auto-transitive dep, t2 would have hit (it references
    # nothing, and the ``auto`` barrier's own stmt_hash also
    # doesn't change since the reference is by unchanged
    # uniquified name).
    assert _hits() == 0, (
        f"expected 0 hits -- editing an auto'd theorem must "
        f"invalidate later proofs that rely on it implicitly; "
        f"got hits={_hits()}, misses={_misses()}"
    )
    assert _misses() == 3


def test_editing_T1_leaves_unrelated_T2_a_hit() -> None:
    """The complement of the above: if T2 does *not* reference T1,
    editing T1 leaves T2's verdict in the cache.  Pins the
    direction-specificity of Step 14 so a regression that conflates
    "any prior statement changed" with "a *referenced* prior
    statement changed" shows up here.

    Two-theorem fixture so the only possible source of T2's
    invalidation is dependency tracking on T1's hash."""
    src = (
        "theorem t1: true\n"
        "proof\n"
        "  .\n"
        "end\n"
        "\n"
        "theorem t2: true = true\n"
        "proof\n"
        "  reflexive\n"
        "end\n"
    )
    check("test.pf", src)

    edited = src.replace(
        "theorem t1: true\n"
        "proof\n"
        "  .\n"
        "end\n",
        "theorem t1: true\n"
        "proof\n"
        "  have h: true by .\n"
        "  h\n"
        "end\n",
    )

    proof_checker._cache_stats["hits"].clear()
    proof_checker._cache_stats["misses"].clear()
    diags = check("test.pf", edited)
    assert diags == []
    # t1 edited -> miss.  t2 doesn't reference t1 -> hit.
    assert _hits() == 1, (
        f"expected 1 hit -- t2 doesn't reference t1; "
        f"got hits={_hits()}, misses={_misses()}"
    )
    assert _misses() == 1


def test_comment_only_edit_in_unchanged_proof_still_hits() -> None:
    """A whitespace/comment edit in a non-edited statement leaves
    its post-uniquify AST structurally identical.  ``_hash_ast``
    skips ``location``, so the cache key is unchanged -> hit."""
    check("test.pf", _THREE_THEOREMS)

    # Add a stray comment line inside t3's proof body without
    # changing the proof's structure.
    edited = _THREE_THEOREMS.replace(
        "  pP\n",
        "  // helpful comment\n"
        "  pP\n",
    )

    proof_checker._cache_stats["hits"].clear()
    proof_checker._cache_stats["misses"].clear()
    diags = check("test.pf", edited)
    assert diags == []
    # All three should be hits: t1, t2 untouched as ever; t3's
    # comment doesn't survive into the parsed AST.
    assert _hits() == 3
    assert _misses() == 0


def test_cache_skips_check_proofs_for_unchanged_stmt() -> None:
    """A more direct check: replace ``check_proofs`` with a stub
    that records calls.  After a re-run on unchanged content, the
    stub should NOT have been invoked for cached statements."""
    check("test.pf", _THREE_THEOREMS)

    calls = []
    real_check_proofs = proof_checker.check_proofs

    def stub(s, env):
        calls.append(s)
        return real_check_proofs(s, env)

    proof_checker.check_proofs = stub
    try:
        check("test.pf", _THREE_THEOREMS)
    finally:
        proof_checker.check_proofs = real_check_proofs

    assert calls == [], (
        f"check_proofs was invoked despite cache hits; "
        f"called {len(calls)} times: {calls}"
    )


# Predicate desugaring (``process_declaration`` for the ``Predicate``
# case) consumes ``proof_checker.name_id`` to mint synthesised names
# for the derivation union (``<Pred>Deriv.<id>``), its constructors
# (``D_<rule>.<id>``), the validator, and the auto-generated
# rule-induction / rule-inversion theorems.  Two consecutive
# ``check_file`` calls on the same source must produce the same
# suffixes -- the post-decl AST has to be reproducible across calls,
# so the per-statement cache keys (and any other state that walks the
# post-decl AST) stay stable.  Issue #368.

_PREDICATE_SRC = (
    "predicate Even : fn Nat -> bool {\n"
    "  even_zero: Even(zero)\n"
    "  even_ss: all n:Nat. if Even(n) then Even(suc(suc(n)))\n"
    "}\n"
    "\n"
    "theorem t1: Even(zero)\n"
    "proof\n"
    "  even_zero\n"
    "end\n"
)


def test_predicate_fresh_names_are_stable_across_calls() -> None:
    """A predicate exercises ``proof_checker.generate_name`` during
    process_declaration.  Two checks of the same source must leave
    ``proof_checker.name_id`` at the same value -- otherwise the
    synthesised names drift between calls, the post-decl AST drifts
    with them, and any post-decl hashing path silently invalidates
    its cache."""
    from lsp.library import reset_prelude_cache
    reset_prelude_cache()
    check("test.pf", _PREDICATE_SRC, prelude=("Nat",))
    name_id_after_first = proof_checker.name_id

    check("test.pf", _PREDICATE_SRC, prelude=("Nat",))
    name_id_after_second = proof_checker.name_id

    assert name_id_after_first == name_id_after_second, (
        f"proof_checker.name_id drifted between identical checks: "
        f"first={name_id_after_first}, second={name_id_after_second}. "
        f"Predicate desugaring uses generate_name, so a drifting "
        f"counter makes the post-decl AST non-reproducible."
    )


def test_predicate_re_check_is_all_hits() -> None:
    """End-to-end: a fixture that triggers predicate desugaring on
    the first run hits the per-statement cache on every user-file
    statement on the second run.  Pins the plan acceptance for
    issue #368 -- the test the issue asks to land alongside the
    name_id snapshot."""
    from lsp.library import reset_prelude_cache
    reset_prelude_cache()
    check("test.pf", _PREDICATE_SRC, prelude=("Nat",))
    proof_checker._cache_stats["hits"].clear()
    proof_checker._cache_stats["misses"].clear()

    calls: list = []
    real_check_proofs = proof_checker.check_proofs

    def stub(s, env):
        calls.append(s)
        return real_check_proofs(s, env)

    proof_checker.check_proofs = stub
    try:
        check("test.pf", _PREDICATE_SRC, prelude=("Nat",))
    finally:
        proof_checker.check_proofs = real_check_proofs

    # All four user-file statements (one ``Import`` for the prelude
    # module, the ``Predicate``, and the ``Theorem``) should hit the
    # cache.  The prelude module itself is checked once during
    # bootstrap; on the second call ``_prepare_state`` restores the
    # post-prelude snapshot so the prelude isn't re-checked.
    assert _hits() >= 3, (
        f"expected the predicate + theorem + import to hit the "
        f"cache on re-run; got hits={_hits()}, misses={_misses()}, "
        f"check_proofs invocations={len(calls)}"
    )
    assert _misses() == 0, (
        f"unexpected misses on re-run of identical source; "
        f"misses={_misses()}, check_proofs invocations={len(calls)}"
    )
    assert calls == [], (
        f"check_proofs ran on a cache hit -- name_id drift would "
        f"cause this by changing the synthesised names in the "
        f"post-decl AST; called {len(calls)} times: "
        f"{[type(c).__name__ for c in calls]}"
    )
