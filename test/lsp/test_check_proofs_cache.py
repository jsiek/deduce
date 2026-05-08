"""Acceptance test for the per-statement ``check_proofs`` cache (Phase 3 / Step 13).

Plan acceptance: ``edit one statement, recheck; instrumentation
confirms untouched statements were cache hits``.

The cache lives in ``proof_checker._stmt_cache`` and is keyed by
``(stmt_hash, chain_hash)``.  ``stmt_hash`` is a structural hash
that skips the ``location`` (``Meta``) field, so adding/removing
*other* statements doesn't perturb the hash of an unchanged one.
``chain_hash`` is a fold over prior statements' hashes -- it
identifies the cumulative state at this position in the AST.

What this file pins:

- a clean run populates the cache with all-misses,
- a re-run on the same content is all-hits,
- editing a statement near the end leaves the unchanged prefix
  cache-hits and only the touched statement misses.

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


def test_editing_a_statement_in_the_middle_invalidates_downstream() -> None:
    """Editing a statement in the middle invalidates it AND every
    statement after it (the chain hash has changed for them)."""
    check("test.pf", _THREE_THEOREMS)

    # Edit the *second* theorem.  Replace the proof body with an
    # intermediate ``have'' step -- AST changes structurally, the
    # proof still passes.  The first theorem is unchanged; the
    # third's `chain` hash now differs from the cached entry, so
    # it has to recheck too.
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
    # Only t1 is upstream of the edit -> one hit.  t2 was edited,
    # t3's chain shifted -> two misses.
    assert _hits() == 1
    assert _misses() == 2


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
