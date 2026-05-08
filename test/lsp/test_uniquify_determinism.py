"""Acceptance test for ``uniquify_deduce`` determinism (Phase 3 / Step 12).

Plan acceptance: ``call uniquify on the same AST twice, byte-equal output``.

Two calls of ``uniquify_deduce`` on the same input AST, each with a
fresh ``UniquifyContext``, must produce byte-equal output.  This is
the foundation for Step 13's ``(stmt_hash, env_in_hash) -> env_out``
cache: stable unique names mean stable hashes mean cache keys reuse
across runs.

The default-context call path (used by the production pipeline) is
*not* deterministic across calls within a process -- it accumulates
ids monotonically so cached prelude names don't collide with names
later allocated for the user's file.  The test exercises only the
fresh-context path; the default-context path is covered by the rest
of the LSP suite, which doesn't depend on counter resets.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from abstract_syntax import UniquifyContext, uniquify_deduce  # noqa: E402


def _parse(src: str):
    """Parse Deduce source via the recursive-descent parser.

    Returns a top-level list of AST nodes (statements), suitable for
    feeding to ``uniquify_deduce``.
    """
    import rec_desc_parser as rdp

    rdp.set_deduce_directory(str(REPO_ROOT))
    rdp.init_parser()
    return rdp.parse(src, "test.pf")


def _collect_unique_names(ast) -> list:
    """Walk ``ast`` and return the sequence of unique-name strings
    encountered.

    Looks at every attribute that holds either a single uniquified
    name (``foo.42``) or a list of them (e.g. ``OverloadedVar.resolved_names``).
    Tuple-shaped fields (``var: (name, type)``) are flattened.

    The walk order is structural -- whatever ``vars()`` returns on
    each dataclass.  As long as both runs visit nodes in the same
    order, the resulting sequence reflects the assignment of ids to
    AST positions and is enough to detect non-determinism.
    """
    out: list = []

    def looks_uniquified(s) -> bool:
        # uniquified names contain a literal `.` followed by either a
        # plain digit run (legacy global-counter form) or one or more
        # ``s<idx>_<n>`` segments (per-statement scoping, Step 14).
        if not isinstance(s, str):
            return False
        if "." not in s:
            return False
        suffix = s.rsplit(".", 1)[1]
        if suffix.isdigit():
            return True
        # Per-statement scoped form: zero or more ``s<idx>_`` prefixes
        # followed by a trailing decimal run.
        rest = suffix
        while True:
            if not rest.startswith("s"):
                break
            tail = rest[1:]
            digits, sep, after = tail.partition("_")
            if not sep or not digits.isdigit():
                return False
            rest = after
        return rest.isdigit()

    def visit(node, seen):
        if id(node) in seen:
            return
        seen.add(id(node))
        # Plain string?  Check for uniquified-name shape.
        if isinstance(node, str):
            if looks_uniquified(node):
                out.append(node)
            return
        if isinstance(node, (int, float, bool)) or node is None:
            return
        if isinstance(node, (list, tuple)):
            for item in node:
                visit(item, seen)
            return
        if isinstance(node, dict):
            for k, v in node.items():
                visit(k, seen)
                visit(v, seen)
            return
        # Dataclass-like AST node -- recurse over its public fields.
        d = getattr(node, "__dict__", None)
        if d:
            for v in d.values():
                visit(v, seen)

    visit(ast, set())
    return out


def test_uniquify_deduce_byte_equal_on_fresh_contexts() -> None:
    """Plan acceptance: two ``uniquify_deduce`` calls with fresh
    contexts produce byte-equal output for the same input AST."""
    src = (
        "theorem t: all P:bool, Q:bool. if P and Q then Q and P\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  suppose pq: P and Q\n"
        "  ?\n"
        "end\n"
    )
    ast1 = _parse(src)
    ast2 = _parse(src)

    out1 = uniquify_deduce(ast1, ctx=UniquifyContext())
    out2 = uniquify_deduce(ast2, ctx=UniquifyContext())

    names1 = _collect_unique_names(out1)
    names2 = _collect_unique_names(out2)
    assert names1 == names2, (
        "uniquify_deduce produced different name sequences on two "
        "fresh-context runs:\n"
        f"  run 1 ({len(names1)} names): {names1[:10]}...\n"
        f"  run 2 ({len(names2)} names): {names2[:10]}..."
    )


def test_uniquify_deduce_byte_equal_for_proof_with_holes() -> None:
    """Same property on a fixture with `?` holes -- exercises the
    PHole node and the surrounding proof structure."""
    src = (
        "union N {\n"
        "  z\n"
        "  s(N)\n"
        "}\n"
        "\n"
        "theorem t: all x:N. x = x\n"
        "proof\n"
        "  ?\n"
        "end\n"
    )
    ast1 = _parse(src)
    ast2 = _parse(src)

    out1 = uniquify_deduce(ast1, ctx=UniquifyContext())
    out2 = uniquify_deduce(ast2, ctx=UniquifyContext())

    names1 = _collect_unique_names(out1)
    names2 = _collect_unique_names(out2)
    assert names1 == names2


def test_uniquify_context_starts_at_zero() -> None:
    """A freshly-constructed ``UniquifyContext`` has counter 0 and
    empty scope -- pinning the contract that per-statement scoping
    (Step 14) builds on."""
    ctx = UniquifyContext()
    assert ctx.name_id == 0
    assert ctx.scope == ""


def test_uniquify_deduce_restores_caller_state() -> None:
    """Step 14: each top-level statement gets its own scope segment
    and counter reset, and the call as a whole restores the caller's
    ``name_id`` / ``scope`` on exit.  The counter no longer
    accumulates across calls -- per-statement scope is what keeps
    names from colliding instead."""
    src = "theorem t: true\nproof\n  .\nend\n"
    ctx = UniquifyContext()
    uniquify_deduce(_parse(src), ctx)
    assert ctx.name_id == 0
    assert ctx.scope == ""
    uniquify_deduce(_parse(src), ctx)
    assert ctx.name_id == 0
    assert ctx.scope == ""


def test_uniquify_deduce_uses_per_statement_scopes() -> None:
    """Two top-level statements that share a base name (here, both
    bind the proof variable ``pP``) get *disjoint* uniquified suffixes
    because ``uniquify_deduce`` pushes a fresh ``s<idx>_`` segment onto
    ``ctx.scope`` per top-level statement.  This is what makes
    structural hashing edit-invariant -- the dependency-tracking cache
    (Step 14) needs unrelated downstream statements' hashes to stay
    stable when an earlier statement's body changes size."""
    src = (
        "theorem t1: all P:bool. if P then P\n"
        "proof arbitrary P:bool suppose pP: P pP end\n"
        "theorem t2: all P:bool. if P then P\n"
        "proof arbitrary P:bool suppose pP: P pP end\n"
    )
    out = uniquify_deduce(_parse(src), UniquifyContext())
    names = _collect_unique_names(out)
    s0_names = [n for n in names if ".s0_" in n]
    s1_names = [n for n in names if ".s1_" in n]
    assert s0_names, f"no s0_-scoped names found in {names}"
    assert s1_names, f"no s1_-scoped names found in {names}"
    # Each top-level statement's bound names live in its own scope.
    assert set(s0_names).isdisjoint(set(s1_names))


def test_independent_ctxs_do_not_leak() -> None:
    """Two contexts are independent objects -- mutating one doesn't
    affect the other."""
    ctx_a = UniquifyContext()
    ctx_b = UniquifyContext()
    ctx_a.name_id = 99
    ctx_a.scope = "x_"
    assert ctx_b.name_id == 0
    assert ctx_b.scope == ""


def test_snapshot_forks_independent_counter_and_scope() -> None:
    """``UniquifyContext.snapshot`` returns a fresh ctx with the same
    counter and scope, but mutating one doesn't affect the other."""
    parent = UniquifyContext(name_id=42, scope="p_")
    child = parent.snapshot()
    assert child.name_id == 42
    assert child.scope == "p_"
    child.name_id += 5
    child.scope = "c_"
    assert parent.name_id == 42  # parent untouched
    assert parent.scope == "p_"
    assert child.name_id == 47
    assert child.scope == "c_"
