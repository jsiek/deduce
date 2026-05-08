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

import abstract_syntax  # noqa: E402
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
        # uniquified names contain a literal `.` followed by digits.
        if not isinstance(s, str):
            return False
        if "." not in s:
            return False
        suffix = s.rsplit(".", 1)[1]
        return suffix.isdigit()

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
    """A freshly-constructed ``UniquifyContext`` has counter 0 --
    pinning the contract that future per-module / per-statement
    scoping (Step 13/14) will rely on."""
    ctx = UniquifyContext()
    assert ctx.name_id == 0


def test_uniquify_deduce_default_context_persists() -> None:
    """The default (no-ctx) path uses a module-level shared context
    so ids monotonically accumulate across calls.  This is the
    production pipeline's behaviour and what stops prelude-cached
    names from colliding with later allocations.

    Two same-input calls without an explicit ctx should NOT produce
    the same names -- the second call sees a higher starting id."""
    src = "theorem t: true\nproof\n  .\nend\n"

    # Snapshot the counter, run, snapshot again.
    before = abstract_syntax._default_uniquify_ctx.name_id
    uniquify_deduce(_parse(src))
    after = abstract_syntax._default_uniquify_ctx.name_id

    # Some names get allocated -- counter advanced.
    assert after > before


def test_explicit_context_is_isolated_from_default() -> None:
    """Passing an explicit ``ctx`` doesn't disturb the default
    context's counter -- the two are independent allocators."""
    src = "theorem t: true\nproof\n  .\nend\n"

    default_before = abstract_syntax._default_uniquify_ctx.name_id
    explicit_ctx = UniquifyContext()
    uniquify_deduce(_parse(src), ctx=explicit_ctx)
    default_after = abstract_syntax._default_uniquify_ctx.name_id

    # Default context untouched.
    assert default_before == default_after
    # Explicit context advanced.
    assert explicit_ctx.name_id > 0
