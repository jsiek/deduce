# mypy: ignore-errors
from checker_common import *

# ---------------------------------------------------------------------------
# Per-statement cache
# ---------------------------------------------------------------------------
#
# ``check_deduce`` runs three loops over the AST: ``process_declaration``,
# ``type_check_stmt``, and ``collect_env``+``check_proofs``. Each loop's
# work for a given statement is determined by (a) the statement's
# post-uniquify structure and (b) the env coming in. Cache by both, and
# we can skip statements unchanged since the previous run.
#
# Key shape: ``(loop_tag, stmt_hash, chain_hash)``.  ``chain_hash`` is
# a fold over the prior statements' hashes -- equivalent to
# ``env_in_hash`` in the plan, but cheaper to maintain and stable
# across calls (since uniquify is now deterministic).
#
# The cache lives at module level and accumulates across
# ``check_deduce`` calls.  ``lsp/library.py`` clears it when the
# prelude key changes (different prelude => different baseline =>
# cache invalid).

_stmt_cache: dict = {}

# Hits and misses bucketed by loop, for the test instrumentation
# the plan requires ("untouched statements were cache hits").
_cache_stats: dict = {"hits": {}, "misses": {}}


def reset_stmt_cache() -> None:
    """Drop everything in ``_stmt_cache`` and zero the stats.  Called
    by the LSP pipeline when the prelude key changes; tests use it
    to start each fixture from a clean slate."""
    global _stmt_cache
    _stmt_cache.clear()
    _cache_stats["hits"].clear()
    _cache_stats["misses"].clear()


def get_cache_stats() -> dict:
    """Return a copy of the per-loop hit/miss counters."""
    return {
        "hits": dict(_cache_stats["hits"]),
        "misses": dict(_cache_stats["misses"]),
    }


def _record_hit(loop_tag: str) -> None:
    _cache_stats["hits"][loop_tag] = _cache_stats["hits"].get(loop_tag, 0) + 1


def _record_miss(loop_tag: str) -> None:
    _cache_stats["misses"][loop_tag] = _cache_stats["misses"].get(loop_tag, 0) + 1


def _hash_ast(node) -> int:
    """Stable structural hash of a (post-uniquify) AST.

    Skips the ``location`` (Meta) attribute, which carries source
    line/column info that shifts with edits to unrelated parts of
    the file -- we want only the structure + names to participate
    in the hash.

    Memoised on the node via ``__hash_cache__`` so each statement
    is hashed at most once per session, even if it appears in
    several of ``check_deduce``'s loops.
    """
    if node is None:
        return 0
    if isinstance(node, (str, int, bool, float)):
        return hash(node)
    if isinstance(node, (list, tuple)):
        return hash(tuple(_hash_ast(x) for x in node))
    if isinstance(node, dict):
        return hash(
            tuple(sorted((k, _hash_ast(v)) for k, v in node.items()))
        )
    cached = getattr(node, "__hash_cache__", None)
    if cached is not None:
        return cached
    if hasattr(node, "__dict__"):
        items = []
        for k, v in node.__dict__.items():
            if k == "location" or k == "__hash_cache__":
                continue
            items.append((k, _hash_ast(v)))
        h = hash((type(node).__name__, tuple(items)))
        try:
            node.__hash_cache__ = h
        except AttributeError:
            pass
        return h
    return hash(repr(node))


def _collect_referenced_names(node, out=None) -> set:
    """Walk a statement's post-uniquify AST and gather every uniquified
    name it references via ``VarRef`` (``Var`` / ``OverloadedVar`` /
    ``ResolvedVar``) or ``PVar``.

    Used by Step 14's dependency-aware invalidation: a statement's
    cache verdict is keyed on the hashes of the prior statements that
    introduced any of these names, so editing an unrelated theorem
    leaves this statement's entry intact.

    Skips ``location`` (irrelevant), ``__hash_cache__`` (memoisation
    artefact), and ``Import.ast`` (the imported module is checked on
    its own pass, and we treat ``Import`` as a global barrier in the
    caller anyway)."""
    if out is None:
        out = set()
    if node is None or isinstance(node, (str, int, bool, float)):
        return out
    if isinstance(node, (list, tuple)):
        for x in node:
            _collect_referenced_names(x, out)
        return out
    if isinstance(node, dict):
        for v in node.values():
            _collect_referenced_names(v, out)
        return out
    if isinstance(node, VarRef):
        out.add(node.get_name())
        return out
    if isinstance(node, PVar):
        out.add(node.name)
        return out
    if isinstance(node, Import):
        # Imports are treated as a global barrier by the caller; we
        # don't want to recurse into the imported module's AST here.
        return out
    if isinstance(node, ViewDecl):
        out.add(node.into)
        out.add(node.out)
        out.add(node.roundtrip)
    if isinstance(node, ViewRecFun):
        out.add(node.view_name)
    if hasattr(node, "__dict__"):
        for k, v in node.__dict__.items():
            if k in ("location", "__hash_cache__"):
                continue
            _collect_referenced_names(v, out)
    return out


def _collect_defined_names(stmt) -> set:
    """Return the uniquified names a top-level statement introduces.

    Includes the statement's own name plus any auxiliary names it
    creates (union constructors; ``predicate`` rules and the
    auto-synthesised ``<pred>_rule_induction`` / ``_rule_inversion``
    theorems). Statements that don't introduce names (``Assert``,
    ``Print``, ``Auto``, ``Module``, ``Trace``, ``Import``) return
    the empty set; ``Import`` and ``Auto`` are handled separately by
    the caller as global barriers."""
    names: set = set()
    name = getattr(stmt, "name", None)
    if isinstance(name, str):
        names.add(name)
    if isinstance(stmt, Union):
        for con in stmt.alternatives:
            if isinstance(con.name, str):
                names.add(con.name)
    elif isinstance(stmt, Predicate):
        for rule in stmt.rules:
            if isinstance(rule.name, str):
                names.add(rule.name)
        rule_ind = getattr(stmt, "rule_induction_name", None)
        if isinstance(rule_ind, str):
            names.add(rule_ind)
        rule_inv = getattr(stmt, "rule_inversion_name", None)
        if isinstance(rule_inv, str):
            names.add(rule_inv)
    return names


def _is_global_barrier(stmt) -> bool:
    """Statements with global side-effects on later checking.

    ``Import`` brings a module's exports into the environment;
    ``Auto`` registers a rewrite rule consulted by every later
    proof. Conservatively treat both as a barrier: every later
    statement implicitly depends on them, so editing or removing
    one invalidates the cache for everything after."""
    return isinstance(stmt, (Import, Auto))
