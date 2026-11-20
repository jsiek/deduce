"""Per-statement proof-check cache and dependency fingerprint helpers.

File charter:
- Put cache storage, cache statistics, stable AST hashing, and dependency-name
  collection here.
- Put logic here only when it affects whether a top-level statement's cached
  proof-check verdict is reused or invalidated.
- Keep declaration processing, type checking, proof rules, and formula rewrite
  behavior in their own checker modules; this module should not decide whether
  a Deduce program is valid except by reporting cache hits and misses.
"""

import copy
from typing import TypeVar, cast

from lark.tree import Meta

from abstract_syntax import (
    Assert,
    Auto,
    ConceptDecl,
    Define,
    GenRecFun,
    Import,
    ModelDecl,
    OverloadedVar,
    Postulate,
    PostulateFun,
    PostulateType,
    Predicate,
    Print,
    PVar,
    RecFun,
    Statement,
    Theorem,
    TypeAlias,
    Union,
    VarRef,
    ViewDecl,
    ViewRecFun,
)
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

# Key shape is ``("check_proofs", stmt_hash, deps_fingerprint, target,
# module_name)``; ``target`` is the LSP target hole location (``None`` outside
# the LSP). The value is always ``True`` -- a sentinel marking "verified
# under this dependency set"; absent keys mean "must re-check".
_StmtCacheKey = tuple[str, int, int, tuple[int, int] | None, str]
_stmt_cache: dict[_StmtCacheKey, bool] = {}

# The processed prelude imports (issue #1245): the leading run of
# location-less ``Import`` statements the LSP puts in front of a file.
# Processing them gives the same result in every check against the same
# post-prelude state, so ``check_deduce`` keeps it here, keyed by the
# imports (and the identity of the module ASTs they carry), and reuses
# it. The value is the processed (statement, hash) pairs, the env after
# them, and the modules they import (each with its env).
_prelude_imports_cache: dict[tuple[object, ...], tuple[list[tuple[object, int]], object, dict[str, object]]] = {}

# Hits and misses bucketed by loop, for the test instrumentation
# the plan requires ("untouched statements were cache hits").
_cache_stats: dict[str, dict[str, int]] = {"hits": {}, "misses": {}}


def reset_stmt_cache() -> None:
    """Drop everything in ``_stmt_cache`` and zero the stats.  Called
    by the LSP pipeline when the prelude key changes; tests use it
    to start each fixture from a clean slate."""
    global _stmt_cache
    _stmt_cache.clear()
    _prelude_imports_cache.clear()
    _type_check_cache.clear()
    _cache_stats["hits"].clear()
    _cache_stats["misses"].clear()


def get_cache_stats() -> dict[str, dict[str, int]]:
    """Return a copy of the per-loop hit/miss counters."""
    return {
        "hits": dict(_cache_stats["hits"]),
        "misses": dict(_cache_stats["misses"]),
    }


def _record_hit(loop_tag: str) -> None:
    _cache_stats["hits"][loop_tag] = _cache_stats["hits"].get(loop_tag, 0) + 1


def _record_miss(loop_tag: str) -> None:
    _cache_stats["misses"][loop_tag] = _cache_stats["misses"].get(loop_tag, 0) + 1


def _hash_ast(node: object) -> int:
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
        seq = cast(list[object] | tuple[object, ...], node)
        return hash(tuple(_hash_ast(x) for x in seq))
    if isinstance(node, dict):
        mapping = cast(dict[object, object], node)
        return hash(
            tuple(
                (k, _hash_ast(v))
                for k, v in sorted(mapping.items(), key=lambda item: repr(item[0]))
            )
        )
    cached = getattr(node, "__hash_cache__", None)
    if isinstance(cached, int):
        return cached
    if hasattr(node, "__dict__"):
        items = []
        for k, v in cast(dict[str, object], vars(node)).items():
            if k == "location" or k == "__hash_cache__":
                continue
            items.append((k, _hash_ast(v)))
        h = hash((type(node).__name__, tuple(items)))
        try:
            setattr(node, "__hash_cache__", h)
        except AttributeError:
            pass
        return h
    return hash(repr(node))


def _collect_referenced_names(
    node: object, out: set[str] | None = None
) -> set[str]:
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
        for x in cast(list[object] | tuple[object, ...], node):
            _collect_referenced_names(x, out)
        return out
    if isinstance(node, dict):
        for v in cast(dict[object, object], node).values():
            _collect_referenced_names(v, out)
        return out
    if isinstance(node, OverloadedVar):
        # Before type checking, any of the candidates may be the one
        # chosen, so the statement depends on all of them (#1301).
        out.update(node.resolved_names)
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
        for k, v in cast(dict[str, object], vars(node)).items():
            if k in ("location", "__hash_cache__"):
                continue
            _collect_referenced_names(v, out)
    return out


def _collect_defined_names(stmt: Statement) -> set[str]:
    """Return the uniquified names a top-level statement introduces.

    Includes the statement's own name plus any auxiliary names it
    creates (union constructors; ``predicate`` rules and the
    auto-synthesised ``<pred>_rule_induction`` / ``_rule_inversion``
    theorems). Statements that don't introduce names (``Assert``,
    ``Print``, ``Auto``, ``Module``, ``Trace``, ``Import``) return
    the empty set; ``Import`` and ``Auto`` are handled separately by
    the caller as global barriers."""
    names: set[str] = set()
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


def _is_global_barrier(stmt: Statement) -> bool:
    """Statements with global side-effects on later checking.

    ``Import`` brings a module's exports into the environment;
    ``Auto`` registers a rewrite rule consulted by every later
    proof. Conservatively treat both as a barrier: every later
    statement implicitly depends on them, so editing or removing
    one invalidates the cache for everything after. So are concepts
    and models (#1264): a where formula names its concepts by string,
    and a model is found by its concept and type, never by name."""
    return isinstance(stmt, (Import, Auto, ConceptDecl, ModelDecl))


# ---------------------------------------------------------------------------
# Per-statement type-check cache (#1301)
# ---------------------------------------------------------------------------
#
# ``type_check_stmt`` checks each statement against the env that
# ``process_declaration`` built from the whole file, and returns the
# checked statement. For each module, ``_type_check_cache`` holds the
# checked statements of its last check, keyed by ``(stmt_hash,
# deps_fingerprint)`` (see ``type_check_fingerprints``), with the
# statement's layout (``statement_layout``) and first position. Each check
# replaces the module's entries with the ones it used or created, so
# the cache holds one file's worth per module.
#
# A checked statement carries its source locations, which later phases
# report and ``goal_at`` matches against. On a hit for a statement that
# only moved, ``_relocated`` shifts the cached statement's locations to
# where it now is. Locations it embeds from other statements (say, the
# type of a function it calls) are left as they were.

# (layout, (first line, first position), checked statement)
T = TypeVar("T")
_TypeCheckEntry = tuple[int, tuple[int, int], Statement]
_type_check_cache: dict[str, dict[tuple[int, int], _TypeCheckEntry]] = {}

# Statements whose effect on type checking other statements goes only
# through the names they define. Every other kind is a barrier: views
# and models are found by type, associativity by operator and type,
# imports bring in whole modules, and so on.
_NAME_ONLY_STATEMENTS = (
    Assert, Define, GenRecFun, Postulate, PostulateFun, PostulateType,
    Predicate, Print, RecFun, Theorem, TypeAlias, Union, ViewRecFun,
)

# The statements whose type check is cached: the ones that do real
# work in ``type_check_stmt`` and have no side effect there.
TYPE_CHECK_CACHED_STATEMENTS = (
    Assert, Define, GenRecFun, Postulate, Print, RecFun, Theorem, ViewRecFun,
)


def type_check_fingerprints(stmts: list[Statement],
                            hashes: list[int]) -> list[int]:
    """For each statement, a fingerprint of the statements its type
    check depends on: the ones defining a name it mentions, what those
    depend on in turn (a function's type can come from a type alias it
    mentions), and every barrier statement in the file (the env is the
    whole file's)."""
    defined_to_idx: dict[str, int] = {}
    for i, s in enumerate(stmts):
        for n in _collect_defined_names(s):
            defined_to_idx.setdefault(n, i)
    barriers = hash(tuple(h for s, h in zip(stmts, hashes)
                          if not isinstance(s, _NAME_ONLY_STATEMENTS)))
    deps_fps: list[int] = []
    full_fps: list[int] = []  # a statement's hash folded with its deps
    for i, s in enumerate(stmts):
        deps = {defined_to_idx[n] for n in _collect_referenced_names(s)
                if n in defined_to_idx} - {i}
        fp = hash((barriers, tuple(full_fps[j] if j < i else hashes[j]
                                   for j in sorted(deps))))
        deps_fps.append(fp)
        full_fps.append(hash((hashes[i], fp)))
    return deps_fps


def statement_start(stmt: Statement) -> tuple[int, int]:
    loc = stmt.location
    return (loc.line, getattr(loc, "start_pos", 0))


def _metas(node: object, out: list[Meta]) -> list[Meta]:
    """Every location in ``node``, in a fixed order."""
    if node is None or isinstance(node, (str, int, bool, float)):
        return out
    if isinstance(node, Meta):
        out.append(node)
        return out
    if isinstance(node, (list, tuple)):
        for x in cast(list[object] | tuple[object, ...], node):
            _metas(x, out)
        return out
    if isinstance(node, dict):
        for v in cast(dict[object, object], node).values():
            _metas(v, out)
        return out
    if hasattr(node, "__dict__"):
        for k, v in cast(dict[str, object], vars(node)).items():
            if k != "__hash_cache__":
                _metas(v, out)
    return out


def statement_layout(stmt: Statement) -> int:
    """A hash of the statement's locations, relative to where it starts
    when they are in its own file. Two statements with the same hash
    (``_hash_ast``) and layout differ only in where they are."""
    filename = getattr(stmt.location, "filename", None)
    line, pos = statement_start(stmt)
    sig: list[tuple[object, ...]] = []
    for m in _metas(stmt, []):
        if m.empty:
            sig.append(())
        elif getattr(m, "filename", None) == filename:
            sig.append((m.line - line, m.column, m.end_line - line,
                        m.end_column, getattr(m, "start_pos", 0) - pos,
                        getattr(m, "end_pos", 0) - pos))
        else:
            sig.append((getattr(m, "filename", None), m.line, m.column,
                        m.end_line, m.end_column))
    return hash(tuple(sig))


def _relocated(node: T, old: Statement, old_first: tuple[int, int],
               new_first: tuple[int, int]) -> T:
    """A copy of ``node``, part of the checked statement ``old`` that
    started at ``old_first``, with ``old``'s own locations moved so that
    it starts at ``new_first``."""
    filename = getattr(old.location, "filename", None)
    start, end = old_first[1], getattr(old.location, "end_pos", 0)
    dline, dpos = new_first[0] - old_first[0], new_first[1] - old_first[1]
    moved = copy.deepcopy(node)
    seen: set[int] = set()
    for m in _metas(moved, []):
        if id(m) in seen or m.empty \
           or getattr(m, "filename", None) != filename \
           or not start <= getattr(m, "start_pos", -1) <= end:
            continue
        seen.add(id(m))
        m.line += dline
        m.end_line += dline
        m.start_pos += dpos
        m.end_pos += dpos
    return moved


def lookup_type_check(module_name: str, key: tuple[int, int], layout: int,
                      stmt: Statement) -> Statement | None:
    """The cached type check of ``stmt``, given its key and layout,
    moved to where ``stmt`` is now."""
    entry = _type_check_cache.get(module_name, {}).get(key)
    if entry is None or entry[0] != layout:
        return None
    _, old_first, checked = entry
    first = statement_start(stmt)
    if isinstance(checked, Theorem) and isinstance(stmt, Theorem):
        # Type checking passes the proof through, so take it from
        # ``stmt``, which is already where it belongs.
        what = checked.what if first == old_first \
            else _relocated(checked.what, checked, old_first, first)
        return Theorem(stmt.location, checked.name, what, stmt.proof,
                       checked.isLemma, visibility=checked.visibility)
    if first != old_first:
        checked = _relocated(checked, checked, old_first, first)
    return checked


def store_type_checks(module_name: str,
                      entries: dict[tuple[int, int], _TypeCheckEntry]) -> None:
    """Replace the module's cached type checks with ``entries``."""
    _type_check_cache[module_name] = entries
