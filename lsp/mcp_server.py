"""MCP adapter for the Deduce query API (Phase 1 / Step 7).

Exposes ``lsp.query``'s four functions as MCP tools over stdio. Each
tool is a thin wrapper that reads the file from disk, calls the
underlying query helper, and serializes the result to JSON-friendly
dicts.

Run directly to start the stdio server::

    python3 -m lsp.mcp_server

Wire it into Claude Code via ``.mcp.json`` (or the user-level
equivalent)::

    {
      "mcpServers": {
        "deduce": {
          "command": "python3",
          "args": ["-m", "lsp.mcp_server"]
        }
      }
    }

The standard library at ``lib/`` is auto-prepended as the default
prelude unless ``DEDUCE_NO_STDLIB=1`` is set in the environment;
that mirrors ``deduce.py``'s ``--no-stdlib`` flag. Set
``DEDUCE_ROOT`` to override where the server looks for ``lib/`` and
``test/test-imports/``; otherwise it falls back to the parent
directory of this module.

The MCP boundary stays protocol-specific: the only consumer of
``mcp`` lives here. Everything reachable from tests and the LSP
adapter (Step 9) goes through ``lsp.query``.
"""

from __future__ import annotations

import os
import sys
from dataclasses import asdict, is_dataclass
from pathlib import Path
from typing import Any, Optional


# ---------------------------------------------------------------------------
# Bootstrap: configure the Deduce environment exactly once at import.
# ---------------------------------------------------------------------------


def _resolve_deduce_root() -> Path:
    env_root = os.environ.get("DEDUCE_ROOT")
    if env_root:
        return Path(env_root).resolve()
    # ``lsp/mcp_server.py`` lives one directory below the repo root.
    return Path(__file__).resolve().parent.parent


_DEDUCE_ROOT = _resolve_deduce_root()
_LIB_DIR = _DEDUCE_ROOT / "lib"
_TEST_IMPORTS_DIR = _DEDUCE_ROOT / "test" / "test-imports"

# ``set_deduce_directory`` -- called by the parsers -- reads
# ``os.path.dirname(sys.argv[0])`` to find ``Deduce.lark``. Make
# sure it points at the repo root regardless of how the server
# was launched.
_PSEUDO_ENTRY = str(_DEDUCE_ROOT / "deduce.py")
sys.argv = [_PSEUDO_ENTRY] + sys.argv[1:]
sys.setrecursionlimit(10000)

# Repo root needs to be on sys.path for ``import abstract_syntax`` etc.
if str(_DEDUCE_ROOT) not in sys.path:
    sys.path.insert(0, str(_DEDUCE_ROOT))

from abstract_syntax import (  # noqa: E402
    add_import_directory,
    init_import_directories,
)
from flags import set_quiet_mode  # noqa: E402

set_quiet_mode(True)
init_import_directories()
add_import_directory(str(_LIB_DIR))
if _TEST_IMPORTS_DIR.is_dir():
    add_import_directory(str(_TEST_IMPORTS_DIR))


def _default_prelude() -> tuple[str, ...]:
    """Module names for every ``.pf`` in ``lib/`` -- the standard
    library prelude, mirroring ``deduce.py`` without ``--no-stdlib``.
    Returns ``()`` when ``DEDUCE_NO_STDLIB=1`` or ``lib/`` is missing.
    """
    if os.environ.get("DEDUCE_NO_STDLIB") == "1":
        return ()
    if not _LIB_DIR.is_dir():
        return ()
    return tuple(
        sorted(p.stem for p in _LIB_DIR.glob("*.pf"))
    )


_PRELUDE = _default_prelude()


def _path_is_in_lib(path: str) -> bool:
    """True iff ``path`` lives inside the standard library directory.

    Files inside ``lib/`` are part of the prelude themselves; checking
    one with the prelude prepended would import the file twice and
    trip ``theorem names may not be overloaded`` (mirrors the
    ``check_in_prelude`` logic in ``deduce.py``)."""
    try:
        Path(path).resolve().relative_to(_LIB_DIR.resolve())
    except (OSError, ValueError):
        return False
    return True


def _prelude_for(path: str) -> tuple[str, ...]:
    """Empty prelude for files in ``lib/``, otherwise the default."""
    return () if _path_is_in_lib(path) else _PRELUDE


# ---------------------------------------------------------------------------
# Server definition
# ---------------------------------------------------------------------------


from lsp import query  # noqa: E402
from mcp.server.fastmcp import FastMCP  # noqa: E402


mcp = FastMCP("deduce-lsp")


def _to_serializable(obj: Any) -> Any:
    """Convert frozen dataclasses (and tuples/enums of them) into
    plain dicts/lists for the MCP JSON wire format."""
    if obj is None:
        return None
    if is_dataclass(obj):
        return {k: _to_serializable(v) for k, v in asdict(obj).items()}
    if isinstance(obj, (list, tuple)):
        return [_to_serializable(x) for x in obj]
    if hasattr(obj, "value") and hasattr(obj, "name"):
        # Enum-ish: surface the .value (e.g. "error" for Severity).
        return obj.value
    return obj


def _read_file(path: str) -> str:
    """Read a file with the same encoding ``check_file`` uses."""
    with open(path, "r", encoding="utf-8") as f:
        return f.read()


@mcp.tool()
def check_file(path: str) -> dict:
    """Run the Deduce pipeline on ``path`` and return diagnostics.

    The standard library at ``lib/`` is auto-prepended unless the
    server was started with ``DEDUCE_NO_STDLIB=1``. Returns a dict
    with a ``diagnostics`` list; an empty list means the file is
    valid. Diagnostic entries have ``severity``, ``range`` (with
    1-indexed line/column positions), ``message``, and an optional
    ``code``.
    """
    content = _read_file(path)
    diagnostics = query.check(path, content, prelude=_prelude_for(path))
    return {"diagnostics": _to_serializable(diagnostics)}


@mcp.tool()
def goal_at(path: str, line: int, column: int) -> Optional[dict]:
    """Return the proof obligation visible at ``line``:``column``.

    Lines and columns are 1-indexed (matching the location text in
    Deduce error messages). Returns ``None`` when the cursor is
    outside any active proof or the file does not parse. The result
    has ``formula`` (a rendered string), ``givens`` (a list of
    ``{label, formula}`` pairs in scope), and ``range``.
    """
    content = _read_file(path)
    pos = query.Position(line=line, column=column)
    goal = query.goal_at(path, content, pos, prelude=_prelude_for(path))
    return _to_serializable(goal)


@mcp.tool()
def definition_of(path: str, line: int, column: int) -> Optional[dict]:
    """Return the source location of the symbol at ``line``:``column``.

    Returns ``None`` when the cursor isn't on a resolvable symbol or
    when the definition lives outside the file (an imported module,
    a built-in). The result has ``path`` and ``range``.
    """
    content = _read_file(path)
    pos = query.Position(line=line, column=column)
    loc = query.definition_of(path, content, pos, prelude=_prelude_for(path))
    return _to_serializable(loc)


@mcp.tool()
def refine_at(path: str, line: int, column: int) -> Optional[dict]:
    """Propose a refinement template for the hole at ``line``:``column``.

    The cursor must sit on (or immediately adjacent to) a ``?`` token.

    Returns ``None`` when the cursor isn't on a ``?`` or the file has
    no incomplete proof at that hole.

    Returns ``{path, range, new_text}`` (a workspace edit) when a
    template applies.

    Returns ``{outcome: "unsupported_shape", goal, supported_shapes}``
    when the cursor *is* on a real hole but the goal's shape isn't in
    the table below -- so the caller can pick another tactic without
    guessing why ``refine_at`` declined.

    Templates by goal shape:
    - ``true`` -> ``.``
    - ``P and Q [and R...]`` -> ``?, ?[, ?...]``
    - ``if P then Q`` -> ``assume H: P\\n?``
    - ``all x:T. body`` -> ``arbitrary x:T\\n?``
    - ``some x:T. body`` -> ``choose ?\\n?``
    - reducible ``e1 = e2`` -> ``reflexive``
    """
    content = _read_file(path)
    pos = query.Position(line=line, column=column)
    edit = query.refine_at(path, content, pos, prelude=_prelude_for(path))
    return _to_serializable(edit)


@mcp.tool()
def case_split_at(
    path: str, line: int, column: int, variable: str
) -> Optional[dict]:
    """Generate a case-split skeleton at the hole at ``line``:``column``,
    splitting on ``variable``.

    The cursor must sit on (or immediately adjacent to) a ``?`` token;
    that ``?`` is the replacement target. ``variable`` names the
    in-scope binding to split on -- either a term variable whose type
    is a ``Union`` (yields a ``switch`` skeleton with one ``case
    Cons(p1, ..., pN) { ? }`` per constructor) or a proof variable
    whose formula is ``Or(...)`` (yields a ``cases`` skeleton with
    one ``case <fresh>: <disjunct> { ? }`` per disjunct).

    Returns ``None`` when the cursor isn't on a ``?``, the file has
    no incomplete proof there, ``variable`` isn't bound at the hole,
    or the binding's shape isn't a union / disjunction. Otherwise
    returns ``{path, range, new_text}``.

    For a list of valid ``variable`` choices at a given cursor, see
    ``splittable_vars_at``.
    """
    content = _read_file(path)
    pos = query.Position(line=line, column=column)
    edit = query.case_split_at(
        path, content, pos, variable, prelude=_prelude_for(path)
    )
    return _to_serializable(edit)


@mcp.tool()
def splittable_vars_at(path: str, line: int, column: int) -> list[str]:
    """Return base names of in-scope variables that case-split can
    target at ``line``:``column``.

    The cursor must sit on a ``?`` token. The result is the union of:

    - term variables whose type is a ``Union`` (or instance of one),
    - proof variables whose formula is ``Or(...)``.

    Constructor names are filtered out -- splitting on a constructor
    would produce a redundant skeleton. Names are sorted and
    deduplicated. Returns ``[]`` when the cursor isn't on a ``?`` or
    no splittable variable is in scope.
    """
    content = _read_file(path)
    pos = query.Position(line=line, column=column)
    return list(
        query.splittable_vars_at(path, content, pos, prelude=_prelude_for(path))
    )


@mcp.tool()
def induction_skeleton_at(
    path: str, line: int, column: int
) -> Optional[dict]:
    """Generate an ``induction T`` skeleton for the goal at ``line``:``column``.

    The cursor must sit on (or immediately adjacent to) a ``?`` token
    whose goal has the shape ``all x:T. P(x)`` where ``T`` is a
    ``Union`` with at least two alternatives.  The skeleton emits one
    ``case <Cons>(<params>) [assume IH<N>: ...] { ? }`` per
    constructor in declaration order; recursive parameters introduce
    ``IH<N>`` bindings whose formula is the goal body with the
    inducted variable substituted.

    Returns ``None`` when the cursor isn't on a ``?``, the goal isn't
    a single ``all`` over a Union, or the union has fewer than 2
    alternatives.  Otherwise returns ``{path, range, new_text}``.

    Distinct from ``case_split_at``:
    - Operates on the *goal*, not a named variable (no ``variable''
      argument).
    - Emits ``induction T`` (term-level) rather than
      ``switch x``/``cases H``.
    - Adds ``assume IH<N>: ...`` bindings for recursive parameters.
    """
    content = _read_file(path)
    pos = query.Position(line=line, column=column)
    edit = query.induction_skeleton_at(
        path, content, pos, prelude=_prelude_for(path)
    )
    return _to_serializable(edit)


@mcp.tool()
def eliminate_at(
    path: str, line: int, column: int, label: str
) -> Optional[dict]:
    """Generate a tactic that uses ``label`` to derive a fact (or
    discharge the goal) at the hole at ``line``:``column``.

    The cursor must sit on (or immediately adjacent to) a ``?`` token;
    that ``?`` is the replacement target.  ``label`` names an in-scope
    proof binding -- typically a hypothesis introduced by ``assume``.
    The template is chosen from the binding's formula shape:

    - ``H: P and Q`` -> destructure with ``have h1: P by conjunct 1
      of H``, etc.
    - ``H: P or Q`` -> ``cases H ...``
    - ``H: if P then Q`` -> ``have h: Q by apply H to ?``
    - ``H: all x:T. P`` -> ``H[?, ...]``
    - ``H: some x:T. P`` -> ``obtain ... where ... from H``
    - ``H: e1 = e2`` -> ``replace H``
    - ``H: false`` -> ``H`` (discharges any goal)
    - ``H: true`` -> ``None`` (no useful template)

    Returns ``None`` when the cursor isn't on a ``?``, ``label`` isn't
    bound at the hole, or the binding's shape isn't supported.
    Otherwise returns ``{path, range, new_text}``.

    For a list of valid ``label`` choices, see ``eliminable_vars_at``.
    """
    content = _read_file(path)
    pos = query.Position(line=line, column=column)
    edit = query.eliminate_at(
        path, content, pos, label, prelude=_prelude_for(path)
    )
    return _to_serializable(edit)


@mcp.tool()
def eliminable_vars_at(
    path: str, line: int, column: int
) -> list[str]:
    """Return labels of in-scope hypotheses that ``eliminate_at`` can
    target at ``line``:``column``.

    The cursor must sit on a ``?`` token.  Includes labels for local
    proof bindings (introduced by ``assume`` / ``suppose`` / ``have``)
    whose formula has a supported template shape.  ``true``-shaped
    facts are filtered out.  Names are sorted and deduplicated.
    Returns ``[]`` when the cursor isn't on a ``?`` or no eliminable
    binding is in scope.
    """
    content = _read_file(path)
    pos = query.Position(line=line, column=column)
    return list(
        query.eliminable_vars_at(path, content, pos, prelude=_prelude_for(path))
    )


@mcp.tool()
def fill_from_given_at(
    path: str, line: int, column: int, label: str
) -> Optional[dict]:
    """Fill the hole at ``line``:``column`` with ``conclude <goal> by
    <label>``.

    The cursor must sit on (or immediately adjacent to) a ``?`` token;
    that ``?`` is the replacement target.  ``label`` names an in-scope
    *local* proof binding (typically a hypothesis introduced by
    ``assume`` / ``suppose`` / ``have``) whose formula equals the goal
    at the hole.

    Returns ``None`` when the cursor isn't on a ``?``, ``label`` isn't
    bound, the bound formula doesn't match the goal, or the binding
    isn't local.  Otherwise returns ``{path, range, new_text}``.

    For a list of valid ``label`` choices, see ``matching_givens_at``.
    """
    content = _read_file(path)
    pos = query.Position(line=line, column=column)
    edit = query.fill_from_given_at(
        path, content, pos, label, prelude=_prelude_for(path)
    )
    return _to_serializable(edit)


@mcp.tool()
def matching_givens_at(
    path: str, line: int, column: int
) -> list[str]:
    """Return labels of in-scope local proof bindings whose formula
    equals the goal at ``line``:``column``.

    The cursor must sit on a ``?`` token.  Names are sorted and
    deduplicated.  Returns ``[]`` when the cursor isn't on a ``?``,
    the goal AST isn't available, or no local binding matches.
    """
    content = _read_file(path)
    pos = query.Position(line=line, column=column)
    return list(
        query.matching_givens_at(path, content, pos, prelude=_prelude_for(path))
    )


@mcp.tool()
def apply_at(
    path: str, line: int, column: int,
    theorem: str,
    args: Optional[list[str]] = None,
) -> Optional[dict]:
    """Preview ``apply <theorem>[<args>] to ?`` at the hole at
    ``line``:``column``.

    The cursor must sit on (or immediately adjacent to) a ``?`` token.
    ``theorem`` is the name of an in-scope hypothesis, theorem, lemma,
    or postulate. ``args`` is the optional ordered list of explicit
    term arguments instantiating ``theorem``'s outermost ``all``
    quantifiers, matching the ``theorem[arg, arg, ...]`` syntax. Each
    entry is the rendered text of a term (parsed in the scope at the
    hole, so ``arbitrary``-bound variables are visible).

    Returns ``None`` when the cursor isn't on a ``?``, the
    surrounding file fails to parse, or the targeted hole isn't
    reached. Otherwise returns a dict whose ``outcome`` field
    discriminates the shape:

    - ``{"outcome": "ok", "conclusion": "<formula>",
       "remaining_premises": ["<formula>", ...]}`` -- the apply would
      succeed; ``remaining_premises`` is the ordered list of
      obligations the user still has to prove (split on top-level
      ``and`` so it maps to what would go after ``to``).
    - ``{"outcome": "unifies_against", "goal": "<formula>",
       "reason": "<message>"}`` -- the conclusion didn't match the
      goal, or all-bound variables couldn't be deduced.
    - ``{"outcome": "unbound", "theorem": "<name>"}`` -- the theorem
      isn't in scope at the hole.
    - ``{"outcome": "arity_mismatch", "expected": N, "got": M}``
      (or ``{"outcome": "arity_mismatch", "reason": "..."}``) --
      too many ``[args]`` for the theorem's outer quantifiers, or
      ``theorem`` is not an implication.

    Companion to ``eliminate_at`` (which generates an ``apply`` /
    ``cases`` / ... template from a hypothesis): ``eliminate_at`` says
    *what tactic to write*; ``apply_at`` says *whether the apply will
    actually unify with the current goal*.
    """
    content = _read_file(path)
    pos = query.Position(line=line, column=column)
    return query.apply_at(
        path, content, pos, theorem,
        args=args, prelude=_prelude_for(path),
    )


@mcp.tool()
def preview_replace_at(
    path: str, line: int, column: int, equation: str
) -> Optional[dict]:
    """Preview the result of ``replace <equation>`` at the hole at
    ``line``:``column``.

    The cursor must sit on (or immediately adjacent to) a ``?`` token.
    ``equation`` is the *name* of an in-scope theorem, lemma, or local
    hypothesis whose formula is an equation, optionally prefixed with
    ``"symmetric "`` for a right-to-left rewrite (e.g. ``"foo"`` or
    ``"symmetric foo"``).

    Returns ``None`` when the cursor isn't on a ``?`` or the file has
    no incomplete proof there. Otherwise returns a dict with an
    ``outcome`` field:

    - ``{outcome: "ok", before: <goal text>, after: <goal text>}``
      -- the rewrite would succeed.
    - ``{outcome: "no_match", reason: <text>}`` -- the equation's LHS
      does not occur in the (post-reduction) goal; usually means an
      ``auto`` rule has already canonicalized it away.
    - ``{outcome: "not_an_equation", formula: <text>}`` -- the named
      binding's formula isn't an equation.
    - ``{outcome: "unbound", name: <input>}`` -- no proof binding by
      that name is in scope at the hole.

    Pure / read-only: the file on disk is not modified. Pairs with
    ``goal_at`` for the inner loop where the agent picks an equation,
    previews the rewrite, and only commits when the after-text matches
    its plan.
    """
    content = _read_file(path)
    pos = query.Position(line=line, column=column)
    preview = query.preview_replace_at(
        path, content, pos, equation, prelude=_prelude_for(path)
    )
    return _to_serializable(preview)


@mcp.tool()
def preview_expand_at(
    path: str, line: int, column: int, names: list[str]
) -> Optional[dict]:
    """Preview the result of ``expand <names>`` at the hole at
    ``line``:``column``.

    The cursor must sit on (or immediately adjacent to) a ``?`` token.
    ``names`` is a list of definitions to unfold (matching the
    ``expand X | Y | Z`` syntactic form).

    Returns ``None`` when the cursor isn't on a ``?`` or the file has
    no incomplete proof there. Otherwise returns a dict with an
    ``outcome`` field:

    - ``{outcome: "ok", before: <goal text>, after: <goal text>}``
      -- every name unfolded at least once.
    - ``{outcome: "no_match", name: <name>}`` -- a name is in scope
      and expandable, but its definition has no place to apply in the
      current goal (often an ``auto`` rule canonicalized the call
      away).
    - ``{outcome: "opaque", name: <name>}`` -- the named binding is
      opaque from the file under check.
    - ``{outcome: "unknown", name: <name>}`` -- no term/type binding
      by that name is in scope.

    Pure / read-only: the file on disk is not modified.
    """
    content = _read_file(path)
    pos = query.Position(line=line, column=column)
    preview = query.preview_expand_at(
        path, content, pos, names, prelude=_prelude_for(path)
    )
    return _to_serializable(preview)


@mcp.tool()
def available_lemmas_at(
    path: str,
    line: int,
    column: int,
    query: Optional[str] = None,
    limit: int = 50,
) -> list[dict]:
    """Search for theorems/lemmas/postulates relevant at a position.

    The cursor at ``line``:``column`` is interpreted as follows:

    - On a ``?`` token: the goal at that hole drives ranking. The
      goal's head operator and operator/function tokens are matched
      against each candidate lemma's conclusion.
    - Off a ``?`` with ``query`` given: ``query`` is a substring
      (matched against the rendered signature) or a goal-shape
      pattern containing ``_`` placeholders (each ``_`` matches any
      run of characters, e.g. ``"_ ≤ _ + _"``).
    - Off a ``?`` with no ``query``: browse mode -- every lemma in
      scope at ``line``:``column`` is returned, ranked by module
      proximity (user-file first) then alphabetically. Lets agents
      explore "what's available here?" without inserting a ``?``.

    Results are returned best-first, capped at ``limit`` entries
    (default 50). Each entry has ``name``, ``kind`` (``"theorem"`` /
    ``"lemma"`` / ``"postulate"``), ``signature``, ``module`` (the
    source module's name; the file's stem for declarations in the
    current file), and ``relevance`` -- a score in ``[0.0, 1.0]``
    where ``1.0`` is the best match in the result set.

    Visibility: lemmas declared ``private`` in the current file are
    surfaced (they're in scope), but private lemmas in prelude
    modules are not (matching what ``print_theorems`` exports).

    Returns ``[]`` only when nothing is in scope at the position or
    a given ``query`` matches nothing.
    """
    from lsp import query as _q

    content = _read_file(path)
    pos = _q.Position(line=line, column=column)
    matches = _q.available_lemmas_at(
        path,
        content,
        pos,
        query=query,
        prelude=_prelude_for(path),
        limit=limit,
    )
    return [_to_serializable(m) for m in matches]


@mcp.tool()
def auto_rules_at(path: str, line: int, column: int) -> list[dict]:
    """Return ``auto`` rewrite rules in scope at ``line``:``column``.

    Lines and columns are 1-indexed.  Each entry has ``name`` (the
    user-visible identifier of the source theorem), ``equation`` (the
    rendered formula the rule rewrites with), and ``module`` (the
    module that declared the ``auto`` statement).  Order matches
    declaration order, which is also the order the auto-rewriter
    tries equations when multiple share a head constructor -- so the
    first hit in the list is the one that fires first.

    Useful when Deduce reports *no need for replace because this
    equation is handled automatically* or a goal silently simplifies
    before a tactic runs: scan the list for the rewrite rule whose
    equation matches the surprise.
    """
    content = _read_file(path)
    pos = query.Position(line=line, column=column)
    rules = query.auto_rules_at(path, content, pos, prelude=_prelude_for(path))
    return _to_serializable(rules)


@mcp.tool()
def list_symbols(path: str) -> list[dict]:
    """Return all top-level declarations in ``path``.

    Includes theorems, lemmas, postulates, defines, recursive
    functions, unions, predicates, and explicit imports. Auto-
    prepended prelude imports are filtered out so the outline shows
    only what the user wrote. Each entry has ``name``, ``kind``
    (e.g. ``"theorem"``), ``location``, and an optional
    ``signature``.
    """
    content = _read_file(path)
    syms = query.list_symbols(path, content, prelude=_prelude_for(path))
    return _to_serializable(syms)


def main() -> None:
    """Run the server over stdio. Used as the ``__main__`` entry."""
    mcp.run()


if __name__ == "__main__":
    main()
