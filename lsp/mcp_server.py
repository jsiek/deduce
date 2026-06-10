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
import re
import sys
from dataclasses import asdict, dataclass, is_dataclass
from pathlib import Path
from typing import Optional, TypeAlias, cast


JSONValue: TypeAlias = object
JSONDict: TypeAlias = dict[str, JSONValue]


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


def _to_serializable(obj: object) -> JSONValue:
    """Convert frozen dataclasses (and tuples/enums of them) into
    plain dicts/lists for the MCP JSON wire format."""
    if obj is None:
        return None
    if is_dataclass(obj) and not isinstance(obj, type):
        return {k: _to_serializable(v) for k, v in asdict(obj).items()}
    if isinstance(obj, (list, tuple)):
        return [_to_serializable(x) for x in obj]
    if hasattr(obj, "value") and hasattr(obj, "name"):
        # Enum-ish: surface the .value (e.g. "error" for Severity).
        value: object = getattr(obj, "value")
        return value
    return obj


def _to_dict_or_none(obj: object) -> Optional[JSONDict]:
    """Typed wrapper: serialize an optional dataclass to a dict-or-None.

    The query helpers that feed the @mcp.tool functions return either
    a frozen dataclass or None; `_to_serializable` collapses that to
    a JSON dict or None, but its declared return type has to cover
    the recursive list/scalar branches too. This
    wrapper pins the type at the @mcp.tool boundary so the tool's
    declared return type narrows cleanly under --strict."""
    return cast(Optional[JSONDict], _to_serializable(obj))


def _to_list_of_dicts(items: object) -> list[JSONDict]:
    """Typed wrapper: serialize an iterable of dataclasses to a list
    of dicts. Pairs with _to_dict_or_none for tools whose query helper
    returns a sequence."""
    return cast(list[JSONDict], _to_serializable(items))


def _read_file(path: str) -> str:
    """Read a file with the same encoding ``check_file`` uses."""
    with open(path, "r", encoding="utf-8") as f:
        return f.read()


_DECL_RE = re.compile(
    r"^\s*(?:private\s+|public\s+|opaque\s+)*"
    r"(?:theorem|lemma|postulate|define|recursive|fun|union|predicate)\s+"
    r"(?P<name>[^\s:{(<]+)"
)
_IDENT_START_RE = r"[^\W\dλ₀₁₂₃₄₅₆₇₈₉]"
_IDENT_CONTINUE_RE = r"(?:[^\Wλ]|[₀₁₂₃₄₅₆₇₈₉!?'])*"
_HOLE_TOKEN_RE = re.compile(
    rf"(?<![^\Wλ])(?<![₀₁₂₃₄₅₆₇₈₉!?'])"
    rf"\?(?P<name>{_IDENT_START_RE}{_IDENT_CONTINUE_RE})?"
)


@dataclass(frozen=True)
class _HoleSite:
    hole_id: str
    range: query.Range
    name: Optional[str] = None


def _mask_comments(
    line: str, in_block_comment: bool
) -> tuple[str, bool]:
    """Replace comment text with spaces while preserving columns."""
    chars = list(line)
    i = 0
    while i < len(line):
        if in_block_comment:
            end = line.find("*/", i)
            stop = len(line) if end < 0 else end + 2
            for j in range(i, stop):
                if chars[j] not in "\r\n":
                    chars[j] = " "
            if end < 0:
                return "".join(chars), True
            i = stop
            in_block_comment = False
            continue

        if line.startswith("//", i):
            for j in range(i, len(line)):
                if chars[j] not in "\r\n":
                    chars[j] = " "
            break
        if line.startswith("/*", i):
            end = line.find("*/", i + 2)
            stop = len(line) if end < 0 else end + 2
            for j in range(i, stop):
                if chars[j] not in "\r\n":
                    chars[j] = " "
            if end < 0:
                return "".join(chars), True
            i = stop
            continue
        i += 1
    return "".join(chars), in_block_comment


def _hole_sites(content: str, path: str) -> list[_HoleSite]:
    """Return source sites for every literal ``?`` / ``?name`` hole."""
    fallback_scope = Path(path).stem or "file"
    current_scope = fallback_scope
    next_ordinal: dict[str, int] = {}
    sites: list[_HoleSite] = []
    in_block_comment = False

    for line_no, raw_line in enumerate(content.splitlines(keepends=True), 1):
        code_line, in_block_comment = _mask_comments(
            raw_line, in_block_comment
        )
        decl_match = _DECL_RE.match(code_line)
        if decl_match is not None:
            current_scope = decl_match.group("name")

        for match in _HOLE_TOKEN_RE.finditer(code_line):
            ordinal = next_ordinal.get(current_scope, 0)
            next_ordinal[current_scope] = ordinal + 1
            hole_id = f"{current_scope}#{ordinal}"
            col = match.start() + 1
            rng = query.Range(
                start=query.Position(line=line_no, column=col),
                end=query.Position(
                    line=line_no, column=col + len(match.group(0))
                ),
            )
            sites.append(
                _HoleSite(
                    hole_id=hole_id, range=rng, name=match.group("name")
                )
            )
    return sites


def _hole_sites_by_id(content: str, path: str) -> dict[str, _HoleSite]:
    return {site.hole_id: site for site in _hole_sites(content, path)}


def _hole_sites_by_start(
    content: str, path: str
) -> dict[tuple[int, int], _HoleSite]:
    return {
        (site.range.start.line, site.range.start.column): site
        for site in _hole_sites(content, path)
    }


def _diagnostic_payloads(
    diagnostics: object, content: str, path: str
) -> list[JSONDict]:
    hole_sites = _hole_sites_by_start(content, path)
    payloads = _to_list_of_dicts(diagnostics)
    for payload in payloads:
        rng = cast(JSONDict, payload.get("range"))
        if payload.get("goal") is None:
            payload.pop("goal", None)
        start = cast(JSONDict, rng.get("start"))
        key = (cast(int, start.get("line")), cast(int, start.get("column")))
        site = hole_sites.get(key)
        if site is not None:
            payload["hole_id"] = site.hole_id
            if site.name is not None:
                payload["hole"] = site.name
    return payloads


def _hole_site_by_name(
    tool_name: str, content: str, path: str, hole: str
) -> _HoleSite:
    matches = [site for site in _hole_sites(content, path) if site.name == hole]
    if not matches:
        raise ValueError(f"{tool_name}: unknown hole {hole!r}")
    if len(matches) > 1:
        raise ValueError(f"{tool_name}: ambiguous hole {hole!r}")
    return matches[0]


def _position_from_args(
    tool_name: str,
    path: str,
    content: str,
    line: Optional[int],
    column: Optional[int],
    hole_id: Optional[str],
    hole: Optional[str],
) -> query.Position:
    if hole_id is not None and hole is not None:
        raise ValueError(
            f"{tool_name}: provide only one of hole_id or hole"
        )
    if hole_id is not None:
        site = _hole_sites_by_id(content, path).get(hole_id)
        if site is None:
            raise ValueError(f"{tool_name}: unknown hole_id {hole_id!r}")
        return site.range.start
    if hole is not None:
        return _hole_site_by_name(tool_name, content, path, hole).range.start
    if line is None or column is None:
        raise ValueError(
            f"{tool_name}: provide line and column, hole_id, or hole"
        )
    return query.Position(line=line, column=column)


@mcp.tool()
def check_file(
    path: str,
    content: Optional[str] = None,
    parser: str = "recursive-descent",
) -> JSONDict:
    """Run the Deduce pipeline on ``path`` and return diagnostics.

    The standard library at ``lib/`` is auto-prepended unless the
    server was started with ``DEDUCE_NO_STDLIB=1``. Returns a dict
    with a ``diagnostics`` list; an empty list means the file is
    valid. Diagnostic entries have ``severity``, ``range`` (with
    1-indexed line/column positions), ``message``, and an optional
    ``code``. When ``content`` is given, validate that text as if it
    were the contents of ``path``; ``path`` is still used for imports,
    prelude selection, and diagnostic locations.

    ``parser`` selects which parser validates the file:

    - ``"recursive-descent"`` (default) -- the hand-written
      recursive-descent parser, matching Deduce's default CLI mode.
    - ``"lalr"`` -- the lark-based LALR parser, matching
      ``deduce.py --lalr``.
    - ``"both"`` -- run both parsers and merge their diagnostics.
      Each entry in the result has an extra ``parser`` field
      (``"recursive-descent"`` or ``"lalr"``) so the caller can tell
      which parser produced which message. Use this to satisfy the
      both-parsers-must-pass contributor rule in one call.
    """
    text = _read_file(path) if content is None else content
    if parser == "both":
        rd_diags = query.check(
            path, text, prelude=_prelude_for(path),
            parser="recursive-descent",
        )
        lalr_diags = query.check(
            path, text, prelude=_prelude_for(path),
            parser="lalr",
        )
        merged: list[JSONDict] = []
        for d in _diagnostic_payloads(rd_diags, text, path):
            merged.append({**d, "parser": "recursive-descent"})
        for d in _diagnostic_payloads(lalr_diags, text, path):
            merged.append({**d, "parser": "lalr"})
        return {"diagnostics": merged}
    if parser not in ("recursive-descent", "lalr"):
        raise ValueError(
            f"check_file: parser must be 'recursive-descent', 'lalr', "
            f"or 'both'; got {parser!r}"
        )
    diagnostics = query.check(
        path, text, prelude=_prelude_for(path), parser=parser,
    )
    return {"diagnostics": _diagnostic_payloads(diagnostics, text, path)}


@mcp.tool()
def goal_at(
    path: str,
    line: Optional[int] = None,
    column: Optional[int] = None,
    hole_id: Optional[str] = None,
    hole: Optional[str] = None,
    content: Optional[str] = None,
) -> Optional[JSONDict]:
    """Return the proof obligation visible at ``line``:``column``.

    Lines and columns are 1-indexed (matching the location text in
    Deduce error messages). Returns ``None`` when the cursor is
    outside any active proof or the file does not parse. The result
    has ``formula`` (a rendered string, source-shaped), ``givens``
    (a list of ``{label, formula, formula_normalized?}`` pairs in
    scope), ``range``, and ``formula_normalized``.

    ``formula_normalized`` (on the goal and on each given) is the
    post-auto-reduction form -- the shape the proof checker uses
    when matching a candidate proof body. It is ``None`` (or absent
    after serialization) when it would equal ``formula`` -- i.e. no
    auto rule fired -- so callers can compare cheaply by presence
    alone.

    When ``content`` is given, that text is used in place of the
    on-disk file -- both for resolving ``hole_id`` and for the query
    itself -- so editor flows can query unsaved buffers with the
    fresh IDs returned by ``check_file(path, content=...)``.
    """
    text = _read_file(path) if content is None else content
    pos = _position_from_args(
        "goal_at", path, text, line, column, hole_id, hole
    )
    goal = query.goal_at(path, text, pos, prelude=_prelude_for(path))
    return _to_dict_or_none(goal)


@mcp.tool()
def definition_of(
    path: str,
    line: Optional[int] = None,
    column: Optional[int] = None,
    hole_id: Optional[str] = None,
    hole: Optional[str] = None,
    content: Optional[str] = None,
) -> Optional[JSONDict]:
    """Return the source location of the symbol at ``line``:``column``.

    Returns ``None`` when the cursor isn't on a resolvable symbol or
    when the definition lives outside the file (an imported module,
    a built-in). The result has ``path`` and ``range``.

    When ``content`` is given, that text is used in place of the
    on-disk file -- both for resolving ``hole_id`` and for the query
    itself.
    """
    text = _read_file(path) if content is None else content
    pos = _position_from_args(
        "definition_of", path, text, line, column, hole_id, hole
    )
    loc = query.definition_of(path, text, pos, prelude=_prelude_for(path))
    return _to_dict_or_none(loc)


@mcp.tool()
def refine_at(
    path: str,
    line: Optional[int] = None,
    column: Optional[int] = None,
    hole_id: Optional[str] = None,
    hole: Optional[str] = None,
    content: Optional[str] = None,
) -> Optional[JSONDict]:
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

    When ``content`` is given, that text is used in place of the
    on-disk file -- both for resolving ``hole_id`` and for the query
    itself.
    """
    text = _read_file(path) if content is None else content
    pos = _position_from_args(
        "refine_at", path, text, line, column, hole_id, hole
    )
    edit = query.refine_at(path, text, pos, prelude=_prelude_for(path))
    return _to_dict_or_none(edit)


@mcp.tool()
def case_split_at(
    path: str, line: int, column: int, variable: str
) -> Optional[JSONDict]:
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
    return _to_dict_or_none(edit)


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
) -> Optional[JSONDict]:
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
    return _to_dict_or_none(edit)


@mcp.tool()
def eliminate_at(
    path: str, line: int, column: int, label: str
) -> Optional[JSONDict]:
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
    return _to_dict_or_none(edit)


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
) -> Optional[JSONDict]:
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
    return _to_dict_or_none(edit)


@mcp.tool()
def matching_givens_at(
    path: str,
    line: Optional[int] = None,
    column: Optional[int] = None,
    hole_id: Optional[str] = None,
    hole: Optional[str] = None,
    content: Optional[str] = None,
) -> list[str]:
    """Return labels of in-scope local proof bindings whose formula
    equals the goal at ``line``:``column``.

    The cursor must sit on a ``?`` token.  Names are sorted and
    deduplicated.  Returns ``[]`` when the cursor isn't on a ``?``,
    the goal AST isn't available, or no local binding matches.

    When ``content`` is given, that text is used in place of the
    on-disk file -- both for resolving ``hole_id`` and for the query
    itself.
    """
    text = _read_file(path) if content is None else content
    pos = _position_from_args(
        "matching_givens_at", path, text, line, column, hole_id, hole
    )
    return list(
        query.matching_givens_at(path, text, pos, prelude=_prelude_for(path))
    )


@mcp.tool()
def preview_conclude_at(
    path: str, line: int, column: int, label: str
) -> Optional[JSONDict]:
    """Preview ``conclude <goal> by <label>`` modulo auto-rule
    normalization at the hole at ``line``:``column``.

    Like ``fill_from_given_at`` / ``matching_givens_at`` but reduces
    both sides via ``.reduce(env)`` before checking implication --
    mirroring what the proof checker does in the catch-all branch of
    ``check_proof_of``. So a label this preview reports as
    ``discharges`` would also validate when used as a proof body.

    The cursor must sit on (or immediately adjacent to) a ``?`` token.
    ``label`` names an in-scope local proof binding.

    Returns ``None`` when the cursor isn't on a ``?`` or the file has
    no incomplete proof there. Otherwise returns a dict whose
    ``outcome`` field discriminates:

    - ``{"outcome": "discharges", "goal_normalized": "<formula>",
       "given_normalized": "<formula>"}`` -- the (reduced) label
      discharges the (reduced) goal.
    - ``{"outcome": "no_match", "goal_normalized": "<formula>",
       "given_normalized": "<formula>", "reason": "<message>"}`` --
      the label is bound but its formula does not discharge the goal,
      even modulo auto.
    - ``{"outcome": "unbound", "label": "<name>"}`` -- ``label`` is
      not bound at the hole.
    - ``{"outcome": "not_local", "label": "<name>"}`` -- ``label``
      refers to a non-local proof binding (theorem reference);
      callers invoke those by name in proof position directly.

    Companion to ``matching_givens_at`` / ``fill_from_given_at``: those
    use bare ``check_implies`` (no reduce); this one matches what the
    proof checker actually accepts. Use this to confirm a hypothesis
    discharges the goal before committing an edit.
    """
    content = _read_file(path)
    pos = query.Position(line=line, column=column)
    return _to_dict_or_none(
        query.preview_conclude_at(
            path, content, pos, label, prelude=_prelude_for(path)
        )
    )


@mcp.tool()
def apply_at(
    path: str, line: int, column: int,
    theorem: str,
    args: Optional[list[str]] = None,
) -> Optional[JSONDict]:
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
    return _to_dict_or_none(
        query.apply_at(
            path, content, pos, theorem,
            args=args, prelude=_prelude_for(path),
        )
    )


@mcp.tool()
def preview_replace_at(
    path: str,
    equation: str,
    line: Optional[int] = None,
    column: Optional[int] = None,
    hole_id: Optional[str] = None,
    hole: Optional[str] = None,
    content: Optional[str] = None,
) -> Optional[JSONDict]:
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

    When ``content`` is given, that text is used in place of the
    on-disk file -- both for resolving ``hole_id`` and for the query
    itself.
    """
    text = _read_file(path) if content is None else content
    pos = _position_from_args(
        "preview_replace_at", path, text, line, column, hole_id, hole
    )
    preview = query.preview_replace_at(
        path, text, pos, equation, prelude=_prelude_for(path)
    )
    return _to_dict_or_none(preview)


@mcp.tool()
def preview_expand_at(
    path: str, line: int, column: int, names: list[str]
) -> Optional[JSONDict]:
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
    return _to_dict_or_none(preview)


@mcp.tool()
def available_lemmas_at(
    path: str,
    line: Optional[int] = None,
    column: Optional[int] = None,
    query: Optional[str] = None,
    limit: int = 50,
    hole_id: Optional[str] = None,
    hole: Optional[str] = None,
    content: Optional[str] = None,
) -> list[JSONDict]:
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

    When ``content`` is given, that text is used in place of the
    on-disk file -- both for resolving ``hole_id`` and for the query
    itself.
    """
    from lsp import query as _q

    text = _read_file(path) if content is None else content
    pos = _position_from_args(
        "available_lemmas_at", path, text, line, column, hole_id, hole
    )
    matches = _q.available_lemmas_at(
        path,
        text,
        pos,
        query=query,
        prelude=_prelude_for(path),
        limit=limit,
    )
    return _to_list_of_dicts(matches)


@mcp.tool()
def auto_rules_at(path: str, line: int, column: int) -> list[JSONDict]:
    """Return ``auto`` rewrite rules in scope at ``line``:``column``.

    Lines and columns are 1-indexed.  Each entry has ``name`` (the
    user-visible identifier of the source theorem), ``equation`` (the
    rendered formula the rule rewrites with), and ``module`` (the
    module that declared the ``auto`` statement).  Order matches
    declaration order, which is also the order the auto-rewriter
    tries equations when multiple share a head constructor -- so the
    first hit in the list is the one that fires first.

    Useful when Deduce warns that an equation in a ``replace`` is
    *handled automatically by an auto rule*, or a goal silently
    simplifies before a tactic runs: scan the list for the rewrite
    rule whose equation matches the surprise.
    """
    content = _read_file(path)
    pos = query.Position(line=line, column=column)
    rules = query.auto_rules_at(path, content, pos, prelude=_prelude_for(path))
    return _to_list_of_dicts(rules)


@mcp.tool()
def list_symbols(path: str) -> list[JSONDict]:
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
    return _to_list_of_dicts(syms)


def main() -> None:
    """Run the server over stdio. Used as the ``__main__`` entry."""
    mcp.run()


if __name__ == "__main__":
    main()
