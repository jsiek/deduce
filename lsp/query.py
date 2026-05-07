"""Protocol-neutral query API for the Deduce LSP/MCP servers.

This module is the contract between the Deduce pipeline (``lsp.library``)
and the protocol-specific adapters (``lsp.mcp_server`` from Step 7,
``lsp.lsp_server`` from Step 9). It MUST NOT import ``pygls``, ``mcp``,
or any other protocol library; both adapters translate to/from these
types at their own boundary.

The function signatures here are load-bearing. Per
``docs/lsp-plan.md``, changes to ``__all__`` or to any signature in
this module require an explicit justification in the PR description --
the adapters are very thin and their wire-format mappings depend on
the shapes here.

Implementations are deferred to Steps 3-5; Step 2 only locks the
surface, and every function below raises ``NotImplementedError`` when
called.

Position convention
-------------------
Positions are 1-indexed: line and column both start at 1. This matches
the locations Deduce already prints in error messages and the lark
``Meta`` objects produced by both parsers, so MCP callers see line
numbers identical to ``deduce.py``'s output. The LSP adapter converts
to LSP's 0-indexed convention at the wire boundary -- a single
subtraction per coordinate.

Range convention
----------------
Ranges are inclusive-start, exclusive-end -- the same convention as
lark Meta and LSP. ``end`` points one position past the last covered
character.

Path convention
---------------
``path`` is a string filesystem path (absolute or relative to the
working directory). Adapters that receive URIs convert to plain paths
before calling. The pipeline uses ``path`` for import resolution and
in user-visible error messages.
"""

import re
from dataclasses import dataclass
from enum import Enum
from typing import Optional, Sequence


__all__ = [
    # Enums
    "Severity",
    "SymbolKind",
    # Data types
    "Position",
    "Range",
    "Location",
    "Diagnostic",
    "Given",
    "Goal",
    "SymbolInfo",
    # Query functions
    "check",
    "goal_at",
    "definition_of",
    "list_symbols",
]


class Severity(Enum):
    """Diagnostic severity level.

    Adapters map this to their wire-format equivalents:
    LSP uses integer ``DiagnosticSeverity`` (Error=1, Warning=2,
    Information=3, Hint=4); MCP exposes the string ``value``.
    """

    ERROR = "error"
    WARNING = "warning"
    INFO = "info"
    HINT = "hint"


class SymbolKind(Enum):
    """Kind of top-level Deduce declaration."""

    THEOREM = "theorem"
    LEMMA = "lemma"
    FUNCTION = "function"
    DEFINE = "define"
    UNION = "union"
    PREDICATE = "predicate"
    POSTULATE = "postulate"
    IMPORT = "import"
    OTHER = "other"


@dataclass(frozen=True)
class Position:
    """A 1-indexed (line, column) position in a source file."""

    line: int
    column: int


@dataclass(frozen=True)
class Range:
    """An inclusive-start, exclusive-end range in a source file.

    ``start`` and ``end`` refer to positions in the same file.
    """

    start: Position
    end: Position


@dataclass(frozen=True)
class Location:
    """A range tagged with the source file it lives in."""

    path: str
    range: Range


@dataclass(frozen=True)
class Diagnostic:
    """A single problem found while checking a file."""

    severity: Severity
    range: Range
    message: str
    # Optional short error code (e.g. ``"incomplete-proof"``). Reserved
    # so adapters can plumb it through; the checker does not yet emit
    # codes.
    code: Optional[str] = None


@dataclass(frozen=True)
class Given:
    """A bound hypothesis available at a proof point.

    ``label`` is ``None`` for anonymous givens (premises without an
    explicit label). ``formula`` is rendered text -- the same string
    Deduce's printer would produce -- not an AST node, so the type
    survives serialization across the MCP boundary.
    """

    label: Optional[str]
    formula: str


@dataclass(frozen=True)
class Goal:
    """The proof obligation visible at a source position.

    Returned by :func:`goal_at`. ``formula`` is the goal as rendered
    text. ``givens`` is a tuple (not list) so ``Goal`` stays hashable.
    ``range`` is the source range the goal corresponds to -- typically
    where the cursor or hole sits.
    """

    formula: str
    givens: tuple
    range: Range


@dataclass(frozen=True)
class SymbolInfo:
    """A top-level declaration in a source file.

    ``signature`` is rendered text suitable for editor hover or LSP
    ``SignatureInformation``; ``None`` when not applicable (e.g. for
    imports).
    """

    name: str
    kind: SymbolKind
    location: Location
    signature: Optional[str] = None


# ---------------------------------------------------------------------------
# Query functions
# ---------------------------------------------------------------------------
#
# Each query takes both ``path`` and ``content``. Passing ``content``
# explicitly means the LSP adapter can ship unsaved buffer contents
# without writing to a temp file, while the MCP adapter just reads from
# disk before calling. ``path`` is still required because import
# resolution and error messages depend on it.


def check(
    path: str, content: str, prelude: Sequence[str] = ()
) -> list[Diagnostic]:
    """Run the full Deduce pipeline on ``content`` (treated as if it
    were the contents of ``path``) and return all diagnostics found.

    An empty list means the file is valid. The current pipeline raises
    on the first error, so today the list will have at most one entry;
    Step 11 (multi-error collection) will lift that limit without
    changing this signature.

    ``prelude`` is the list of module names auto-imported in front of
    the file (matching ``deduce.py``'s ``--no-stdlib`` flag: empty by
    default; the MCP / LSP server passes the standard library here).
    """
    # Imported here, not at module top, so this module stays free of
    # any pipeline import while it is just a stub at module-load time.
    # That keeps the protocol-neutral boundary cheap to enforce.
    from lsp.library import check_file

    result = check_file(path, content=content, prelude=prelude)
    if result.ok:
        return []

    return [_diagnostic_from_exception(result.exception, str_fallback=result.error_message)]


def _diagnostic_from_exception(
    exc: Optional[BaseException], str_fallback: Optional[str]
) -> Diagnostic:
    """Build a Diagnostic from an exception raised by the pipeline.

    Reads ``exc.location`` and ``exc.message_body`` if present
    (attached by ``error.py`` for all error/incomplete/static/match/
    parse errors). Falls back to ``str_fallback`` plus a sentinel
    range when the exception is unstructured -- which only happens
    for unexpected internal exceptions.
    """
    sentinel = Range(Position(1, 1), Position(1, 1))

    if exc is None:
        # Should not happen in practice; defensive fallback.
        return Diagnostic(Severity.ERROR, sentinel, str_fallback or "unknown error")

    location = getattr(exc, "location", None)
    if location is not None and not getattr(location, "empty", True):
        rng = Range(
            start=Position(location.line, location.column),
            end=Position(location.end_line, location.end_column),
        )
    else:
        rng = sentinel

    body = getattr(exc, "message_body", None)
    if body is None:
        body = str_fallback if str_fallback is not None else str(exc)

    return Diagnostic(severity=Severity.ERROR, range=rng, message=body)


def goal_at(
    path: str, content: str, pos: Position, prelude: Sequence[str] = ()
) -> Optional[Goal]:
    """Return the proof obligation visible at ``pos``.

    Returns ``None`` when there is no active proof at that position --
    e.g. the cursor is outside any ``proof ... end`` block, or the file
    does not parse. Implemented by inserting a ``?`` hole at ``pos``
    (more precisely: replacing the content from ``pos`` up to the next
    ``end`` keyword with ``?``) and capturing the goal text the checker
    prints when it reaches the hole.

    ``prelude`` matches the meaning in :func:`check`.
    """
    from lsp.library import check_file

    modified = _insert_hole(content, pos)
    if modified is None:
        return None

    result = check_file(path, content=modified, prelude=prelude)
    if result.ok:
        # No PHole was hit -- the surrounding proof was already complete
        # without needing the inserted ?. Nothing to report.
        return None

    return _goal_from_exception(result.exception, pos)


def _insert_hole(content: str, pos: Position) -> Optional[str]:
    """Modify ``content`` so that the proof at ``pos`` halts on a ``?``.

    Strategy: find the byte offset for ``pos``, then scan forward
    tracking ``{``/``}`` depth. Truncate at whichever comes first:
    the closer of the enclosing case block (a ``}`` that would make
    the depth negative) or the proof body's ``end`` keyword (matched
    only at depth 0). Replace the dropped span with ``\\n?\\n`` so
    the parser sees a complete proof terminating at the hole.

    The depth tracker is what makes this work inside nested ``case``
    blocks: a naive "next ``end``" search would consume the case's
    own closing ``}`` and leave the parser with an unbalanced brace.

    Returns ``None`` when ``pos`` is out of range. If no closer is
    found we append ``?`` at the cursor and leave the rest -- the
    parser may still error, in which case ``goal_at`` returns
    ``None``.
    """
    offset = _line_col_to_offset(content, pos)
    if offset is None:
        return None

    before = content[:offset]
    after = content[offset:]
    cut = _find_block_end(after)
    if cut is None:
        return before + "\n?\n" + after
    return before + "\n?\n" + after[cut:]


def _find_block_end(s: str) -> Optional[int]:
    """Return the offset in ``s`` where the enclosing proof block closes.

    Tracks ``{``/``}`` depth from the start of ``s``. Stops at:
    - The first ``}`` that would make depth go negative (the closer
      of the block that encloses the cursor).
    - The first ``\\bend\\b`` keyword at depth 0 (the proof body
      terminator).

    Returns ``None`` if neither is found before EOF.
    """
    depth = 0
    i = 0
    n = len(s)
    while i < n:
        c = s[i]
        if c == "{":
            depth += 1
            i += 1
        elif c == "}":
            if depth == 0:
                return i
            depth -= 1
            i += 1
        elif depth == 0:
            m = _END_RE.match(s, i)
            if m:
                return m.start()
            i += 1
        else:
            i += 1
    return None


def _line_col_to_offset(content: str, pos: Position) -> Optional[int]:
    """Convert a 1-indexed (line, column) to a 0-indexed byte offset.

    Returns ``None`` when the position is past the end of the file.
    Columns past the end of a line clamp to the line's length.
    """
    if pos.line < 1 or pos.column < 1:
        return None
    lines = content.splitlines(keepends=True)
    if pos.line > len(lines):
        return None
    line_start = sum(len(line) for line in lines[: pos.line - 1])
    line = lines[pos.line - 1]
    # splitlines(keepends=True) keeps the trailing newline; clamp the
    # column to the line length minus that newline so we don't insert
    # past it.
    visible_len = len(line.rstrip("\r\n"))
    col = min(pos.column - 1, visible_len)
    return line_start + col


_END_RE = re.compile(r"\bend\b")


def _goal_from_exception(
    exc: Optional[BaseException], pos: Position
) -> Optional[Goal]:
    """Parse an ``IncompleteProof`` message into a ``Goal``.

    The pipeline raises ``IncompleteProof`` from ``incomplete_error``
    with a message body of the form::

        incomplete proof
        Goal:
        \\t<formula>
        [<advice text -- may or may not start with "Advice:">]
        [Givens:
        \\t<label>: <formula>[,
        \\t<label>: <formula>]*]

    Formula AST objects always render to a single line, so we take the
    first non-blank line after ``Goal:`` as the formula and stop. The
    advice that follows is intentionally discarded -- callers that want
    advice can read ``Diagnostic.message`` from ``check`` instead.

    Returns ``None`` when the message doesn't match (e.g. the exception
    is something other than the goal-bearing PHole, like a parse error
    triggered by the inserted ``?`` ending up in a bad spot).
    """
    if exc is None:
        return None
    body = getattr(exc, "message_body", None)
    if body is None:
        return None

    formula = _extract_goal_formula(body)
    if formula is None:
        return None

    givens = _parse_givens_section(body)

    cursor_range = Range(start=pos, end=pos)
    return Goal(formula=formula, givens=givens, range=cursor_range)


def _extract_goal_formula(body: str) -> Optional[str]:
    """Return the formula on the line immediately after ``Goal:``.

    The formula is always a single line because Deduce's ``__str__``
    renderers don't emit newlines inside a formula. Returns ``None``
    when no ``Goal:`` header is present.
    """
    idx = body.find("Goal:")
    if idx < 0:
        return None
    after = body[idx + len("Goal:"):]
    for line in after.splitlines():
        if not line.strip():
            continue
        # Section content is indented with a tab; drop one level.
        if line.startswith("\t"):
            line = line[1:]
        return line.strip()
    return None


def _parse_givens_section(body: str) -> tuple:
    """Pull a ``Givens:`` block (if any) into a tuple of ``Given``.

    Each entry has the form ``<label>: <formula>``, joined by ``,\\n``
    (see ``Env.proofs_str``). Lines that don't start with a tab are
    treated as outside the section and stop iteration -- which never
    actually happens today since Givens is the last section, but keeps
    us robust if a future change appends more text.
    """
    idx = body.find("Givens:")
    if idx < 0:
        return ()
    after = body[idx + len("Givens:"):]
    if after.startswith("\n"):
        after = after[1:]

    section_lines = []
    for line in after.splitlines():
        if line == "" or line.startswith("\t"):
            section_lines.append(line)
        else:
            break
    block = "\n".join(section_lines)

    givens = []
    # Split on ",\n" rather than just commas because formulas can
    # contain commas (e.g. argument lists).
    for entry in block.split(",\n"):
        entry = entry.strip()
        if not entry:
            continue
        sep = entry.find(":")
        if sep < 0:
            givens.append(Given(label=None, formula=entry))
            continue
        label = entry[:sep].strip()
        formula = entry[sep + 1:].strip()
        givens.append(Given(label=label or None, formula=formula))
    return tuple(givens)


def definition_of(
    path: str, content: str, pos: Position, prelude: Sequence[str] = ()
) -> Optional[Location]:
    """Return the source location of the symbol under ``pos``.

    Walks the post-typecheck AST returned by ``check_file``, finds the
    ``Var`` whose source range contains ``pos``, takes its first
    (i.e. type-resolved) entry from ``resolved_names``, and looks up
    the matching top-level declaration.

    Returns ``None`` when there is no resolvable symbol at ``pos``
    (whitespace, keyword, unparseable region) or when the definition
    is outside any source file the server can see -- e.g. it lives in
    an imported module, since today the only AST we consult is the
    user's file.

    ``prelude`` matches the meaning in :func:`check`.
    """
    from lsp.library import check_file

    result = check_file(path, content=content, prelude=prelude)
    if result.ast is None:
        return None

    target_name = _find_reference_at(result.ast, pos)
    if target_name is None:
        return None

    decl_meta = _find_declaration(result.ast, target_name)
    if decl_meta is None:
        return None

    return Location(path=path, range=_range_from_meta(decl_meta))


def list_symbols(
    path: str, content: str, prelude: Sequence[str] = ()
) -> list[SymbolInfo]:
    """Return all top-level declarations in ``content``.

    Used for editor outline views and the MCP ``list_symbols`` tool.
    Includes theorems, lemmas, functions, defines, unions, predicates,
    postulates, postulates, and imports; does not descend into nested
    definitions inside proofs. Uses the post-typecheck AST so signature
    text reflects type-checked formulas.

    ``prelude`` matches the meaning in :func:`check`. Symbols that
    come from prelude imports are *not* included in the result --
    only declarations in ``content`` itself.
    """
    from lsp.library import check_file

    from abstract_syntax import Import as _ImportNode

    result = check_file(path, content=content, prelude=prelude)
    if result.ast is None:
        return []

    prelude_set = set(prelude)
    out: list[SymbolInfo] = []
    for stmt in result.ast:
        # Skip the auto-prepended prelude imports -- the user didn't
        # write them, so they shouldn't show up in the outline.
        if isinstance(stmt, _ImportNode) and stmt.name in prelude_set:
            continue
        info = _symbol_info_for(stmt, path)
        if info is not None:
            out.append(info)
    return out


# ---------------------------------------------------------------------------
# Internals shared by definition_of and list_symbols
# ---------------------------------------------------------------------------


def _range_from_meta(meta) -> Range:
    """Convert a lark ``Meta`` (or compatible duck) to a ``Range``."""
    return Range(
        start=Position(line=meta.line, column=meta.column),
        end=Position(line=meta.end_line, column=meta.end_column),
    )


def _meta_contains(meta, pos: Position) -> bool:
    """Test whether 1-indexed ``pos`` falls inside the ``meta`` range.

    The range is inclusive-start, exclusive-end (matches lark's
    convention and the documented Range semantics).
    """
    if getattr(meta, "empty", True):
        return False
    after_start = (meta.line, meta.column) <= (pos.line, pos.column)
    before_end = (pos.line, pos.column) < (meta.end_line, meta.end_column)
    return after_start and before_end


def _find_reference_at(ast_nodes, pos: Position) -> Optional[str]:
    """Locate the smallest reference node whose range contains ``pos``.

    Recognises term references (``Var``, with overload resolution via
    ``resolved_names[0]``) and proof references (``PVar``, whose
    ``name`` is already the chosen uniquified name post-uniquify).
    "Smallest" means the deepest match in the AST -- inner refs take
    precedence over enclosing constructs that happen to share a range.

    Returns the resolved (uniquified) name, or ``None`` when no
    reference node contains ``pos``. The ``base_name`` of the return
    value is the user-visible identifier; the suffix is what
    ``_find_declaration`` matches against.
    """
    # Late import: lsp/query.py is the protocol-neutral surface, so we
    # don't pull in abstract_syntax until a query actually runs.
    from abstract_syntax import AST, PVar, Var, VarRef

    best: list[Optional[str]] = [None]
    best_span: list[Optional[int]] = [None]

    def visit(node):
        if isinstance(node, VarRef):
            resolved = node.get_name()
        elif isinstance(node, PVar):
            resolved = node.name
        else:
            return
        meta = getattr(node, "location", None)
        if meta is None or not _meta_contains(meta, pos):
            return
        span = _meta_span(meta)
        if best_span[0] is None or span < best_span[0]:
            best_span[0] = span
            best[0] = resolved

    for top in ast_nodes:
        _walk_ast(top, visit, ast_class=AST)

    return best[0]


def _meta_span(meta) -> int:
    """Crude size measure for a ``Meta``; smaller wins ties in tree
    descent so inner nodes outrank enclosing ones."""
    if meta.line == meta.end_line:
        return meta.end_column - meta.column
    # Multi-line ranges are larger than any single-line range. Use a
    # huge per-line cost so we never pick a multi-line Var over a
    # single-line one that contains the cursor.
    return 10_000 * (meta.end_line - meta.line) + meta.end_column


def _find_declaration(ast_nodes, target_name: str):
    """Find the top-level declaration whose uniquified ``name`` field
    equals ``target_name``. Returns its ``Meta`` location or ``None``.
    """
    from abstract_syntax import (
        Define,
        Import,
        Postulate,
        Predicate,
        RecFun,
        Theorem,
        Union,
    )

    decl_types = (Theorem, Postulate, Define, RecFun, Union, Predicate, Import)
    for stmt in ast_nodes:
        if isinstance(stmt, decl_types) and getattr(stmt, "name", None) == target_name:
            return stmt.location
    return None


def _walk_ast(node, visit, ast_class, seen=None):
    """Recursively visit every AST descendant of ``node``.

    Uses dataclass reflection so we don't have to enumerate every
    concrete class. The ``seen`` set guards against shared sub-trees
    (e.g. the env reused across statements after type checking).
    """
    if seen is None:
        seen = set()
    nid = id(node)
    if nid in seen:
        return
    seen.add(nid)
    visit(node)

    from dataclasses import fields, is_dataclass

    if not is_dataclass(node):
        return
    for f in fields(node):
        value = getattr(node, f.name, None)
        if isinstance(value, ast_class):
            _walk_ast(value, visit, ast_class, seen)
        elif isinstance(value, (list, tuple)):
            for item in value:
                if isinstance(item, ast_class):
                    _walk_ast(item, visit, ast_class, seen)


def _symbol_info_for(stmt, path: str) -> Optional[SymbolInfo]:
    """Build a ``SymbolInfo`` for a top-level statement, or ``None``
    if the node isn't a kind we surface (e.g. ``Auto``)."""
    from abstract_syntax import (
        Auto,
        Define,
        Import,
        Postulate,
        Predicate,
        RecFun,
        Theorem,
        Union,
        base_name,
    )

    location = Location(path=path, range=_range_from_meta(stmt.location))

    if isinstance(stmt, Theorem):
        kind = SymbolKind.LEMMA if stmt.isLemma else SymbolKind.THEOREM
        signature = f"{base_name(stmt.name)}: {stmt.what}"
    elif isinstance(stmt, Postulate):
        kind = SymbolKind.POSTULATE
        signature = f"{base_name(stmt.name)}: {stmt.what}"
    elif isinstance(stmt, Define):
        kind = SymbolKind.DEFINE
        ty_text = f": {stmt.typ}" if stmt.typ is not None else ""
        signature = f"define {base_name(stmt.name)}{ty_text}"
    elif isinstance(stmt, RecFun):
        kind = SymbolKind.FUNCTION
        params = ", ".join(str(p) for p in stmt.params)
        typarams = (
            f"<{', '.join(stmt.type_params)}>" if stmt.type_params else ""
        )
        signature = (
            f"function {base_name(stmt.name)}{typarams}({params}) -> {stmt.returns}"
        )
    elif isinstance(stmt, Union):
        kind = SymbolKind.UNION
        typarams = (
            f"<{', '.join(stmt.type_params)}>" if stmt.type_params else ""
        )
        signature = f"union {base_name(stmt.name)}{typarams}"
    elif isinstance(stmt, Predicate):
        kind = SymbolKind.PREDICATE
        signature = f"{stmt.original_keyword} {base_name(stmt.name)}: {stmt.signature}"
    elif isinstance(stmt, Import):
        kind = SymbolKind.IMPORT
        signature = f"import {stmt.name}"
    elif isinstance(stmt, Auto):
        # Auto declares an auto-rewrite rule and doesn't introduce a
        # named symbol of its own; skip it from the outline.
        return None
    else:
        return None

    return SymbolInfo(
        name=base_name(stmt.name) if hasattr(stmt, "name") else "",
        kind=kind,
        location=location,
        signature=signature,
    )
