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
    "WorkspaceEdit",
    # Query functions
    "check",
    "goal_at",
    "definition_of",
    "list_symbols",
    "refine_at",
    "case_split_at",
    "splittable_vars_at",
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
class WorkspaceEdit:
    """A single textual edit to apply to a file.

    Adapters map this to their wire-format equivalents:

    - LSP wraps it in ``WorkspaceEdit`` / ``TextDocumentEdit`` /
      ``TextEdit`` and exposes it via ``textDocument/codeAction``.
    - MCP returns the dict ``{path, range, new_text}`` as a tool
      result; the agent applies it through its own edit tooling.

    The semantics are "replace ``range`` with ``new_text``". Multi-
    file edits and file creates/renames aren't represented here --
    the Phase-4 refactoring operations in this module all return a
    single-file, single-range edit, so a flat shape is enough.
    """

    path: str
    range: Range
    new_text: str


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
    from abstract_syntax import AST, PVar, Var

    best: list[Optional[str]] = [None]
    best_span: list[Optional[int]] = [None]

    def visit(node):
        if isinstance(node, Var):
            resolved = (node.resolved_names or [None])[0] or node.name
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


# ---------------------------------------------------------------------------
# refine_at -- Phase 4 / Step 15: hole refine
# ---------------------------------------------------------------------------
#
# Given a cursor on a `?` token, return a WorkspaceEdit that replaces
# the hole with a tactic skeleton chosen from the goal's shape. The
# adapters expose this as a code action (LSP) and as an MCP tool.
#
# Mechanism: the source already has a `?`, so re-running ``check_file``
# raises ``IncompleteProof`` at that hole. ``proof_checker.py`` stashes
# the goal AST and the type-checking env on the exception
# (``incomplete_error(..., formula=, env=)``), which we read here to
# select the template -- string-based shape detection isn't expressive
# enough for the reducible-equality case (``e1.reduce(env) ==
# e2.reduce(env)``).
#
# Limitation (v1): in a multi-theorem file with earlier `?`s, the
# checker raises on the first hole encountered; the goal returned may
# not be for the cursor's hole. The same limitation applies to
# ``goal_at``; both will lift it together when the pipeline gains
# per-hole goal extraction.


def refine_at(
    path: str, content: str, pos: Position, prelude: Sequence[str] = ()
) -> Optional[WorkspaceEdit]:
    """Propose a refinement template for the hole at ``pos``.

    The cursor must sit on (or immediately adjacent to) a ``?`` token
    in the source. The template is selected based on the goal's shape:

    - ``true`` -> ``.``
    - ``P and Q [and R...]`` -> ``?, ?[, ?...]``
    - ``if P then Q`` -> ``assume H: P\\n?``
    - ``all x:T. body`` -> ``arbitrary x:T\\n?`` (one quantifier per
      invocation; nested quantifiers are refined in further steps)
    - ``some x:T. body`` -> ``choose ?\\n?``
    - reducible ``e1 = e2`` -> ``reflexive``

    Returns ``None`` when the cursor is not on a ``?``, when the file
    does not raise at a hole, or when the goal shape is not in the
    list above.

    ``prelude`` matches the meaning in :func:`check`.
    """
    hole_range = _find_hole_at(content, pos)
    if hole_range is None:
        return None

    from lsp.library import check_file

    result = check_file(path, content=content, prelude=prelude)
    if result.ok:
        return None

    exc = result.exception
    formula = getattr(exc, "formula", None)
    env = getattr(exc, "env", None)
    if formula is None:
        return None

    template = _refine_template(formula, env)
    if template is None:
        return None

    template = _indent_continuation(
        template, _line_indent_at(content, hole_range.start)
    )
    return WorkspaceEdit(path=path, range=hole_range, new_text=template)


def _find_hole_at(content: str, pos: Position) -> Optional[Range]:
    """Return the source range of a ``?`` token at or adjacent to ``pos``.

    Tries the cursor offset itself, then one position to the left
    (cursor sits just after the ``?``). Returns ``None`` when neither
    matches.
    """
    offset = _line_col_to_offset(content, pos)
    if offset is None:
        return None
    for try_off in (offset, offset - 1):
        if 0 <= try_off < len(content) and content[try_off] == "?":
            return _char_range_at(content, try_off)
    return None


def _char_range_at(content: str, offset: int) -> Range:
    """Return the 1-indexed Range covering exactly the character at ``offset``."""
    line, col = _offset_to_line_col(content, offset)
    return Range(
        start=Position(line=line, column=col),
        end=Position(line=line, column=col + 1),
    )


def _line_indent_at(content: str, pos: Position) -> str:
    """Return the leading whitespace of the source line containing ``pos``.

    "Whitespace" here means spaces and tabs only -- newlines aren't
    counted. Used to re-indent multi-line refactor templates so the
    inserted text matches the surrounding proof body's indentation
    instead of starting subsequent lines at column 0.
    """
    offset = _line_col_to_offset(content, pos)
    if offset is None:
        return ""
    line_start = content.rfind("\n", 0, offset) + 1
    indent_end = line_start
    while indent_end < len(content) and content[indent_end] in " \t":
        indent_end += 1
    return content[line_start:indent_end]


def _indent_continuation(template: str, indent: str) -> str:
    """Prefix every newline-introduced line in ``template`` with ``indent``.

    The first line is left alone -- it gets the indentation of the
    line containing the ``?`` it replaces, since the WorkspaceEdit
    inserts at that column. The continuation lines, by contrast, would
    naturally land at column 0 without this prefix; that's the bug
    issue #333 is about.

    No-op when ``indent`` is empty or the template has no newlines.
    """
    if not indent or "\n" not in template:
        return template
    return template.replace("\n", "\n" + indent)


def _offset_to_line_col(content: str, offset: int) -> tuple:
    """Inverse of ``_line_col_to_offset``: 0-indexed offset to 1-indexed (line, col)."""
    line = 1
    line_start = 0
    for i in range(offset):
        if content[i] == "\n":
            line += 1
            line_start = i + 1
    return (line, offset - line_start + 1)


def _refine_template(formula, env) -> Optional[str]:
    """Select a refinement template based on the goal AST.

    Imports the AST node classes lazily so this module's import-time
    cost stays minimal -- the same pattern the rest of ``query.py``
    uses for pipeline-level imports.
    """
    from abstract_syntax import (
        All, And, Bool, Call, IfThen, Some, Var, base_name,
    )

    match formula:
        case Bool(_, _, True):
            return "."
        case And(_, _, args):
            return ", ".join(["?"] * len(args))
        case IfThen(_, _, prem, _conc):
            label = _fresh_assume_label(env)
            return f"assume {label}: {prem}\n?"
        case All(_, _, var, _, _body):
            x, ty = var
            return f"arbitrary {base_name(x)}:{ty}\n?"
        case Some(_, _, vars, _body):
            choices = ", ".join("?" for _ in vars)
            return f"choose {choices}\n?"
        case Call(_, _, Var(_, _, "=", _), [lhs, rhs]) if env is not None:
            try:
                if lhs.reduce(env) == rhs.reduce(env):
                    return "reflexive"
            except Exception:
                # If reduction fails (e.g. a malformed env after a
                # mid-check error), don't crash the editor request --
                # just report "no template".
                return None
            return None
    return None


def _fresh_assume_label(env) -> str:
    """Return the lowest ``H<N>`` (N >= 1) not already bound in ``env``.

    Successive ``assume H1: ...``, ``assume H2: ...`` invocations
    keep climbing rather than collide -- otherwise repeatedly
    refining nested implications produces several ``assume H: ...``
    lines in a row, which Deduce accepts (with a warning) but
    confuses any subsequent proof step that names the hypothesis.

    Checks against the *base* names in ``env.dict`` so we look at
    pre-uniquification source-level identifiers, not the post-
    uniquify ``foo.42`` form. Falls back to ``"H1"`` when ``env``
    is None (the `IfThen` case is reachable today only via the
    `IncompleteProof` exception, so ``env`` is always non-None in
    practice; the guard is for defensive composition).
    """
    if env is None:
        return "H1"
    from abstract_syntax import base_name
    used_bases = {base_name(k) for k in env.dict.keys()}
    n = 1
    while f"H{n}" in used_bases:
        n += 1
    return f"H{n}"


# ---------------------------------------------------------------------------
# case_split_at -- Phase 4 / Step 16: case split on a named variable
# ---------------------------------------------------------------------------
#
# UX shape: cursor on a `?`, *plus* an explicit ``variable`` argument
# (the name of the in-scope variable to split on). The replacement
# target is the `?` the cursor sits on; the variable arg drives the
# template choice. This separation is what lets the editor binding
# read the variable name from the user (with completion against
# `splittable_vars_at`) before issuing the request -- the cursor's
# role is unambiguous.
#
# Mechanism: same trick as ``refine_at`` -- the cursor's `?` is what
# raises ``IncompleteProof``, and ``incomplete_error`` stashes the
# proof env on the exception (Step 15 plumbing). We read that env to
# look up ``variable``'s binding and render the case skeleton against
# ``Union.alternatives`` or ``Or.args``.


def case_split_at(
    path: str, content: str, pos: Position,
    variable: str,
    prelude: Sequence[str] = (),
) -> Optional[WorkspaceEdit]:
    """Generate a case-split skeleton for ``variable`` at the hole at ``pos``.

    The cursor must sit on (or immediately adjacent to) a ``?`` token;
    that ``?`` is the replacement target. The ``variable`` argument
    names an in-scope binding to split on:

    - a *term variable* whose type is a ``Union`` (or an instance of
      a parameterised union like ``List<T>``) -- yields a ``switch``
      skeleton with one ``case Cons(p1, ..., pN) { ? }`` per
      constructor.
    - a *proof variable* whose formula is ``Or(...)`` -- yields a
      ``cases`` skeleton with one ``case <fresh>: <disjunct> { ? }``
      per disjunct.

    Returns ``None`` when:

    - the cursor isn't on a ``?``,
    - the file has no incomplete proof at the cursor,
    - ``variable`` isn't bound at the hole,
    - or the binding's shape isn't a union / disjunction.

    For client-side completion of valid ``variable`` choices at a
    given cursor position, see :func:`splittable_vars_at`.
    """
    hole_range = _find_hole_at(content, pos)
    if hole_range is None:
        return None

    from lsp.library import check_file

    result = check_file(path, content=content, prelude=prelude)
    if result.ok:
        return None

    exc = result.exception
    env = getattr(exc, "env", None)
    if env is None:
        return None

    template = _case_split_template(variable, env)
    if template is None:
        return None

    template = _indent_continuation(
        template, _line_indent_at(content, hole_range.start)
    )
    return WorkspaceEdit(path=path, range=hole_range, new_text=template)


def splittable_vars_at(
    path: str, content: str, pos: Position, prelude: Sequence[str] = ()
) -> tuple:
    """Return base names of in-scope variables that case-split can target.

    Computes the env at the ``?`` token the cursor is on (via the
    same ``IncompleteProof``-based mechanism as ``case_split_at``),
    then walks the env for bindings whose shape supports a case
    split: term variables of ``Union`` type and proof variables of
    ``Or`` formulas.

    Used by editor clients to populate completion candidates when the
    user types ``C-c C-c`` and is prompted for a variable name.
    Returns an empty tuple when the cursor isn't on a ``?`` or no
    splittable variable is in scope. Names are deduplicated and
    sorted.
    """
    hole_range = _find_hole_at(content, pos)
    if hole_range is None:
        return ()

    from lsp.library import check_file

    result = check_file(path, content=content, prelude=prelude)
    if result.ok:
        return ()

    exc = result.exception
    env = getattr(exc, "env", None)
    if env is None:
        return ()

    return _splittable_vars(env)


def _splittable_vars(env) -> tuple:
    """Names of bindings whose ``case_split`` would succeed.

    Excludes constructor names: the env stores each union's
    constructor as a TermBinding of the union's type, structurally
    indistinguishable from a local variable like ``arbitrary x:N``.
    Splitting on a constructor name would just produce a redundant
    skeleton (``switch z { case z {...} case s(...) {...} }``), so
    we filter the constructor set out by walking every Union in the
    env up front.
    """
    from abstract_syntax import (
        Or, ProofBinding, TermBinding, TypeBinding, Union, Var, base_name,
        get_type_name,
    )

    # Collect constructor names from every union in scope.
    constructor_names = set()
    for unique, binding in env.dict.items():
        if isinstance(binding, TypeBinding) and isinstance(binding.defn, Union):
            for alt in binding.defn.alternatives:
                constructor_names.add(base_name(alt.name))

    seen = set()
    for unique in env.dict.keys():
        bname = base_name(unique)
        if bname in seen or bname in constructor_names:
            continue
        binding = env.dict[unique]
        if isinstance(binding, ProofBinding):
            if isinstance(binding.formula, Or):
                seen.add(bname)
        elif isinstance(binding, TermBinding):
            ty = binding.typ
            try:
                type_var = get_type_name(ty)
            except Exception:
                continue
            if not isinstance(type_var, Var):
                continue
            type_binding = env.dict.get(type_var.name)
            if (
                isinstance(type_binding, TypeBinding)
                and isinstance(type_binding.defn, Union)
            ):
                seen.add(bname)
    return tuple(sorted(seen))


def _case_split_template(name: str, env) -> Optional[str]:
    """Render a switch/cases skeleton for the variable named ``name``.

    Looks up ``name`` in ``env`` by base name (the dict is keyed by
    post-uniquify names like ``foo.42``; the user types the source
    name ``foo``). Dispatches on the binding's kind:

    - ``ProofBinding`` whose formula is ``Or(...)`` -> ``cases``
    - ``TermBinding`` whose type resolves to a ``Union`` -> ``switch``

    Returns ``None`` for any other shape (built-in atom, function,
    non-disjunctive proof, etc.).
    """
    from abstract_syntax import (
        Or, ProofBinding, TermBinding, TypeBinding, Union, Var, base_name,
        get_type_name,
    )

    matches = [k for k in env.dict if base_name(k) == name]
    if not matches:
        return None
    binding = env.dict[matches[0]]

    if isinstance(binding, ProofBinding):
        if isinstance(binding.formula, Or):
            return _cases_template(name, binding.formula, env)
        return None

    if isinstance(binding, TermBinding):
        # The variable's type may be a Var (named type), a TypeInst
        # (parameterised), or built-in (BoolType etc.). Walk to the
        # underlying type definition.
        ty = binding.typ
        try:
            type_var = get_type_name(ty)
        except Exception:
            return None
        if not isinstance(type_var, Var):
            return None
        type_binding = env.dict.get(type_var.name)
        if not isinstance(type_binding, TypeBinding):
            return None
        defn = type_binding.defn
        if isinstance(defn, Union):
            return _switch_template(name, defn, env)
        return None

    return None


def _cases_template(var_name: str, formula, env) -> str:
    """Render a ``cases <var> ...`` block for an ``Or`` formula.

    Each disjunct gets a fresh per-branch label so successive
    refinements inside the cases stay collision-free. The labels
    follow the same ``H<N>`` convention ``_fresh_assume_label`` uses.
    """
    from abstract_syntax import base_name
    used = {base_name(k) for k in env.dict.keys()}

    def fresh() -> str:
        n = 1
        while f"h{n}" in used:
            n += 1
        used.add(f"h{n}")
        return f"h{n}"

    args = formula.args
    case_lines = [
        f"  case {fresh()}: {arg} {{ ? }}" for arg in args
    ]
    return f"cases {var_name}\n" + "\n".join(case_lines)


def _switch_template(var_name: str, union_def, env) -> str:
    """Render a ``switch <var> { ... }`` block for a ``Union`` type.

    Each constructor's parameters get fresh names against the
    *enclosing* env -- but not against names introduced by *other*
    cases, since each ``case Cons(...) { ... }`` opens its own scope.
    Cases are emitted in the declaration order of
    ``union_def.alternatives``.
    """
    from abstract_syntax import base_name

    env_used = {base_name(k) for k in env.dict.keys()}

    case_lines = []
    for alt in union_def.alternatives:
        cons_name = base_name(alt.name)
        # Reset per-case: each case body opens a new scope, so
        # naming conflicts only matter against the enclosing env
        # plus the other params of *this* case.
        used = set(env_used)
        params = []
        # Use the first letter of each param's type as the name stem,
        # mirroring proof_advice/gen_custom_induction_advice.
        for i, p_ty in enumerate(alt.parameters):
            stem = _type_first_letter(p_ty)
            candidate = f"{stem}{i + 1}"
            n = 0
            while candidate in used:
                n += 1
                candidate = f"{stem}{i + 1}_{n}"
            used.add(candidate)
            params.append(candidate)
        if params:
            case_lines.append(
                f"  case {cons_name}({', '.join(params)}) {{ ? }}"
            )
        else:
            case_lines.append(f"  case {cons_name} {{ ? }}")
    return f"switch {var_name} {{\n" + "\n".join(case_lines) + "\n}"


def _type_first_letter(ty) -> str:
    """First letter of a type's printed form, lowercased.

    Mirrors the naming convention in ``proof_advice``: a parameter of
    type ``Nat`` becomes ``n1``, ``n2``, ...; ``List<T>`` -> ``l1``,
    etc. Falls back to ``"x"`` for types whose printer output starts
    with something non-alphabetic.
    """
    s = str(ty)
    for c in s:
        if c.isalpha():
            return c.lower()
    return "x"
