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
from typing import Optional


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


def check(path: str, content: str) -> list[Diagnostic]:
    """Run the full Deduce pipeline on ``content`` (treated as if it
    were the contents of ``path``) and return all diagnostics found.

    An empty list means the file is valid. The current pipeline raises
    on the first error, so today the list will have at most one entry;
    Step 11 (multi-error collection) will lift that limit without
    changing this signature.
    """
    # Imported here, not at module top, so this module stays free of
    # any pipeline import while it is just a stub at module-load time.
    # That keeps the protocol-neutral boundary cheap to enforce.
    from lsp.library import check_file

    result = check_file(path, content=content)
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


def goal_at(path: str, content: str, pos: Position) -> Optional[Goal]:
    """Return the proof obligation visible at ``pos``.

    Returns ``None`` when there is no active proof at that position --
    e.g. the cursor is outside any ``proof ... end`` block, or the file
    does not parse. Implemented by inserting a ``?`` hole at ``pos``
    (more precisely: replacing the content from ``pos`` up to the next
    ``end`` keyword with ``?``) and capturing the goal text the checker
    prints when it reaches the hole.
    """
    from lsp.library import check_file

    modified = _insert_hole(content, pos)
    if modified is None:
        return None

    result = check_file(path, content=modified)
    if result.ok:
        # No PHole was hit -- the surrounding proof was already complete
        # without needing the inserted ?. Nothing to report.
        return None

    return _goal_from_exception(result.exception, pos)


def _insert_hole(content: str, pos: Position) -> Optional[str]:
    """Modify ``content`` so that the proof at ``pos`` halts on a ``?``.

    Strategy: find the byte offset for ``pos``, replace everything from
    there up to (but not including) the next ``end`` keyword with
    ``\\n?\\n``. The intervening tactics are dropped so the parser sees
    a complete proof terminating at the hole.

    Returns ``None`` when ``pos`` is out of range. If no ``end`` keyword
    follows the cursor we fall back to "append ``?`` at the cursor and
    leave the rest" -- the parser may still error, in which case
    ``goal_at`` returns ``None``.
    """
    offset = _line_col_to_offset(content, pos)
    if offset is None:
        return None

    before = content[:offset]
    after = content[offset:]
    m = _END_RE.search(after)
    if m is None:
        return before + "\n?\n" + after
    return before + "\n?\n" + after[m.start():]


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
    path: str, content: str, pos: Position
) -> Optional[Location]:
    """Return the source location of the symbol under ``pos``.

    Returns ``None`` when there is no resolvable symbol at ``pos``
    (whitespace, keyword, unparseable region) or when the definition
    is outside any source file the server can see.

    Implemented in Step 5.
    """
    raise NotImplementedError("Step 5 implements definition_of.")


def list_symbols(path: str, content: str) -> list[SymbolInfo]:
    """Return all top-level declarations in ``content``.

    Used for editor outline views and the MCP ``list_symbols`` tool.
    Includes theorems, lemmas, functions, defines, unions, predicates,
    postulates, and imports; does not descend into nested definitions
    inside proofs.

    Implemented in Step 5.
    """
    raise NotImplementedError("Step 5 implements list_symbols.")
