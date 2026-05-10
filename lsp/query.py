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

import contextlib
import re
import traceback as _traceback
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
    "LemmaInfo",
    "LemmaMatch",
    "HoleContext",
    "ValidationResult",
    "RewritePreview",
    "ExpandPreview",
    # Query functions
    "check",
    "goal_at",
    "definition_of",
    "list_symbols",
    "refine_at",
    "case_split_at",
    "splittable_vars_at",
    "induction_skeleton_at",
    "eliminate_at",
    "eliminable_vars_at",
    "fill_from_given_at",
    "matching_givens_at",
    "hole_context_at",
    "available_lemmas_at",
    "validate_proof_at",
    "preview_replace_at",
    "preview_expand_at",
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


@dataclass(frozen=True)
class LemmaInfo:
    """A theorem, lemma, or postulate visible from a hole site.

    Returned (in tuples) inside :class:`HoleContext`. ``signature`` is
    rendered text -- the same one-line form :func:`list_symbols`
    produces -- so the hole-fill sidecar can drop it into a model
    prompt without re-rendering the AST. ``kind`` distinguishes
    public theorems from module-private lemmas and from postulates.
    """

    name: str
    kind: SymbolKind
    signature: str


@dataclass(frozen=True)
class LemmaMatch:
    """A lemma surfaced by :func:`available_lemmas_at`, with ranking.

    Like :class:`LemmaInfo` but adds the ``module`` of origin (the
    file's stem for the user file, the module name for prelude
    lemmas) and a ``relevance`` score in ``[0.0, 1.0]`` -- ``1.0``
    is the best match in the result set.

    ``kind`` is restricted to ``THEOREM``, ``LEMMA``, or ``POSTULATE``;
    other declaration kinds aren't returned.
    """

    name: str
    kind: SymbolKind
    signature: str
    module: Optional[str]
    relevance: float


@dataclass(frozen=True)
class HoleContext:
    """The proof obligation, hypotheses, and lemmas-in-scope at a hole.

    Returned by :func:`hole_context_at` for the ``?`` token at the
    cursor. The shape extends :class:`Goal` with a list of theorems
    visible from the hole site (for the hole-fill sidecar's prompt)
    and a stable fingerprint over goal and givens so async callers
    can detect that the context has changed by the time they want
    to apply a generated proof.

    ``hole_range`` covers the ``?`` token itself (1-char span);
    ``goal`` and ``givens`` echo :class:`Goal`'s shape; the
    ``lemmas_in_scope`` tuple is empty when ``include_lemmas=False``
    was passed to :func:`hole_context_at`. ``fingerprint`` is a
    hex SHA-256 over a canonical rendering of goal + givens; lemmas
    are deliberately excluded from the fingerprint so that adding a
    new lemma between request and response doesn't invalidate an
    otherwise valid generated proof.
    """

    hole_range: Range
    goal: str
    givens: tuple
    lemmas_in_scope: tuple
    fingerprint: str


@dataclass(frozen=True)
class RewritePreview:
    """Outcome of previewing a ``replace <equation>`` rewrite at a hole.

    Returned by :func:`preview_replace_at`. ``outcome`` is one of:

    - ``"ok"`` -- the rewrite would succeed; ``before`` and ``after``
      are the rendered goal text before and after the rewrite.
    - ``"no_match"`` -- the equation's LHS does not occur in the
      current goal (or an auto-rule has already canonicalized it
      away); ``reason`` is a human-readable explanation.
    - ``"not_an_equation"`` -- the named binding's formula is not an
      ``=``; ``formula`` is the rendered formula text.
    - ``"unbound"`` -- no proof binding by that name is in scope at
      the hole; ``name`` echoes the input.

    Fields not relevant to the chosen ``outcome`` are ``None``.
    """

    outcome: str
    before: Optional[str] = None
    after: Optional[str] = None
    reason: Optional[str] = None
    formula: Optional[str] = None
    name: Optional[str] = None


@dataclass(frozen=True)
class ExpandPreview:
    """Outcome of previewing an ``expand <names>`` unfolding at a hole.

    Returned by :func:`preview_expand_at`. ``outcome`` is one of:

    - ``"ok"`` -- every name unfolded at least once; ``before`` and
      ``after`` are the rendered goal text before and after.
    - ``"no_match"`` -- a name is in scope and expandable but its
      definition has no place to apply in the current goal (often an
      auto-rule canonicalized the call away); ``name`` is the first
      name that produced no change.
    - ``"opaque"`` -- the named binding exists but is opaque from the
      file under check (private/abstracted); ``name`` is that name.
    - ``"unknown"`` -- no term/type binding by that name is in scope;
      ``name`` is that name.

    Fields not relevant to the chosen ``outcome`` are ``None``.
    """

    outcome: str
    before: Optional[str] = None
    after: Optional[str] = None
    name: Optional[str] = None


@dataclass(frozen=True)
class ValidationResult:
    """Outcome of splicing a candidate proof into a hole and rechecking.

    Returned by :func:`validate_proof_at`. ``ok`` is ``True`` iff the
    spliced source checks. ``error`` carries the checker's message
    (location + body, the same text ``deduce.py`` would print) on
    failure; ``None`` when ``ok`` is ``True``.

    Callers that want a structured error -- a location plus the
    diagnostic body -- should use :func:`check` on the spliced source
    instead. For the hole-fill sidecar a plain string is enough; the
    LLM doesn't need a parsed range.
    """

    ok: bool
    error: Optional[str] = None


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

    An empty list means the file is valid. With Step 11 (multi-error
    collection) this returns one ``Diagnostic`` per top-level
    statement that fails, plus one per ``?`` hole — so editors paint
    every error and incomplete proof in the buffer instead of just
    the first.

    Recovery boundary is the top-level statement, so an error inside
    one theorem doesn't suppress the diagnostic for an unrelated
    theorem later in the file. Cascading errors (a downstream stmt
    that depended on a broken decl) are reported too: usually they
    point at a real follow-on problem the user wants to see, and
    suppressing them risks hiding errors.

    A parse / uniquify failure still short-circuits the run — the
    pipeline can't produce a partial AST in those cases, so the result
    is always one diagnostic for the parse error.

    ``prelude`` is the list of module names auto-imported in front of
    the file (matching ``deduce.py``'s ``--no-stdlib`` flag: empty by
    default; the MCP / LSP server passes the standard library here).
    """
    # Imported here, not at module top, so this module stays free of
    # any pipeline import while it is just a stub at module-load time.
    # That keeps the protocol-neutral boundary cheap to enforce.
    from lsp.library import check_file

    result = check_file(path, content=content, prelude=prelude, collect_errors=True)
    if result.ok:
        return []

    if result.errors:
        return [
            _diagnostic_from_exception(exc, str_fallback=str(exc))
            for exc in result.errors
        ]
    # Fallback: parse/uniquify failure (raised before check_deduce
    # ever ran, so the sink stayed empty). Single-diagnostic path.
    return [_diagnostic_from_exception(result.exception, str_fallback=result.error_message)]


def _diagnostic_from_exception(
    exc: Optional[BaseException], str_fallback: Optional[str]
) -> Diagnostic:
    """Build a Diagnostic from an exception raised by the pipeline.

    Reads ``exc.location`` and ``exc.message_body`` if present
    (attached by ``error.py`` for all error/incomplete/static/match/
    parse errors). When the exception is unstructured -- a Python
    exception that escaped the checker without being wrapped as a
    Deduce error, almost always a bug in Deduce itself -- the
    diagnostic message includes the formatted traceback so the user
    reporting the bug knows which frame raised, instead of seeing a
    bare ``name 'X' is not defined`` at the sentinel position.

    For ``IncompleteProof``, the message is replaced with a clean
    ``Goal: ... \\n Givens: ...`` block formatted to match
    :func:`goal_at`'s output (2-space indent, no advice text). The
    raw checker message includes "Advice:" sections that are useful
    in CLI output but noisy as an editor diagnostic. Detection: the
    PHole site stashes ``formula`` and ``env`` on the exception
    (Step 15 plumbing); presence of ``formula`` is the signal that
    we have an IncompleteProof shaped for this re-render.
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

    formula = getattr(exc, "formula", None)
    if formula is not None:
        body = _format_incomplete_proof_message(formula)
    else:
        body = getattr(exc, "message_body", None)
        if body is None:
            body = _format_unstructured_exception(exc, str_fallback)

    return Diagnostic(severity=Severity.ERROR, range=rng, message=body)


def _format_unstructured_exception(
    exc: BaseException, str_fallback: Optional[str]
) -> str:
    """Format an unstructured exception with its traceback.

    The pipeline catches ``Diagnostic`` subclasses (``UserError``,
    ``IncompleteProof``, ``StaticError``) and decorates them with
    ``location`` / ``message_body``. Anything else -- ``NameError``,
    ``AttributeError``, an unexpected ``KeyError``, etc. -- is a bug
    in Deduce. Without the traceback the user only sees ``str(exc)``
    pinned to line 1, column 1, which is useless for filing a report.
    """
    msg = str_fallback if str_fallback is not None else str(exc)
    tb = exc.__traceback__
    if tb is not None:
        formatted = "".join(_traceback.format_exception(type(exc), exc, tb))
        return f"internal error in Deduce: {msg}\n\n{formatted}"
    return f"internal error in Deduce: {msg}"


def _format_incomplete_proof_message(formula) -> str:
    """Render an ``IncompleteProof`` as a one-line diagnostic.

    LSP diagnostic messages land in space-constrained UI: the echo
    area, the mode-line, the underline tooltip. Multi-line text
    truncates badly (often to just the first line). A goal/givens
    *display* belongs in :func:`goal_at`'s ``*Deduce Goal*`` buffer
    instead -- the editor binding (`C-c C-g`) is one keystroke away
    and gets the full structured view.

    The diagnostic itself just signals "this `?` needs filling, and
    here's what type of thing": the literal phrase ``incomplete
    proof`` (matching the CLI prefix for continuity) plus the goal
    formula. Givens are deliberately omitted -- they'd push the
    line past one screen width on most proofs, and the user has
    `C-c C-g` for them.
    """
    return f"incomplete proof; goal: {formula}"


def goal_at(
    path: str, content: str, pos: Position, prelude: Sequence[str] = ()
) -> Optional[Goal]:
    """Return the proof obligation visible at ``pos``.

    Returns ``None`` when there is no active proof at that position --
    e.g. the cursor is outside any ``proof ... end`` block, or the file
    does not parse.

    When the cursor sits on or immediately adjacent to a ``?`` already
    present in the source, that hole IS the goal site and we run
    ``check`` on the original content -- the existing ``?`` raises
    ``IncompleteProof`` and we read the goal off the exception. The
    returned ``Goal.range`` covers exactly the ``?`` token (1-char
    span), matching what :func:`refine_at` and :func:`case_split_at`
    return.

    Otherwise we insert a synthetic ``?`` at the cursor (truncating
    forward to the enclosing block end) and capture the goal text the
    checker prints when it reaches that hole. The returned
    ``Goal.range`` is then a degenerate range at the cursor.

    ``prelude`` matches the meaning in :func:`check`.
    """
    from lsp.library import check_file

    # Cursor on (or just past) an existing `?`?  Don't insert a
    # second one -- `_insert_hole` would emit `?\n?` which the parser
    # rejects (issue #341).
    existing_hole = _find_hole_at(content, pos)
    if existing_hole is not None:
        modified = content
        goal_range = existing_hole
        target = (existing_hole.start.line, existing_hole.start.column)
    else:
        inserted = _insert_hole(content, pos)
        if inserted is None:
            return None
        modified, hole_pos = inserted
        goal_range = Range(start=pos, end=pos)
        target = (hole_pos.line, hole_pos.column)

    with _target_hole(target):
        result = check_file(path, content=modified, prelude=prelude)
    if result.ok:
        # No PHole was hit -- the surrounding proof was already complete
        # without needing the inserted ?. Nothing to report.
        return None

    return _goal_from_exception(result.exception, goal_range)


def _insert_hole(content: str, pos: Position) -> Optional[tuple]:
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

    Returns ``None`` when ``pos`` is out of range. Otherwise returns a
    tuple ``(modified, hole_pos)`` where ``hole_pos`` is the 1-indexed
    ``Position`` of the inserted ``?`` in ``modified`` -- callers use
    this to target that specific hole when running the proof checker.
    If no closer is found we append ``?`` at the cursor and leave the
    rest -- the parser may still error, in which case ``goal_at``
    returns ``None``.
    """
    offset = _line_col_to_offset(content, pos)
    if offset is None:
        return None

    before = content[:offset]
    after = content[offset:]
    cut = _find_block_end(after)
    if cut is None:
        modified = before + "\n?\n" + after
    else:
        modified = before + "\n?\n" + after[cut:]
    # The inserted `?` sits at offset len(before) + 1 (after the
    # leading "\n") in `modified`.
    line, col = _offset_to_line_col(modified, len(before) + 1)
    return (modified, Position(line=line, column=col))


@contextlib.contextmanager
def _target_hole(loc):
    """Tell the proof checker to raise IncompleteProof only at ``loc``.

    ``loc`` is a (line, column) tuple matching the hole's lark
    ``Meta`` location. While the context is active, every other ``?``
    the checker encounters is treated as a successful proof of its
    goal, so the checker can keep going and reach the targeted hole
    in a multi-hole file. See ``flags.target_hole_location`` and the
    ``PHole`` arm of ``check_proof_of`` in ``proof_checker.py``.
    """
    import flags

    prev = flags.get_target_hole_location()
    flags.set_target_hole_location(loc)
    try:
        yield
    finally:
        flags.set_target_hole_location(prev)


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
    exc: Optional[BaseException], goal_range: Range
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

    ``goal_range`` is the source range to attach to the returned
    :class:`Goal` -- typically the 1-char span of an existing ``?``
    token, or a degenerate range at the cursor when ``goal_at``
    inserted a synthetic hole.

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
    return Goal(formula=formula, givens=givens, range=goal_range)


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

    target_name = _find_reference_at(result.ast, pos, path)
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


def _find_reference_at(ast_nodes, pos: Position, path: str) -> Optional[str]:
    """Locate the smallest reference node whose range contains ``pos``.

    Recognises term references (``Var``, with overload resolution via
    ``resolved_names[0]``) and proof references (``PVar``, whose
    ``name`` is already the chosen uniquified name post-uniquify).
    "Smallest" means the deepest match in the AST -- inner refs take
    precedence over enclosing constructs that happen to share a range.

    Only considers nodes whose ``location.filename`` matches ``path``.
    The post-typecheck AST is threaded with references back into
    imported library files (constructors, types, overload candidates),
    and those nodes carry the *library* file's line/column. Without
    this filter, a cursor in the user's file can spuriously match a
    library node whose range happens to overlap the same coordinates.

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
        if not _meta_in_file(meta, path):
            return
        span = _meta_span(meta)
        if best_span[0] is None or span < best_span[0]:
            best_span[0] = span
            best[0] = resolved

    for top in ast_nodes:
        _walk_ast(top, visit, ast_class=AST)

    return best[0]


def _meta_in_file(meta, path: str) -> bool:
    """True iff ``meta``'s source file is ``path``.

    Compares the ``filename`` attribute the parsers stash on each
    ``Meta`` against ``path``. We accept a match when either the raw
    strings are equal or the resolved absolute paths agree, so a
    relative ``path`` from the caller still matches an absolute
    ``meta.filename`` from the parser (and vice versa). When neither
    side has a filename, fall back to permissive behaviour -- the
    pre-prelude code path didn't filter at all.
    """
    import os

    fname = getattr(meta, "filename", None)
    if fname is None or fname == "???":
        # No reliable file info on this node. Don't reject -- some
        # synthetic nodes never get a filename, and rejecting them
        # outright would regress same-file lookups.
        return True
    if fname == path:
        return True
    try:
        return os.path.realpath(fname) == os.path.realpath(path)
    except (OSError, ValueError):
        return False


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
# Multi-hole files: ``_target_hole`` (above) tells the checker to skip
# every ``?`` whose location doesn't match the cursor's hole, so the
# goal/env we read here is the one at the cursor specifically -- not
# whichever hole happens to come first in source order.


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

    target = (hole_range.start.line, hole_range.start.column)
    with _target_hole(target):
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
        All, And, Bool, Call, IfThen, Some, VarRef, base_name,
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
        # Match the equality operator at any stage of name resolution
        # (`Var', `OverloadedVar', or `ResolvedVar' all subclass
        # `VarRef').  Mirrors the dispatch in `proof_checker.py'
        # `PReflexive' after the Var/ResolvedVar split (PR #330).
        case Call(_, _, rator, [lhs, rhs]) if (
            isinstance(rator, VarRef)
            and rator.get_name() == "="
            and env is not None
        ):
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

    target = (hole_range.start.line, hole_range.start.column)
    with _target_hole(target):
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

    target = (hole_range.start.line, hole_range.start.column)
    with _target_hole(target):
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
        Or, ProofBinding, TermBinding, TypeBinding, Union, VarRef, base_name,
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
            # Match any name-resolution stage: pre-uniquify ``Var',
            # post-uniquify ``OverloadedVar', or post-typecheck
            # ``ResolvedVar' -- all subclass ``VarRef'.  Pre-#330
            # this used ``isinstance(type_var, Var)' which only
            # caught the pre-uniquify form and silently dropped the
            # rest.
            if not isinstance(type_var, VarRef):
                continue
            type_binding = env.dict.get(type_var.get_name())
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
        Or, ProofBinding, TermBinding, TypeBinding, Union, VarRef, base_name,
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
        # The variable's type may be a VarRef (named type), a TypeInst
        # (parameterised), or built-in (BoolType etc.). Walk to the
        # underlying type definition. ``VarRef'' covers pre-uniquify
        # ``Var'', post-uniquify ``OverloadedVar'', and post-typecheck
        # ``ResolvedVar'' (issue: PR #330 split these classes).
        ty = binding.typ
        try:
            type_var = get_type_name(ty)
        except Exception:
            return None
        if not isinstance(type_var, VarRef):
            return None
        type_binding = env.dict.get(type_var.get_name())
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


# ---------------------------------------------------------------------------
# induction_skeleton_at -- Phase 4 / Step 17: induction over the goal
# ---------------------------------------------------------------------------
#
# Distinct from Step 16 (case split) in three ways:
#
# - It operates on the *goal* (an `all x:T. P(x)` quantifier) rather
#   than a named variable.  No `variable' parameter; the cursor on a
#   `?' is the only input.
# - The skeleton uses Deduce's `induction' keyword instead of `switch'
#   / `cases'.
# - For recursive constructor parameters (those of the union's own
#   type), each case gets `assume IH<N>: <body>[var := param]'
#   bindings -- the inductive hypothesis(es).
#
# Reuses the Step 15 plumbing: the cursor's `?' raises
# ``IncompleteProof'' and we read the goal AST + env off the
# exception.  Same single-theorem caveat as the rest of Phase 4.


def induction_skeleton_at(
    path: str, content: str, pos: Position, prelude: Sequence[str] = ()
) -> Optional[WorkspaceEdit]:
    """Generate an ``induction T`` skeleton for the goal at ``pos``.

    The cursor must sit on (or immediately adjacent to) a ``?`` token
    whose goal has the shape ``all x:T. P(x)`` where ``T`` is a Union
    with at least two alternatives.  The skeleton emits one
    ``case <Cons>(<params>) [assume IH<N>: ...] { ? }`` per
    constructor, in declaration order.  Recursive parameters (those
    of type ``T``) introduce ``IH<N>`` bindings whose formula is the
    goal body with the inducted variable substituted.

    Returns ``None`` when:

    - the cursor isn't on a ``?``,
    - the file doesn't reach an incomplete proof there,
    - the goal isn't a single ``all`` over a Union, or
    - the union has fewer than 2 alternatives (no induction to do).
    """
    hole_range = _find_hole_at(content, pos)
    if hole_range is None:
        return None

    from lsp.library import check_file

    target = (hole_range.start.line, hole_range.start.column)
    with _target_hole(target):
        result = check_file(path, content=content, prelude=prelude)
    if result.ok:
        return None

    exc = result.exception
    formula = getattr(exc, "formula", None)
    env = getattr(exc, "env", None)
    if formula is None or env is None:
        return None

    template = _induction_template(formula, env)
    if template is None:
        return None

    template = _indent_continuation(
        template, _line_indent_at(content, hole_range.start)
    )
    return WorkspaceEdit(path=path, range=hole_range, new_text=template)


def _induction_template(formula, env) -> Optional[str]:
    """Render an ``induction T`` skeleton if ``formula`` is
    ``all x:T. P(x)`` with T a multi-alternative union."""
    from abstract_syntax import (
        All, TypeBinding, Union, VarRef, base_name, get_type_name,
    )

    if not isinstance(formula, All):
        return None
    var_x, var_ty = formula.var
    body = formula.body

    try:
        type_var = get_type_name(var_ty)
    except Exception:
        return None
    if not isinstance(type_var, VarRef):
        return None
    type_binding = env.dict.get(type_var.get_name())
    if not isinstance(type_binding, TypeBinding):
        return None
    union_def = type_binding.defn
    if not isinstance(union_def, Union):
        return None
    if len(union_def.alternatives) < 2:
        # `induction' requires at least two alternatives -- otherwise
        # it'd just be a no-op / direct proof.
        return None

    return _render_induction(var_x, var_ty, body, union_def, env)


def _render_induction(var_x, var_ty, body, union_def, env) -> str:
    """Build the ``induction T\\n  case ... { ? }\\n  ...`` text."""
    from abstract_syntax import ResolvedVar, base_name
    # `is_recursive' and `update_all_head' live in proof_checker;
    # they're pipeline-side helpers, not protocol-specific, so the
    # protocol-neutrality guard in this module's docstring isn't
    # broken by importing them.
    from proof_checker import is_recursive, update_all_head

    union_name = union_def.name  # uniquified, e.g. ``N.0''
    env_used = {base_name(k) for k in env.dict.keys()}

    case_lines = []
    for alt in union_def.alternatives:
        cons_name = base_name(alt.name)
        used = set(env_used)
        params = []  # list of (name, type) pairs for this case
        for i, p_ty in enumerate(alt.parameters):
            stem = _type_first_letter(p_ty)
            candidate = f"{stem}{i + 1}"
            n = 0
            while candidate in used:
                n += 1
                candidate = f"{stem}{i + 1}_{n}"
            used.add(candidate)
            params.append((candidate, p_ty))

        if params:
            line = (
                f"  case {cons_name}("
                + ", ".join(p for p, _ in params)
                + ")"
            )
        else:
            line = f"  case {cons_name}"

        # Recursive params -> IH bindings.
        rec_params = [
            (p, ty) for (p, ty) in params if is_recursive(union_name, ty)
        ]
        if rec_params:
            ih_clauses = []
            for i, (p, p_ty) in enumerate(rec_params):
                ih_var = ResolvedVar(p_ty.location, p_ty, p)
                ih_body = update_all_head(body.substitute({var_x: ih_var}))
                ih_clauses.append(f"IH{i + 1}: {ih_body}")
            line += " assume " + ", ".join(ih_clauses)

        line += " { ? }"
        case_lines.append(line)

    return f"induction {var_ty}\n" + "\n".join(case_lines)


# ---------------------------------------------------------------------------
# eliminate_at -- Phase 4 / Step 18: use-fact / hypothesis elimination
# ---------------------------------------------------------------------------
#
# Dual to Step 15 (refine).  Step 15 picks a template based on the
# *goal* shape (introduction); Step 18 picks based on a named
# *hypothesis* shape (elimination).
#
# UX shape: cursor on a `?', plus an explicit ``label'' argument
# naming the in-scope proof binding to use.  Same wire/transport
# pattern as Step 16 (case split): the editor binding fetches
# candidate labels via ``eliminable_vars_at'' and prompts via
# ``completing-read'' before issuing ``deduce/eliminateAt''.
#
# Templates by hypothesis shape (mirrors ``proof_use_advice'' in
# proof_checker.py):
#
# - ``H: true''         -> None ("the `true' fact is useless")
# - ``H: false''        -> ``H'' (discharges any goal)
# - ``H: P and Q''      -> ``have h1: P by conjunct 1 of H\nhave
#                            h2: Q by conjunct 2 of H\n?''
# - ``H: P or Q''       -> ``cases H\n  case h1: P { ? }\n
#                            case h2: Q { ? }''
# - ``H: if P then Q''  -> ``have h: Q by apply H to ?\n?''
# - ``H: all x:T. P''   -> ``H[?, ?, ...]'' (or ``H<?, ?, ...>''
#                            for type-arg quantifiers)
# - ``H: some x:T. P''  -> ``obtain x1, ... where h: <body[subst]>
#                            from H\n?''
# - ``H: e1 = e2''      -> ``replace H\n?''


def eliminate_at(
    path: str, content: str, pos: Position,
    label: str,
    prelude: Sequence[str] = (),
) -> Optional[WorkspaceEdit]:
    """Generate a tactic that uses ``label'' to derive a new fact
    or to discharge the goal at the hole at ``pos``.

    The cursor must sit on (or immediately adjacent to) a ``?`` token;
    that ``?`` is the replacement target. ``label`` names an in-scope
    proof binding (a hypothesis introduced by ``assume`` or a
    theorem/lemma reference). The template is chosen from the
    binding's formula shape -- see the table at the top of this
    section.

    Returns ``None`` when:

    - the cursor isn't on a ``?``,
    - the file has no incomplete proof at the cursor,
    - ``label`` isn't bound at the hole, or
    - the binding's shape isn't in the supported template table
      (e.g. ``H: true`` -- usability nil).

    For client-side completion of valid ``label`` choices, see
    :func:`eliminable_vars_at`.
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

    template = _eliminate_template(label, env)
    if template is None:
        return None

    template = _indent_continuation(
        template, _line_indent_at(content, hole_range.start)
    )
    return WorkspaceEdit(path=path, range=hole_range, new_text=template)


def eliminable_vars_at(
    path: str, content: str, pos: Position, prelude: Sequence[str] = ()
) -> tuple:
    """Return base names of in-scope proof bindings that
    ``eliminate_at'' can target.

    Used by editor clients to populate completion candidates for the
    ``Eliminate on:'' prompt.  Includes labels for local hypotheses
    (introduced by ``assume''/``suppose''/``have'') whose formula
    matches one of the supported template shapes.  ``true''-shaped
    facts are filtered out (no useful template) but everything else
    is included; the client gets a wider candidate list at the cost
    of the rare "Eliminate produced no edit" round-trip.

    Empty when the cursor isn't on a ``?`` or no eliminable binding
    is in scope.  Names are sorted and deduplicated.
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

    return _eliminable_vars(env)


def _eliminable_vars(env) -> tuple:
    """Names of local proof bindings whose ``eliminate'' would
    produce a meaningful edit."""
    from abstract_syntax import (
        Bool, ProofBinding, base_name,
    )

    seen = set()
    for unique, binding in env.dict.items():
        bname = base_name(unique)
        if bname in seen:
            continue
        if not isinstance(binding, ProofBinding):
            continue
        if not binding.local:
            # Skip theorem references: they're not what users mean
            # when they say "eliminate <label>".  Theorems are
            # invoked by name without completion in any case.
            continue
        formula = binding.formula
        # `true' is the one shape we filter out -- there's no
        # useful template for "use the `true' fact".
        if isinstance(formula, Bool) and formula.value is True:
            continue
        if _eliminate_template_for_formula(formula, binding_name=bname,
                                           env=env, dry_run=True) is None:
            continue
        seen.add(bname)
    return tuple(sorted(seen))


def _eliminate_template(label: str, env) -> Optional[str]:
    """Look up ``label'' in ``env'' and dispatch to the appropriate
    template.

    Returns ``None'' when the label isn't bound, isn't a proof
    binding, or its formula's shape isn't in the supported table.
    """
    from abstract_syntax import ProofBinding, base_name

    matches = [k for k in env.dict if base_name(k) == label]
    if not matches:
        return None
    binding = env.dict[matches[0]]
    if not isinstance(binding, ProofBinding):
        return None
    return _eliminate_template_for_formula(
        binding.formula, binding_name=label, env=env, dry_run=False,
    )


def _eliminate_template_for_formula(
    formula, binding_name: str, env, dry_run: bool
) -> Optional[str]:
    """Pick a template for ``formula''.

    ``binding_name'' is the user-facing name of the hypothesis (e.g.
    ``H1''); it appears in the rendered template.  ``dry_run'' is
    set by ``_eliminable_vars'' to detect "is there a template?"
    without paying the rendering cost; in that mode we just return
    a non-None sentinel string when the shape is supported.
    """
    from abstract_syntax import (
        All, And, Bool, Call, IfThen, Or, ResolvedVar, Some, TypeType,
        VarRef, base_name,
    )

    if isinstance(formula, Bool):
        if formula.value is True:
            return None
        # `false' discharges any goal: replace ? with the label.
        return binding_name

    if isinstance(formula, And):
        if dry_run:
            return "and"
        return _eliminate_and(binding_name, formula, env)

    if isinstance(formula, Or):
        if dry_run:
            return "or"
        return _eliminate_or(binding_name, formula, env)

    if isinstance(formula, IfThen):
        if dry_run:
            return "if"
        return _eliminate_ifthen(binding_name, formula, env)

    if isinstance(formula, All):
        if dry_run:
            return "all"
        return _eliminate_all(binding_name, formula, env)

    if isinstance(formula, Some):
        if dry_run:
            return "some"
        return _eliminate_some(binding_name, formula, env)

    if (
        isinstance(formula, Call)
        and isinstance(formula.rator, VarRef)
        and formula.rator.get_name() == "="
        and len(formula.args) == 2
    ):
        if dry_run:
            return "eq"
        return f"replace {binding_name}\n?"

    return None


def _fresh_h_labels(env, count: int) -> list:
    """Generate ``count`` fresh ``H<N>``-style labels not in env."""
    from abstract_syntax import base_name
    used = {base_name(k) for k in env.dict.keys()}
    out = []
    n = 1
    for _ in range(count):
        while f"H{n}" in used:
            n += 1
        out.append(f"H{n}")
        used.add(f"H{n}")
        n += 1
    return out


def _eliminate_and(label: str, formula, env) -> str:
    """``have h1: P by conjunct 1 of H\\nhave h2: Q by conjunct 2
    of H\\n?''"""
    labels = _fresh_h_labels(env, len(formula.args))
    lines = [
        f"have {h}: {arg} by conjunct {i + 1} of {label}"
        for i, (h, arg) in enumerate(zip(labels, formula.args))
    ]
    lines.append("?")
    return "\n".join(lines)


def _eliminate_or(label: str, formula, env) -> str:
    """``cases H\\n  case h1: P { ? }\\n  case h2: Q { ? } ...''"""
    from abstract_syntax import base_name

    used = {base_name(k) for k in env.dict.keys()}

    def fresh_lower() -> str:
        n = 1
        while f"h{n}" in used:
            n += 1
        used.add(f"h{n}")
        return f"h{n}"

    case_lines = [
        f"  case {fresh_lower()}: {arg} {{ ? }}" for arg in formula.args
    ]
    return f"cases {label}\n" + "\n".join(case_lines)


def _eliminate_ifthen(label: str, formula, env) -> str:
    """``have h: Q by apply H to ?\\n?''"""
    h = _fresh_h_labels(env, 1)[0]
    return f"have {h}: {formula.conclusion} by apply {label} to ?\n?"


def _eliminate_all(label: str, formula, env) -> str:
    """``H[?, ?, ...]'' (term args) or ``H<?, ?, ...>'' (type args).

    Handles a single all-block: ``all x:T1, y:T2. P'' yields
    ``H[?, ?]''.  Separate blocks (``all x:T1. all y:T2. P'')
    instantiate one at a time -- the user can chain.
    """
    from abstract_syntax import All, TypeType

    vars_in_block = []
    cur = formula
    while isinstance(cur, All):
        x, ty = cur.var
        vars_in_block.append((x, ty))
        s, e = cur.pos
        if s == 0:
            # Last var in this block; following body is no longer an
            # All-of-the-same-block.
            break
        cur = cur.body

    if not vars_in_block:
        return f"{label}[?]"

    has_type_param = any(isinstance(ty, TypeType) for _, ty in vars_in_block)
    open_b, close_b = ("<", ">") if has_type_param else ("[", "]")
    placeholders = ", ".join(["?"] * len(vars_in_block))
    return f"{label}{open_b}{placeholders}{close_b}"


def _eliminate_some(label: str, formula, env) -> str:
    """``obtain x1, ... where h: <body[subst]> from H\\n?''"""
    from abstract_syntax import ResolvedVar, base_name

    used = {base_name(k) for k in env.dict.keys()}
    fresh_witnesses = []
    sub = {}
    for (x, ty) in formula.vars:
        stem = _type_first_letter(ty)
        n = 1
        while f"{stem}{n}" in used:
            n += 1
        candidate = f"{stem}{n}"
        used.add(candidate)
        fresh_witnesses.append(candidate)
        sub[x] = ResolvedVar(ty.location, ty, candidate)

    new_body = formula.body.substitute(sub)

    h = None
    n = 1
    while f"H{n}" in used:
        n += 1
    h = f"H{n}"
    used.add(h)

    return (
        f"obtain {', '.join(fresh_witnesses)} where "
        f"{h}: {new_body} from {label}\n?"
    )


# ---------------------------------------------------------------------------
# fill_from_given_at -- issue #353: fill a hole with a matching given
# ---------------------------------------------------------------------------
#
# Sibling of ``eliminate_at''.  Where ``eliminate_at'' picks a template
# from the *shape* of a named hypothesis, ``fill_from_given_at'' picks
# by formula *equality*: the chosen given's formula must equal the goal,
# and the replacement is just ``conclude <goal> by <label>'' -- the same
# advice ``proof_advice'' in proof_checker.py emits when an exact match
# is in scope.
#
# The proof checker already does this matching internally (see
# proof_checker.py around line 893: it walks env.dict for ProofBindings
# whose formula equals the goal and offers a `conclude ... by ...'
# completion).  The LSP just surfaces it as an editor command.
#
# UX shape mirrors ``eliminate_at'': the editor binding fetches
# candidate labels via ``matching_givens_at'' and prompts via
# ``completing-read'' before issuing ``deduce/fillFromGivenAt''.


def fill_from_given_at(
    path: str, content: str, pos: Position,
    label: str,
    prelude: Sequence[str] = (),
) -> Optional[WorkspaceEdit]:
    """Fill the hole at ``pos`` with ``conclude <goal> by <label>``.

    The cursor must sit on (or immediately adjacent to) a ``?`` token;
    that ``?`` is the replacement target.  ``label`` names an in-scope
    local proof binding whose formula equals the goal at the hole.

    Returns ``None`` when:

    - the cursor isn't on a ``?``,
    - the file has no incomplete proof at the cursor,
    - ``label`` isn't bound at the hole,
    - the bound formula doesn't equal the goal, or
    - the bound formula isn't local (theorems are referred to by name
      directly, not via this command).

    For client-side completion of valid ``label`` choices, see
    :func:`matching_givens_at`.
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
    goal = getattr(exc, "formula", None)
    if env is None or goal is None:
        return None

    template = _fill_from_given_template(label, goal, env)
    if template is None:
        return None

    template = _indent_continuation(
        template, _line_indent_at(content, hole_range.start)
    )
    return WorkspaceEdit(path=path, range=hole_range, new_text=template)


def matching_givens_at(
    path: str, content: str, pos: Position, prelude: Sequence[str] = ()
) -> tuple:
    """Return base names of in-scope local proof bindings whose
    formula equals the goal at the hole at ``pos``.

    Used by editor clients to populate completion candidates for the
    ``Fill from given:'' prompt.  Empty when the cursor isn't on a
    ``?``, the goal AST isn't available, or no local binding matches.
    Names are sorted and deduplicated.
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
    goal = getattr(exc, "formula", None)
    if env is None or goal is None:
        return ()

    return _matching_given_names(goal, env)


def _matching_given_names(goal, env) -> tuple:
    """Names of local proof bindings whose formula equals ``goal``."""
    from abstract_syntax import ProofBinding, base_name

    seen = set()
    for unique, binding in env.dict.items():
        if not isinstance(binding, ProofBinding):
            continue
        if not binding.local:
            continue
        if binding.formula != goal:
            continue
        seen.add(base_name(unique))
    return tuple(sorted(seen))


def _fill_from_given_template(label: str, goal, env) -> Optional[str]:
    """Return ``conclude <goal> by <label>`` when ``label`` names a
    local proof binding in ``env`` whose formula equals ``goal``.

    Returns ``None`` when the label isn't bound, isn't a local proof
    binding, or its formula doesn't match the goal.  The base-name
    match (rather than unique-name) mirrors :func:`_eliminate_template`.
    """
    from abstract_syntax import ProofBinding, base_name

    matches = [k for k in env.dict if base_name(k) == label]
    if not matches:
        return None
    binding = env.dict[matches[0]]
    if not isinstance(binding, ProofBinding):
        return None
    if not binding.local:
        return None
    if binding.formula != goal:
        return None
    return f"conclude {goal} by {label}"


# ---------------------------------------------------------------------------
# hole_context_at -- Phase 5 / Step 1: rich context for the hole-fill sidecar
# ---------------------------------------------------------------------------
#
# Sibling to ``goal_at``: returns goal + givens for the cursor's hole,
# plus a list of theorems/lemmas/postulates visible at that hole (so
# the hole-fill sidecar can include them in the model prompt) and a
# stable fingerprint over goal+givens (so async callers can detect
# that the context has changed by the time a generated proof comes
# back). See docs/hole-fill-plan.md.


def hole_context_at(
    path: str,
    content: str,
    pos: Position,
    prelude: Sequence[str] = (),
    include_lemmas: bool = True,
) -> Optional[HoleContext]:
    """Return rich context for the ``?`` hole at ``pos``.

    Unlike :func:`goal_at`, this function does **not** synthesise a
    hole when the cursor is not on one; it returns ``None`` instead.
    The hole-fill sidecar only ever fires on an existing ``?``.

    The cursor must sit on (or one column past) a ``?`` token; uses
    the same per-cursor hole targeting machinery as :func:`refine_at`.
    Returns ``None`` when:

    - the cursor is not on a ``?``,
    - the file does not parse,
    - the targeted hole isn't reached by the checker (e.g. an earlier
      error short-circuits before ever hitting it),
    - the surfaced exception is not an ``IncompleteProof``-shaped one.

    ``include_lemmas`` toggles the lemma list. When ``False``, the
    returned ``HoleContext`` has ``lemmas_in_scope=()``. The lemma
    list is computed from the user's file (top-level theorems,
    lemmas, and postulates from ``content``) plus all prelude
    modules' uniquified ASTs -- not strictly scope-aware (a theorem
    defined later in the file is still surfaced), but a good
    approximation for the hole-fill prompt.

    The fingerprint is hex SHA-256 over ``goal + "\\n" + sorted
    "label: formula" lines``. Lemmas are deliberately excluded so
    that adding a new lemma between request and response doesn't
    invalidate an otherwise valid generated proof.
    """
    hole_range = _find_hole_at(content, pos)
    if hole_range is None:
        return None

    from lsp.library import check_file

    target = (hole_range.start.line, hole_range.start.column)
    with _target_hole(target):
        result = check_file(path, content=content, prelude=prelude)
    if result.ok:
        return None

    goal = _goal_from_exception(result.exception, hole_range)
    if goal is None:
        return None

    if include_lemmas:
        lemmas = _collect_lemmas_in_scope(result.ast, prelude)
    else:
        lemmas = ()

    fingerprint = _hole_fingerprint(goal.formula, goal.givens)
    return HoleContext(
        hole_range=hole_range,
        goal=goal.formula,
        givens=goal.givens,
        lemmas_in_scope=lemmas,
        fingerprint=fingerprint,
    )


def _collect_lemmas_in_scope(ast_nodes, prelude: Sequence[str]) -> tuple:
    """Build the ``lemmas_in_scope`` tuple for :class:`HoleContext`.

    Walks two sources of top-level declarations:

    - ``ast_nodes`` -- the user file's post-typecheck AST. Skips the
      auto-prepended prelude ``Import`` nodes (they're not real
      declarations, just pointers). All declarations from the user's
      file are surfaced (including private ``lemma``s and
      private-visibility declarations) since they are in scope at
      the hole.
    - ``get_uniquified_modules()`` -- the post-uniquify ASTs of every
      module imported into the pipeline. We pull from each module
      named in ``prelude``, applying the same visibility filter as
      ``print_theorems_statement`` (only public declarations -- the
      same set that ends up in ``.thm`` files).

    Surfaces theorems, postulates, ``auto`` rules, and the full
    pretty-printed source of functions / defines / unions /
    predicates -- the same content the .thm files carry. The model
    sees, for each function, its full pattern-matching body, which
    is what teaches it how to ``expand`` calls correctly.

    Order is: user-file declarations first (in source order), then
    prelude declarations (grouped by module name in ``prelude`` order,
    in source order within each module). Duplicates are not deduped.
    """
    from abstract_syntax import (
        Import as _ImportNode,
        get_uniquified_modules,
    )

    out: list[LemmaInfo] = []

    if ast_nodes is not None:
        prelude_set = set(prelude)
        for stmt in ast_nodes:
            if isinstance(stmt, _ImportNode) and stmt.name in prelude_set:
                continue
            info = _lemma_info_for(stmt, public_only=False)
            if info is not None:
                out.append(info)

    if prelude:
        modules = get_uniquified_modules()
        for module_name in prelude:
            module_ast = modules.get(module_name)
            if module_ast is None:
                continue
            for stmt in module_ast:
                info = _lemma_info_for(stmt, public_only=True)
                if info is not None:
                    out.append(info)

    return tuple(out)


def _lemma_info_for(stmt, public_only: bool = False) -> Optional[LemmaInfo]:
    """Build a :class:`LemmaInfo` from a top-level statement, or
    ``None`` if the node isn't surfaced (``Import``, etc.).

    The ``signature`` field carries the pretty-printed declaration
    in the same format as ``.thm`` files (see
    ``abstract_syntax.print_theorems_statement``):

      - Theorems / lemmas / postulates: ``name: formula``
      - Auto rules: ``auto NAME``
      - Functions / defines / unions / predicates: full
        ``pretty_print(0)`` source, including the body

    Multi-line for declarations with bodies; that's by design --
    the model needs to see the function body to know how
    ``expand fn`` will rewrite a call.

    When ``public_only`` is set, private theorems (``lemma``) and
    private-visibility declarations are skipped, matching what
    ``print_theorems`` writes to ``.thm``. The user's own file
    bypasses this filter (everything in the file is in scope).
    """
    from abstract_syntax import (
        Auto,
        Define,
        Postulate,
        Predicate,
        RecFun,
        Theorem,
        Union,
        base_name,
    )

    if isinstance(stmt, Theorem):
        if public_only and stmt.isLemma:
            return None
        kind = SymbolKind.LEMMA if stmt.isLemma else SymbolKind.THEOREM
        name = base_name(stmt.name)
        signature = f"{name}: {stmt.what}"
    elif isinstance(stmt, Postulate):
        kind = SymbolKind.POSTULATE
        name = base_name(stmt.name)
        signature = f"{name}: {stmt.what}"
    elif isinstance(stmt, Auto):
        kind = SymbolKind.OTHER  # no dedicated SymbolKind value for ``auto``
        # ``Auto.name`` is a ``Term`` (typically a ``Var``/``PVar``),
        # not a string -- ``base_name`` would crash on it.  ``str()``
        # gives the rendered identifier, which is what
        # ``print_theorems_statement`` writes to ``.thm`` too.
        name = str(stmt.name)
        signature = f"auto {name}"
    elif isinstance(stmt, (RecFun, Define, Union, Predicate)):
        # Allowlist of declaration kinds we surface.  ``Import`` is
        # also a ``Declaration`` subclass but isn't a definition
        # itself; ``GenRecFun`` is a niche generic-recursion form
        # that ``print_theorems_statement`` doesn't currently emit.
        if public_only and getattr(stmt, "visibility", "public") == "private":
            return None
        if isinstance(stmt, RecFun):
            kind = SymbolKind.FUNCTION
        elif isinstance(stmt, Define):
            kind = SymbolKind.DEFINE
        elif isinstance(stmt, Union):
            kind = SymbolKind.UNION
        else:
            kind = SymbolKind.PREDICATE
        name = base_name(str(stmt.name)) if getattr(stmt, "name", None) else ""
        signature = stmt.pretty_print(0).rstrip("\n")
    else:
        return None

    return LemmaInfo(
        name=name,
        kind=kind,
        signature=signature,
    )


def available_lemmas_at(
    path: str,
    content: str,
    pos: Position,
    query: Optional[str] = None,
    prelude: Sequence[str] = (),
    limit: int = 50,
) -> tuple:
    """Return ranked lemmas visible at ``pos``, best matches first.

    Driven by either (or both) of two signals:

    - The cursor sits on a ``?`` token: the goal at that hole defines
      the shape we're searching for.  ``available_lemmas_at`` extracts
      the goal text and uses its head operator and operator/function
      tokens for ranking.
    - ``query`` is given: a substring (matched against the rendered
      lemma signature) or a goal-shape pattern containing ``_``
      placeholders (each ``_`` matches any run of characters).

    When both are given they combine -- a lemma that matches the goal
    *and* the query ranks above one that matches only one.

    The result is a tuple of :class:`LemmaMatch` ordered by descending
    ``relevance``; ties broken by name.  ``relevance`` is normalised
    so the best match in the set is ``1.0`` and others scale linearly.
    Only theorems, lemmas, and postulates are surfaced.

    The lemma set is the same one :func:`hole_context_at` collects
    (user-file declarations plus public declarations from each module
    in ``prelude``), so this works without a hole as long as the file
    parses.  Returns ``()`` when neither a hole nor a ``query`` is
    available, or when no lemma matches even minimally.
    """
    from lsp.library import check_file

    hole_range = _find_hole_at(content, pos)
    goal_text: Optional[str] = None
    if hole_range is not None:
        target = (hole_range.start.line, hole_range.start.column)
        with _target_hole(target):
            result = check_file(path, content=content, prelude=prelude)
        if not result.ok:
            goal = _goal_from_exception(result.exception, hole_range)
            if goal is not None:
                goal_text = goal.formula
        ast_nodes = result.ast
    else:
        result = check_file(path, content=content, prelude=prelude)
        ast_nodes = result.ast

    if goal_text is None and not query:
        return ()

    candidates = _collect_lemma_candidates(path, ast_nodes, prelude)
    if not candidates:
        return ()

    ranked = _rank_lemmas(candidates, goal_text, query, _module_for_path(path))
    if not ranked:
        return ()

    if limit > 0:
        ranked = ranked[:limit]
    return tuple(ranked)


def _module_for_path(path: str) -> str:
    """Module name for the file at ``path`` -- the path's stem."""
    from pathlib import Path

    return Path(path).stem


def _collect_lemma_candidates(
    path: str, ast_nodes, prelude: Sequence[str]
) -> tuple:
    """Build the ranking input: theorems/lemmas/postulates with their
    formula AST and module of origin.

    Returns a tuple of ``(LemmaInfo, formula_ast, module)`` triples,
    drawn from the user file (one entry per ``Theorem``/``Postulate``
    in source order, including private ones) and from each module
    named in ``prelude`` (public theorems/postulates only, matching
    ``print_theorems``' visibility filter).
    """
    from abstract_syntax import (
        Import as _ImportNode,
        Postulate,
        Theorem,
        get_uniquified_modules,
    )

    out = []
    user_module = _module_for_path(path)

    if ast_nodes is not None:
        prelude_set = set(prelude)
        for stmt in ast_nodes:
            if isinstance(stmt, _ImportNode) and stmt.name in prelude_set:
                continue
            if not isinstance(stmt, (Theorem, Postulate)):
                continue
            info = _lemma_info_for(stmt, public_only=False)
            if info is None:
                continue
            out.append((info, stmt.what, user_module))

    if prelude:
        modules = get_uniquified_modules()
        for module_name in prelude:
            module_ast = modules.get(module_name)
            if module_ast is None:
                continue
            for stmt in module_ast:
                if not isinstance(stmt, (Theorem, Postulate)):
                    continue
                info = _lemma_info_for(stmt, public_only=True)
                if info is None:
                    continue
                out.append((info, stmt.what, module_name))

    return tuple(out)


# Operator-like rator names whose appearance in a goal we can extract
# from rendered text.  Order is the precedence order used by Deduce's
# pretty printer (coarsely): the lowest-precedence operator that
# appears at depth 0 in a formula's text is its head.
_GOAL_HEAD_OPERATORS = (
    " iff ",
    " or ",
    " and ",
    " = ",
    " ≠ ",
    " ≤ ",
    " ≥ ",
    " < ",
    " > ",
    " + ",
    " - ",
    " * ",
    " ÷ ",
    " / ",
    " % ",
)


# Tokens that are language keywords / type names rather than the
# function/operator names we want to count for symbol overlap.
_GOAL_TOKEN_STOPWORDS = frozenset({
    "all", "some", "if", "then", "else", "and", "or", "not",
    "iff", "true", "false", "fun", "switch", "case", "where",
    "obtain", "from", "by", "have", "suppose", "assume",
    "lemma", "theorem", "proof", "end", "of", "in",
})


def _strip_outer_parens(text: str) -> str:
    """Strip a single pair of outer parens iff they are balanced and
    wrap the entire expression."""
    s = text.strip()
    while len(s) >= 2 and s[0] == "(" and s[-1] == ")":
        depth = 0
        inner_min = 1
        for i, ch in enumerate(s):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and i < len(s) - 1:
                    inner_min = 0
                    break
        if inner_min == 0:
            break
        s = s[1:-1].strip()
    return s


def _strip_outer_quantifiers(text: str) -> str:
    """Repeatedly strip leading ``all <bindings>. `` and ``if <p> then ``
    prefixes from rendered goal text, returning the conclusion body.

    Stops as soon as neither prefix matches.  Paren-aware: an ``all``
    or ``if`` inside parens at depth >0 is not a candidate."""
    s = _strip_outer_parens(text)

    while True:
        prev = s
        # all <bindings>. body
        if s.startswith("all "):
            dot = _find_top_level(s, ".")
            if dot is not None:
                s = s[dot + 1:].lstrip()
                s = _strip_outer_parens(s)
                continue
        # if <prem> then <conc>
        if s.startswith("if "):
            then_pos = _find_top_level(s, " then ")
            if then_pos is not None:
                s = s[then_pos + len(" then "):].lstrip()
                s = _strip_outer_parens(s)
                continue
        if s == prev:
            break
    return s


def _find_top_level(s: str, needle: str) -> Optional[int]:
    """Return the offset of ``needle`` at paren-depth 0 in ``s``, or
    ``None``.  Used to strip top-level binders from rendered goals."""
    depth = 0
    n = len(needle)
    for i, ch in enumerate(s):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        elif depth == 0 and s.startswith(needle, i):
            return i
    return None


def _goal_head_symbol(text: Optional[str]) -> Optional[str]:
    """Best-effort extraction of the head operator from rendered goal
    text.  Returns the operator with surrounding spaces stripped (e.g.
    ``"="``, ``"≤"``, ``"and"``), or ``None`` when no recognised
    operator appears at depth 0.

    For function-call goals (e.g. ``less(x, y)``), returns the
    function name."""
    if not text:
        return None
    s = _strip_outer_quantifiers(text)
    if not s:
        return None

    # Bare bool literal or identifier with nothing else: that's the head.
    for op in _GOAL_HEAD_OPERATORS:
        if _find_top_level(s, op) is not None:
            return op.strip()

    # Function call: ``name(...)`` at the top level.
    m = re.match(r"\s*([A-Za-z_][A-Za-z0-9_]*)\s*\(", s)
    if m:
        return m.group(1)

    # Negation prefix.
    if s.startswith("not "):
        return "not"

    return None


_TOKEN_RE = re.compile(
    r"[A-Za-z_][A-Za-z0-9_]*|[+\-*/%<>=≤≥≠÷]|and|or|iff|not"
)


def _goal_tokens(text: Optional[str]) -> frozenset:
    """Operator and function-name tokens appearing in rendered goal
    text, with stopwords (binders, language keywords) and short
    identifiers (1 char) filtered out."""
    if not text:
        return frozenset()
    tokens = set()
    for raw in _TOKEN_RE.findall(text):
        if raw in _GOAL_TOKEN_STOPWORDS:
            continue
        if raw.isalpha() and len(raw) == 1:
            # Skip bare ``x``/``y``/``n``/``P``/``Q`` -- almost always
            # bound variables or schematic placeholders, not symbols
            # that distinguish lemmas.
            continue
        if raw.isdigit():
            continue
        tokens.add(raw)
    return frozenset(tokens)


def _formula_head_symbol(formula) -> Optional[str]:
    """Head operator of a lemma's formula (peeling outer ``All`` and
    ``IfThen``).  Returns the rator's base name for a ``Call``, or a
    string token for non-Call shapes (``and``/``or``/``not``/etc.).
    Returns ``None`` for unsupported shapes."""
    from abstract_syntax import (
        All, And, Bool, Call, IfThen, Or, TermInst, VarRef, base_name,
    )

    f = formula
    while True:
        if isinstance(f, All):
            f = f.body
        elif isinstance(f, IfThen):
            f = f.conclusion
        else:
            break

    if isinstance(f, Call):
        rator = f.rator
        if isinstance(rator, TermInst):
            inner = getattr(rator, "subject", None)
            if isinstance(inner, VarRef):
                return base_name(inner.get_name())
        if isinstance(rator, VarRef):
            return base_name(rator.get_name())
        return None
    if isinstance(f, And):
        return "and"
    if isinstance(f, Or):
        return "or"
    if isinstance(f, Bool):
        return "true" if f.value else "false"
    return None


def _formula_symbols(formula) -> frozenset:
    """Set of all rator names appearing in ``formula`` (recursively).

    Drives the symbol-overlap signal in lemma ranking.  Bound
    variables introduced by ``All``/``Some`` are excluded -- only the
    uniquified rator names of ``Call`` nodes count.  Names are
    returned as their ``base_name`` so they line up with the
    user-visible operator/function names used in goal text."""
    from abstract_syntax import (
        AST, And, Bool, Call, IfThen, Or, TermInst, VarRef, base_name,
    )

    out = set()

    def visit(node):
        if isinstance(node, Call):
            rator = node.rator
            if isinstance(rator, TermInst):
                inner = getattr(rator, "subject", None)
                if isinstance(inner, VarRef):
                    out.add(base_name(inner.get_name()))
            elif isinstance(rator, VarRef):
                out.add(base_name(rator.get_name()))
        elif isinstance(node, And):
            out.add("and")
        elif isinstance(node, Or):
            out.add("or")
        elif isinstance(node, IfThen):
            # IfThen is logical implication; we don't add ``then`` or
            # ``if`` to the symbol set -- the head match handles it.
            pass
        elif isinstance(node, Bool):
            out.add("true" if node.value else "false")

    _walk_ast(formula, visit, ast_class=AST)
    return frozenset(out)


def _query_pattern(query: Optional[str]):
    """Return a compiled regex if ``query`` is a goal-shape pattern
    (contains ``_``), else ``None``.  Each ``_`` becomes ``.+?`` and
    other characters are matched literally with whitespace
    flexibility (any run of whitespace matches any other run)."""
    if not query or "_" not in query:
        return None
    parts = []
    for chunk in query.split("_"):
        if not chunk:
            parts.append("")
            continue
        # Collapse runs of whitespace in the literal, then split on
        # them so we can re-emit ``\s+`` between literal pieces.
        words = chunk.split()
        if not words:
            parts.append(r"\s*")
            continue
        prefix = r"\s*" if chunk[:1].isspace() else ""
        suffix = r"\s*" if chunk[-1:].isspace() else ""
        parts.append(prefix + r"\s+".join(re.escape(w) for w in words) + suffix)
    body = ".+?".join(parts)
    try:
        return re.compile(body)
    except re.error:
        return None


def _rank_lemmas(
    candidates: tuple,
    goal_text: Optional[str],
    query: Optional[str],
    user_module: str,
) -> list:
    """Score and sort candidate lemmas.

    ``candidates`` is the tuple from :func:`_collect_lemma_candidates`.
    Returns a list of :class:`LemmaMatch` with normalised relevance
    in ``[0.0, 1.0]``; only candidates with a strictly positive raw
    score are included.

    The four signals from issue #403:

    1. Exact head-symbol match between conclusion and goal.
    2. Goal symbols appearing in the lemma's full formula symbols.
    3. Module proximity to the file under cursor.
    4. Fuzzy substring of the query against the lemma name as
       tiebreaker.

    Plus one extra: a goal-shape pattern (a ``query`` containing ``_``
    placeholders) matched against the rendered signature.
    """
    goal_head = _goal_head_symbol(goal_text)
    goal_syms = _goal_tokens(goal_text)
    pattern = _query_pattern(query)
    query_substr = (query or "").strip().lower()
    has_substring_query = bool(query_substr) and pattern is None

    raw_scores: list = []
    for info, formula, module in candidates:
        head = _formula_head_symbol(formula)
        symbols = _formula_symbols(formula)

        head_score = 1.0 if (goal_head is not None and head == goal_head) else 0.0

        if goal_syms:
            overlap = len(goal_syms & symbols) / len(goal_syms)
        else:
            overlap = 0.0

        proximity = 1.0 if module == user_module else 0.0

        sig_lower = info.signature.lower()
        name_lower = info.name.lower()

        substring_score = 0.0
        if has_substring_query:
            if query_substr in name_lower:
                substring_score = 1.0
            elif query_substr in sig_lower:
                substring_score = 0.5

        pattern_score = 0.0
        if pattern is not None and pattern.search(info.signature):
            pattern_score = 1.0

        raw = (
            4.0 * head_score
            + 2.0 * overlap
            + 1.0 * proximity
            + 2.0 * substring_score
            + 3.0 * pattern_score
        )

        # When the user typed a goal-shape pattern or substring, only
        # surface lemmas that match it -- other signals shouldn't
        # promote unrelated lemmas above a query-only baseline.
        if has_substring_query and substring_score == 0.0:
            continue
        if pattern is not None and pattern_score == 0.0:
            continue

        # No goal AND no query that this lemma matched -> nothing to
        # score on.  Skip.
        if raw <= 0.0:
            continue

        raw_scores.append((raw, info, module))

    if not raw_scores:
        return []

    max_raw = max(r for r, _, _ in raw_scores)
    if max_raw <= 0.0:
        return []

    raw_scores.sort(key=lambda t: (-t[0], t[1].name))
    matches = []
    for raw, info, module in raw_scores:
        matches.append(
            LemmaMatch(
                name=info.name,
                kind=info.kind,
                signature=info.signature,
                module=module,
                relevance=raw / max_raw,
            )
        )
    return matches


def _hole_fingerprint(goal_formula: str, givens: tuple) -> str:
    """Hex SHA-256 over a canonical rendering of goal + givens.

    Givens are sorted alphabetically by ``"label: formula"`` so the
    fingerprint doesn't depend on the order Deduce happens to print
    them in -- adding/removing an unrelated hypothesis stays detected,
    but reshuffling doesn't trigger a spurious mismatch.
    """
    import hashlib

    given_lines = sorted(
        f"{g.label or ''}: {g.formula}" for g in givens
    )
    canonical = goal_formula + "\n" + "\n".join(given_lines)
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


# ---------------------------------------------------------------------------
# validate_proof_at -- Phase 5 / Step 3: splice-and-recheck for the sidecar
# ---------------------------------------------------------------------------
#
# The Claude hole-fill sidecar calls this once per proof candidate it
# generates. v0 just splices and re-runs check_file; the prelude is
# already cached across calls (lsp.library snapshot machinery), so
# the warm cost is roughly parse + uniquify + check of the user's
# file. Once the in-flight incremental-checking work lands, this
# function is the single call site to swap to the cheap path -- the
# signature is shaped to survive that change.


def validate_proof_at(
    path: str,
    content: str,
    hole_range: Range,
    proof_text: str,
    prelude: Sequence[str] = (),
) -> ValidationResult:
    """Splice ``proof_text`` into ``content`` at ``hole_range`` and
    return whether the resulting file checks.

    ``hole_range`` must cover exactly the ``?`` token at the hole;
    the function rejects any range whose source slice is not the
    one-character string ``"?"``. That catches stale ranges from
    async callers (the sidecar's hole moved while Claude was
    thinking) cleanly, rather than splicing in a random location.

    Returns ``ValidationResult(ok=True)`` on success; on failure,
    ``ok=False`` with ``error`` set to the checker's message
    (the same string ``deduce.py`` would print, location prefix
    included). The sidecar truncates this before sending it back
    to the model.

    ``prelude`` matches the meaning in :func:`check`.
    """
    start_off = _line_col_to_offset(content, hole_range.start)
    end_off = _line_col_to_offset(content, hole_range.end)
    if start_off is None or end_off is None:
        return ValidationResult(
            ok=False, error="hole range out of bounds for content"
        )
    if start_off >= end_off:
        return ValidationResult(ok=False, error="hole range is empty")
    if content[start_off:end_off] != "?":
        return ValidationResult(
            ok=False,
            error="hole range does not cover a `?` token",
        )

    spliced = content[:start_off] + proof_text + content[end_off:]

    from lsp.library import check_file

    result = check_file(path, content=spliced, prelude=prelude)
    if result.ok:
        return ValidationResult(ok=True, error=None)
    return ValidationResult(ok=False, error=result.error_message)


# ---------------------------------------------------------------------------
# preview_replace_at / preview_expand_at -- issue #401: rewrite previews
# ---------------------------------------------------------------------------
#
# Pure read-only previews of what ``replace <equation>`` or ``expand
# <names>`` would do to the current goal. The mechanism mirrors the
# Phase 4 query helpers: target the cursor's `?`, run the pipeline so
# `incomplete_error` stashes the goal AST and env on the exception,
# then call into the same ``apply_rewrites`` / ``expand_definitions``
# helpers that the proof checker uses for the real tactic. Failure
# modes (no match, opaque, unbound) are returned as structured
# outcomes rather than raised, so the agent can decide what to do
# without round-tripping through `check_file`.


_REPLACE_SYMMETRIC_PREFIX = "symmetric "


def preview_replace_at(
    path: str,
    content: str,
    pos: Position,
    equation: str,
    prelude: Sequence[str] = (),
) -> Optional[RewritePreview]:
    """Preview the result of ``replace <equation>`` at the hole at ``pos``.

    The cursor must sit on (or immediately adjacent to) a ``?`` token.
    ``equation`` is the *name* of an in-scope theorem, lemma, or local
    hypothesis whose formula is an equation, optionally prefixed with
    ``"symmetric "`` for a right-to-left rewrite.

    Returns ``None`` when the cursor isn't on a ``?`` or the file has
    no incomplete proof there. Otherwise returns a :class:`RewritePreview`
    with one of four outcomes; see that class's docstring.

    The preview reduces the goal first (matching what the proof checker
    does for ``replace``) so ``before`` reflects what the equation is
    actually applied against -- this is what catches the "an auto rule
    already canonicalized the LHS away" case the issue calls out.
    """
    hole_range = _find_hole_at(content, pos)
    if hole_range is None:
        return None

    from lsp.library import check_file

    target = (hole_range.start.line, hole_range.start.column)
    with _target_hole(target):
        result = check_file(path, content=content, prelude=prelude)
    if result.ok:
        return None

    exc = result.exception
    env = getattr(exc, "env", None)
    formula = getattr(exc, "formula", None)
    if env is None or formula is None:
        return None

    raw = equation.strip()
    is_symmetric = raw.startswith(_REPLACE_SYMMETRIC_PREFIX)
    name = raw[len(_REPLACE_SYMMETRIC_PREFIX):].strip() if is_symmetric else raw

    return _preview_replace(
        name=name,
        is_symmetric=is_symmetric,
        original_input=equation,
        formula=formula,
        env=env,
        loc=getattr(exc, "location", None),
    )


def _preview_replace(
    name: str,
    is_symmetric: bool,
    original_input: str,
    formula,
    env,
    loc,
) -> RewritePreview:
    """Look up ``name`` and apply the rewrite (or report a structured
    failure). ``loc`` is the hole's source location, used for the
    diagnostic-shaped exceptions raised by ``apply_rewrites``."""
    from abstract_syntax import (
        ProofBinding, base_name, is_equation, mkEqual, split_equation,
    )

    matches = [k for k in env.dict if base_name(k) == name]
    binding = None
    for k in matches:
        cand = env.dict[k]
        if isinstance(cand, ProofBinding):
            binding = cand
            break
    if binding is None:
        return RewritePreview(outcome="unbound", name=original_input)

    eq_formula = binding.formula
    if not is_equation(eq_formula):
        return RewritePreview(
            outcome="not_an_equation",
            formula=str(eq_formula),
        )

    if is_symmetric:
        # Mirror PSymmetric: split off the (a,b) pair (descends through
        # any outer Alls) and swap. PSymmetric's behavior on quantified
        # equations drops the quantifier; preview_replace mirrors that
        # so the preview matches what the real tactic would do.
        try:
            (lhs, rhs) = split_equation(loc, eq_formula, env)
        except Exception:
            return RewritePreview(
                outcome="not_an_equation",
                formula=str(eq_formula),
            )
        eq_formula = mkEqual(loc, rhs, lhs)

    eq_reduced = eq_formula.reduce(env)
    before = formula.reduce(env)

    from error import UserError
    from proof_checker import apply_rewrites

    try:
        after = apply_rewrites(loc, before, [eq_reduced], env)
    except UserError as exc:
        msg = getattr(exc, "message_body", None) or str(exc)
        if "no need for replace" in msg:
            reason = (
                "this equation is handled automatically -- "
                "no `replace` needed"
            )
        elif "could not find any matches" in msg:
            try:
                (lhs, _rhs) = split_equation(loc, eq_reduced, env)
                reason = (
                    f"LHS '{lhs}' does not occur in the current goal"
                )
            except Exception:
                reason = "no matches for the equation in the current goal"
        else:
            reason = msg
        return RewritePreview(outcome="no_match", reason=reason)

    return RewritePreview(
        outcome="ok",
        before=str(before),
        after=str(after),
    )


def preview_expand_at(
    path: str,
    content: str,
    pos: Position,
    names: Sequence[str],
    prelude: Sequence[str] = (),
) -> Optional[ExpandPreview]:
    """Preview the result of ``expand <names>`` at the hole at ``pos``.

    The cursor must sit on (or immediately adjacent to) a ``?`` token.
    ``names`` is a list of definition names to unfold, matching the
    ``expand X | Y | Z`` syntax (each name in turn is substituted into
    the goal and reduced).

    Returns ``None`` when the cursor isn't on a ``?`` or the file has
    no incomplete proof there. Otherwise returns an :class:`ExpandPreview`
    with one of four outcomes; see that class's docstring.

    Names are resolved in order: the first name that fails (unknown,
    opaque, or no match) determines the failure outcome. If every name
    expands at least once, the result is ``ok``.
    """
    hole_range = _find_hole_at(content, pos)
    if hole_range is None:
        return None

    from lsp.library import check_file

    target = (hole_range.start.line, hole_range.start.column)
    with _target_hole(target):
        result = check_file(path, content=content, prelude=prelude)
    if result.ok:
        return None

    exc = result.exception
    env = getattr(exc, "env", None)
    formula = getattr(exc, "formula", None)
    if env is None or formula is None:
        return None

    return _preview_expand(
        list(names),
        formula=formula,
        env=env,
        loc=getattr(exc, "location", None),
    )


def _preview_expand(
    names: list, formula, env, loc
) -> ExpandPreview:
    """Resolve each name then call ``expand_definitions`` with the
    constructed var list. Pre-checks unknown / all-opaque names so the
    failure is reported as a structured outcome instead of an exception."""
    from abstract_syntax import (
        OverloadedVar, TermBinding, TypeBinding, base_name,
    )

    defs = []
    for name in names:
        candidates = [k for k in env.dict if base_name(k) == name]
        # Skip non-term/type bindings (proof labels can't be expanded).
        defn_candidates = [
            k for k in candidates
            if isinstance(env.dict[k], (TermBinding, TypeBinding))
        ]
        if not defn_candidates:
            return ExpandPreview(outcome="unknown", name=name)
        current_module = env.get_current_module()
        non_opaque = [
            k for k in defn_candidates
            if not (
                env.dict[k].visibility == "opaque"
                and env.dict[k].module != current_module
            )
        ]
        if not non_opaque:
            return ExpandPreview(outcome="opaque", name=name)
        defs.append(OverloadedVar(loc, None, non_opaque))

    from error import UserError
    from proof_checker import expand_definitions

    try:
        after = expand_definitions(loc, formula, defs, env)
    except UserError as exc:
        msg = getattr(exc, "message_body", None) or str(exc)
        # Find which name failed by parsing the message: messages from
        # ``expand_definitions`` echo the failing identifier.
        failing = None
        for name in names:
            if name in msg:
                failing = name
                break
        return ExpandPreview(outcome="no_match", name=failing or names[0])

    return ExpandPreview(
        outcome="ok",
        before=str(formula),
        after=str(after),
    )
