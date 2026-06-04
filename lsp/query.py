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
from lark.tree import Meta
from typing import (
    TYPE_CHECKING, Any, Callable, Iterator, Optional, Sequence, Union, cast,
)

if TYPE_CHECKING:
    # Type-only imports.  The runtime body keeps its lazy ``from
    # abstract_syntax import ...`` pattern so this module stays free of
    # any pipeline import at module-load time (the protocol-neutral
    # boundary the docstring guarantees); these names exist only for
    # annotations and never execute.
    from abstract_syntax import (
        AST, All, And, Auto, Env, Formula, IfThen, Import, Or,
        ResolvedVar, Some, Statement, Term, Type,
    )
    from abstract_syntax import Union as UnionDecl


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
    "CompletionCandidate",
    "UnsupportedRefineShape",
    "LemmaInfo",
    "LemmaMatch",
    "HoleContext",
    "ValidationResult",
    "RewritePreview",
    "ExpandPreview",
    "AutoRule",
    # Query functions
    "check",
    "goal_at",
    "definition_of",
    "list_symbols",
    "completions_at",
    "refine_at",
    "case_split_at",
    "splittable_vars_at",
    "induction_skeleton_at",
    "eliminate_at",
    "eliminable_vars_at",
    "fill_from_given_at",
    "matching_givens_at",
    "preview_conclude_at",
    "apply_at",
    "hole_context_at",
    "available_lemmas_at",
    "insert_lemma_at",
    "validate_proof_at",
    "preview_replace_at",
    "preview_expand_at",
    "auto_rules_at",
]

# TODO: remove the _call_untyped function.
def _call_untyped(fn: Callable[..., Any], *args: Any, **kwargs: Any) -> Any:
    # Any: dynamic-dispatch boundary into lazily-imported pipeline
    # helpers (set_reduce_all, instantiate, collect_all_if_then,
    # formula_match, split_equation, apply_rewrites, expand_definitions,
    # ...). The call site casts the result to the concrete type it
    # expects; the variadic signature can't express that per-callee.
    return fn(*args, **kwargs)


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

    ``formula_normalized`` is the post-auto-reduction form -- the shape
    the proof checker actually compares against. ``None`` when it
    coincides with ``formula`` (no auto rule fired), or when the
    structured AST/env wasn't available to compute it.
    """

    label: Optional[str]
    formula: str
    formula_normalized: Optional[str] = None


@dataclass(frozen=True)
class Goal:
    """The proof obligation visible at a source position.

    Returned by :func:`goal_at`. ``formula`` is the goal as rendered
    text. ``givens`` is a tuple (not list) so ``Goal`` stays hashable.
    ``range`` is the source range the goal corresponds to -- typically
    where the cursor or hole sits.

    ``formula_normalized`` is the post-auto-reduction form of the goal
    -- the shape the proof checker compares against when matching a
    candidate proof body. ``None`` when it coincides with ``formula``
    (no auto rule fired), or when the structured AST/env wasn't
    available to compute it. See issue #421.
    """

    formula: str
    givens: tuple[Given, ...]
    range: Range
    formula_normalized: Optional[str] = None


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


# Stable list of goal shapes that ``refine_at`` knows a template for.
# Surfaced on ``UnsupportedRefineShape`` so callers don't have to
# re-read the docstring to find out which shapes are covered.
REFINE_SUPPORTED_SHAPES: tuple[str, ...] = (
    "true",
    "_ and _",
    "if _ then _",
    "all _. _",
    "some _. _",
    "reducible _ = _",
)


# Deduce keywords surfaced by :func:`completions_at`.  Mirrors
# ``deduce-mode--keywords`` in editor/emacs/deduce-mode.el and the
# keyword categories in editor/vscode/syntaxes/deduce.tmLanguage.json
# (kept in sync by hand for now; a generator off ``Deduce.lark`` would
# eventually replace the three copies).  Categorisation feeds the
# LSP-side ``CompletionItemKind`` mapping: ``keyword`` -> Keyword,
# ``constant`` -> Constant, ``type`` -> Class.
COMPLETION_KEYWORDS: tuple[str, ...] = (
    # declaration / structure
    "theorem", "lemma", "postulate", "define", "recursive", "recfun",
    "union", "inductive", "predicate", "relation", "import", "export",
    "module", "auto", "assert", "print", "operator", "associative",
    "terminates", "measure", "trace", "generic", "fun", "λ",
    # visibility
    "public", "private", "opaque",
    # module-import filters
    "using", "hiding",
    # proof structure
    "proof", "end", "case", "cases", "with", "where",
    # tactics
    "arbitrary", "assume", "suppose", "have", "show", "obtain", "from", "for",
    "induction", "rule", "inversion", "switch", "replace", "expand",
    "evaluate", "simplify", "equations", "recall", "reflexive", "symmetric",
    "transitive", "injective", "extensionality", "apply", "to", "conclude",
    "conjunct", "contradict", "suffices", "choose", "stop", "help", "by", "of",
    # logical / control
    "if", "then", "else", "all", "some", "in",
    "not", "and", "or", "iff",
    # built-in operators / forms
    "fn", "array",
)

COMPLETION_CONSTANT_KEYWORDS: tuple[str, ...] = ("true", "false")
COMPLETION_TYPE_KEYWORDS: tuple[str, ...] = ("bool", "type")


@dataclass(frozen=True)
class CompletionCandidate:
    """A single completion candidate returned by :func:`completions_at`.

    ``label`` is the user-visible text the client filters against.

    ``kind`` is a string tag from a stable vocabulary:

    - ``"keyword"`` (e.g. ``theorem``, ``arbitrary``, ``proof``)
    - ``"constant"`` (``true``, ``false``)
    - ``"type"`` (``bool``, ``type``)
    - ``"theorem"`` / ``"lemma"`` / ``"postulate"``
    - ``"define"`` / ``"function"`` (a ``recursive`` / ``recfun``)
    - ``"union"`` / ``"constructor"``
    - ``"predicate"`` / ``"rule"``
    - ``"label"`` (a local proof binding -- ``assume H: P``,
      ``obtain ... where ... from H``, hypotheses from ``cases``, ...)
    - ``"variable"`` (a local term binding -- ``arbitrary x:T``,
      pattern-bound names inside ``switch`` / ``case`` blocks, ...)

    Adapters map this to their wire format: the LSP server translates
    to ``CompletionItemKind``; MCP would surface the string directly.

    ``detail`` is an optional one-line signature (e.g. ``"plus_zero:
    all n:Nat. n + 0 = n"``) shown alongside the label in the picker
    UI.  ``None`` when no signature is known.

    ``priority`` is a sort hint: smaller floats the candidate to the
    top of the picker.  ``0`` is reserved for hole-aware matches (a
    label whose formula equals or implies the goal at the hole the
    cursor sits on); ``1`` is the default for everything else.  The
    LSP adapter encodes ``priority`` as the ``sortText`` field, so
    matches sort lexicographically before the rest.
    """

    label: str
    kind: str
    detail: Optional[str] = None
    priority: int = 1


@dataclass(frozen=True)
class UnsupportedRefineShape:
    """Reason returned by :func:`refine_at` when the cursor sits on a
    real hole but no template matches the goal's shape.

    Distinguishes "there's nothing to refine" (``refine_at`` returns
    ``None``) from "there's a goal but no template applies"
    (``refine_at`` returns this). ``goal`` is the rendered goal text;
    ``supported_shapes`` enumerates the shapes ``refine_at`` does
    cover, so the caller can decide what to try next without
    re-reading the docstring.
    """

    outcome: str
    goal: str
    supported_shapes: tuple[str, ...]


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

    ``unify_tier`` classifies how the lemma's conclusion relates to
    the goal AST at the hole (issue #690):

    - ``"full"`` -- conclusion unifies with the goal and every premise
      is discharged by a local given;
    - ``"premises_remain"`` -- conclusion unifies but some premises
      become fresh subgoals;
    - ``"rewrite_subterm"`` -- the conclusion is an equation whose
      LHS (or RHS) unifies with a subterm of the goal -- a candidate
      for ``replace``;
    - ``None`` -- no unification path was found, or the structured
      goal/env wasn't available (e.g. browse mode, parse error).

    ``discharged_premises`` lists ``(premise_text, given_label)`` pairs
    for the ``"full"`` tier: the editor uses these to splice the right
    ``conclude ... by name(...)`` argument list. Empty for other
    tiers.
    """

    name: str
    kind: SymbolKind
    signature: str
    module: Optional[str]
    relevance: float
    unify_tier: Optional[str] = None
    discharged_premises: tuple[tuple[str, str], ...] = ()


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
    givens: tuple[Given, ...]
    lemmas_in_scope: tuple[LemmaInfo, ...]
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


@dataclass(frozen=True)
class AutoRule:
    """An ``auto`` rewrite rule visible at a source position.

    Returned (in tuples) by :func:`auto_rules_at`. ``name`` is the
    user-visible identifier of the theorem the rule was declared from
    (i.e. ``base_name`` of the uniquified name). ``equation`` is the
    rendered formula -- the same string Deduce's printer would
    produce for the theorem's body -- so callers can see what shape
    the auto-rewriter will rewrite. ``module`` is the module that
    declared the ``auto`` statement (the file stem for prelude
    modules and for the user file itself), useful to disambiguate
    rules with the same base name from different modules.
    """

    name: str
    equation: str
    module: str
    premise: Optional[str] = None


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
    path: str, content: str, prelude: Sequence[str] = (),
    parser: Optional[str] = None,
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

    ``parser`` selects which parser checks the user file: ``None``
    (default) uses whatever ``flags.recursive_descent`` selects --
    matches CLI behaviour. ``"recursive-descent"`` and ``"lalr"``
    force that specific parser, bypassing the AST cache so the
    requested parser actually runs. The prelude is served from its
    existing snapshot regardless (parser-equivalent by CI).
    """
    # Imported here, not at module top, so this module stays free of
    # any pipeline import while it is just a stub at module-load time.
    # That keeps the protocol-neutral boundary cheap to enforce.
    from lsp.library import check_file

    result = check_file(
        path, content=content, prelude=prelude,
        collect_errors=True, parser=parser,
    )
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
    body: str
    if formula is not None:
        body = _format_incomplete_proof_message(formula)
    else:
        msg = getattr(exc, "message_body", None)
        body = msg if msg is not None else _format_unstructured_exception(exc, str_fallback)

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


def _format_incomplete_proof_message(formula: "Formula") -> str:
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


def _insert_hole(content: str, pos: Position) -> Optional[tuple[str, Position]]:
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
def _target_hole(loc: tuple[int, int]) -> Iterator[None]:
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

    formula_ast = getattr(exc, "formula", None)
    env = getattr(exc, "env", None)
    formula_normalized = _normalize_formula(formula_ast, env, formula)

    givens = _parse_givens_section(body)
    givens = _attach_normalized_givens(givens, env)

    return Goal(
        formula=formula,
        givens=givens,
        range=goal_range,
        formula_normalized=formula_normalized,
    )


def _normalize_formula(
    formula_ast: Optional["Formula"], env: Optional["Env"], rendered: str
) -> Optional[str]:
    """Render the auto-reduced form of ``formula_ast`` under ``env``.

    Returns ``None`` when reduction is unavailable (missing AST or env)
    or when the result matches the source-shaped ``rendered`` string,
    so callers don't have to compare to know "no auto rule fired".
    """
    if formula_ast is None or env is None:
        return None
    try:
        reduced = formula_ast.reduce(env)
    except Exception:
        return None
    text = str(reduced)
    if text == rendered:
        return None
    return text


def _attach_normalized_givens(
    givens: tuple[Given, ...], env: Optional["Env"]
) -> tuple[Given, ...]:
    """Add ``formula_normalized`` to each given when env exposes its AST.

    Walks ``env``'s ``ProofBinding`` entries to map each printed label
    back to its formula AST, reduces under ``env``, and attaches the
    string form when it differs from what the given carries. Givens
    that we can't match (anonymous, env unavailable, label collisions)
    pass through unchanged.
    """
    if env is None or not givens:
        return givens
    try:
        from abstract_syntax import ProofBinding, name2str
    except Exception:
        return givens

    by_label: dict[str, "Formula"] = {}
    for unique, binding in env.dict.items():
        if not isinstance(binding, ProofBinding):
            continue
        label = name2str(unique)
        # A label could appear more than once across nested scopes;
        # keep the most recent (later-inserted) binding to match what
        # the proof checker resolves to at the hole.
        by_label[label] = binding.formula

    result = []
    for given in givens:
        if given.label is None or given.label not in by_label:
            result.append(given)
            continue
        try:
            reduced = by_label[given.label].reduce(env)
        except Exception:
            result.append(given)
            continue
        text = str(reduced)
        if text == given.formula:
            result.append(given)
            continue
        result.append(
            Given(
                label=given.label,
                formula=given.formula,
                formula_normalized=text,
            )
        )
    return tuple(result)


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


def _parse_givens_section(body: str) -> tuple[Given, ...]:
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
    the matching declaration.  Cross-file references are followed
    through ``Import.ast`` (see :func:`_find_declaration`), so F12 on
    a name imported from the prelude or a user import resolves to the
    declaration site in that file.

    The returned ``Location``'s ``path`` is taken from the matched
    declaration's ``Meta.filename`` — for same-file matches this is
    ``path``; for cross-file matches it's the imported module's source
    path (e.g. ``lib/NatDefs.pf``).  Callers that turn this back into
    an LSP URI (the LSP server's ``on_definition``) need to be ready
    for a different file than the request URI.

    Returns ``None`` when there is no resolvable symbol at ``pos``
    (whitespace, keyword, unparseable region) or when the declaration
    can't be found anywhere reachable from the file's import graph.

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

    # Prefer the meta's recorded source file when available: for
    # cross-file matches this is the imported module's path.  Falling
    # back to the request path keeps the behaviour consistent for
    # synthetic AST nodes whose meta lacks ``filename`` (e.g. test
    # fixtures built without a parser pass).
    resolved_path = getattr(decl_meta, "filename", None) or path
    return Location(path=resolved_path, range=_range_from_meta(decl_meta))


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


def completions_at(
    path: str, content: str, pos: Position, prelude: Sequence[str] = (),
) -> tuple[CompletionCandidate, ...]:
    """Return completion candidates visible at ``pos``.

    Candidate set:

    1. Deduce keywords (always included): the static lists
       :data:`COMPLETION_KEYWORDS`, :data:`COMPLETION_CONSTANT_KEYWORDS`,
       :data:`COMPLETION_TYPE_KEYWORDS`.  Clients filter against the
       prefix the user is typing, so we always return the full set;
       the cost is fixed and cheap.
    2. Top-level names declared in ``content`` itself -- theorems,
       lemmas, postulates, defines, recursive functions, unions (plus
       their constructors), predicates (plus their introduction rules).
    3. Top-level names reachable through ``Import.ast`` -- the
       user-written imports plus the auto-prepended prelude.  Walks
       transitively so e.g. ``import Nat`` surfaces ``suc``, ``zero``,
       ``+``, ``length``, ... reached through Nat's barrel chain to
       NatDefs / NatAdd / ... .  Diamond imports are guarded by a
       visited-module set.

    Local bindings carried in the env at ``pos`` are surfaced too --
    proof labels (``assume H: P``) and term variables (``arbitrary
    x:T``) and anything else the proof checker has put into scope by
    the time the cursor's enclosing proof statement runs.  We get the
    env by inserting a synthetic ``?`` at the cursor (stripping any
    partial identifier the user is typing first) and reading
    ``IncompleteProof.env``.

    Hole-aware priority: when the cursor sits on (or immediately past)
    an existing ``?`` and the check returns both an env and a goal,
    any local label whose formula equals or implies the goal is
    emitted with ``priority=0``.  Everything else stays at the default
    ``priority=1``.  The LSP adapter encodes this in ``sortText`` so
    matching labels float to the top of the picker -- user pressing
    ``Ctrl+Space`` on a ``?`` sees the proof terms that can plausibly
    close it first.

    ``prelude`` matches the meaning in :func:`check`.

    Returns at minimum the keyword / constant / type set when nothing
    else parses -- those alone still beat the client's word-based
    fallback while the user is mid-edit.
    """
    out: list[CompletionCandidate] = []
    seen_labels: set[str] = set()

    def _add(cand: CompletionCandidate) -> None:
        if cand.label in seen_labels:
            return
        seen_labels.add(cand.label)
        out.append(cand)

    for kw in COMPLETION_KEYWORDS:
        _add(CompletionCandidate(label=kw, kind="keyword"))
    for kw in COMPLETION_CONSTANT_KEYWORDS:
        _add(CompletionCandidate(label=kw, kind="constant"))
    for kw in COMPLETION_TYPE_KEYWORDS:
        _add(CompletionCandidate(label=kw, kind="type"))

    # Top-level names first.  The env walk below dedups against
    # ``seen_labels``, so any name already surfaced as a constructor /
    # theorem / function / ... isn't re-emitted as a generic
    # ``variable`` -- the AST walk's kind is more specific.
    from lsp.library import check_file
    result = check_file(path, content=content, prelude=prelude)
    if result.ast is not None:
        for cand in _collect_completion_names_from_ast(result.ast):
            _add(cand)

    env, goal = _completion_env_and_goal(path, content, pos, prelude)

    if env is not None:
        matching: set[str] = set()
        if goal is not None:
            try:
                matching = set(_matching_given_names(goal, env))
            except Exception:
                # Implication checks can raise on partially-populated
                # env state.  Treat any failure as "no boost" rather
                # than dropping local-binding candidates altogether.
                matching = set()
        for cand in _local_completion_candidates(env, seen=seen_labels):
            if cand.label in matching:
                cand = _bump_priority(cand, 0)
            _add(cand)

    return tuple(out)


def _completion_env_and_goal(
    path: str, content: str, pos: Position, prelude: Sequence[str],
) -> tuple[Optional["Env"], Optional["Formula"]]:
    """Return ``(env, goal)`` visible at ``pos``, or ``(None, None)``.

    Two paths:

    - Cursor on an existing ``?``: run :func:`check_file` on the
      original content with the hole targeted, read both fields off
      the ``IncompleteProof`` exception.
    - Anywhere else: scan backward over identifier characters to find
      the start of any partial identifier the user is typing, strip
      it, insert a synthetic ``?`` at the adjusted position, run
      :func:`check_file` against the modified content.  ``goal`` is
      returned alongside the env even though callers usually only
      care about it in the existing-hole case -- the synthetic-hole
      branch sets it to whatever goal happens to be visible at that
      point, which is fine for the matching-given priority boost.
    """
    from lsp.library import check_file

    existing = _find_hole_at(content, pos)
    if existing is not None:
        target = (existing.start.line, existing.start.column)
        with _target_hole(target):
            result = check_file(path, content=content, prelude=prelude)
        if result.ok:
            return (None, None)
        exc = result.exception
        return (getattr(exc, "env", None), getattr(exc, "formula", None))

    stripped = _strip_partial_word(content, pos)
    if stripped is None:
        return (None, None)
    adjusted_content, adjusted_pos = stripped
    inserted = _insert_hole(adjusted_content, adjusted_pos)
    if inserted is None:
        return (None, None)
    modified, hole_pos = inserted
    target = (hole_pos.line, hole_pos.column)
    with _target_hole(target):
        result = check_file(path, content=modified, prelude=prelude)
    if result.ok:
        return (None, None)
    exc = result.exception
    return (getattr(exc, "env", None), getattr(exc, "formula", None))


def _is_completion_ident_char(c: str) -> bool:
    """True iff ``c`` is a continuation character of a Deduce
    identifier.  Mirrors the ``wordPattern`` in
    ``editor/vscode/language-configuration.json``: ASCII alphanumerics,
    underscore, prime, bang, query, and Unicode subscript digits
    ``₀-₉``.
    """
    if c.isalnum():
        return True
    if c in ("_", "'", "!", "?"):
        return True
    if "₀" <= c <= "₉":
        return True
    return False


def _strip_partial_word(
    content: str, pos: Position
) -> Optional[tuple[str, Position]]:
    """Return ``(content with partial word at pos removed, adjusted_pos)``.

    Scans backward from the cursor over identifier characters and
    drops them from the buffer, returning the adjusted ``Position``
    of the word's start.  When the cursor isn't sitting just after an
    identifier (blank line, between tokens) returns ``(content, pos)``
    unchanged.  ``None`` when ``pos`` is out of range.
    """
    offset = _line_col_to_offset(content, pos)
    if offset is None:
        return None
    word_start = offset
    while word_start > 0 and _is_completion_ident_char(content[word_start - 1]):
        word_start -= 1
    if word_start == offset:
        return (content, pos)
    stripped = content[:word_start] + content[offset:]
    prefix = content[:word_start]
    line_no = prefix.count("\n") + 1
    last_nl = prefix.rfind("\n")
    col = word_start - (last_nl + 1) + 1 if last_nl >= 0 else word_start + 1
    return (stripped, Position(line=line_no, column=col))


def _local_completion_candidates(
    env: "Env", seen: set[str]
) -> Iterator[CompletionCandidate]:
    """Yield :class:`CompletionCandidate` items for in-scope bindings
    in ``env`` whose base name isn't already in ``seen``.

    Walks ``env.dict`` for ``ProofBinding`` (kind ``"label"``) and
    ``TermBinding`` (kind ``"variable"``).  The ``local`` flag on
    ``TermBinding`` is *module visibility*, not lexical scope, so we
    can't use it to distinguish hypothesis-bound names like the ``n``
    from ``arbitrary n:Nat`` from imported top-level decls.  Instead we
    let the AST walker run first and pass its ``seen`` set in, so
    every top-level name (theorem / define / union / constructor /
    function / predicate / rule / imported lemma) is already in
    ``seen`` by the time we get here -- the env walk only contributes
    *new* names, which by elimination are lexically local.

    ``ProofBinding`` has a real lexical-scope marker (the existing
    ``local`` flag, set by ``declare_local_proof_var``); we use it as
    an extra correctness check, though in practice dedup against
    ``seen`` would catch the same cases.
    """
    from abstract_syntax import ProofBinding, TermBinding, base_name

    for unique_name, binding in env.dict.items():
        name = base_name(unique_name)
        if name in seen:
            continue
        if isinstance(binding, ProofBinding):
            if not binding.local:
                continue
            yield CompletionCandidate(
                label=name,
                kind="label",
                detail=f"{name}: {binding.formula}",
            )
        elif isinstance(binding, TermBinding):
            type_str = str(binding.typ) if binding.typ is not None else ""
            yield CompletionCandidate(
                label=name,
                kind="variable",
                detail=f"{name}: {type_str}" if type_str else None,
            )


def _bump_priority(cand: CompletionCandidate, priority: int) -> CompletionCandidate:
    """Return a copy of ``cand`` with ``priority`` overridden.
    ``CompletionCandidate`` is frozen, so we can't mutate in place.
    """
    return CompletionCandidate(
        label=cand.label,
        kind=cand.kind,
        detail=cand.detail,
        priority=priority,
    )


def _collect_completion_names_from_ast(
    ast_nodes: Sequence["Statement"],
    _seen: Optional[set[str]] = None,
) -> Iterator[CompletionCandidate]:
    """Yield a :class:`CompletionCandidate` per named top-level decl.

    Walks the user file's top-level statements plus ``Import.ast``
    chains (mirror of the descent used in :func:`_find_declaration`).
    Constructors inside ``Union.alternatives`` and introduction rules
    inside ``Predicate.rules`` are yielded as their own candidates so
    e.g. ``suc`` shows up alongside ``Nat`` in the completion list.

    ``_seen`` is the visited-module set used to break diamond imports;
    callers should leave it ``None``.
    """
    from abstract_syntax import (
        Define,
        GenRecFun,
        Import,
        Postulate,
        Predicate,
        RecFun,
        Theorem,
        Union,
        base_name,
    )

    if _seen is None:
        _seen = set()

    for stmt in ast_nodes:
        if isinstance(stmt, Theorem):
            label = base_name(stmt.name)
            yield CompletionCandidate(
                label=label,
                kind="lemma" if stmt.isLemma else "theorem",
                detail=f"{label}: {stmt.what}",
            )
        elif isinstance(stmt, Postulate):
            label = base_name(stmt.name)
            yield CompletionCandidate(
                label=label,
                kind="postulate",
                detail=f"{label}: {stmt.what}",
            )
        elif isinstance(stmt, Define):
            label = base_name(stmt.name)
            detail = f"define {label}: {stmt.typ}" if stmt.typ is not None else None
            yield CompletionCandidate(label=label, kind="define", detail=detail)
        elif isinstance(stmt, RecFun):
            label = base_name(stmt.name)
            yield CompletionCandidate(label=label, kind="function")
        elif isinstance(stmt, GenRecFun):
            # ``recfun'' -- the polymorphic-recursion form.  Same
            # surface as ``recursive''/`RecFun' for completion purposes
            # (it's a callable with a name); the AST class is
            # different to track type-parameter bookkeeping.
            label = base_name(stmt.name)
            yield CompletionCandidate(label=label, kind="function")
        elif isinstance(stmt, Union):
            yield CompletionCandidate(label=base_name(stmt.name), kind="union")
            for cons in stmt.alternatives:
                yield CompletionCandidate(
                    label=base_name(cons.name), kind="constructor"
                )
        elif isinstance(stmt, Predicate):
            yield CompletionCandidate(label=base_name(stmt.name), kind="predicate")
            for rule in stmt.rules:
                yield CompletionCandidate(label=base_name(rule.name), kind="rule")
        elif isinstance(stmt, Import) and stmt.ast:
            if stmt.name in _seen:
                continue
            _seen.add(stmt.name)
            yield from _collect_completion_names_from_ast(stmt.ast, _seen=_seen)


# ---------------------------------------------------------------------------
# Internals shared by definition_of and list_symbols
# ---------------------------------------------------------------------------


def _range_from_meta(meta: Meta) -> Range:
    """Convert a lark ``Meta`` (or compatible duck) to a ``Range``."""
    return Range(
        start=Position(line=meta.line, column=meta.column),
        end=Position(line=meta.end_line, column=meta.end_column),
    )


def _meta_contains(meta: Meta, pos: Position) -> bool:
    """Test whether 1-indexed ``pos`` falls inside the ``meta`` range.

    The range is inclusive-start, exclusive-end (matches lark's
    convention and the documented Range semantics).
    """
    if getattr(meta, "empty", True):
        return False
    after_start = (meta.line, meta.column) <= (pos.line, pos.column)
    before_end = (pos.line, pos.column) < (meta.end_line, meta.end_column)
    return after_start and before_end


def _find_reference_at(
    ast_nodes: Sequence["Statement"], pos: Position, path: str
) -> Optional[str]:
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
    from abstract_syntax import AST, PVar, VarRef

    best: list[Optional[str]] = [None]
    best_span: list[Optional[int]] = [None]

    def visit(node: "AST") -> None:
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


def _meta_in_file(meta: Meta, path: str) -> bool:
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
    if not isinstance(fname, str) or fname == "???":
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


def _meta_span(meta: Meta) -> int:
    """Crude size measure for a ``Meta``; smaller wins ties in tree
    descent so inner nodes outrank enclosing ones."""
    line = int(meta.line)
    end_line = int(meta.end_line)
    column = int(meta.column)
    end_column = int(meta.end_column)
    if line == end_line:
        return end_column - column
    # Multi-line ranges are larger than any single-line range. Use a
    # huge per-line cost so we never pick a multi-line Var over a
    # single-line one that contains the cursor.
    return 10_000 * (end_line - line) + end_column


def _find_declaration(
    ast_nodes: Sequence["Statement"], target_name: str,
    _seen: Optional[set[str]] = None,
) -> Optional[Meta]:
    """Find a declaration whose uniquified ``name`` field equals
    ``target_name``.  Returns its ``Meta`` location, or ``None``.

    Walks top-level statements first, then descends into:

    - ``Union.alternatives`` — each ``Constructor`` carries its own
      uniquified name + ``Meta``, so F12 on ``suc`` from a
      ``case suc(n')`` pattern or a ``suc(n+m)`` expression resolves
      to the constructor's declaration line inside the ``union``
      block.
    - ``Predicate.rules`` — each introduction ``Rule`` likewise carries
      a uniquified name + ``Meta``, so F12 on a rule label inside a
      ``rule`` invocation jumps to the rule's declaration inside the
      ``predicate``/``relation`` block.
    - ``Import.ast`` — each ``Import`` (both user-written and prelude-
      injected) stashes the imported module's processed AST on the node
      itself.  Walking it gives us cross-file F12: a reference to a
      name declared in an imported module resolves to that file's
      Meta (whose ``filename`` field points at the source file).  The
      walk is transitive — ``Nat`` is a "barrel" module that imports
      ``NatDefs``, ``Base``, etc., so reaching the actual constructor
      declaration requires descending through the chain.

    ``_seen`` tracks already-visited module names so a diamond import
    (A → B, A → C, both → D) doesn't double-walk D's AST.  It's a
    private recursion parameter; callers should leave it ``None``.
    """
    from abstract_syntax import (
        Define,
        GenRecFun,
        Import,
        Postulate,
        Predicate,
        RecFun,
        Theorem,
        Union,
    )

    if _seen is None:
        _seen = set()

    # ``GenRecFun'' (the ``recfun'' keyword -- polymorphic recursion)
    # uses a different AST class than ``RecFun'' (``recursive'') but
    # is structurally the same for F12 purposes: top-level name +
    # location.  Without it here, F12 on ``gcd'' / ``div_alt'' /
    # other ``recfun'' declarations returned None.
    decl_types = (Theorem, Postulate, Define, RecFun, GenRecFun, Union, Predicate)
    for stmt in ast_nodes:
        if isinstance(stmt, decl_types) and getattr(stmt, "name", None) == target_name:
            return cast(Meta, stmt.location)
        if isinstance(stmt, Union):
            for cons in stmt.alternatives:
                if getattr(cons, "name", None) == target_name:
                    return cast(Meta, cons.location)
        elif isinstance(stmt, Predicate):
            for rule in stmt.rules:
                if getattr(rule, "name", None) == target_name:
                    return cast(Meta, rule.location)
        elif isinstance(stmt, Import) and stmt.ast:
            if stmt.name in _seen:
                continue
            _seen.add(stmt.name)
            found = _find_declaration(stmt.ast, target_name, _seen)
            if found is not None:
                return found
    return None


def _walk_ast(
    node: "AST",
    visit: Callable[["AST"], None],
    ast_class: type["AST"],
    seen: Optional[set[int]] = None,
) -> None:
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


def _symbol_info_for(stmt: "Statement", path: str) -> Optional[SymbolInfo]:
    """Build a ``SymbolInfo`` for a top-level statement, or ``None``
    if the node isn't a kind we surface (e.g. ``Auto``)."""
    from abstract_syntax import (
        Auto,
        Define,
        GenRecFun,
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
    elif isinstance(stmt, GenRecFun):
        # ``recfun'' -- the polymorphic-recursion form.  Same surface
        # as ``RecFun'' but parameter list is a list of (name, type)
        # tuples rather than parsed ``Param'' nodes.
        kind = SymbolKind.FUNCTION
        params = ", ".join(f"{n}: {t}" for (n, t) in stmt.vars)
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
) -> Union[WorkspaceEdit, UnsupportedRefineShape, None]:
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

    Returns:

    - :class:`WorkspaceEdit` when a template applies.
    - :class:`UnsupportedRefineShape` when the cursor is on a real
      hole with a goal but the goal's shape isn't in the table above.
      The shape list is surfaced so the caller can decide what to try
      next without re-reading the docstring.
    - ``None`` when the cursor isn't on a ``?`` or the file has no
      incomplete proof at that hole.

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
        return UnsupportedRefineShape(
            outcome="unsupported_shape",
            goal=str(formula),
            supported_shapes=REFINE_SUPPORTED_SHAPES,
        )

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


def _offset_to_line_col(content: str, offset: int) -> tuple[int, int]:
    """Inverse of ``_line_col_to_offset``: 0-indexed offset to 1-indexed (line, col)."""
    line = 1
    line_start = 0
    for i in range(offset):
        if content[i] == "\n":
            line += 1
            line_start = i + 1
    return (line, offset - line_start + 1)


def _refine_template(formula: "Formula", env: Optional["Env"]) -> Optional[str]:
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


def _fresh_assume_label(env: Optional["Env"]) -> str:
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
) -> tuple[str, ...]:
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


def _splittable_vars(env: "Env") -> tuple[str, ...]:
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
            if ty is None:
                continue
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


def _case_split_template(name: str, env: "Env") -> Optional[str]:
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
        if ty is None:
            return None
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


def _cases_template(var_name: str, formula: "Or", env: "Env") -> str:
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


def _switch_template(var_name: str, union_def: "UnionDecl", env: "Env") -> str:
    """Render a ``switch <var> { ... }`` block for a ``Union`` type.

    Each constructor's parameters get fresh names against the
    *enclosing* env -- but not against names introduced by *other*
    cases, since each ``case Cons(...) { ... }`` opens its own scope.
    Cases are emitted in the declaration order of
    ``union_def.alternatives``.
    """
    from abstract_syntax import base_name

    env_used = {base_name(k) for k in env.dict.keys()}

    case_lines: list[str] = []
    for alt in union_def.alternatives:
        cons_name = base_name(alt.name)
        # Reset per-case: each case body opens a new scope, so
        # naming conflicts only matter against the enclosing env
        # plus the other params of *this* case.
        used = set(env_used)
        params: list[str] = []
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


def _type_first_letter(ty: "Type") -> str:
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


def _induction_template(formula: "Formula", env: "Env") -> Optional[str]:
    """Render an ``induction T`` skeleton if ``formula`` is
    ``all x:T. P(x)`` with T a multi-alternative union."""
    from abstract_syntax import (
        All, TypeBinding, Union, VarRef, get_type_name,
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


def _render_induction(
    var_x: str, var_ty: "Type", body: "Formula", union_def: "UnionDecl", env: "Env"
) -> str:
    """Build the ``induction T\\n  case ... { ? }\\n  ...`` text."""
    from abstract_syntax import ResolvedVar, base_name
    # `is_recursive' and `update_all_head' live in proof_checker;
    # they're pipeline-side helpers, not protocol-specific, so the
    # protocol-neutrality guard in this module's docstring isn't
    # broken by importing them.
    from proof_checker import is_recursive, update_all_head

    union_name = union_def.name  # uniquified, e.g. ``N.0''
    env_used = {base_name(k) for k in env.dict.keys()}

    case_lines: list[str] = []
    for alt in union_def.alternatives:
        cons_name = base_name(alt.name)
        used = set(env_used)
        params: list[tuple[str, Type]] = []  # (name, type) pairs for this case
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
            (p, ty)
            for (p, ty) in params
            if is_recursive(union_name, ty)
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
) -> tuple[str, ...]:
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


def _eliminable_vars(env: "Env") -> tuple[str, ...]:
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


def _eliminate_template(label: str, env: "Env") -> Optional[str]:
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
    formula: "Formula", binding_name: str, env: "Env", dry_run: bool
) -> Optional[str]:
    """Pick a template for ``formula''.

    ``binding_name'' is the user-facing name of the hypothesis (e.g.
    ``H1''); it appears in the rendered template.  ``dry_run'' is
    set by ``_eliminable_vars'' to detect "is there a template?"
    without paying the rendering cost; in that mode we just return
    a non-None sentinel string when the shape is supported.
    """
    from abstract_syntax import (
        All, And, Bool, Call, IfThen, Or, Some, VarRef,
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


def _fresh_h_labels(env: "Env", count: int) -> list[str]:
    """Generate ``count`` fresh ``H<N>``-style labels not in env."""
    from abstract_syntax import base_name
    used = {base_name(k) for k in env.dict.keys()}
    out: list[str] = []
    n = 1
    for _ in range(count):
        while f"H{n}" in used:
            n += 1
        out.append(f"H{n}")
        used.add(f"H{n}")
        n += 1
    return out


def _eliminate_and(label: str, formula: "And", env: "Env") -> str:
    """``have h1: P by conjunct 1 of H\\nhave h2: Q by conjunct 2
    of H\\n?''"""
    labels = _fresh_h_labels(env, len(formula.args))
    lines = [
        f"have {h}: {arg} by conjunct {i + 1} of {label}"
        for i, (h, arg) in enumerate(zip(labels, formula.args))
    ]
    lines.append("?")
    return "\n".join(lines)


def _eliminate_or(label: str, formula: "Or", env: "Env") -> str:
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


def _eliminate_ifthen(label: str, formula: "IfThen", env: "Env") -> str:
    """``have h: Q by apply H to ?\\n?''"""
    h = _fresh_h_labels(env, 1)[0]
    return f"have {h}: {formula.conclusion} by apply {label} to ?\n?"


def _eliminate_all(label: str, formula: "All", env: "Env") -> str:
    """``H[?, ?, ...]'' (term args) or ``H<?, ?, ...>'' (type args).

    Handles a single all-block: ``all x:T1, y:T2. P'' yields
    ``H[?, ?]''.  Separate blocks (``all x:T1. all y:T2. P'')
    instantiate one at a time -- the user can chain.
    """
    from abstract_syntax import All, TypeType

    vars_in_block: list[tuple[str, Type]] = []
    cur: "Formula" = formula
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


def _eliminate_some(label: str, formula: "Some", env: "Env") -> str:
    """``obtain x1, ... where h: <body[subst]> from H\\n?''"""
    from abstract_syntax import ResolvedVar, base_name

    used = {base_name(k) for k in env.dict.keys()}
    fresh_witnesses: list[str] = []
    sub: dict[str, "Term"] = {}
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
    """Fill the hole at ``pos`` with a proof drawn from ``label``.

    The cursor must sit on (or immediately adjacent to) a ``?`` token;
    that ``?`` is the replacement target.  ``label`` names an in-scope
    local proof binding whose formula equals (or implies) the goal at
    the hole.

    Template shape depends on the match kind:

    - **Exact** (``binding.formula == goal``): replaces ``?`` with just
      ``<label>``.  A bare proof term is valid in both statement and
      term positions, so this is the only shape that's safe inside a
      conjunction slot ``pf1, pf2``, the body of ``have ... by``, etc.
    - **Implies-only** (the binding's formula strictly implies the goal
      via ``check_implies``): replaces ``?`` with ``conclude <goal> by
      <label>``.  Statement-level shape; the verbose form lets the
      proof checker run its auto-rule normalisation.

    Returns ``None`` when:

    - the cursor isn't on a ``?``,
    - the file has no incomplete proof at the cursor,
    - ``label`` isn't bound at the hole,
    - the bound formula neither equals nor implies the goal, or
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
) -> tuple[str, ...]:
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


def _implies(frm1: "Formula", frm2: "Formula") -> bool:
    """Side-effect-free wrapper around ``proof_checker.check_implies``.

    ``check_implies`` raises ``UserError`` (or ``MatchFailed``) on failure
    and prints when ``--verbose`` is set. Here we silence verbose
    temporarily and treat any exception as a negative answer, so this
    function can be used as a predicate inside candidate filters.
    """
    import flags
    from proof_checker import check_implies

    saved = flags.verbose
    flags.verbose = False
    try:
        check_implies(frm1.location, frm1, frm2)
        return True
    except Exception:
        return False
    finally:
        flags.verbose = saved


def _matching_given_names(goal: "Formula", env: "Env") -> tuple[str, ...]:
    """Names of local proof bindings that discharge ``goal``.

    Exact equality matches come first (alphabetical), followed by
    implies-only matches (alphabetical) -- the latter where the given's
    formula strictly implies the goal via ``proof_checker.check_implies``
    (handles ``Or`` introduction, ``And`` elimination, ``IfThen``
    covariance, ``All`` instantiation; see issue #361).
    """
    from abstract_syntax import ProofBinding, base_name

    exact: set[str] = set()
    implies: set[str] = set()
    for unique, binding in env.dict.items():
        if not isinstance(binding, ProofBinding):
            continue
        if not binding.local:
            continue
        name = base_name(unique)
        if binding.formula == goal:
            exact.add(name)
            implies.discard(name)
            continue
        if name in exact:
            continue
        if _implies(binding.formula, goal):
            implies.add(name)
    return tuple(sorted(exact)) + tuple(sorted(implies))


def _fill_from_given_template(label: str, goal: "Formula", env: "Env") -> Optional[str]:
    """Return a proof of ``goal`` using ``label`` when ``label`` names
    a local proof binding in ``env`` whose formula equals or implies
    ``goal``.

    Two template shapes:

    - **Exact match** (``binding.formula == goal``): returns just the
      bare label.  A bare proof term works as a proof in *both*
      statement position (top of a proof body, after ``assume``, ...)
      and term position (the slots of a conjunction ``pf1, pf2``, the
      body of ``have ... by``, an argument to ``apply``, ...).
      ``conclude <goal> by <label>`` would be syntactically rejected
      in term positions (``conclude`` is statement-level only), so the
      bare label is the only universally safe shape.
    - **Implies-only match** (``binding.formula`` strictly implies the
      goal via ``check_implies``; e.g. ``Or`` introduction, ``And``
      elimination): returns ``conclude <goal> by <label>``.  The
      verbose form lets the proof checker run its auto-rule
      normalisation, which a bare label wouldn't trigger.  This shape
      stays statement-level; users hitting it in a term position will
      need to wrap or restructure.  In practice exact matches dominate
      (the whole point of fill-from-given is that the formulas match),
      so the term-position breakage is mostly hypothetical.

    Returns ``None`` when the label isn't bound, isn't a local proof
    binding, or its formula neither equals nor implies the goal. The
    base-name match (rather than unique-name) mirrors
    :func:`_eliminate_template`. Implication checks use
    ``proof_checker.check_implies`` -- the same routine ``conclude ... by
    ...`` runs at proof-check time -- so any accepted label produces a
    template the proof checker will validate.
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
    if binding.formula == goal:
        return label
    if _implies(binding.formula, goal):
        return f"conclude {goal} by {label}"
    return None


# ---------------------------------------------------------------------------
# preview_conclude_at -- issue #420: like ``fill_from_given_at`` but
# matches modulo auto-rule normalization.
# ---------------------------------------------------------------------------
#
# ``fill_from_given_at`` / ``matching_givens_at`` compare ``binding.formula``
# against the goal under ``check_implies`` directly. The proof checker's
# catch-all branch of ``check_proof_of`` (proof_checker.py, ~line 1870) does
# more: it calls ``.reduce(env)`` on both sides first, which applies the
# active ``auto`` rewrite rules. So the checker accepts a label whose
# formula becomes the goal *after* auto fires, but ``matching_givens_at``
# reports no match. Concrete example from PR #413: given
# ``mult_le: 2^a * 1 ≤ 2^a * 2^(b - a)`` and goal ``2^a ≤ 2^a * 2^(b - a)``,
# the goal and given differ by ``uint_mult_one: n * 1 = n`` (an auto rule),
# so they are equal post-reduce but unequal pre-reduce.
#
# ``preview_conclude_at`` reproduces the checker's reduce-then-implies
# step as a read-only preview, so an agent can confirm "this label
# discharges the goal once auto fires" before committing the edit.


def preview_conclude_at(
    path: str, content: str, pos: Position,
    label: str,
    prelude: Sequence[str] = (),
    # Any: MCP tool-result payload -- a discriminated dict whose value
    # types vary by ``outcome`` (str fields, ``label``, etc.); the
    # adapter serializes it straight to JSON.
) -> Optional[dict[str, Any]]:
    """Preview ``conclude <goal> by <label>`` modulo auto-rule
    normalization.

    The cursor must sit on (or immediately adjacent to) a ``?`` token.
    ``label`` names an in-scope local proof binding. Both the binding's
    formula and the goal are reduced via ``.reduce(env)`` -- which
    applies any active ``auto`` rewrites -- and then
    ``proof_checker.check_implies`` decides whether the (reduced)
    binding discharges the (reduced) goal. This mirrors the catch-all
    branch of the proof checker, so any label this preview reports as
    ``discharges`` would also validate when used as the proof body of
    a ``conclude ... by ...``.

    Returns ``None`` when the cursor isn't on a ``?`` or the file has
    no incomplete proof at that hole. Otherwise returns a dict whose
    ``outcome`` field discriminates:

    - ``{"outcome": "discharges", "goal_normalized": "<str>",
       "given_normalized": "<str>"}`` -- the label's formula
       (post-reduce) implies the goal (post-reduce).

    - ``{"outcome": "no_match", "goal_normalized": "<str>",
       "given_normalized": "<str>", "reason": "<msg>"}`` -- the label
       is bound but its formula does not discharge the goal, even
       modulo auto.

    - ``{"outcome": "unbound", "label": "<name>"}`` -- ``label`` isn't
       bound at the hole.

    - ``{"outcome": "not_local", "label": "<name>"}`` -- ``label``
       refers to a non-local proof binding (a theorem reference).
       Theorem references are invoked by name in proof position
       directly, not via ``conclude ... by ...`` -- matching the
       filter already in :func:`fill_from_given_at`.
    """
    from abstract_syntax import ProofBinding, base_name

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

    matches = [k for k in env.dict if base_name(k) == label]
    if not matches:
        return {"outcome": "unbound", "label": label}
    binding = env.dict[matches[0]]
    if not isinstance(binding, ProofBinding):
        return {"outcome": "unbound", "label": label}
    if not binding.local:
        return {"outcome": "not_local", "label": label}

    from abstract_syntax import remove_mark

    given_red = binding.formula.reduce(env)
    goal_red = remove_mark(goal).reduce(env)

    if given_red == goal_red or _implies(given_red, goal_red):
        return {
            "outcome": "discharges",
            "goal_normalized": str(goal_red),
            "given_normalized": str(given_red),
        }

    return {
        "outcome": "no_match",
        "goal_normalized": str(goal_red),
        "given_normalized": str(given_red),
        "reason": (
            f"{label}: {given_red} does not imply {goal_red} "
            "(checked modulo auto-rule normalization)"
        ),
    }


# ---------------------------------------------------------------------------
# apply_at -- issue #402: forward `apply` preview tool
# ---------------------------------------------------------------------------
#
# Sibling to ``eliminate_at`` / ``fill_from_given_at``: simulates
# ``apply <theorem>[<args>] to ?`` against the goal at the cursor's
# hole and reports whether the apply would succeed, what conclusion it
# produces, and what premises the user would still have to discharge.
#
# Strategy: do the matching manually rather than splicing ``apply ...
# to ?`` and reading the result. Splicing looked simpler but suffers
# from a short-circuit in ``proof_checker.ModusPonens``: the inner
# ``?`` raises ``IncompleteProof`` *before* the apply's conclusion is
# compared with the outer goal, so a mismatched conclusion looks like
# success. Manual matching reproduces what the checker would do
# (``collect_all_if_then`` + ``formula_match``) and gives us full
# visibility into both the conclusion match and the premise.
#
# When ``args`` is non-empty, we splice ``define`` statements at the
# hole so the proof checker parses and type-checks the user-supplied
# arg expressions in the right scope (the variables ``arbitrary``-
# bound by the surrounding proof have to be visible). We then read the
# resulting term ASTs out of ``env`` and feed them to ``instantiate``.


def apply_at(
    path: str, content: str, pos: Position,
    theorem: str,
    args: Optional[Sequence[str]] = None,
    prelude: Sequence[str] = (),
    # Any: MCP tool-result payload -- a discriminated dict keyed on
    # ``outcome`` with heterogeneous values (rendered formulas, the
    # ``remaining_premises`` list, int counts); serialized to JSON.
) -> Optional[dict[str, Any]]:
    """Preview ``apply <theorem>[<args>] to ?`` at the cursor's hole.

    The cursor must sit on (or immediately adjacent to) a ``?`` token.
    ``theorem`` names an in-scope hypothesis, theorem, lemma, or
    postulate. ``args`` is the optional list of explicit term arguments
    instantiating the theorem's outermost ``all`` quantifiers --
    matching the ``theorem[arg, arg, ...]`` syntax. Each entry is the
    rendered text of a term (parsed in the scope at the hole, so
    ``arbitrary``-bound variables are visible).

    Returns ``None`` when the cursor isn't on a ``?`` or when the
    surrounding file fails to reach an ``IncompleteProof`` at the
    targeted hole (e.g. earlier parse / type errors). Otherwise returns
    a dict whose ``outcome`` field discriminates the shape:

    - ``{"outcome": "ok", "conclusion": "<rendered formula>",
       "remaining_premises": ["<formula>", ...]}``
       The apply would succeed; ``conclusion`` is the goal at the hole
       (which the apply matched), and ``remaining_premises`` is the
       ordered list of obligations the user still has to prove. A
       conjunctive premise is split on top-level ``and`` so the list
       maps to what the user would put after ``to``.

    - ``{"outcome": "unifies_against", "goal": "<rendered formula>",
       "reason": "<message>"}``
       The conclusion did not match the goal, or instantiation could
       not deduce the all-bound variables.

    - ``{"outcome": "unbound", "theorem": "<name>"}``
       ``theorem`` is not in scope at the hole.

    - ``{"outcome": "arity_mismatch", "expected": N, "got": M}``
       Too many ``[args]`` were supplied for the theorem's outer
       quantifiers (``expected`` is the maximum acceptable count;
       ``got`` is ``len(args)``). Also returned without ``expected`` /
       ``got`` when ``theorem`` is not an implication at all.
    """
    hole_range = _find_hole_at(content, pos)
    if hole_range is None:
        return None

    from error import IncompleteProof
    from lsp.library import check_file

    # Splice ``define`` statements at the hole so user-supplied arg
    # expressions are parsed and type-checked in the surrounding
    # proof's scope. Without args we just check the file as-is.
    if args:
        run_path, run_content, target = _splice_apply_args(
            path, content, hole_range, args
        )
    else:
        run_path = path
        run_content = content
        target = (hole_range.start.line, hole_range.start.column)

    with _target_hole(target):
        result = check_file(run_path, content=run_content, prelude=prelude)
    if result.ok:
        return None

    exc = result.exception
    if not isinstance(exc, IncompleteProof):
        # Splicing a malformed arg expression can produce a UserError
        # at the synthetic ``define`` line. Surface it as a parse-of-
        # arg error rather than pretending the apply itself failed.
        if args:
            msg = getattr(exc, "message_body", None) or str(exc) or ""
            return {
                "outcome": "unifies_against",
                "goal": "",
                "reason": "could not parse args: " + msg.strip(),
            }
        return None
    goal = getattr(exc, "formula", None)
    env = getattr(exc, "env", None)
    if goal is None or env is None:
        return None

    # When ``args`` were spliced via ``define _apply_at_arg_N = <arg>``,
    # the goal printed by the checker is in terms of the synthetic
    # alias instead of the user's original term (e.g. ``_apply_at_arg_0``
    # in place of ``Q``). Render the goal with full reduction so the
    # user-visible string is unaffected by the splice.
    from abstract_syntax import set_reduce_all
    if args:
        _call_untyped(set_reduce_all, True)
        try:
            goal_for_display = goal.reduce(env)
        finally:
            _call_untyped(set_reduce_all, False)
        goal_str = str(goal_for_display)
    else:
        goal_str = str(goal)

    from abstract_syntax import ProofBinding, TermBinding, base_name
    matches = [k for k in env.dict if base_name(k) == theorem]
    if not matches or not isinstance(env.dict[matches[0]], ProofBinding):
        return {"outcome": "unbound", "theorem": theorem}
    formula = env.dict[matches[0]].formula

    # Resolve and apply each user-supplied arg by instantiating the
    # outermost ``All``-quantifier on the theorem formula.
    if args:
        from proof_checker import instantiate
        from abstract_syntax import All
        for i, raw_arg in enumerate(args):
            arg_key = _APPLY_AT_ARG_PREFIX + str(i)
            arg_matches = [k for k in env.dict if base_name(k) == arg_key]
            if not arg_matches:
                return {
                    "outcome": "unifies_against",
                    "goal": goal_str,
                    "reason": "could not parse arg #" + str(i + 1)
                              + ": " + raw_arg,
                }
            binding = env.dict[arg_matches[0]]
            if not isinstance(binding, TermBinding) or binding.defn is None:
                return {
                    "outcome": "unifies_against",
                    "goal": goal_str,
                    "reason": "arg #" + str(i + 1) + " is not a term: "
                              + raw_arg,
                }
            if not isinstance(formula, All):
                already_consumed = i
                return {
                    "outcome": "arity_mismatch",
                    "expected": already_consumed,
                    "got": len(args),
                }
            formula = _call_untyped(instantiate, formula.location, formula, binding.defn)

    return _apply_match_manual(formula, goal, env, goal_str)


_APPLY_AT_ARG_PREFIX = "_apply_at_arg_"


def _splice_apply_args(
    path: str, content: str, hole_range: Range, args: Sequence[str]
) -> tuple[str, str, tuple[int, int]]:
    """Splice ``define _apply_at_arg_N = <arg_N>`` statements before
    the hole and return ``(path, modified_content, target_pos)``.

    The new ``?`` ends up on the line after the last define so the
    surrounding proof body's indentation isn't disturbed.
    """
    start_off = _line_col_to_offset(content, hole_range.start)
    end_off = _line_col_to_offset(content, hole_range.end)
    assert start_off is not None and end_off is not None
    indent = _line_indent_at(content, hole_range.start)

    define_lines = "".join(
        f"define {_APPLY_AT_ARG_PREFIX}{i} = {raw}\n{indent}"
        for i, raw in enumerate(args)
    )
    splice_text = define_lines + "?"
    spliced = content[:start_off] + splice_text + content[end_off:]

    new_offset = start_off + len(splice_text) - 1
    new_line, new_col = _offset_to_line_col(spliced, new_offset)
    return path, spliced, (new_line, new_col)


def _apply_match_manual(
    formula: "Formula", goal: "Formula", env: "Env", goal_str: str
    # Any: MCP tool-result payload -- discriminated dict (see apply_at).
) -> dict[str, Any]:
    """Compute the result of ``apply <formula> to ?`` against ``goal``.

    Mirrors what ``ModusPonens`` does in ``proof_checker``:

    - ``if P then C``: ``C`` must reduce to the goal; ``P`` is the
      premise the user still has to prove.
    - ``all xs. <body>``: collect outer ``all``-quantifiers and the
      ``(prem, conc)`` pairs of the body via ``collect_all_if_then``,
      then ``formula_match`` each conclusion against the goal to
      deduce the all-bound variables; substitute those back into the
      premise.
    - anything else: ``arity_mismatch`` -- the theorem isn't an
      implication.

    Reductions happen with ``reduce_all`` enabled so the synthetic
    ``define _apply_at_arg_N = <arg>`` bindings the splice introduces
    fold back to their definitions before the comparison.
    """
    from abstract_syntax import All, IfThen, formula_match, set_reduce_all
    from error import MatchFailed
    from proof_checker import collect_all_if_then

    location = formula.location

    _call_untyped(set_reduce_all, True)
    try:
        if isinstance(formula, IfThen):
            if formula.conclusion.reduce(env) == goal.reduce(env):
                premise = formula.premise.reduce(env)
                return {
                    "outcome": "ok",
                    "conclusion": goal_str,
                    "remaining_premises": _split_premise_on_and(premise),
                }
            return {
                "outcome": "unifies_against",
                "goal": goal_str,
                "reason": (
                    "the proved formula\n\t" + str(formula.conclusion)
                    + "\ndoes not match the goal\n\t" + goal_str
                ),
            }

        if isinstance(formula, All):
            try:
                vars, imps = _call_untyped(collect_all_if_then, location, formula, env)
            except Exception as e:
                msg = getattr(e, "message_body", None) or str(e) or ""
                return {
                    "outcome": "arity_mismatch",
                    "reason": msg.strip() if msg else (
                        "expected an if-then formula under "
                        "the all-quantifiers, not " + str(formula)
                    ),
                }
            reasons = []
            for prem, conc in imps:
                matching: dict[str, "Term"] = {}
                try:
                    _call_untyped(
                        formula_match,
                        location,
                        vars,
                        conc,
                        goal,
                        matching,
                        env,
                        numeric_literals=True,
                    )
                except MatchFailed as e:
                    reasons.append(str(e))
                    continue
                unmatched = [v for v in vars if v.name not in matching]
                if unmatched:
                    reasons.append(
                        "could not deduce instantiations for "
                        + ", ".join(str(v) for v in unmatched)
                    )
                    continue
                premise = prem.substitute(matching).reduce(env)
                return {
                    "outcome": "ok",
                    "conclusion": goal_str,
                    "remaining_premises": _split_premise_on_and(premise),
                }
            return {
                "outcome": "unifies_against",
                "goal": goal_str,
                "reason": (
                    "\n".join(reasons) if reasons
                    else "no quantified implication conclusion matched the goal"
                ),
            }

        return {
            "outcome": "arity_mismatch",
            "reason": "expected an if-then formula, not " + str(formula),
        }
    finally:
        _call_untyped(set_reduce_all, False)


def _split_premise_on_and(formula: "Formula") -> list[str]:
    """If ``formula`` is a top-level conjunction, render each conjunct
    separately so the result maps to what the user would put after
    ``to`` (Deduce desugars ``to A, B`` into a tuple proof of an
    ``And``). Otherwise return a singleton list."""
    from abstract_syntax import And

    if isinstance(formula, And):
        return [str(arg) for arg in formula.args]
    return [str(formula)]


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


def _collect_lemmas_in_scope(
    ast_nodes: Optional[Sequence["Statement"]], prelude: Sequence[str]
) -> tuple[LemmaInfo, ...]:
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


def _lemma_info_for(stmt: "Statement", public_only: bool = False) -> Optional[LemmaInfo]:
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
        signature = cast(str, _call_untyped(stmt.pretty_print, 0)).rstrip("\n")
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
) -> tuple[LemmaMatch, ...]:
    """Return ranked lemmas visible at ``pos``, best matches first.

    Driven by zero, one, or both of two signals:

    - The cursor sits on a ``?`` token: the goal at that hole defines
      the shape we're searching for.  ``available_lemmas_at`` extracts
      the goal text and uses its head operator and operator/function
      tokens for ranking.
    - ``query`` is given: a substring (matched against the rendered
      lemma signature) or a goal-shape pattern containing ``_``
      placeholders (each ``_`` matches any run of characters).

    When both are given they combine -- a lemma that matches the goal
    *and* the query ranks above one that matches only one.  When
    neither is given (off-hole exploration), every in-scope lemma is
    surfaced, ranked by module proximity (user-file first) then by
    name -- useful for "what's available here?" browsing without
    inserting a synthetic ``?``.

    The result is a tuple of :class:`LemmaMatch` ordered by descending
    ``relevance``; ties broken by name.  ``relevance`` is normalised
    so the best match in the set is ``1.0`` and others scale linearly.
    Only theorems, lemmas, and postulates are surfaced.

    The lemma set covers everything in scope at the cursor: the
    user-file's own declarations, the modules it explicitly
    ``import``s (transitively, through public imports), and any
    module named in ``prelude``.  Returns ``()`` only when the file
    produces no candidates at all, or when a given ``query`` matches
    nothing.
    """
    from lsp.library import check_file

    hole_range = _find_hole_at(content, pos)
    goal_text: Optional[str] = None
    goal_ast: Optional["Formula"] = None
    env: Optional["Env"] = None
    if hole_range is not None:
        target = (hole_range.start.line, hole_range.start.column)
        with _target_hole(target):
            result = check_file(path, content=content, prelude=prelude)
        if not result.ok:
            goal = _goal_from_exception(result.exception, hole_range)
            if goal is not None:
                goal_text = goal.formula
            exc = result.exception
            goal_ast = getattr(exc, "formula", None)
            env = getattr(exc, "env", None)
        ast_nodes = result.ast
    else:
        result = check_file(path, content=content, prelude=prelude)
        ast_nodes = result.ast

    # A proof can't cite the theorem it's proving -- circularity --
    # so drop the enclosing theorem from candidates before ranking.
    # Only applies when the cursor is at a hole inside a proof body;
    # browse mode (cursor anywhere else) keeps every declaration
    # visible, including the theorem that happens to start at pos.
    exclude = (
        _enclosing_theorem_name(ast_nodes, pos)
        if hole_range is not None
        else None
    )
    candidates = _collect_lemma_candidates(
        path, ast_nodes, prelude, exclude_name=exclude
    )
    if not candidates:
        return ()

    given_pairs = _collect_local_givens(env)
    typed_by_name = _typed_formula_index(env)
    ranked = _rank_lemmas(
        candidates,
        goal_text,
        query,
        _module_for_path(path),
        goal_ast=goal_ast,
        env=env,
        given_pairs=given_pairs,
        typed_formula_by_name=typed_by_name,
    )
    if not ranked:
        return ()

    if limit > 0:
        ranked = ranked[:limit]
    return tuple(ranked)


def insert_lemma_at(
    path: str,
    content: str,
    pos: Position,
    name: str,
    prelude: Sequence[str] = (),
) -> Optional[WorkspaceEdit]:
    """Return a tier-aware ``WorkspaceEdit`` that references ``name`` at
    ``pos``.

    Template shape depends on how the lemma's conclusion relates to the
    current goal at the hole at ``pos`` -- the same tier classifier
    :func:`available_lemmas_at` uses to rank candidates (see
    :class:`LemmaMatch`). The four shapes:

    - **full** (conclusion unifies, every premise discharged by a local
      given): replaces ``?`` with ``conclude <goal> by apply <name> to
      <p1>, ..., <pN>`` -- or just ``conclude <goal> by <name>`` when
      the lemma has no premises.
    - **premises_remain** (conclusion unifies, some premises stay open):
      replaces ``?`` with ``apply <name> to ?`` -- one fresh ``?`` for
      the user to fill.
    - **rewrite_subterm** (equation lemma whose LHS/RHS matches a goal
      subterm): replaces ``?`` with ``replace <name>``.
    - **none** (no tier match, or cursor not on a hole, or browse mode):
      inserts the bare ``<name>`` at ``pos`` (zero-width edit when not
      on a hole, otherwise replacing the ``?``).

    Tier is recomputed server-side from the current buffer, so callers
    don't have to round-trip it through the prior
    :func:`available_lemmas_at` response -- a buffer that changed
    between picker and insertion still produces a sensible template.

    Returns ``None`` when ``name`` is not in scope as a theorem, lemma,
    or postulate at ``pos``.
    """
    from lsp.library import check_file

    hole_range = _find_hole_at(content, pos)
    goal_text: Optional[str] = None
    goal_ast: Optional["Formula"] = None
    env: Optional["Env"] = None

    if hole_range is not None:
        target = (hole_range.start.line, hole_range.start.column)
        with _target_hole(target):
            result = check_file(path, content=content, prelude=prelude)
        if not result.ok:
            exc = result.exception
            goal = _goal_from_exception(exc, hole_range)
            if goal is not None:
                goal_text = goal.formula
            goal_ast = getattr(exc, "formula", None)
            env = getattr(exc, "env", None)
        ast_nodes = result.ast
    else:
        result = check_file(path, content=content, prelude=prelude)
        ast_nodes = result.ast

    candidates = _collect_lemma_candidates(path, ast_nodes, prelude)
    target_formula: Optional["Formula"] = None
    for info, formula, _module in candidates:
        if info.name == name:
            target_formula = formula
            break
    if target_formula is None:
        return None

    tier: Optional[str] = None
    discharged: tuple[tuple[str, str], ...] = ()
    instantiations: tuple[str, ...] = ()
    if goal_ast is not None and env is not None:
        given_pairs = _collect_local_givens(env)
        _score, tier, discharged, instantiations = _unify_score(
            target_formula, goal_ast, env, given_pairs
        )

    template = _insert_lemma_template(
        name, target_formula, tier, discharged, goal_text, instantiations
    )

    if hole_range is None:
        zero_range = Range(start=pos, end=pos)
        return WorkspaceEdit(path=path, range=zero_range, new_text=template)

    template = _indent_continuation(
        template, _line_indent_at(content, hole_range.start)
    )
    return WorkspaceEdit(path=path, range=hole_range, new_text=template)


def _insert_lemma_template(
    name: str,
    formula: "Formula",
    tier: Optional[str],
    discharged: tuple[tuple[str, str], ...],
    goal_text: Optional[str],
    instantiations: tuple[str, ...] = (),
) -> str:
    """Pick the tactic-shape template for ``insert_lemma_at`` (issue #690).

    The tier picks the surrounding shape; ``discharged`` supplies the
    given labels for the ``full`` case; ``formula`` is consulted to
    count premises when there are no labels (e.g. ``premises_remain``
    where every premise is open, or ``full`` with 0 premises).

    ``instantiations`` (issue #734) supplies the explicit ``[t1, ..., tN]``
    forall-instantiation suffix: when the unifier resolved every
    all-bound variable of the lemma, the splice writes
    ``name[t1, ..., tN]`` instead of bare ``name`` so the resulting
    ``apply ... to ?`` (or ``conclude``/``replace``) elaborates with
    the right inner subgoal. Empty tuple ``()`` means either no
    forall to instantiate, or the unifier didn't resolve all vars.
    """
    name_inst = f"{name}[{', '.join(instantiations)}]" if instantiations else name
    if tier == "full":
        if not discharged and goal_text is not None:
            return f"conclude {goal_text} by {name_inst}"
        labels = ", ".join(label for _, label in discharged)
        if goal_text is not None:
            return f"conclude {goal_text} by apply {name_inst} to {labels}"
        return f"apply {name_inst} to {labels}"
    if tier == "premises_remain":
        return f"apply {name_inst} to ?"
    if tier == "rewrite_subterm":
        return f"replace {name_inst}"
    return name


def _module_for_path(path: str) -> str:
    """Module name for the file at ``path`` -- the path's stem."""
    from pathlib import Path

    return Path(path).stem


def _enclosing_theorem_name(
    ast_nodes: Optional[Sequence["Statement"]], pos: Position
) -> Optional[str]:
    """Return the base name of the user-file ``Theorem`` whose body
    encloses ``pos``, or ``None`` when ``pos`` isn't inside one.

    Theorems don't nest at the top level, so the enclosing one is the
    last ``Theorem`` whose start ``location`` is at or before ``pos``
    and which has no later top-level statement starting at or before
    ``pos``. The intent is to skip the theorem currently being proved
    when surfacing lemmas at one of its holes -- the proof can't
    refer to itself.
    """
    if ast_nodes is None:
        return None
    from abstract_syntax import Theorem, base_name

    enclosing: Optional[str] = None
    for stmt in ast_nodes:
        loc = getattr(stmt, "location", None)
        if loc is None or getattr(loc, "empty", True):
            continue
        if not _meta_at_or_before(loc, pos):
            # ``ast_nodes`` is in source order; no later sibling can be
            # at-or-before ``pos`` either.
            break
        if isinstance(stmt, Theorem):
            enclosing = base_name(stmt.name)
        else:
            # A non-Theorem starts at-or-before pos, which means any
            # earlier Theorem ended before this stmt -- pos is outside
            # it. Reset.
            enclosing = None
    return enclosing


def _collect_lemma_candidates(
    path: str,
    ast_nodes: Optional[Sequence["Statement"]],
    prelude: Sequence[str],
    exclude_name: Optional[str] = None,
) -> tuple[tuple[LemmaInfo, "Formula", str], ...]:
    """Build the ranking input: theorems/lemmas/postulates with their
    formula AST and module of origin.

    Returns a tuple of ``(LemmaInfo, formula_ast, module)`` triples,
    drawn from:

    - The user file: one entry per ``Theorem``/``Postulate`` in source
      order, including private ones (everything in the file is in
      scope at a hole there).
    - Each module the user file explicitly ``import``s, and the
      transitive closure of those modules' public imports (matching
      what ``Import.collect_exports`` propagates): public theorems
      and postulates only, filtered through the import's
      ``using``/``hiding`` clause.
    - Each module named in ``prelude`` (public theorems/postulates
      only, matching ``print_theorems``' visibility filter).

    When ``exclude_name`` is set, any theorem/postulate with that
    base name is dropped from the user-file slice -- used to keep
    the theorem currently being proved out of the picker at one of
    its own holes.
    """
    from abstract_syntax import (
        Import as _ImportNode,
        Postulate,
        Theorem,
        get_uniquified_modules,
    )

    out = []
    seen_names: set[str] = set()
    user_module = _module_for_path(path)
    prelude_set = set(prelude)
    seen_modules: set[str] = set()

    def _collect_from_module(
        module_ast: Optional[Sequence["Statement"]], module_name: str,
        importer: Optional["Import"],
    ) -> None:
        if module_ast is None:
            return
        for stmt in module_ast:
            if importer is not None and not importer._filter_admits(stmt):
                continue
            if isinstance(stmt, (Theorem, Postulate)):
                info = _lemma_info_for(stmt, public_only=True)
                if info is not None and info.name not in seen_names:
                    seen_names.add(info.name)
                    out.append((info, stmt.what, module_name))
            elif isinstance(stmt, _ImportNode) and stmt.visibility == "public":
                if stmt.name in seen_modules or stmt.name == user_module:
                    continue
                if stmt.name in prelude_set:
                    # Prelude is walked separately below.
                    continue
                seen_modules.add(stmt.name)
                _collect_from_module(stmt.ast, stmt.name, stmt)

    if ast_nodes is not None:
        for stmt in ast_nodes:
            if isinstance(stmt, _ImportNode):
                if stmt.name in prelude_set or stmt.name == user_module:
                    continue
                if stmt.name in seen_modules:
                    continue
                seen_modules.add(stmt.name)
                _collect_from_module(stmt.ast, stmt.name, stmt)
                continue
            if not isinstance(stmt, (Theorem, Postulate)):
                continue
            info = _lemma_info_for(stmt, public_only=False)
            if info is None:
                continue
            if info.name in seen_names:
                continue
            if exclude_name is not None and info.name == exclude_name:
                continue
            seen_names.add(info.name)
            out.append((info, stmt.what, user_module))

    if prelude:
        modules = get_uniquified_modules()
        for module_name in prelude:
            if module_name in seen_modules:
                continue
            module_ast = modules.get(module_name)
            if module_ast is None:
                continue
            seen_modules.add(module_name)
            _collect_from_module(module_ast, module_name, None)

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


def _goal_tokens(text: Optional[str]) -> frozenset[str]:
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


def _formula_head_symbol(formula: "Formula") -> Optional[str]:
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
                return cast(str, base_name(cast(str, inner.get_name())))
        if isinstance(rator, VarRef):
            return cast(str, base_name(cast(str, rator.get_name())))
        return None
    if isinstance(f, And):
        return "and"
    if isinstance(f, Or):
        return "or"
    if isinstance(f, Bool):
        return "true" if f.value else "false"
    return None


def _formula_symbols(formula: "Formula") -> frozenset[str]:
    """Set of all rator names appearing in ``formula`` (recursively).

    Drives the symbol-overlap signal in lemma ranking.  Bound
    variables introduced by ``All``/``Some`` are excluded -- only the
    uniquified rator names of ``Call`` nodes count.  Names are
    returned as their ``base_name`` so they line up with the
    user-visible operator/function names used in goal text."""
    from abstract_syntax import (
        AST, And, Bool, Call, IfThen, Or, TermInst, VarRef, base_name,
    )

    out: set[str] = set()

    def visit(node: "AST") -> None:
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


def _query_pattern(query: Optional[str]) -> Optional[re.Pattern[str]]:
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


# Score per unify tier (issue #690). Tier names match what's emitted
# on ``LemmaMatch.unify_tier`` and what the LSP ``deduce/insertLemma``
# request branches on when choosing a tactic shape.
_UNIFY_TIER_SCORE: dict[str, float] = {
    "full": 1.0,
    "premises_remain": 0.7,
    "rewrite_subterm": 0.4,
}


def _collect_local_givens(env: Optional["Env"]) -> tuple[tuple[str, "Formula"], ...]:
    """``(label, formula_ast)`` for local proof bindings in ``env``.

    Mirrors how :func:`_matching_given_names` walks ``env.dict``, but
    returns the formula AST too so the unify scorer can match a
    lemma's substituted premise against each given. ``label`` is the
    user-visible base name; duplicates collapse to the first hit so
    later phases can look up by label as a dict.
    """
    if env is None:
        return ()
    from abstract_syntax import ProofBinding, base_name

    seen: set[str] = set()
    out: list[tuple[str, Formula]] = []
    try:
        items = env.dict.items()
    except AttributeError:
        return ()
    for unique, binding in items:
        if not isinstance(binding, ProofBinding):
            continue
        if not binding.local:
            continue
        name = base_name(unique)
        if name in seen:
            continue
        seen.add(name)
        out.append((name, binding.formula))
    return tuple(out)


def _peel_quantified_implication(
    formula: Optional["Formula"],
) -> Optional[tuple[list["ResolvedVar"], list["Formula"], "Formula"]]:
    """Peel outer ``All`` and ``IfThen`` to ``(vars, premises, conc)``.

    Returns the list of all-bound variables (as :class:`VarRef`), the
    list of premise formulas (flattening top-level ``And``), and the
    final conclusion. ``None`` when the formula's shape is one the
    unifier can't handle (the matcher itself is recursive over the
    conclusion -- we only need the *outer* structure here).
    """
    from abstract_syntax import All, And, IfThen, ResolvedVar

    f = formula
    if f is None:
        return None

    vars: list["ResolvedVar"] = []
    while isinstance(f, All):
        name, ty = f.var
        vars.append(ResolvedVar(f.location, ty, name))
        f = f.body

    premises: list["Formula"] = []
    while isinstance(f, IfThen):
        prem = f.premise
        if isinstance(prem, And):
            premises.extend(prem.args)
        else:
            premises.append(prem)
        f = f.conclusion

    return vars, premises, f


def _formulas_match_modulo_env(
    frm1: "Formula", frm2: "Formula", env: Optional["Env"]
) -> bool:
    """Best-effort equality of two formulas under ``env`` reduction.

    Used to ask "does this substituted premise match a given?".
    Wraps a comparison that first tries identity, then auto-reduces
    both sides; on any internal exception falls back to identity so
    a ranker bug never crashes ``available_lemmas_at``.
    """
    if frm1 is frm2:
        return True
    try:
        if frm1 == frm2:
            return True
    except Exception:
        pass
    if env is None:
        return False
    try:
        return bool(frm1.reduce(env) == frm2.reduce(env))
    except Exception:
        return False


def _iter_subterms(node: "AST") -> list["AST"]:
    """Yield ``node`` and every AST descendant (depth-first).

    Used by the ``rewrite_subterm`` tier: walk the goal's subterms
    looking for one that the equation's LHS (or RHS) can match.
    Shared-subtree guard via :func:`_walk_ast` keeps this O(n).
    """
    from abstract_syntax import AST

    out: list[AST] = []
    _walk_ast(node, out.append, ast_class=AST)
    return out


def _typed_formula_index(env: Optional["Env"]) -> dict[str, "Formula"]:
    """Build a one-shot ``base_name -> typed_formula`` index over the
    proof bindings in ``env``.

    The formula stored on :class:`abstract_syntax.declarations.Theorem`
    and :class:`Postulate` is the parsed, pre-typecheck AST -- bound
    variables and operators are still :class:`OverloadedVar` carrying
    a list of candidate resolved names. The matcher's
    ``get_name()`` returns only the first candidate, which produces
    both false positives (an unrelated lemma whose first overload
    happens to alias the goal's resolved operator -- e.g.
    ``add_commute_uint_int : all x:UInt, y:Int. x + y = y + x``
    against a ``UInt + UInt`` goal) and false negatives (a
    right-type lemma whose first overload doesn't alias the goal --
    e.g. ``uint_add_commute`` when its first candidate is the
    inherited Nat ``+``).

    The proof environment, by contrast, stores the post-typecheck
    formula -- overloads have been resolved to single names and
    variable types pinned to a single overload candidate during the
    prelude's check pass. Using that formula for unification (issue
    #690) fixes both classes of bug at once.

    Theorem names are forbidden from being overloaded (see
    :meth:`Postulate.uniquify`), so a base-name lookup uniquely
    identifies the binding.

    Building this index once per request -- instead of scanning
    ``env.dict`` per lemma in the ranker -- saves a quadratic walk
    over an env that holds ~2000 entries when the full stdlib is in
    scope.
    """
    if env is None or not hasattr(env, "dict"):
        return {}
    from abstract_syntax import ProofBinding, base_name

    out: dict[str, "Formula"] = {}
    for key, binding in env.dict.items():
        if not isinstance(binding, ProofBinding):
            continue
        # First entry wins -- the env may have shadowed re-bindings,
        # but theorem names can't be overloaded so this is at most
        # one real entry per base name anyway.
        out.setdefault(base_name(key), binding.formula)
    return out


def _render_instantiations(
    vars: Sequence["ResolvedVar"], matching: dict[str, "Term"]
) -> tuple[str, ...]:
    """Render ``matching[v.name]`` for each ``v`` in ``vars``.

    Returns the rendered terms in declaration order so the caller can
    emit ``name[t1, ..., tN]``. Returns ``()`` if any var is missing
    from ``matching`` or any rendering raises -- a partial
    instantiation suffix would be ill-formed.
    """
    out: list[str] = []
    for v in vars:
        if v.name not in matching:
            return ()
        try:
            out.append(str(matching[v.name]))
        except Exception:
            return ()
    return tuple(out)


def _unify_score(
    formula: Optional["Formula"],
    goal_ast: Optional["Formula"],
    env: Optional["Env"],
    given_pairs: tuple[tuple[str, "Formula"], ...],
) -> tuple[
    float,
    Optional[str],
    tuple[tuple[str, str], ...],
    tuple[str, ...],
]:
    """Score how well ``formula``'s conclusion unifies with ``goal_ast``.

    Three-tier classifier (see :class:`LemmaMatch` for the meaning of
    each tier):

    - ``"full"`` -- conclusion unifies, every premise discharged by a
      given. Score ``1.0``.
    - ``"premises_remain"`` -- conclusion unifies, some premises stay
      open. Score ``0.7``.
    - ``"rewrite_subterm"`` -- conclusion is an equation whose LHS
      (or RHS) unifies with a subterm of the goal. Score ``0.4``.
    - falls back to ``(0.0, None, (), ())`` on no match, missing AST/
      env, or any internal exception in the unifier.

    Returns ``(score, tier, discharged_premises, instantiations)``.
    ``discharged_premises`` is a tuple of ``(premise_text, given_label)``
    pairs filled in for the ``"full"`` tier (empty otherwise).
    ``instantiations`` is the rendered substitution for the lemma's
    outermost ``all``-bound variables, in declaration order, so
    callers can emit ``name[t1, ..., tN]`` splices (issue #734).
    Empty when no tier matched or the lemma had no forall to peel.

    The implementation reuses :func:`formula_match` from
    ``abstract_syntax.rewrite`` -- the same first-order matcher
    ``apply_at`` uses to deduce all-bound instantiations against a
    goal. Wrapped in a broad ``except`` because this is a ranking
    heuristic: a failed unification must never crash the caller.
    """
    if goal_ast is None or env is None or formula is None:
        return (0.0, None, (), ())

    from abstract_syntax import Call, VarRef, formula_match
    from error import MatchFailed

    peeled = _peel_quantified_implication(formula)
    if peeled is None:
        return (0.0, None, (), ())
    vars, premises, conc = peeled

    location = getattr(formula, "location", None)

    # Tier 1/2: try to unify the conclusion against the goal.
    matching: dict[str, "Term"] = {}
    conc_matched = False
    try:
        formula_match(location, vars, conc, goal_ast, matching, env)
        unmatched = [v for v in vars if v.name not in matching]
        if not unmatched:
            conc_matched = True
    except MatchFailed:
        pass
    except Exception:
        pass

    if conc_matched:
        instantiations = _render_instantiations(vars, matching)
        if not premises:
            return (_UNIFY_TIER_SCORE["full"], "full", (), instantiations)

        discharged: list[tuple[str, str]] = []
        all_discharged = True
        for prem in premises:
            try:
                instantiated = prem.substitute(matching)
            except Exception:
                all_discharged = False
                break
            label = None
            for given_label, given_frm in given_pairs:
                if _formulas_match_modulo_env(instantiated, given_frm, env):
                    label = given_label
                    break
            if label is None:
                all_discharged = False
                break
            discharged.append((str(instantiated), label))

        if all_discharged:
            return (
                _UNIFY_TIER_SCORE["full"],
                "full",
                tuple(discharged),
                instantiations,
            )
        return (
            _UNIFY_TIER_SCORE["premises_remain"],
            "premises_remain",
            (),
            instantiations,
        )

    # Tier 3: equation conclusion -> try LHS/RHS against goal subterms.
    if isinstance(conc, Call) and isinstance(conc.rator, VarRef):
        try:
            if conc.rator.get_name() == "=" and len(conc.args) == 2:
                lhs, rhs = conc.args
                subterms = _iter_subterms(goal_ast)
                for side in (lhs, rhs):
                    # When the side is a bare forall-var, ``formula_match``
                    # binds it to the first subterm visited -- typically
                    # the whole goal -- which is a meaningless
                    # "instantiation" for the splice. Skip emitting
                    # instantiations in that case: a bare ``replace name``
                    # lets the rewrite engine pattern-match across the
                    # goal as before.
                    side_is_bare_var = isinstance(side, VarRef) and side in vars
                    for sub in subterms:
                        sub_matching: dict[str, "Term"] = {}
                        try:
                            formula_match(
                                location, vars, side, sub, sub_matching, env
                            )
                        except MatchFailed:
                            continue
                        except Exception:
                            continue
                        unmatched = [
                            v for v in vars if v.name not in sub_matching
                        ]
                        if unmatched:
                            continue
                        insts: tuple[str, ...] = (
                            ()
                            if side_is_bare_var
                            else _render_instantiations(vars, sub_matching)
                        )
                        return (
                            _UNIFY_TIER_SCORE["rewrite_subterm"],
                            "rewrite_subterm",
                            (),
                            insts,
                        )
        except Exception:
            pass

    return (0.0, None, (), ())


def _rank_lemmas(
    candidates: tuple[tuple[LemmaInfo, "Formula", str], ...],
    goal_text: Optional[str],
    query: Optional[str],
    user_module: str,
    goal_ast: Optional["Formula"] = None,
    env: Optional["Env"] = None,
    given_pairs: tuple[tuple[str, "Formula"], ...] = (),
    typed_formula_by_name: Optional[dict[str, "Formula"]] = None,
) -> list[LemmaMatch]:
    """Score and sort candidate lemmas.

    ``candidates`` is the tuple from :func:`_collect_lemma_candidates`.
    Returns a list of :class:`LemmaMatch` with normalised relevance
    in ``[0.0, 1.0]``; only candidates with a strictly positive raw
    score are included.

    Six signals contribute to the score:

    1. ``8.0 * unify_score`` -- first-order match of the conclusion
       against the goal AST, with credit for premises discharged by
       a local given (issue #690). Dominates the textual signals so
       that a lemma whose conclusion actually unifies outranks one
       that only shares a head symbol.
    2. ``4.0 * head_score`` -- rendered head-operator match (the
       string-level signal from issue #403; used as a fallback when
       the goal AST isn't available).
    3. ``2.0 * overlap`` -- fraction of goal tokens that appear in
       the lemma's formula symbols.
    4. ``1.0 * proximity`` -- ``1`` if the lemma comes from the
       user's own file, ``0`` otherwise.
    5. ``2.0 * substring_score`` -- query substring against name (1)
       or signature (0.5).
    6. ``3.0 * pattern_score`` -- query goal-shape pattern (``_``
       placeholders) against the rendered signature.

    When neither a goal nor a query is given, runs in *browse mode*:
    every candidate is surfaced, ranked only by module proximity
    (user-file lemmas first) then alphabetically. This is what makes
    off-hole exploration usable -- an agent can ask "what's in scope
    here?" without inserting a synthetic hole.
    """
    goal_head = _goal_head_symbol(goal_text)
    goal_syms = _goal_tokens(goal_text)
    pattern = _query_pattern(query)
    query_substr = (query or "").strip().lower()
    has_substring_query = bool(query_substr) and pattern is None
    browse_mode = goal_text is None and not query
    has_unify_signal = goal_ast is not None and env is not None

    raw_scores: list[
        tuple[float, LemmaInfo, str, Optional[str], tuple[tuple[str, str], ...]]
    ] = []

    # First pass: compute every cheap signal (proximity, head, overlap,
    # substring, pattern) for each candidate.  ``_unify_score`` is the
    # only expensive scorer -- it walks the lemma's conclusion against
    # the goal AST, applying ``auto_rewrites`` at every subterm, and
    # costs ~10ms per lemma on the typical stdlib (Bug 1 of #690: with
    # ~600 lemmas in scope this added up to ~6s before the picker
    # appeared).  Deferring the unifier to a top-K subset of cheap-
    # ranked candidates trims that to ~1s while keeping the lemmas
    # that actually unify (which always share head/operator tokens
    # with the goal) in the considered set.
    prelim: list[
        tuple[float, LemmaInfo, "Formula", str, float]
    ] = []  # (cheap_raw, info, formula, module, proximity-marker)
    for info, formula, module in candidates:
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

        # When the user typed a goal-shape pattern or substring, only
        # surface lemmas that match it. Run this cheap filter before
        # walking formula ASTs; query-only MCP calls otherwise pay the
        # recursive symbol extraction cost for every in-scope theorem.
        if has_substring_query and substring_score == 0.0:
            continue
        if pattern is not None and pattern_score == 0.0:
            continue

        if browse_mode:
            # Surface every candidate; ranking is proximity then name.
            # Use a fixed baseline so out-of-module candidates aren't
            # dropped by the ``raw <= 0`` filter below.
            raw_scores.append((1.0 + proximity, info, module, None, ()))
            continue

        if goal_head is not None:
            head = _formula_head_symbol(formula)
            head_score = 1.0 if head == goal_head else 0.0
        else:
            head_score = 0.0

        if goal_syms:
            symbols = _formula_symbols(formula)
            shared = goal_syms & symbols
            overlap = len(shared) / len(goal_syms)
            # Jaccard breaks ties between lemmas with the same overlap
            # by preferring those whose formula has no symbols outside
            # the goal -- ``uint_add_commute`` ({+, =}) outranks
            # ``uint_minus_add`` ({+, -, =}) on a ``+ = +`` goal because
            # the latter is "noisier". Important once UNIFY_TOP_K cuts
            # off the tail: without this, dozens of equation lemmas
            # tied at overlap=1.0 elbowed the real match out of the
            # window (issue #690 Bug 1).
            denom = len(goal_syms | symbols)
            specificity = len(shared) / denom if denom else 0.0
        else:
            overlap = 0.0
            specificity = 0.0

        cheap_raw = (
            4.0 * head_score
            + 2.0 * overlap
            + 1.5 * specificity
            + 1.0 * proximity
            + 2.0 * substring_score
            + 3.0 * pattern_score
        )

        # Skip candidates with no positive cheap signal: a lemma whose
        # conclusion head differs from the goal, shares no operator
        # tokens with it, lives in another module, and matches no
        # query has zero chance of being relevant.  Running the
        # unifier on it would be pure waste.
        if cheap_raw <= 0.0:
            continue

        prelim.append((cheap_raw, info, formula, module, proximity))

    # Second pass: run the unifier only on the K cheapest-ranked
    # survivors.  K is intentionally a few multiples of the LSP
    # default ``limit`` (50) -- a lemma that would unify but ranks
    # outside the top 150 by textual signals is exotic, and the
    # latency win (≈6s -> ≈1s on stdlib-sized preludes) outweighs
    # the rare miss.  When a future request needs a bigger window,
    # widen this constant rather than the per-candidate cost.
    prelim.sort(key=lambda t: (-t[0], t[1].name))
    UNIFY_TOP_K = 50
    for idx, (cheap_raw, info, formula, module, _proximity) in enumerate(
        prelim
    ):
        if has_unify_signal and idx < UNIFY_TOP_K:
            # Prefer the env-resolved typed formula over the parsed
            # one when available: the latter still has OverloadedVar
            # candidate lists for both operators and variable types,
            # and the matcher's first-candidate-only comparison
            # produces both false-positive and false-negative full
            # tiers depending on lexical order (issue #690 Bug 2/3).
            typed_formula = (
                typed_formula_by_name.get(info.name)
                if typed_formula_by_name is not None
                else None
            )
            unify_input = typed_formula if typed_formula is not None else formula
            unify_score, unify_tier, discharged, _insts = _unify_score(
                unify_input, goal_ast, env, given_pairs
            )
        else:
            unify_score, unify_tier, discharged = 0.0, None, ()

        raw = 8.0 * unify_score + cheap_raw
        raw_scores.append((raw, info, module, unify_tier, discharged))

    if not raw_scores:
        return []

    max_raw = max(r for r, _, _, _, _ in raw_scores)
    if max_raw <= 0.0:
        return []

    raw_scores.sort(key=lambda t: (-t[0], t[1].name))
    matches = []
    seen_names: set[str] = set()
    for raw, info, module, unify_tier, discharged in raw_scores:
        if info.name in seen_names:
            continue
        seen_names.add(info.name)
        matches.append(
            LemmaMatch(
                name=info.name,
                kind=info.kind,
                signature=info.signature,
                module=module,
                relevance=raw / max_raw,
                unify_tier=unify_tier,
                discharged_premises=discharged,
            )
        )
    return matches


def _hole_fingerprint(goal_formula: str, givens: tuple[Given, ...]) -> str:
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
    formula: "Formula",
    env: "Env",
    loc: Optional[Meta],
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
    if not cast(bool, _call_untyped(is_equation, eq_formula)):
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
            (lhs, rhs) = _call_untyped(split_equation, loc, eq_formula, env)
        except Exception:
            return RewritePreview(
                outcome="not_an_equation",
                formula=str(eq_formula),
            )
        eq_formula = _call_untyped(mkEqual, loc, rhs, lhs)

    eq_reduced = eq_formula.reduce(env)
    before = formula.reduce(env)

    from error import UserError
    from proof_checker import apply_rewrites

    try:
        after = _call_untyped(apply_rewrites, loc, before, [eq_reduced], env)
    except UserError as exc:
        msg = getattr(exc, "message_body", None) or str(exc)
        if "no need for replace" in msg:
            reason = (
                "this equation is handled automatically -- "
                "no `replace` needed"
            )
        elif "could not find any matches" in msg:
            try:
                (lhs, _rhs) = _call_untyped(split_equation, loc, eq_reduced, env)
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
    names: list[str], formula: "Formula", env: "Env", loc: Optional[Meta]
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
        after = _call_untyped(expand_definitions, loc, formula, defs, env)
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


# ---------------------------------------------------------------------------
# auto_rules_at -- list `auto` rewrite rules in scope at a position
# ---------------------------------------------------------------------------
#
# Issue #404: when Deduce reports "no need for replace because this
# equation is handled automatically" or a goal silently simplifies
# before a tactic can fire, the user wants to know which `auto`
# declaration is responsible without grepping the prelude.  This
# function returns every `auto` rule visible at the cursor in
# declaration order -- the same order ``auto_rewrites`` (in
# ``abstract_syntax``) tries them when several heads match.


def auto_rules_at(
    path: str,
    content: str,
    pos: Position,
    prelude: Sequence[str] = (),
) -> tuple[AutoRule, ...]:
    """Return the ``auto`` rewrite rules in scope at ``pos``.

    The returned tuple lists rules in *declaration order* -- the same
    order the auto-rewriter applies them when multiple equations
    share a head constructor.  Sources are walked in this order:

    1. Every module currently cached in ``get_uniquified_modules()``
       (the prelude transitively, plus any module the user file
       imports), each module's ``Auto`` statements in source order.
       Modules are visited in the alphabetical iteration order of
       the cache, which is stable for a given prelude key.
    2. The user's file itself, ``Auto`` statements in source order,
       restricted to those whose location is at or before ``pos``.

    Each entry's ``equation`` is the rendered formula of the theorem
    the rule references; if the theorem can't be located in any
    walked AST (rare -- e.g. a private lemma in a module we can
    only see through a filtered import), ``equation`` is ``""``.

    ``prelude`` matches the meaning in :func:`check`.  Returns ``()``
    when the file fails to parse before any prelude is loaded.
    """
    from abstract_syntax import (
        Auto,
        Postulate,
        Theorem,
        get_uniquified_modules,
    )
    from lsp.library import check_file
    from pathlib import Path as _Path

    # Run the pipeline once. We don't bail on errors -- partial
    # results are still useful (and the prelude state is loaded by
    # ``_prepare_state`` before the user file is even parsed).
    result = check_file(path, content=content, prelude=prelude)

    user_module = _Path(path).stem
    cached_modules = get_uniquified_modules()

    # Build a lookup ``unique_name -> formula_text`` so each Auto
    # can resolve its referenced theorem.  Walk every module we
    # know about, then the user file's own AST (which overrides any
    # cached entry that happens to share a unique name -- shouldn't
    # happen in practice, but the cache could be slightly stale).
    formula_by_name: dict[str, "Formula"] = {}
    for module_name, module_ast in cached_modules.items():
        if module_name == user_module:
            continue
        for stmt in module_ast:
            if isinstance(stmt, (Theorem, Postulate)):
                formula_by_name[stmt.name] = stmt.what
    if result.ast is not None:
        for stmt in result.ast:
            if isinstance(stmt, (Theorem, Postulate)):
                formula_by_name[stmt.name] = stmt.what

    rules: list[AutoRule] = []

    for module_name in sorted(cached_modules.keys()):
        if module_name == user_module:
            continue
        module_ast = cached_modules[module_name]
        for stmt in module_ast:
            if isinstance(stmt, Auto):
                rules.append(_auto_rule_from_stmt(stmt, module_name, formula_by_name))

    if result.ast is not None:
        for stmt in result.ast:
            if isinstance(stmt, Auto) and _meta_at_or_before(stmt.location, pos):
                rules.append(_auto_rule_from_stmt(stmt, user_module, formula_by_name))

    return tuple(rules)


def _meta_at_or_before(meta: Meta, pos: Position) -> bool:
    """True iff ``meta`` starts at or before 1-indexed ``pos``.

    Empty/missing meta counts as "before" so we don't drop a rule
    just because the parser elided its location info.
    """
    if getattr(meta, "empty", True):
        return True
    if meta.line < pos.line:
        return True
    if meta.line == pos.line and meta.column <= pos.column:
        return True
    return False


def _auto_rule_from_stmt(
    stmt: "Auto", module_name: str, formula_by_name: dict[str, "Formula"]
) -> "AutoRule":
    """Render an ``Auto`` AST node into an :class:`AutoRule`.

    ``Auto.name`` is a ``PVar`` (or compatible proof reference) whose
    ``.name`` field holds the uniquified identifier after
    ``uniquify``.  ``base_name`` strips the suffix to recover what
    the user wrote.  ``formula_by_name`` is the lookup built in
    :func:`auto_rules_at`.
    """
    from abstract_syntax import Env, base_name, split_auto_rule

    unique = getattr(stmt.name, "name", None)
    if unique is None:
        # Best effort: render whatever Term is here (shouldn't happen
        # in practice -- the parsers always emit a PVar).
        return AutoRule(
            name=str(stmt.name), equation="", module=module_name
        )
    formula = formula_by_name.get(unique)
    if formula is None:
        return AutoRule(name=base_name(unique), equation="", module=module_name)
    rule = split_auto_rule(stmt.location, formula, Env())
    premise = " and ".join(str(prem) for prem in rule.premises) or None
    return AutoRule(
        name=base_name(unique),
        equation=str(formula),
        module=module_name,
        premise=premise,
    )
