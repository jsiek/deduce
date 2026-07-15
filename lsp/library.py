"""Library-mode entry point for the Deduce pipeline.

Started life as Step 1 of the LSP/MCP plan (see docs/lsp-plan.md), where
``check_file`` ran the parse + uniquify + type/proof check pipeline and
returned a structured ``CheckResult`` instead of printing and calling
``exit``. The CLI in ``deduce.py`` is a thin wrapper around it.

**Step 6** added per-call state isolation. The pipeline keeps a lot of
module-level mutable state (caches, sets, dicts) in ``proof_checker``
and ``abstract_syntax``. Without intervention, two consecutive
``check_file`` calls in one process can pollute each other -- the CLI
never noticed because each invocation runs in a fresh process. The
helpers below snapshot the post-prelude container state once per
unique prelude and restore it before each user-file check, so:

* the same prelude isn't re-parsed and re-checked on every call (the
  expensive ``lib/`` reload only happens once); and

* state from one call doesn't leak into the next.

``abstract_syntax``'s fresh-name counter (Step 12) is now an
explicit ``UniquifyContext`` threaded through ``uniquify_deduce``.
We keep a ``_post_prelude_ctx`` baseline -- a snapshot of the
counter just after the prelude finished -- and fork a fresh
context from it for each user-file check.  That way successive
checks produce reproducible names *and* never collide with
prelude-cached names.

``proof_checker.name_id`` (its own counter, used post-uniquify
for synthesis paths -- predicate desugaring, induction/switch
fresh labels) is captured the same way as the tracked containers
and restored between calls.  Without this, two checks of the same
source would produce different suffixes for ``EvenDeriv.<id>`` /
``D_<rule>.<id>`` / etc. -- which would survive the per-statement
cache only because ``_hash_ast`` is memoised on the pre-decl AST
node, and any future change that recomputes the hash post-decl
would silently invalidate the cache for every predicate-using
module.  Issue #368.
"""

from __future__ import annotations

import os
import sys
import threading
import traceback as _traceback
from dataclasses import dataclass, field
from pathlib import Path
from types import ModuleType
from typing import TYPE_CHECKING, Optional, Sequence, cast

if TYPE_CHECKING:
    from lsp.debugger import Debugger


_TrackedAttr = tuple[ModuleType, str]
_SnapshotKey = tuple[str, str]
_TrackedContainer = dict[object, object] | set[object] | list[object]
_ContainerSnapshot = dict[_SnapshotKey, _TrackedContainer]
_ScalarSnapshot = dict[_SnapshotKey, object]


# Process-wide lock around ``check_file``.  The Deduce pipeline
# mutates module-level state (prelude caches, name counters, the
# ``uniquified_modules`` dict).  Concurrent callers race -- e.g. a
# leaked daemon program-thread from a stale DAP debug session can
# corrupt the prelude bootstrap of the next session, surfacing as
# "undefined variable: Nat" because the second bootstrap cleared
# ``uniquified_modules`` from under the first.  Serialise here
# rather than asking every caller to do it.
_check_file_lock = threading.Lock()

from lark.tree import Meta

import abstract_syntax as _abstract_syntax
import parser as _lark_parser
import proof_checker as _proof_checker
import rec_desc_parser as _rd_parser
from abstract_syntax import (
    Import,
    Statement,
    UniquifyContext,
    add_uniquified_module,
    get_recursive_descent,
    get_uniquified_modules,
)
from error import ErrorSink, WarningRecord, set_active_warning_sink
from flags import (
    get_experimental_imperative,
    get_debugger,
    get_verbose,
    set_debugger,
)
from proof_checker import check_deduce, uniquify_deduce


@dataclass
class CheckResult:
    """Outcome of running the Deduce pipeline on a single file.

    Attributes:
        ok:               True iff parse + uniquify + check_deduce all
                          succeeded.
        error_message:    ``str(exception)`` if the pipeline raised.
                          ``None`` when ``ok`` is True.
        error_traceback:  Full Python traceback at the point of failure,
                          for callers that want it (e.g. ``--traceback``).
                          ``None`` when ``ok`` is True.
        exception:        The first raised exception object, preserved
                          so structured callers (``lsp.query.check``)
                          can read ``e.location`` / ``e.message_body``
                          without re-parsing strings. ``None`` when ok.
                          When ``check_file`` runs in collect-errors
                          mode, this is just ``errors[0]``; the full
                          list lives in ``errors``.
        errors:           All exceptions collected during this run.
                          Empty list when ``ok`` is True; one-element
                          list in the default raise-on-first mode;
                          potentially several entries when
                          ``collect_errors=True`` was passed (one per
                          failing top-level statement / hole).
        module_name:      Module name derived from the filename
                          (``Path(filename).stem``).
        ast:              On success, the **post-typecheck** AST: the
                          form returned by ``proof_checker.check_deduce``
                          after type checking has resolved overloaded
                          ``Var.resolved_names`` to the single chosen
                          name. On failure, the post-uniquify AST that
                          existed before the error (still with
                          unresolved overload candidates) when parse +
                          uniquify succeeded; ``None`` on parse or
                          uniquify failure. See issue #305.
    """

    ok: bool
    error_message: Optional[str]
    error_traceback: Optional[str]
    exception: Optional[BaseException]
    module_name: str
    ast: Optional[list[Statement]]
    # In collect-errors mode every entry is a ``Diagnostic``; in
    # single-error fallback mode (see ``__post_init__``) the list
    # carries whatever was raised — including non-``Diagnostic``
    # exceptions like ``InternalError``. Typed as ``BaseException`` so
    # both shapes flow through unchanged.
    errors: Optional[list[BaseException]] = None
    # ``warning()`` emissions captured during this run. Only populated
    # when ``check_file`` was called with ``collect_errors=True`` (the
    # LSP/MCP path); the CLI leaves this empty because warnings were
    # printed to stdout in the usual way.
    warnings: list[WarningRecord] = field(default_factory=list)

    def __post_init__(self) -> None:
        if self.errors is None:
            # Default: a single-error result (or no error). Mirrors the
            # historical ``exception`` field so unchanged callers see
            # the same shape.
            self.errors = [self.exception] if self.exception is not None else []


def check_file(
    filename: str,
    tracing_functions: Sequence[str] = (),
    prelude: Sequence[str] = (),
    content: Optional[str] = None,
    collect_errors: bool = False,
    debugger: Optional["Debugger"] = None,
    prewarm_modules: Sequence[str] = (),
    parser: Optional[str] = None,
) -> CheckResult:
    """Run the Deduce pipeline on ``filename`` and return a CheckResult.

    Does not print to stdout (apart from verbose-mode tracing controlled
    by ``flags.py``) and never calls ``sys.exit``. All recoverable errors
    surface through ``CheckResult.error_message``.

    Args:
        filename:           Path to the ``.pf`` file to check.
        tracing_functions:  Function names to trace (``--trace``).
        prelude:            Module names to import as a private prelude
                            in front of the file. Pass ``[]`` for no
                            prelude (matches ``--no-stdlib``).
        content:            If given, parsed instead of reading
                            ``filename`` from disk. Use this to check
                            an unsaved editor buffer. ``filename`` is
                            still used for import resolution and
                            error messages. Bypasses the
                            ``uniquified_modules`` cache, since the
                            cached AST corresponds to disk content.
        collect_errors:     When ``False`` (default), the pipeline
                            raises on the first error and ``result``
                            carries that single exception — matching
                            the CLI / ``goal_at`` / MCP behaviour.
                            When ``True``, an :class:`ErrorSink` is
                            threaded through ``check_deduce`` so each
                            top-level statement that fails (and each
                            ``?`` hole) appears as a separate entry in
                            ``result.errors``; ``result.exception`` is
                            still the first one for backward compat.
                            ``lsp.query.check`` opts in to this so
                            every error in the buffer becomes its own
                            editor diagnostic.
        parser:             Optional parser override. ``None`` (default)
                            uses whichever parser ``flags.recursive_descent``
                            currently selects -- matches the CLI behaviour
                            and is what every existing caller wants.
                            ``"recursive-descent"`` and ``"lalr"`` force the
                            user file to be parsed with that specific
                            parser, regardless of the global flag.
                            When an explicit parser is given, the
                            user-file AST cache is bypassed (a cached
                            entry could have been produced by the other
                            parser; the whole point of asking for a
                            specific parser is to actually run it).
                            The prelude is still served from its
                            existing snapshot -- prelude AST equivalence
                            across parsers is verified by CI.
        prewarm_modules:    Module names to pre-load into the
                            ``uniquified_modules`` cache during prelude
                            bootstrap, but **not** prepended as imports
                            to ``filename``. Useful for batch test
                            runners where many files independently
                            ``import`` a fixed set of library modules:
                            paying the parse+uniquify once amortises
                            across the whole batch, while keeping the
                            user-visible import surface identical to
                            ``--no-stdlib`` semantics. Becomes part of
                            the prelude cache key alongside ``prelude``.
        debugger:           When given, attached to the active session
                            via ``flags.set_debugger`` for the user
                            file's check_proofs / reduce hooks (Phase
                            5 / Step 21).  ``None`` (the default) means
                            no debug session; hook callbacks short-
                            circuit so non-debug runs pay one attribute
                            load per hook site and nothing else.  The
                            prelude is *always* loaded debugger-detached
                            (``_prepare_state`` runs before we attach),
                            so a ``--debug`` user lands at the first
                            statement of *their* file rather than
                            stepping through ``lib/``.

    Concurrency note: this function is NOT thread-safe. The Deduce
    pipeline mutates module-level state, and the snapshot/restore
    machinery here assumes a single caller at a time. Callers that
    want to fan out should serialize.
    """
    if parser is not None and parser not in ("recursive-descent", "lalr"):
        raise ValueError(
            f"check_file: parser must be None, 'recursive-descent', or "
            f"'lalr'; got {parser!r}"
        )
    with _check_file_lock:
        return _check_file_locked(
            filename, tracing_functions, prelude, content,
            collect_errors=collect_errors, debugger=debugger,
            prewarm_modules=prewarm_modules,
            parser=parser,
        )


def _check_file_locked(
    filename: str,
    tracing_functions: Sequence[str],
    prelude: Sequence[str],
    content: Optional[str],
    collect_errors: bool,
    debugger: Optional["Debugger"],
    prewarm_modules: Sequence[str] = (),
    parser: Optional[str] = None,
) -> CheckResult:
    """Body of ``check_file``, run under the global pipeline lock."""
    # Prelude bootstrap runs without a debugger attached -- the user
    # asked to step through their own file, not lib/.  Phase 5 plan
    # rationale: this is the only sensible default and avoids PR #269's
    # "first prelude statement traps" bug in long-lived daemons.
    _prepare_state(tuple(prelude), tuple(prewarm_modules))
    # Each user-file check forks a fresh ctx from the post-prelude
    # baseline so successive checks produce reproducible names.  See
    # ``UniquifyContext`` and the ``_post_prelude_ctx`` machinery
    # below for the rationale.
    ctx = (
        _post_prelude_ctx.snapshot()
        if _post_prelude_ctx is not None
        else UniquifyContext()
    )
    if debugger is None:
        return _check_file_impl(
            filename, tracing_functions, prelude, content, ctx,
            collect_errors=collect_errors,
            parser=parser,
        )
    # Attach the debugger only for the user-file check; detach in a
    # ``finally`` so a quit/crash mid-session leaves the next check_file
    # call with a clean ``flags.debugger == None``.  ``DebuggerQuit`` is
    # caught and translated into a normal failed CheckResult so callers
    # don't have to special-case it.
    from lsp.debugger import DebuggerQuit
    prev = get_debugger()
    set_debugger(debugger)
    try:
        return _check_file_impl(
            filename, tracing_functions, prelude, content, ctx,
            collect_errors=collect_errors,
            parser=parser,
        )
    except DebuggerQuit as e:
        module_name = Path(filename).stem
        return CheckResult(
            ok=False,
            error_message=f"debugger session ended: {e}",
            error_traceback=None,
            exception=e,
            module_name=module_name,
            ast=None,
        )
    finally:
        set_debugger(prev)


def _check_file_impl(
    filename: str,
    tracing_functions: Sequence[str],
    prelude: Sequence[str],
    content: Optional[str],
    ctx: UniquifyContext,
    collect_errors: bool = False,
    parser: Optional[str] = None,
) -> CheckResult:
    """The original ``check_file`` body.

    Kept private so ``_prepare_state`` can call it during prelude
    bootstrap without re-entering the snapshot machinery.
    """
    module_name = Path(filename).stem
    if get_verbose():
        print("Deducing file:", filename)

    ast: Optional[list[Statement]] = None
    try:
        cached = get_uniquified_modules()
        # The cache is keyed by module name and corresponds to a
        # specific on-disk state. When the caller passes in-memory
        # content, it is usually an unsaved editor buffer, so the cache
        # may be stale. MCP tools, however, read the file from disk and
        # pass that exact text through this same API; those calls are
        # cacheable because they match the cache's on-disk contract.
        # When an explicit ``parser`` is requested, skip the cache: a
        # cached entry may have been produced by the *other* parser,
        # and the whole point of the explicit choice is to actually
        # run that parser on this file.
        experimental_imperative = get_experimental_imperative()
        use_cache = (
            parser is None
            and not experimental_imperative
            and (content is None or _content_matches_file(filename, content))
        )
        if use_cache and module_name in cached:
            ast = cached[module_name]
        else:
            if content is None:
                with open(filename, "r", encoding="utf-8") as f:
                    program_text = f.read()
            else:
                program_text = content

            if parser is None:
                use_rd = get_recursive_descent()
            else:
                use_rd = parser == "recursive-descent"

            deduce_dir = os.path.dirname(sys.argv[0])
            if use_rd:
                _rd_parser.set_deduce_directory(deduce_dir)
                _rd_parser.set_filename(filename)
                _rd_parser.init_parser()
                ast = _rd_parser.parse(
                    program_text, trace=get_verbose(), error_expected=False,
                    experimental_imperative=experimental_imperative,
                )
            else:
                _lark_parser.set_deduce_directory(deduce_dir)
                _lark_parser.set_filename(filename)
                _lark_parser.init_parser()
                ast = _lark_parser.parse(
                    program_text, trace=get_verbose(), error_expected=False,
                    experimental_imperative=experimental_imperative,
                )

            if len(prelude) > 0:
                # Suppress the prelude entry for any module the user explicitly
                # imports with `using`/`hiding`. Both imports run during
                # ``uniquify_deduce`` and additively populate the env, so an
                # unfiltered prelude entry races ahead of a filtered user
                # entry and pollutes the env with names the user wanted to
                # exclude. Skipping the prelude entry leaves the user's
                # filtered import as the only one for that module. See #365.
                user_filtered_modules = {
                    s.name
                    for s in ast
                    if isinstance(s, Import)
                    and (s.using is not None or s.hiding is not None)
                }
                imports = [
                    # `Meta` is from lark.tree and has minimal type
                    # stubs (mypy reports its constructor as untyped).
                    # Tag the call with `type: ignore[no-untyped-call]`;
                    # the runtime behavior is unchanged.
                    Import(Meta(), name, visibility="private")  # type: ignore[no-untyped-call, unused-ignore]
                    for name in prelude
                    if name not in user_filtered_modules
                ]
                ast = imports + ast

            ast = uniquify_deduce(ast, ctx)
            if use_cache:
                add_uniquified_module(module_name, ast)

        # check_deduce returns the post-typecheck AST (ast3 internally)
        # so callers like the Deduce-to-C compiler see overload-resolved
        # Var.resolved_names. On failure the variable retains the
        # post-uniquify ast for best-effort partial info.
        sink = ErrorSink() if collect_errors else None
        # Capture warnings alongside errors when the caller opted into
        # collect-errors mode. ``lsp.query.check`` uses this to surface
        # style hints (e.g. the auto-rule ``replace`` advice) as
        # WARNING-severity diagnostics. Issue #991.
        warning_sink: Optional[list[WarningRecord]] = (
            [] if collect_errors else None
        )
        prev_warning_sink = set_active_warning_sink(warning_sink)
        try:
            typechecked_ast = check_deduce(
                ast, module_name, True, list(tracing_functions), error_sink=sink
            )
        finally:
            set_active_warning_sink(prev_warning_sink)
        captured_warnings = list(warning_sink) if warning_sink is not None else []
        if sink is not None and sink.errors:
            # collect-errors mode: at least one statement failed but
            # the pipeline kept running. Surface the full list while
            # preserving the historical single-error fields so
            # unchanged callers (CLI, goal_at, MCP) still work.
            first = sink.errors[0]
            return CheckResult(
                ok=False,
                error_message=str(first),
                error_traceback=None,  # no single Python traceback in this mode
                exception=first,
                module_name=module_name,
                ast=typechecked_ast,
                errors=list(sink.errors),
                warnings=captured_warnings,
            )
        return CheckResult(
            ok=True,
            error_message=None,
            error_traceback=None,
            exception=None,
            module_name=module_name,
            ast=typechecked_ast,
            warnings=captured_warnings,
        )
    except Exception as e:
        # ``DebuggerQuit`` is control flow (the user typed ``quit`` or
        # closed the input pipe) -- not a checker error.  Re-raise so
        # ``check_file``'s outer handler translates it into a
        # human-friendly result instead of letting "EOF on debugger
        # input" leak as the error_message.  Local import to avoid
        # forcing every check_file caller to load the debugger module.
        from lsp.debugger import DebuggerQuit
        if isinstance(e, DebuggerQuit):
            raise
        if isinstance(e, RecursionError):
            # A bare "maximum recursion depth exceeded" is exactly the
            # kind of opaque crash Deduce's beginner-friendly diagnostics
            # avoid. The usual cause is an oversized integer literal:
            # numbers desugar to a *unary* term whose depth equals the
            # value, so every tree-walking pass recurses that deep. Skip
            # ``format_exc`` -- the traceback is thousands of frames deep
            # and re-walking it risks tripping the limit again. Issue
            # #1021.
            return CheckResult(
                ok=False,
                error_message=(
                    "this file is too deeply nested for Deduce to check "
                    "(exceeded the recursion limit). The most common cause "
                    "is a very large integer literal: Deduce represents a "
                    "number as a unary term whose depth equals its value, "
                    "so a literal like 100000 builds a term too deep to "
                    "check. Use a smaller value, or raise RECURSION_LIMIT "
                    "in flags.py if you really need it."
                ),
                error_traceback=None,
                exception=e,
                module_name=module_name,
                ast=ast,
            )
        return CheckResult(
            ok=False,
            error_message=str(e),
            error_traceback=_traceback.format_exc(),
            exception=e,
            module_name=module_name,
            ast=ast,
        )


def _content_matches_file(filename: str, content: str) -> bool:
    """Return true when ``content`` exactly matches ``filename`` on disk.

    A missing or unreadable file means the caller's text is necessarily
    an in-memory buffer, so it must bypass the module cache.
    """
    try:
        with open(filename, "r", encoding="utf-8") as f:
            return f.read() == content
    except OSError:
        return False


# ---------------------------------------------------------------------------
# Per-call state isolation (Step 6)
# ---------------------------------------------------------------------------


# Module-level mutable containers in the pipeline whose post-prelude
# state we capture once and restore between calls. The uniquify
# counter is *not* in this list -- it's now an explicit
# ``UniquifyContext`` (Step 12) managed via ``_post_prelude_ctx``
# below.  ``proof_checker.name_id`` is *also* not in this list --
# it's a scalar and lives in ``_TRACKED_SCALARS`` below.
_TRACKED_CONTAINERS: tuple[_TrackedAttr, ...] = (
    (_abstract_syntax, "uniquified_modules"),
    (_abstract_syntax, "_predicate_decls_by_unique_name"),
    (_abstract_syntax, "collected_imports"),
    (_abstract_syntax, "reduce_only"),
    (_abstract_syntax, "reduced_defs"),
    (_proof_checker, "imported_modules"),
    (_proof_checker, "checked_modules"),
    (_proof_checker, "modules"),
    (_proof_checker, "dirty_files"),
)

# Module-level scalar counters in the pipeline whose post-prelude
# value we capture and restore between calls.  Scalars are handled
# separately from containers because they aren't ``.clear()``-able
# -- restore is a plain ``setattr``.  ``proof_checker.name_id`` is
# the fresh-name counter consumed during predicate desugaring,
# induction / switch fresh-label generation, and the rest of the
# post-uniquify synthesis paths.  Snapshotting it keeps the
# post-decl AST reproducible across calls (issue #368).
_TRACKED_SCALARS: tuple[_TrackedAttr, ...] = (
    (_proof_checker, "name_id"),
)

# The cache key (prelude tuple, prewarm tuple) the snapshot below was
# captured for. ``None`` until the first ``check_file`` call. The
# prewarm half is the set of modules pre-loaded into
# ``uniquified_modules`` without being injected as imports -- batch
# test runners use this to amortise lib parsing across a sweep while
# keeping per-file import semantics intact.
_prelude_key: Optional[tuple[tuple[str, ...], tuple[str, ...]]] = None

# Snapshot of ``_TRACKED_CONTAINERS`` taken right after the prelude
# load. Each entry is a fresh shallow copy of the live container.
_prelude_snapshot: Optional[_ContainerSnapshot] = None

# Snapshot of ``_TRACKED_SCALARS`` taken right after the prelude
# load.  Each entry is the captured scalar value (an int for the
# fresh-name counter).
_prelude_scalars: Optional[_ScalarSnapshot] = None

# Post-prelude ``UniquifyContext`` baseline. After the prelude has
# been uniquified, its counter records the highest id allocated.
# Each user-file ``check_file`` call forks a fresh context from this
# snapshot, so user-file uniquify starts at the same baseline every
# time -- reproducible names across calls -- without colliding with
# prelude-cached names. ``None`` until the first prepare-state.
_post_prelude_ctx: Optional[UniquifyContext] = None


def _prepare_state(
    prelude_key: tuple[str, ...],
    prewarm_key: tuple[str, ...] = (),
) -> None:
    """Make the global pipeline state ready for a fresh check.

    First time we see ``(prelude_key, prewarm_key)`` (or any time
    either changes): clear every tracked container, run the prelude
    through the pipeline so the lib modules end up cached in
    ``uniquified_modules`` / ``checked_modules``, optionally pre-load
    any ``prewarm_key`` modules into the same cache (without
    injecting them as imports into the user buffer), then take a
    snapshot.

    On subsequent calls with the same key: just restore the
    snapshot. The prelude reload is the expensive part (~3s for the
    full stdlib); restore is a handful of dict/set copies.
    """
    global _prelude_key, _prelude_snapshot, _prelude_scalars, _post_prelude_ctx

    cache_key = (prelude_key, prewarm_key)
    if _prelude_snapshot is not None and _prelude_key == cache_key:
        _restore_containers(_prelude_snapshot)
        _restore_scalars(_prelude_scalars)
        return

    _clear_containers()
    bootstrap_ctx = UniquifyContext()
    if prelude_key:
        # Bootstrap the prelude by running the pipeline on an empty
        # buffer with the requested imports. ``__prelude__`` isn't a
        # real file -- ``content=""`` means we never touch the disk
        # for it, and the resilient ``error.py`` helpers from Step 4
        # won't crash if a parse error tries to render an excerpt.
        _check_file_impl(
            filename="__prelude__.pf",
            tracing_functions=(),
            prelude=prelude_key,
            content="",
            ctx=bootstrap_ctx,
        )
    # Pre-warm phase: load each prewarm module into ``uniquified_modules``
    # by uniquifying a buffer that imports it.  We feed them one at a
    # time so dependency order doesn't matter -- each ``import`` chases
    # its own dependencies via the cache mechanism.  The bootstrap env
    # is discarded, so the prewarm imports don't show up at the
    # user-file check site.
    for name in prewarm_key:
        if name in _abstract_syntax.uniquified_modules:
            continue
        _check_file_impl(
            filename="__prewarm__.pf",
            tracing_functions=(),
            prelude=(name,),
            content="",
            ctx=bootstrap_ctx,
        )
    _prelude_key = cache_key
    _prelude_snapshot = _capture_containers()
    _prelude_scalars = _capture_scalars()
    _post_prelude_ctx = bootstrap_ctx.snapshot()


def _capture_containers() -> _ContainerSnapshot:
    """Shallow-copy each tracked container into a fresh snapshot dict."""
    snap: _ContainerSnapshot = {}
    for module, attr in _TRACKED_CONTAINERS:
        live: object = getattr(module, attr)
        snap[(module.__name__, attr)] = _shallow_copy(live)
    return snap


def _restore_containers(snapshot: _ContainerSnapshot) -> None:
    """In-place restore: clear the live container and refill from
    ``snapshot``. We mutate in place rather than rebinding the module
    attribute because other modules in the pipeline hold direct
    references (e.g. ``from abstract_syntax import collected_imports``
    binds at import time, and rebinding would leave stale aliases)."""
    for module, attr in _TRACKED_CONTAINERS:
        live: object = getattr(module, attr)
        saved = snapshot[(module.__name__, attr)]
        if isinstance(live, dict):
            if not isinstance(saved, dict):  # pragma: no cover -- defensive
                raise TypeError(f"snapshot for {module.__name__}.{attr} is not a dict")
            live = cast(dict[object, object], live)
            live.clear()
            live.update(saved)
        elif isinstance(live, set):
            if not isinstance(saved, set):  # pragma: no cover -- defensive
                raise TypeError(f"snapshot for {module.__name__}.{attr} is not a set")
            live = cast(set[object], live)
            live.clear()
            live.update(saved)
        elif isinstance(live, list):
            if not isinstance(saved, list):  # pragma: no cover -- defensive
                raise TypeError(f"snapshot for {module.__name__}.{attr} is not a list")
            live = cast(list[object], live)
            live.clear()
            live.extend(saved)
        else:  # pragma: no cover -- defensive
            raise TypeError(
                f"unexpected container type for {module.__name__}.{attr}: "
                f"{type(live).__name__}"
            )


def _capture_scalars() -> _ScalarSnapshot:
    """Capture the current value of each tracked scalar."""
    snap: _ScalarSnapshot = {}
    for module, attr in _TRACKED_SCALARS:
        snap[(module.__name__, attr)] = getattr(module, attr)
    return snap


def _restore_scalars(snapshot: Optional[_ScalarSnapshot]) -> None:
    """Re-bind each tracked scalar to its captured value."""
    if snapshot is None:
        return
    for module, attr in _TRACKED_SCALARS:
        setattr(module, attr, snapshot[(module.__name__, attr)])


def _clear_containers() -> None:
    """Reset every tracked container to empty."""
    for module, attr in _TRACKED_CONTAINERS:
        getattr(module, attr).clear()
    # The Step-13 statement cache lives outside the snapshot list
    # (it accumulates across calls), but it's only valid for a given
    # prelude key.  Clear it whenever we clear the rest of the state.
    _proof_checker.reset_stmt_cache()


def _shallow_copy(obj: object) -> _TrackedContainer:
    """Shallow-copy a tracked container to a fresh instance.

    The values inside (AST nodes, mostly) are shared with the live
    container, which is fine: prelude AST nodes shouldn't be mutated
    by user-file checks. If that assumption ever breaks, the failure
    surfaces as a ``CheckResult`` mismatch caught by Step 6's
    acceptance tests in ``test/lsp/test_state_isolation.py``.
    """
    if isinstance(obj, dict):
        obj = cast(dict[object, object], obj)
        return dict(obj)
    if isinstance(obj, set):
        obj = cast(set[object], obj)
        return set(obj)
    if isinstance(obj, list):
        obj = cast(list[object], obj)
        return list(obj)
    raise TypeError(  # pragma: no cover -- defensive
        f"unsupported tracked container type: {type(obj).__name__}"
    )


def reset_prelude_cache() -> None:
    """Drop the cached prelude snapshot.

    Forces the next ``check_file`` call to rebuild the prelude from
    scratch. Used by the test suite to test the bootstrap path and by
    long-running daemons that want to pick up changes to ``lib/``.
    """
    global _prelude_key, _prelude_snapshot, _prelude_scalars, _post_prelude_ctx
    _prelude_key = None
    _prelude_snapshot = None
    _prelude_scalars = None
    _post_prelude_ctx = None
    _clear_containers()
