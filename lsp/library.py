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
for synthesis paths) is still a process-monotonic global; Steps 13
and 14 may give it the same treatment if cache keys end up
depending on those names.
"""

from __future__ import annotations

import os
import sys
import traceback as _traceback
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Optional, Sequence

from lark.tree import Meta

import abstract_syntax as _abstract_syntax
import parser as _lark_parser
import proof_checker as _proof_checker
import rec_desc_parser as _rd_parser
from abstract_syntax import (
    Import,
    UniquifyContext,
    add_uniquified_module,
    get_recursive_descent,
    get_uniquified_modules,
)
from flags import get_verbose
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
        exception:        The raised exception object, preserved so
                          structured callers (``lsp.query.check``) can
                          read ``e.location`` / ``e.message_body``
                          without re-parsing strings. ``None`` when ok.
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
    ast: Optional[Any]


def check_file(
    filename: str,
    tracing_functions: Sequence[str] = (),
    prelude: Sequence[str] = (),
    content: Optional[str] = None,
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

    Concurrency note: this function is NOT thread-safe. The Deduce
    pipeline mutates module-level state, and the snapshot/restore
    machinery here assumes a single caller at a time. Callers that
    want to fan out should serialize.
    """
    _prepare_state(tuple(prelude))
    # Each user-file check forks a fresh ctx from the post-prelude
    # baseline so successive checks produce reproducible names.  See
    # ``UniquifyContext`` and the ``_post_prelude_ctx`` machinery
    # below for the rationale.
    ctx = (
        _post_prelude_ctx.snapshot()
        if _post_prelude_ctx is not None
        else UniquifyContext()
    )
    return _check_file_impl(filename, tracing_functions, prelude, content, ctx)


def _check_file_impl(
    filename: str,
    tracing_functions: Sequence[str],
    prelude: Sequence[str],
    content: Optional[str],
    ctx: UniquifyContext,
) -> CheckResult:
    """The original ``check_file`` body.

    Kept private so ``_prepare_state`` can call it during prelude
    bootstrap without re-entering the snapshot machinery.
    """
    module_name = Path(filename).stem
    if get_verbose():
        print("Deducing file:", filename)

    ast: Optional[Any] = None
    try:
        cached = get_uniquified_modules()
        # The cache is keyed by module name and corresponds to a
        # specific on-disk state. When the caller passes in-memory
        # content, the cache may be stale, so we bypass it and re-parse.
        use_cache = content is None
        if use_cache and module_name in cached:
            ast = cached[module_name]
        else:
            if content is None:
                with open(filename, "r", encoding="utf-8") as f:
                    program_text = f.read()
            else:
                program_text = content

            deduce_dir = os.path.dirname(sys.argv[0])
            if get_recursive_descent():
                _rd_parser.set_deduce_directory(deduce_dir)
                _rd_parser.set_filename(filename)
                _rd_parser.init_parser()
                ast = _rd_parser.parse(
                    program_text, trace=get_verbose(), error_expected=False
                )
            else:
                _lark_parser.set_deduce_directory(deduce_dir)
                _lark_parser.set_filename(filename)
                _lark_parser.init_parser()
                ast = _lark_parser.parse(
                    program_text, trace=get_verbose(), error_expected=False
                )

            if len(prelude) > 0:
                imports = [
                    Import(Meta(), name, visibility="private") for name in prelude
                ]
                ast = imports + ast

            ast = uniquify_deduce(ast, ctx)
            if use_cache:
                add_uniquified_module(module_name, ast)

        # check_deduce returns the post-typecheck AST (ast3 internally)
        # so callers like the Deduce-to-C compiler see overload-resolved
        # Var.resolved_names. On failure the variable retains the
        # post-uniquify ast for best-effort partial info.
        typechecked_ast = check_deduce(
            ast, module_name, True, list(tracing_functions)
        )
        return CheckResult(
            ok=True,
            error_message=None,
            error_traceback=None,
            exception=None,
            module_name=module_name,
            ast=typechecked_ast,
        )
    except Exception as e:
        return CheckResult(
            ok=False,
            error_message=str(e),
            error_traceback=_traceback.format_exc(),
            exception=e,
            module_name=module_name,
            ast=ast,
        )


# ---------------------------------------------------------------------------
# Per-call state isolation (Step 6)
# ---------------------------------------------------------------------------


# Module-level mutable containers in the pipeline whose post-prelude
# state we capture once and restore between calls. The uniquify
# counter is *not* in this list -- it's now an explicit
# ``UniquifyContext`` (Step 12) managed via ``_post_prelude_ctx``
# below.  ``proof_checker.name_id`` is still a process-monotonic
# global; if a future change adds a new container that contributes
# to per-call results, it goes here.
_TRACKED_CONTAINERS: tuple[tuple[Any, str], ...] = (
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

# The prelude key (tuple of module names) that the snapshot below was
# captured for. ``None`` until the first ``check_file`` call.
_prelude_key: Optional[tuple[str, ...]] = None

# Snapshot of ``_TRACKED_CONTAINERS`` taken right after the prelude
# load. Each entry is a fresh shallow copy of the live container.
_prelude_snapshot: Optional[dict[tuple[str, str], Any]] = None

# Post-prelude ``UniquifyContext`` baseline. After the prelude has
# been uniquified, its counter records the highest id allocated.
# Each user-file ``check_file`` call forks a fresh context from this
# snapshot, so user-file uniquify starts at the same baseline every
# time -- reproducible names across calls -- without colliding with
# prelude-cached names. ``None`` until the first prepare-state.
_post_prelude_ctx: Optional[UniquifyContext] = None


def _prepare_state(prelude_key: tuple[str, ...]) -> None:
    """Make the global pipeline state ready for a fresh check.

    First time we see ``prelude_key`` (or any time it changes): clear
    every tracked container, run the prelude through the pipeline so
    the lib modules end up cached in ``uniquified_modules`` /
    ``checked_modules``, then take a snapshot.

    On subsequent calls with the same prelude key: just restore the
    snapshot. The prelude reload is the expensive part (~3s for the
    full stdlib); restore is a handful of dict/set copies.
    """
    global _prelude_key, _prelude_snapshot, _post_prelude_ctx

    if _prelude_snapshot is not None and _prelude_key == prelude_key:
        _restore_containers(_prelude_snapshot)
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
    _prelude_key = prelude_key
    _prelude_snapshot = _capture_containers()
    _post_prelude_ctx = bootstrap_ctx.snapshot()


def _capture_containers() -> dict[tuple[str, str], Any]:
    """Shallow-copy each tracked container into a fresh snapshot dict."""
    snap: dict[tuple[str, str], Any] = {}
    for module, attr in _TRACKED_CONTAINERS:
        live = getattr(module, attr)
        snap[(module.__name__, attr)] = _shallow_copy(live)
    return snap


def _restore_containers(snapshot: dict[tuple[str, str], Any]) -> None:
    """In-place restore: clear the live container and refill from
    ``snapshot``. We mutate in place rather than rebinding the module
    attribute because other modules in the pipeline hold direct
    references (e.g. ``from abstract_syntax import collected_imports``
    binds at import time, and rebinding would leave stale aliases)."""
    for module, attr in _TRACKED_CONTAINERS:
        live = getattr(module, attr)
        saved = snapshot[(module.__name__, attr)]
        live.clear()
        if isinstance(live, dict):
            live.update(saved)
        elif isinstance(live, set):
            live.update(saved)
        elif isinstance(live, list):
            live.extend(saved)
        else:  # pragma: no cover -- defensive
            raise TypeError(
                f"unexpected container type for {module.__name__}.{attr}: "
                f"{type(live).__name__}"
            )


def _clear_containers() -> None:
    """Reset every tracked container to empty."""
    for module, attr in _TRACKED_CONTAINERS:
        getattr(module, attr).clear()


def _shallow_copy(obj: Any) -> Any:
    """Shallow-copy a tracked container to a fresh instance.

    The values inside (AST nodes, mostly) are shared with the live
    container, which is fine: prelude AST nodes shouldn't be mutated
    by user-file checks. If that assumption ever breaks, the failure
    surfaces as a ``CheckResult`` mismatch caught by Step 6's
    acceptance tests in ``test/lsp/test_state_isolation.py``.
    """
    if isinstance(obj, dict):
        return dict(obj)
    if isinstance(obj, set):
        return set(obj)
    if isinstance(obj, list):
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
    global _prelude_key, _prelude_snapshot, _post_prelude_ctx
    _prelude_key = None
    _prelude_snapshot = None
    _post_prelude_ctx = None
    _clear_containers()
