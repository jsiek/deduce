"""CLI entry point: ``python -m tools.claude_fill_hole``.

Reads one JSON request on stdin, runs the agent loop, writes one
JSON response on stdout.  Progress events stream to stderr as NDJSON.

Three modes:

- ``--backend anthropic`` (default): Anthropic SDK, model id
  ``claude-opus-4-7``, API key from ``ANTHROPIC_API_KEY``.
- ``--backend openai-compat``: OpenAI-compatible HTTP endpoint.
  Set ``--base-url`` (e.g. ``https://reallms.rescloud.iu.edu/direct/v1``
  for IU REALLMs, ``http://localhost:11434/v1`` for local Ollama,
  omit for real OpenAI).  Set ``--api-key-env`` to the env var
  holding the bearer token.  Set ``--model`` to the model id.
- ``--dry-run``: skip the API entirely, splice a stub proof
  through the validator, report whether the splice/validate
  pipeline works.  No API key needed.

See ``tools/claude_fill_hole/README.md`` for the full CLI contract.
"""

from __future__ import annotations

import argparse
import os
import sys
import time
from pathlib import Path
from typing import Any, IO, Optional

from .agent import AgentResult, Backend
from .prompt import build_system_prompt, build_user_message, slice_around_hole
from .schema import (
    HoleFillRequest,
    HoleFillResponse,
    ValidationAttempt,
    progress_event,
    request_from_json,
    response_to_json,
)
from .validator import HoleQuerier, SubprocessValidator


def _default_prelude(deduce_root: Path) -> tuple[str, ...]:
    """Return the standard-library prelude tuple for `hole_context_at'.

    Matches what `lsp.lsp_server' does: every `.pf' file under `lib/'
    is auto-prepended as a private import.  Returns an empty tuple
    when `lib/' is missing.
    """
    lib_dir = deduce_root / "lib"
    if not lib_dir.is_dir():
        return ()
    return tuple(sorted(p.stem for p in lib_dir.glob("*.pf")))


def _bootstrap_deduce_env(deduce_root: Path) -> None:
    """Configure module-level state in `abstract_syntax`/`flags' so the
    in-process ``lsp.query.hole_context_at'' (used by HoleQuerier) can
    resolve imports and produce sensible diagnostics.

    Mirrors what `lsp.lsp_server' does at module-load time.  Running
    this is harmless even if the sidecar never calls query_goal --
    the validator's subprocess path is unaffected.

    Idempotent: calling multiple times is OK (init_import_directories
    resets the list each call).
    """
    if str(deduce_root) not in sys.path:
        sys.path.insert(0, str(deduce_root))
    sys.setrecursionlimit(10000)
    # The deduce parser locates `Deduce.lark' via
    # ``os.path.dirname(sys.argv[0])'' (see parser.py:get_deduce_directory).
    # When the sidecar is launched as ``python -m tools.claude_fill_hole'',
    # ``sys.argv[0]'' points at the runpy entry, not at deduce.py, so the
    # in-process parser (used by query_goal) can't find the grammar.
    # Repoint argv[0] at the deduce.py in our resolved root, mirroring
    # what lsp.lsp_server does.
    pseudo_entry = str(deduce_root / "deduce.py")
    sys.argv = [pseudo_entry] + sys.argv[1:]
    try:
        from abstract_syntax import (  # noqa: E402
            add_import_directory,
            init_import_directories,
        )
        from flags import set_quiet_mode  # noqa: E402
    except ImportError:
        # Bootstrap is best-effort -- if the deduce repo isn't on
        # sys.path (e.g. user invoked sidecar from outside a checkout
        # with the wrong --deduce-root), validate_proof still works
        # via subprocess; only query_goal will fail with a clear
        # message.
        return
    set_quiet_mode(True)
    init_import_directories()
    lib_dir = deduce_root / "lib"
    if lib_dir.is_dir():
        add_import_directory(str(lib_dir))
    test_imports = deduce_root / "test" / "test-imports"
    if test_imports.is_dir():
        add_import_directory(str(test_imports))


_BACKEND_CHOICES = ("anthropic", "openai-compat")
_DEFAULT_MODELS = {
    "anthropic": "claude-opus-4-7",
    "openai-compat": "gemma-4-31B-it",  # IU REALLMs default
}
_DEFAULT_API_KEY_ENVS = {
    "anthropic": "ANTHROPIC_API_KEY",
    "openai-compat": "OPENAI_API_KEY",
}


def main(argv: Optional[list[str]] = None) -> int:
    args = _parse_args(argv)

    # Claim stdout for the JSON response and redirect ``sys.stdout`` to
    # ``sys.stderr`` so any stray ``print()`` from the in-process deduce
    # checker pipeline (or a third-party SDK that logs to stdout) lands
    # in the progress buffer instead of corrupting the response.  Without
    # this, a single leaked path-shaped line is enough to make emacs
    # fail with ``JSON readtable error: 47`` (47 == ``/``).  See #383.
    response_stream = sys.stdout
    sys.stdout = sys.stderr
    try:
        return _main_with_response_stream(args, response_stream)
    except BaseException as exc:
        # Last-ditch: an uncaught exception (deduce internal_error,
        # SDK fault, OOM, ...) still produces a parseable response so
        # the editor doesn't fall back to the generic "could not parse"
        # path with no diagnostic.  Re-raise SystemExit so test runners
        # and ``sys.exit`` calls behave normally.
        _emit_response(
            response_stream,
            HoleFillResponse(
                ok=False,
                fingerprint="",
                attempts=0,
                elapsed_ms=0,
                model=getattr(args, "model", "") or "",
                proof=None,
                error=f"sidecar crashed: {type(exc).__name__}: {exc}",
                validations=(),
            ),
        )
        if isinstance(exc, SystemExit):
            raise
        return 1
    finally:
        sys.stdout = response_stream


def _main_with_response_stream(args: argparse.Namespace, response_stream: IO[str]) -> int:
    raw = sys.stdin.read()
    if not raw.strip():
        _emit_progress("error", message="empty stdin")
        _emit_response(
            response_stream,
            _failure_response(
                fingerprint="",
                error="empty stdin -- expected a JSON request",
                model="",
            ),
        )
        return 2

    try:
        request = request_from_json(raw)
    except (ValueError, KeyError) as e:
        _emit_progress("error", message=f"bad request: {e}")
        _emit_response(
            response_stream,
            _failure_response(
                fingerprint="",
                error=f"could not parse stdin as a HoleFillRequest: {e}",
                model="",
            ),
        )
        return 2

    content = _resolve_content(request)
    if content is None:
        _emit_response(
            response_stream,
            _failure_response(
                fingerprint=request.fingerprint,
                error=f"could not read content for {request.file}",
                model="",
            ),
        )
        return 2

    hole_start_offset, hole_end_offset = _hole_offsets(content, request)
    if hole_start_offset is None or hole_end_offset is None:
        _emit_response(
            response_stream,
            _failure_response(
                fingerprint=request.fingerprint,
                error="hole range out of bounds",
                model="",
            ),
        )
        return 2

    # Default `--deduce-cmd` to `<this Python> deduce.py` so the
    # checker subprocess inherits our site-packages.  Bare "python3"
    # picks up whatever's first on PATH, which on macOS GUI emacs is
    # typically the system Python -- which doesn't have lark, so
    # every validate would crash with a ModuleNotFoundError.
    if args.deduce_cmd:
        deduce_cmd = tuple(args.deduce_cmd.split())
    else:
        deduce_cmd = (sys.executable, "deduce.py")
    validator = SubprocessValidator(
        file_path=request.file,
        content=content,
        hole_start_offset=hole_start_offset,
        hole_end_offset=hole_end_offset,
        deduce_cmd=deduce_cmd,
        deduce_root=args.deduce_root,
        no_stdlib=args.no_stdlib,
        timeout_seconds=float(args.timeout),
    )

    # Bootstrap the deduce env so HoleQuerier's in-process
    # `lsp.query.hole_context_at' call can resolve imports.  Best-
    # effort: query_goal will fail with a clear message if the
    # bootstrap couldn't load `abstract_syntax' (e.g. user pointed
    # --deduce-root somewhere else than a real checkout).  Use the
    # sidecar's own location as the deduce root when --deduce-root
    # isn't given -- the sidecar lives at <root>/tools/claude_fill_hole/.
    sidecar_root = (
        Path(args.deduce_root)
        if args.deduce_root
        else Path(__file__).resolve().parents[2]
    )
    _bootstrap_deduce_env(sidecar_root)
    prelude = () if args.no_stdlib else _default_prelude(sidecar_root)
    querier = HoleQuerier(
        file_path=request.file,
        content=content,
        hole_start_offset=hole_start_offset,
        hole_end_offset=hole_end_offset,
        prelude=prelude,
    )

    if args.dry_run:
        return _run_dry_run(request, validator, args, response_stream)

    api_key = os.environ.get(args.api_key_env)
    if not api_key:
        _emit_response(
            response_stream,
            _failure_response(
                fingerprint=request.fingerprint,
                error=f"{args.api_key_env} not set",
                model=args.model,
            ),
        )
        return 2

    try:
        backend = _build_backend(args, api_key)
    except _BackendBuildError as e:
        _emit_response(
            response_stream,
            _failure_response(
                fingerprint=request.fingerprint,
                error=str(e),
                model=args.model,
            ),
        )
        return 2

    system_text = build_system_prompt(max_attempts=args.max_attempts)
    excerpt = request.surrounding_excerpt or slice_around_hole(
        content, hole_start_offset, hole_end_offset
    )
    user_message = build_user_message(
        goal=request.goal,
        givens=request.givens,
        lemmas_in_scope=request.lemmas_in_scope,
        surrounding_excerpt=excerpt,
    )

    _emit_progress(
        "start",
        fingerprint=request.fingerprint,
        maxAttempts=args.max_attempts,
        backend=backend.name,
        model=backend.model,
    )

    result = backend.run(
        system_text=system_text,
        user_message=user_message,
        validator=validator,
        max_attempts=args.max_attempts,
        querier=querier,
        on_progress=_emit_progress,
    )

    response = _agent_result_to_response(request, result, backend.model)
    _emit_response(response_stream, response)
    return 0 if result.ok else 1


class _BackendBuildError(RuntimeError):
    """Raised when we can't construct the requested backend (missing
    optional package, missing required CLI arg, etc.)."""


def _build_backend(args: argparse.Namespace, api_key: str) -> Backend:
    """Construct the backend selected by ``args.backend``.

    Imports SDK packages lazily so a sidecar invocation that uses
    only one backend doesn't blow up on a missing optional dep.
    """
    if args.backend == "anthropic":
        try:
            import anthropic
        except ImportError as e:
            raise _BackendBuildError(
                "the `anthropic` package is required for --backend anthropic; "
                "install via `pip install -r requirements-fill-hole.txt`"
            ) from e
        from .anthropic_backend import AnthropicBackend

        client = anthropic.Anthropic(api_key=api_key)
        return AnthropicBackend(client=client, model=args.model)

    if args.backend == "openai-compat":
        try:
            import openai
        except ImportError as e:
            raise _BackendBuildError(
                "the `openai` package is required for --backend openai-compat; "
                "install via `pip install -r requirements-fill-hole.txt`"
            ) from e
        from .openai_backend import OpenAICompatBackend

        client_kwargs: dict[str, Any] = {"api_key": api_key}
        if args.base_url:
            client_kwargs["base_url"] = args.base_url
        openai_client = openai.OpenAI(**client_kwargs)
        return OpenAICompatBackend(client=openai_client, model=args.model)

    raise _BackendBuildError(f"unknown backend: {args.backend!r}")


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _parse_args(argv: Optional[list[str]]) -> argparse.Namespace:
    p = argparse.ArgumentParser(
        prog="python -m tools.claude_fill_hole",
        description=(
            "Read a hole-fill request on stdin, drive a model through "
            "validate_proof, write the validated proof on stdout."
        ),
    )
    p.add_argument(
        "--backend",
        choices=_BACKEND_CHOICES,
        default="anthropic",
        help=(
            "model backend (default anthropic). 'openai-compat' works "
            "with IU REALLMs, real OpenAI, or local Ollama -- pair "
            "with --base-url and --model."
        ),
    )
    p.add_argument(
        "--base-url",
        default=None,
        help=(
            "base URL for openai-compat backend "
            "(e.g. https://reallms.rescloud.iu.edu/direct/v1, "
            "http://localhost:11434/v1, or omit for real OpenAI). "
            "Ignored for the anthropic backend."
        ),
    )
    p.add_argument(
        "--max-attempts",
        type=int,
        default=5,
        help="maximum number of validate_proof calls (default 5)",
    )
    p.add_argument(
        "--model",
        default=None,
        help=(
            "model id; defaults to claude-opus-4-7 (anthropic) or "
            "gemma-4-31B-it (openai-compat)"
        ),
    )
    p.add_argument(
        "--deduce-cmd",
        default=None,
        help=(
            "command (space-separated) used to invoke deduce.py "
            "(default '<sys.executable> deduce.py' so the checker "
            "subprocess inherits this Python's site-packages -- "
            "important when the host Python (e.g. the one the LSP "
            "/ sidecar is pinned to) has lark while the system "
            "`python3` does not)"
        ),
    )
    p.add_argument(
        "--deduce-root",
        default=None,
        help="working directory for deduce.py invocations "
        "(default: directory of the request file)",
    )
    p.add_argument(
        "--no-stdlib",
        action="store_true",
        help="pass --no-stdlib to deduce.py on each validate call",
    )
    p.add_argument(
        "--timeout",
        type=float,
        default=60.0,
        help="per-validate timeout in seconds (default 60)",
    )
    p.add_argument(
        "--api-key-env",
        default=None,
        help=(
            "environment variable holding the API key; defaults to "
            "ANTHROPIC_API_KEY (anthropic) or OPENAI_API_KEY (openai-compat)"
        ),
    )
    p.add_argument(
        "--dry-run",
        action="store_true",
        help=(
            "skip the API; run the validator with a known stub proof "
            "and report whether the splice/validate pipeline works"
        ),
    )
    args = p.parse_args(argv)
    # Apply backend-specific defaults.
    if args.model is None:
        args.model = _DEFAULT_MODELS[args.backend]
    if args.api_key_env is None:
        args.api_key_env = _DEFAULT_API_KEY_ENVS[args.backend]
    return args


def _resolve_content(request: HoleFillRequest) -> Optional[str]:
    if request.content is not None:
        return request.content
    try:
        return Path(request.file).read_text(encoding="utf-8")
    except OSError as e:
        _emit_progress("error", message=f"read failed: {e}")
        return None


def _hole_offsets(
    content: str, request: HoleFillRequest
) -> tuple[Optional[int], Optional[int]]:
    """Convert LSP-shaped (line, character) into byte offsets in content.

    LSP coordinates are 0-indexed UTF-16 code units in the spec, but
    the LSP server in this repo treats them as character offsets in
    the source string. We do the same here for symmetry.
    """
    return (
        _line_char_to_offset(content, request.hole_range.start.line, request.hole_range.start.character),
        _line_char_to_offset(content, request.hole_range.end.line, request.hole_range.end.character),
    )


def _line_char_to_offset(content: str, line: int, character: int) -> Optional[int]:
    if line < 0 or character < 0:
        return None
    lines = content.splitlines(keepends=True)
    if line >= len(lines):
        return None
    line_start = sum(len(lines[i]) for i in range(line))
    visible_len = len(lines[line].rstrip("\r\n"))
    if character > visible_len:
        return None
    return line_start + character


def _agent_result_to_response(
    request: HoleFillRequest, result: AgentResult, model: str
) -> HoleFillResponse:
    validations = tuple(
        ValidationAttempt(
            attempt=record.attempt,
            ok=record.outcome.ok,
            proof_preview=_preview(record.proof_text),
            error_tail=record.outcome.error,
        )
        for record in result.history
    )
    return HoleFillResponse(
        ok=result.ok,
        fingerprint=request.fingerprint,
        attempts=result.attempts,
        elapsed_ms=result.elapsed_ms,
        model=model,
        proof=result.proof,
        error=result.error,
        validations=validations,
    )


def _failure_response(
    *, fingerprint: str, error: str, model: str
) -> HoleFillResponse:
    return HoleFillResponse(
        ok=False,
        fingerprint=fingerprint,
        attempts=0,
        elapsed_ms=0,
        model=model,
        proof=None,
        error=error,
        validations=(),
    )


def _run_dry_run(
    request: HoleFillRequest,
    validator: SubprocessValidator,
    args: argparse.Namespace,
    response_stream: IO[str],
) -> int:
    """Validate a known-trivial stub proof and report the outcome.

    Doesn't touch the API. Useful for smoke-testing a deployment:
    if --dry-run returns ok, the splice + subprocess pipeline works
    and the deduce.py invocation is configured correctly.
    """
    started = time.monotonic()
    _emit_progress(
        "start", fingerprint=request.fingerprint, dryRun=True
    )

    stub = "?"  # the original hole content -- guaranteed to "fail" in
    # the same way as before, validating the splice mechanics
    outcome = validator.validate(stub)
    elapsed = int((time.monotonic() - started) * 1000)
    _emit_progress("finish", ok=outcome.ok, dryRun=True)

    response = HoleFillResponse(
        ok=outcome.ok,
        fingerprint=request.fingerprint,
        attempts=1,
        elapsed_ms=elapsed,
        model="<dry-run>",
        proof=stub if outcome.ok else None,
        error=None if outcome.ok else outcome.error,
        validations=(
            ValidationAttempt(
                attempt=1,
                ok=outcome.ok,
                proof_preview=stub,
                error_tail=outcome.error,
            ),
        ),
    )
    _emit_response(response_stream, response)
    return 0 if outcome.ok else 1


def _emit_response(stream: IO[str], response: HoleFillResponse) -> None:
    """Write the JSON response and a trailing newline to ``stream``.

    All response writes go through this helper so the response channel
    stays a single, well-defined object -- ``main()`` captures the
    real stdout into ``stream`` once at startup and points
    ``sys.stdout`` at stderr; nothing else writes to ``stream``."""
    stream.write(response_to_json(response))
    stream.write("\n")
    stream.flush()


def _emit_progress(event: str, **fields: Any) -> None:
    sys.stderr.write(progress_event(event, **fields))
    sys.stderr.write("\n")
    sys.stderr.flush()


def _preview(s: str, n: int = 80) -> str:
    if len(s) <= n:
        return s
    return s[:n] + "..."


if __name__ == "__main__":
    sys.exit(main())
