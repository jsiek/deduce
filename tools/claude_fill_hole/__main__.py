"""CLI entry point: ``python -m tools.claude_fill_hole``.

Reads one JSON request on stdin, runs the agent loop, writes one
JSON response on stdout. Progress events stream to stderr as NDJSON.

Two modes:

- Default: real run. Requires an ``ANTHROPIC_API_KEY`` and connects
  to the Anthropic API to drive Claude.
- ``--dry-run``: skips the API entirely, splices a known stub proof
  through the validator, and reports whether the validate path
  works. Useful for testing the spawn/validate pipeline without
  burning API credits.

See ``tools/claude_fill_hole/README.md`` for the full CLI contract.
"""

from __future__ import annotations

import argparse
import os
import sys
import time
from pathlib import Path
from typing import Optional

from .agent import AgentResult, run as run_agent
from .prompt import build_system_prompt, build_user_message, slice_around_hole
from .schema import (
    HoleFillRequest,
    HoleFillResponse,
    ValidationAttempt,
    progress_event,
    request_from_json,
    response_to_json,
)
from .validator import SubprocessValidator, ValidationOutcome


_DEFAULT_DEDUCE_CMD = "python3 deduce.py"


def main(argv: Optional[list[str]] = None) -> int:
    args = _parse_args(argv)

    raw = sys.stdin.read()
    if not raw.strip():
        _emit_progress("error", message="empty stdin")
        sys.stdout.write(
            response_to_json(
                _failure_response(
                    fingerprint="",
                    error="empty stdin -- expected a JSON request",
                    model="",
                )
            )
        )
        sys.stdout.write("\n")
        return 2

    try:
        request = request_from_json(raw)
    except (ValueError, KeyError) as e:
        _emit_progress("error", message=f"bad request: {e}")
        sys.stdout.write(
            response_to_json(
                _failure_response(
                    fingerprint="",
                    error=f"could not parse stdin as a HoleFillRequest: {e}",
                    model="",
                )
            )
        )
        sys.stdout.write("\n")
        return 2

    content = _resolve_content(request)
    if content is None:
        sys.stdout.write(
            response_to_json(
                _failure_response(
                    fingerprint=request.fingerprint,
                    error=f"could not read content for {request.file}",
                    model="",
                )
            )
        )
        sys.stdout.write("\n")
        return 2

    hole_start_offset, hole_end_offset = _hole_offsets(content, request)
    if hole_start_offset is None or hole_end_offset is None:
        sys.stdout.write(
            response_to_json(
                _failure_response(
                    fingerprint=request.fingerprint,
                    error="hole range out of bounds",
                    model="",
                )
            )
        )
        sys.stdout.write("\n")
        return 2

    deduce_cmd = tuple(args.deduce_cmd.split())
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

    if args.dry_run:
        return _run_dry_run(request, validator, args)

    api_key = os.environ.get(args.api_key_env)
    if not api_key:
        sys.stdout.write(
            response_to_json(
                _failure_response(
                    fingerprint=request.fingerprint,
                    error=f"{args.api_key_env} not set",
                    model=args.model,
                )
            )
        )
        sys.stdout.write("\n")
        return 2

    try:
        import anthropic  # type: ignore[import-not-found]
    except ImportError:
        sys.stdout.write(
            response_to_json(
                _failure_response(
                    fingerprint=request.fingerprint,
                    error=(
                        "the `anthropic` package is required; install via "
                        "`pip install -r requirements-fill-hole.txt`"
                    ),
                    model=args.model,
                )
            )
        )
        sys.stdout.write("\n")
        return 2

    client = anthropic.Anthropic(api_key=api_key)
    system = build_system_prompt(max_attempts=args.max_attempts)
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
    )

    result = run_agent(
        client=client,
        system=system,
        user_message=user_message,
        validator=validator,
        model=args.model,
        max_attempts=args.max_attempts,
        on_progress=_emit_progress,
    )

    response = _agent_result_to_response(request, result, args.model)
    sys.stdout.write(response_to_json(response))
    sys.stdout.write("\n")
    return 0 if result.ok else 1


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _parse_args(argv: Optional[list[str]]) -> argparse.Namespace:
    p = argparse.ArgumentParser(
        prog="python -m tools.claude_fill_hole",
        description=(
            "Read a hole-fill request on stdin, drive Claude through "
            "validate_proof, write the validated proof on stdout."
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
        default="claude-opus-4-7",
        help="Claude model id (default claude-opus-4-7)",
    )
    p.add_argument(
        "--deduce-cmd",
        default=_DEFAULT_DEDUCE_CMD,
        help="command (space-separated) used to invoke deduce.py "
        "(default 'python3 deduce.py')",
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
        default="ANTHROPIC_API_KEY",
        help="environment variable holding the API key "
        "(default ANTHROPIC_API_KEY)",
    )
    p.add_argument(
        "--dry-run",
        action="store_true",
        help=(
            "skip the API; run the validator with a known stub proof "
            "and report whether the splice/validate pipeline works"
        ),
    )
    return p.parse_args(argv)


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
    request: HoleFillRequest, validator: SubprocessValidator, args: argparse.Namespace
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
    sys.stdout.write(response_to_json(response))
    sys.stdout.write("\n")
    return 0 if outcome.ok else 1


def _emit_progress(event: str, **fields):
    sys.stderr.write(progress_event(event, **fields))
    sys.stderr.write("\n")
    sys.stderr.flush()


def _preview(s: str, n: int = 80) -> str:
    if len(s) <= n:
        return s
    return s[:n] + "..."


if __name__ == "__main__":
    sys.exit(main())
