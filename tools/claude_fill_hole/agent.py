"""Manual tool-use loop driving Claude with the validate_proof tool.

The shape is canonical (see the claude-api skill's tool-use docs):
loop until ``stop_reason == "end_turn"`` or the budget is exhausted,
appending tool_use blocks and tool_result blocks to ``messages`` on
each turn. First-valid-wins -- as soon as ``validator.validate``
returns ok, the loop exits and that proof is returned.

The sidecar's protocol layer (``__main__.py``) is responsible for
serialising the result; this module only knows about the loop.
"""

from __future__ import annotations

import time
from dataclasses import dataclass
from typing import Any, Callable, Optional

from .validator import Validator, ValidationOutcome


_DEFAULT_MODEL = "claude-opus-4-7"
_DEFAULT_MAX_TOKENS = 16000
_DEFAULT_MAX_ATTEMPTS = 5

# What we tell the model the tool does. Kept brief; the SCAFFOLD
# in ``prompt.py`` already explains the iteration model.
_VALIDATE_TOOL = {
    "name": "validate_proof",
    "description": (
        "Splice the given proof text into the file at the hole and run "
        "the Deduce checker. Returns {ok, error}. Call repeatedly to "
        "iterate; first valid proof wins."
    ),
    "input_schema": {
        "type": "object",
        "required": ["proof_text"],
        "properties": {
            "proof_text": {
                "type": "string",
                "description": (
                    "The complete Deduce proof text to splice into the "
                    "hole. Multi-line allowed; do NOT wrap in code "
                    "fences; do NOT include English commentary."
                ),
            }
        },
        "additionalProperties": False,
    },
}


@dataclass(frozen=True)
class AttemptRecord:
    """One ``validate_proof`` invocation, captured for the response trace."""

    attempt: int
    proof_text: str
    outcome: ValidationOutcome


@dataclass(frozen=True)
class AgentResult:
    """Outcome of the agent loop, returned to the protocol layer."""

    ok: bool
    proof: Optional[str]
    attempts: int
    elapsed_ms: int
    model: str
    history: tuple[AttemptRecord, ...]
    error: Optional[str] = None  # hard-failure top-level message


# Type alias for the progress callback. Matches what __main__.py uses
# to write NDJSON events to stderr; agent.py itself just calls back
# through this so it stays decoupled from the protocol layer.
ProgressFn = Callable[..., None]


def run(
    *,
    client: Any,
    system: list[dict],
    user_message: str,
    validator: Validator,
    model: str = _DEFAULT_MODEL,
    max_attempts: int = _DEFAULT_MAX_ATTEMPTS,
    max_tokens: int = _DEFAULT_MAX_TOKENS,
    effort: str = "high",
    on_progress: Optional[ProgressFn] = None,
) -> AgentResult:
    """Run the manual tool-use loop until a valid proof is produced
    or the budget is exhausted.

    ``client`` is duck-typed -- any object exposing
    ``messages.create(...)`` returning a Claude-shaped response works,
    which makes the function trivially testable with a fake client.

    ``system`` should already include cheatsheet content with
    ``cache_control`` set (see ``prompt.build_system_prompt``).
    """
    started = time.monotonic()

    def _progress(event: str, **fields):
        if on_progress is not None:
            on_progress(event, **fields)

    messages: list[dict] = [{"role": "user", "content": user_message}]
    history: list[AttemptRecord] = []

    _progress("start", maxAttempts=max_attempts)

    for attempt in range(1, max_attempts + 1):
        _progress("model_request", attempt=attempt)

        try:
            response = client.messages.create(
                model=model,
                max_tokens=max_tokens,
                thinking={"type": "adaptive"},
                output_config={"effort": effort},
                system=system,
                tools=[_VALIDATE_TOOL],
                messages=messages,
            )
        except Exception as exc:
            elapsed = int((time.monotonic() - started) * 1000)
            _progress(
                "finish", ok=False, attempts=attempt - 1, error=str(exc)
            )
            return AgentResult(
                ok=False,
                proof=None,
                attempts=attempt - 1,
                elapsed_ms=elapsed,
                model=model,
                history=tuple(history),
                error=f"API call failed on attempt {attempt}: {exc}",
            )

        tool_uses = [
            block for block in response.content if _is_tool_use(block)
        ]

        if not tool_uses:
            # Model emitted text-only response (or nothing). Treated
            # as "model gave up" -- not a hard failure, but no proof
            # to apply either.
            elapsed = int((time.monotonic() - started) * 1000)
            _progress(
                "finish", ok=False, attempts=attempt, reason="no_tool_call"
            )
            return AgentResult(
                ok=False,
                proof=None,
                attempts=attempt,
                elapsed_ms=elapsed,
                model=model,
                history=tuple(history),
                error="model returned no validate_proof call",
            )

        # Append the assistant message verbatim so the next turn
        # sees its own tool_use blocks.
        messages.append({"role": "assistant", "content": response.content})

        tool_results: list[dict] = []
        for block in tool_uses:
            proof_text = _extract_proof_text(block)
            if proof_text is None:
                # Malformed tool input -- tell the model and let it retry.
                tool_results.append(
                    _tool_result_block(
                        _block_id(block),
                        ok=False,
                        error="tool input missing required `proof_text`",
                    )
                )
                history.append(
                    AttemptRecord(
                        attempt=attempt,
                        proof_text="",
                        outcome=ValidationOutcome(
                            ok=False, error="missing proof_text"
                        ),
                    )
                )
                _progress(
                    "tool_call",
                    attempt=attempt,
                    proofPreview="",
                )
                _progress(
                    "tool_result",
                    attempt=attempt,
                    ok=False,
                    errorTail="missing proof_text",
                )
                continue

            _progress(
                "tool_call",
                attempt=attempt,
                proofPreview=_preview(proof_text),
            )
            outcome = validator.validate(proof_text)
            history.append(
                AttemptRecord(
                    attempt=attempt, proof_text=proof_text, outcome=outcome
                )
            )
            _progress(
                "tool_result",
                attempt=attempt,
                ok=outcome.ok,
                errorTail=_preview(outcome.error or "", 200),
            )

            if outcome.ok:
                # First valid wins. We still need to walk the rest of
                # the tool_uses to build a tool_result for each (the
                # API requires it) -- but we'll exit immediately
                # after.
                tool_results.append(
                    _tool_result_block(_block_id(block), ok=True, error=None)
                )
                # Drain remaining tool_uses with a noop result so the
                # transcript is well-formed even though we won't send it.
                for remaining in tool_uses[len(tool_results):]:
                    tool_results.append(
                        _tool_result_block(
                            _block_id(remaining),
                            ok=False,
                            error="superseded by earlier valid proof",
                        )
                    )
                elapsed = int((time.monotonic() - started) * 1000)
                _progress("finish", ok=True, attempts=attempt)
                return AgentResult(
                    ok=True,
                    proof=proof_text,
                    attempts=attempt,
                    elapsed_ms=elapsed,
                    model=model,
                    history=tuple(history),
                )

            tool_results.append(
                _tool_result_block(
                    _block_id(block), ok=False, error=outcome.error
                )
            )

        # Feed the tool_results back as a user message and loop.
        messages.append({"role": "user", "content": tool_results})

    # Budget exhausted with no valid proof.
    elapsed = int((time.monotonic() - started) * 1000)
    _progress("finish", ok=False, attempts=max_attempts, reason="budget_exhausted")
    return AgentResult(
        ok=False,
        proof=None,
        attempts=max_attempts,
        elapsed_ms=elapsed,
        model=model,
        history=tuple(history),
        error="budget exhausted without a valid proof",
    )


# ---------------------------------------------------------------------------
# Block introspection helpers.
#
# The Anthropic SDK returns Pydantic models with attribute access, but
# the test suite uses simple dict/SimpleNamespace stand-ins. Read both
# shapes through these helpers so the loop doesn't care which form the
# fake client uses.
# ---------------------------------------------------------------------------


def _is_tool_use(block) -> bool:
    return _block_type(block) == "tool_use"


def _block_type(block) -> str:
    if isinstance(block, dict):
        return block.get("type", "")
    return getattr(block, "type", "")


def _block_id(block) -> str:
    if isinstance(block, dict):
        return block.get("id", "")
    return getattr(block, "id", "")


def _extract_proof_text(block) -> Optional[str]:
    if isinstance(block, dict):
        inp = block.get("input", {})
    else:
        inp = getattr(block, "input", {})
    if not isinstance(inp, dict):
        return None
    proof = inp.get("proof_text")
    if not isinstance(proof, str):
        return None
    return proof


def _tool_result_block(tool_use_id: str, *, ok: bool, error: Optional[str]) -> dict:
    """Format a tool_result the API will accept, carrying our outcome."""
    if ok:
        content = "ok"
    else:
        content = f"error: {error or 'unknown'}"
    return {
        "type": "tool_result",
        "tool_use_id": tool_use_id,
        "content": content,
        "is_error": not ok,
    }


def _preview(s: str, n: int = 80) -> str:
    if len(s) <= n:
        return s
    return s[:n] + "..."
