"""Anthropic SDK backend for the validate_proof tool-use loop.

Drives ``client.messages.create`` directly with adaptive thinking
and the cheatsheet-cache prompt-control breakpoint.  This was the
original sidecar implementation before the OpenAI-compat backend
joined; the loop body is preserved verbatim, just lifted into a
class with the shared types from ``agent.py``.
"""

from __future__ import annotations

import time
from typing import Any, Optional

from .agent import (
    AgentResult,
    AttemptRecord,
    Backend,
    ProgressFn,
    VALIDATE_TOOL_DESCRIPTION,
    VALIDATE_TOOL_NAME,
    VALIDATE_TOOL_PARAMETERS,
    preview,
)
from .validator import Validator, ValidationOutcome


_DEFAULT_MODEL = "claude-opus-4-7"
_DEFAULT_MAX_TOKENS = 16000


# Anthropic's tool definition shape: name + description + input_schema
# at the top level.
_VALIDATE_TOOL = {
    "name": VALIDATE_TOOL_NAME,
    "description": VALIDATE_TOOL_DESCRIPTION,
    "input_schema": VALIDATE_TOOL_PARAMETERS,
}


class AnthropicBackend(Backend):
    """Drive Claude through the validate_proof loop via the Anthropic SDK.

    ``client`` is duck-typed -- any object exposing
    ``messages.create(...)`` returning a Claude-shaped response works,
    which makes the class trivially testable with a fake client.
    """

    name = "anthropic"

    def __init__(
        self,
        *,
        client: Any,
        model: str = _DEFAULT_MODEL,
        max_tokens: int = _DEFAULT_MAX_TOKENS,
        effort: str = "high",
    ) -> None:
        self.client = client
        self.model = model
        self.max_tokens = max_tokens
        self.effort = effort

    def run(
        self,
        *,
        system_text: str,
        user_message: str,
        validator: Validator,
        max_attempts: int,
        on_progress: Optional[ProgressFn] = None,
    ) -> AgentResult:
        started = time.monotonic()

        def _progress(event: str, **fields):
            if on_progress is not None:
                on_progress(event, **fields)

        # Wrap the system text in Anthropic's text-block shape with a
        # cache breakpoint.  The cheatsheets dominate token count, so
        # the cache hit on subsequent attempts is the load-bearing
        # cost optimisation.
        system_blocks = [
            {
                "type": "text",
                "text": system_text,
                "cache_control": {"type": "ephemeral"},
            }
        ]

        messages: list[dict] = [{"role": "user", "content": user_message}]
        history: list[AttemptRecord] = []

        _progress("start", maxAttempts=max_attempts)

        for attempt in range(1, max_attempts + 1):
            _progress("model_request", attempt=attempt)

            try:
                response = self.client.messages.create(
                    model=self.model,
                    max_tokens=self.max_tokens,
                    thinking={"type": "adaptive"},
                    output_config={"effort": self.effort},
                    system=system_blocks,
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
                    model=self.model,
                    history=tuple(history),
                    error=f"API call failed on attempt {attempt}: {exc}",
                )

            tool_uses = [
                block for block in response.content if _is_tool_use(block)
            ]

            if not tool_uses:
                # Model emitted text-only response (or nothing).
                # Treated as "model gave up" -- not a hard failure,
                # but no proof to apply either.
                elapsed = int((time.monotonic() - started) * 1000)
                _progress(
                    "finish", ok=False, attempts=attempt, reason="no_tool_call"
                )
                return AgentResult(
                    ok=False,
                    proof=None,
                    attempts=attempt,
                    elapsed_ms=elapsed,
                    model=self.model,
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
                    _progress("tool_call", attempt=attempt, proofPreview="")
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
                    proofPreview=preview(proof_text),
                )
                outcome = validator.validate(proof_text)
                history.append(
                    AttemptRecord(
                        attempt=attempt,
                        proof_text=proof_text,
                        outcome=outcome,
                    )
                )
                _progress(
                    "tool_result",
                    attempt=attempt,
                    ok=outcome.ok,
                    errorTail=preview(outcome.error or "", 200),
                )

                if outcome.ok:
                    tool_results.append(
                        _tool_result_block(
                            _block_id(block), ok=True, error=None
                        )
                    )
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
                        model=self.model,
                        history=tuple(history),
                    )

                tool_results.append(
                    _tool_result_block(
                        _block_id(block), ok=False, error=outcome.error
                    )
                )

            messages.append({"role": "user", "content": tool_results})

        # Budget exhausted with no valid proof.
        elapsed = int((time.monotonic() - started) * 1000)
        _progress(
            "finish",
            ok=False,
            attempts=max_attempts,
            reason="budget_exhausted",
        )
        return AgentResult(
            ok=False,
            proof=None,
            attempts=max_attempts,
            elapsed_ms=elapsed,
            model=self.model,
            history=tuple(history),
            error="budget exhausted without a valid proof",
        )


# ---------------------------------------------------------------------------
# Block introspection helpers.
#
# The Anthropic SDK returns Pydantic models with attribute access, but
# the test suite uses simple dict/SimpleNamespace stand-ins.  Read both
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


def _tool_result_block(
    tool_use_id: str, *, ok: bool, error: Optional[str]
) -> dict:
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
