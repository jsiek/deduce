"""Anthropic SDK backend for the validate_proof + query_goal tool loop.

Drives ``client.messages.create`` directly with adaptive thinking
and the cheatsheet-cache prompt-control breakpoint.

Two tools are exposed (when ``querier`` is provided to ``run``):

  - ``validate_proof'' -- splice and run the full checker.  Counts
    toward ``max_attempts''.
  - ``query_goal'' -- splice a partial proof containing a `?', report
    the goal at that `?'.  Doesn't count toward attempts.

The loop runs at most ``max_attempts * 2'' turns total: that's
generous enough that a model can interleave queries and validates,
but bounded so a confused model can't loop on free queries
indefinitely.
"""

from __future__ import annotations

import json
import time
from typing import Any, Optional, cast

from .agent import (
    AgentResult,
    AttemptRecord,
    Backend,
    ProgressFn,
    QUERY_GOAL_TOOL_DESCRIPTION,
    QUERY_GOAL_TOOL_NAME,
    QUERY_GOAL_TOOL_PARAMETERS,
    VALIDATE_TOOL_DESCRIPTION,
    VALIDATE_TOOL_NAME,
    VALIDATE_TOOL_PARAMETERS,
    preview,
)
from .validator import HoleQuerier, QueryOutcome, Validator, ValidationOutcome


_DEFAULT_MODEL = "claude-opus-4-7"
_DEFAULT_MAX_TOKENS = 16000


_VALIDATE_TOOL = {
    "name": VALIDATE_TOOL_NAME,
    "description": VALIDATE_TOOL_DESCRIPTION,
    "input_schema": VALIDATE_TOOL_PARAMETERS,
}

_QUERY_GOAL_TOOL = {
    "name": QUERY_GOAL_TOOL_NAME,
    "description": QUERY_GOAL_TOOL_DESCRIPTION,
    "input_schema": QUERY_GOAL_TOOL_PARAMETERS,
}


class AnthropicBackend(Backend):
    """Drive Claude through the proof-completion tool loop via the
    Anthropic SDK.

    ``client`` is duck-typed -- any object exposing
    ``messages.create(...)`` returning a Claude-shaped response
    works, which makes the class trivially testable with a fake
    client.
    """

    name = "anthropic"

    def __init__(
        self,
        *,
        client: Any,  # Any: the anthropic SDK client (optional dependency, untyped here)
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
        querier: Optional[HoleQuerier] = None,
        on_progress: Optional[ProgressFn] = None,
    ) -> AgentResult:
        started = time.monotonic()

        def _progress(event: str, **fields: object) -> None:
            if on_progress is not None:
                on_progress(event, **fields)

        system_blocks = [
            {
                "type": "text",
                "text": system_text,
                "cache_control": {"type": "ephemeral"},
            }
        ]

        tools = [_VALIDATE_TOOL]
        if querier is not None:
            tools = [_VALIDATE_TOOL, _QUERY_GOAL_TOOL]

        messages: list[dict[str, object]] = [
            {"role": "user", "content": user_message}
        ]
        history: list[AttemptRecord] = []

        _progress("start", maxAttempts=max_attempts)

        validate_attempts = 0
        # Bound the total loop so a model that only ever calls
        # query_goal can't run forever.  2x the validate budget gives
        # the model headroom to interleave queries with validates.
        max_turns = max_attempts * 2

        for turn in range(1, max_turns + 1):
            _progress(
                "model_request",
                turn=turn,
                attempt=validate_attempts,
            )

            try:
                response = self.client.messages.create(
                    model=self.model,
                    max_tokens=self.max_tokens,
                    thinking={"type": "adaptive"},
                    output_config={"effort": self.effort},
                    system=system_blocks,
                    tools=tools,
                    messages=messages,
                )
            except Exception as exc:
                elapsed = int((time.monotonic() - started) * 1000)
                _progress(
                    "finish", ok=False, attempts=validate_attempts,
                    error=str(exc),
                )
                return AgentResult(
                    ok=False,
                    proof=None,
                    attempts=validate_attempts,
                    elapsed_ms=elapsed,
                    model=self.model,
                    history=tuple(history),
                    error=f"API call failed on turn {turn}: {exc}",
                )

            tool_uses = [
                block for block in response.content if _is_tool_use(block)
            ]

            if not tool_uses:
                elapsed = int((time.monotonic() - started) * 1000)
                _progress(
                    "finish", ok=False, attempts=validate_attempts,
                    reason="no_tool_call",
                )
                return AgentResult(
                    ok=False,
                    proof=None,
                    attempts=validate_attempts,
                    elapsed_ms=elapsed,
                    model=self.model,
                    history=tuple(history),
                    error="model returned no tool call",
                )

            messages.append(
                {"role": "assistant", "content": response.content}
            )

            tool_results: list[dict[str, object]] = []
            success_proof: Optional[str] = None

            for block in tool_uses:
                tool_name = _tool_use_name(block)
                proof_text = _extract_proof_text(block)

                if tool_name == VALIDATE_TOOL_NAME:
                    if validate_attempts >= max_attempts:
                        # Budget already used; tell the model and
                        # don't increment further.
                        tool_results.append(
                            _tool_result_block(
                                _block_id(block),
                                ok=False,
                                error=(
                                    "validate_proof budget exhausted; "
                                    "you must commit your best guess "
                                    "but no further validates will run"
                                ),
                            )
                        )
                        continue
                    validate_attempts += 1

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
                                attempt=validate_attempts,
                                proof_text="",
                                outcome=ValidationOutcome(
                                    ok=False, error="missing proof_text"
                                ),
                            )
                        )
                        _progress(
                            "tool_call",
                            tool=VALIDATE_TOOL_NAME,
                            attempt=validate_attempts,
                            proofPreview="",
                        )
                        _progress(
                            "tool_result",
                            tool=VALIDATE_TOOL_NAME,
                            attempt=validate_attempts,
                            ok=False,
                            errorTail="missing proof_text",
                        )
                        continue

                    _progress(
                        "tool_call",
                        tool=VALIDATE_TOOL_NAME,
                        attempt=validate_attempts,
                        proofPreview=preview(proof_text),
                    )
                    outcome = validator.validate(proof_text)
                    history.append(
                        AttemptRecord(
                            attempt=validate_attempts,
                            proof_text=proof_text,
                            outcome=outcome,
                        )
                    )
                    _progress(
                        "tool_result",
                        tool=VALIDATE_TOOL_NAME,
                        attempt=validate_attempts,
                        ok=outcome.ok,
                        errorTail=preview(outcome.error or "", 200),
                    )

                    if outcome.ok and success_proof is None:
                        success_proof = proof_text
                        tool_results.append(
                            _tool_result_block(
                                _block_id(block), ok=True, error=None
                            )
                        )
                    else:
                        tool_results.append(
                            _tool_result_block(
                                _block_id(block),
                                ok=False,
                                error=outcome.error,
                            )
                        )

                elif tool_name == QUERY_GOAL_TOOL_NAME and querier is not None:
                    _progress(
                        "tool_call",
                        tool=QUERY_GOAL_TOOL_NAME,
                        proofPreview=preview(proof_text or ""),
                    )
                    if proof_text is None:
                        tool_results.append(
                            _tool_result_block(
                                _block_id(block),
                                ok=False,
                                error="tool input missing required `proof_text`",
                            )
                        )
                        _progress(
                            "tool_result",
                            tool=QUERY_GOAL_TOOL_NAME,
                            ok=False,
                            errorTail="missing proof_text",
                        )
                        continue
                    query_outcome = querier.query(proof_text)
                    tool_results.append(
                        _query_result_block(_block_id(block), query_outcome)
                    )
                    _progress(
                        "tool_result",
                        tool=QUERY_GOAL_TOOL_NAME,
                        ok=query_outcome.ok,
                        goal=preview(query_outcome.goal or "", 100),
                        errorTail=preview(query_outcome.error or "", 200),
                    )
                else:
                    tool_results.append(
                        _tool_result_block(
                            _block_id(block),
                            ok=False,
                            error=(
                                f"unknown tool {tool_name!r}; available: "
                                f"{VALIDATE_TOOL_NAME}"
                                + (
                                    f", {QUERY_GOAL_TOOL_NAME}"
                                    if querier is not None
                                    else ""
                                )
                            ),
                        )
                    )

            if success_proof is not None:
                elapsed = int((time.monotonic() - started) * 1000)
                _progress("finish", ok=True, attempts=validate_attempts)
                return AgentResult(
                    ok=True,
                    proof=success_proof,
                    attempts=validate_attempts,
                    elapsed_ms=elapsed,
                    model=self.model,
                    history=tuple(history),
                )

            messages.append({"role": "user", "content": tool_results})

            if validate_attempts >= max_attempts:
                # Budget gone and last attempt didn't succeed.
                break

        elapsed = int((time.monotonic() - started) * 1000)
        _progress(
            "finish",
            ok=False,
            attempts=validate_attempts,
            reason="budget_exhausted",
        )
        return AgentResult(
            ok=False,
            proof=None,
            attempts=validate_attempts,
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


# SDK-response accessor boundary. ``block`` is an Anthropic content block --
# either a Pydantic model from the optional `anthropic` package or a plain dict.
# We accept the input as ``object`` (consistent with schema.py's parsed-JSON
# boundary) and produce typed results via local isinstance guards.
def _is_tool_use(block: object) -> bool:
    return _block_type(block) == "tool_use"


def _block_type(block: object) -> str:
    val = (
        cast(dict[object, object], block).get("type", "")
        if isinstance(block, dict)
        else getattr(block, "type", "")
    )
    return val if isinstance(val, str) else ""


def _block_id(block: object) -> str:
    val = (
        cast(dict[object, object], block).get("id", "")
        if isinstance(block, dict)
        else getattr(block, "id", "")
    )
    return val if isinstance(val, str) else ""


def _tool_use_name(block: object) -> str:
    val = (
        cast(dict[object, object], block).get("name", "")
        if isinstance(block, dict)
        else getattr(block, "name", "")
    )
    return val if isinstance(val, str) else ""


def _extract_proof_text(block: object) -> Optional[str]:
    if isinstance(block, dict):
        inp = cast(dict[object, object], block).get("input", {})
    else:
        inp = getattr(block, "input", {})
    if not isinstance(inp, dict):
        return None
    proof = cast(dict[object, object], inp).get("proof_text")
    if not isinstance(proof, str):
        return None
    return proof


def _tool_result_block(
    tool_use_id: str, *, ok: bool, error: Optional[str]
) -> dict[str, object]:
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


def _query_result_block(
    tool_use_id: str, outcome: QueryOutcome
) -> dict[str, object]:
    """Format a tool_result carrying a structured query response.

    JSON-encode the {goal, givens} (or {error}) payload so the model
    sees it as a parseable structure rather than a free-form string.
    """
    if outcome.ok:
        payload: dict[str, object] = {
            "goal": outcome.goal,
            "givens": [
                {"label": g.label, "formula": g.formula}
                for g in outcome.givens
            ],
        }
        return {
            "type": "tool_result",
            "tool_use_id": tool_use_id,
            "content": json.dumps(payload),
            "is_error": False,
        }
    return {
        "type": "tool_result",
        "tool_use_id": tool_use_id,
        "content": json.dumps({"error": outcome.error or "unknown"}),
        "is_error": True,
    }
