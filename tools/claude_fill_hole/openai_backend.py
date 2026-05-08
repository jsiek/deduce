"""OpenAI-compatible backend for the validate_proof tool-use loop.

Drives any OpenAI-shaped ``/v1/chat/completions`` endpoint.  Used
for three concrete deployments today:

- **Indiana University REALLMs** (default for IU users):
  ``base_url=https://reallms.rescloud.iu.edu/direct/v1``, models
  like ``Qwen3-Coder-Next`` or ``gpt-oss-120b``, bearer auth via
  the user's REALLMS_API_KEY.
- **Real OpenAI**: omit ``base_url``; ``api_key`` from
  ``OPENAI_API_KEY``.
- **Local Ollama**: ``base_url=http://localhost:11434/v1``,
  any non-empty key (Ollama ignores it).

The OpenAI tool-use shape differs from Anthropic's in three places:

1. Tool definitions are wrapped in ``{"type": "function",
   "function": {...}}`` rather than appearing at the top level.
2. The model's tool calls land in ``message.tool_calls``, each
   carrying ``function.name`` + ``function.arguments`` (a JSON
   *string* -- we have to parse it ourselves).
3. Tool results come back as ``role: "tool"`` messages addressed
   by ``tool_call_id``, not user-role blocks like Anthropic.

Loop semantics are otherwise identical: first valid proof wins,
``finish_reason: "tool_calls"`` is what we expect on every
non-final turn.
"""

from __future__ import annotations

import json
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


_DEFAULT_MAX_TOKENS = 16000


_VALIDATE_TOOL = {
    "type": "function",
    "function": {
        "name": VALIDATE_TOOL_NAME,
        "description": VALIDATE_TOOL_DESCRIPTION,
        "parameters": VALIDATE_TOOL_PARAMETERS,
    },
}


# Substrings (lower-cased) that indicate a 400 response is the result
# of malformed JSON in a tool-call's `arguments` field, which is
# recoverable -- we can retry with a synthetic correction note.  Seen
# in production against LiteLLM in front of vLLM serving Qwen3-Coder;
# see https://github.com/jsiek/deduce/issues/376.
_RECOVERABLE_BAD_REQUEST_MARKERS = (
    "json parse",
    "unterminated string",
    "invalid arguments",
    "invalid tool call",
    "bad json",
)

_MALFORMED_RETRY_NOTE = (
    "(previous tool call was rejected for malformed JSON in `arguments`; "
    "retry with well-formed JSON, e.g. {\"proof_text\": \"...\"})"
)


class OpenAICompatBackend(Backend):
    """Drive a model through the validate_proof loop via an OpenAI client.

    ``client`` is duck-typed -- any object exposing
    ``chat.completions.create(...)`` returning an OpenAI-shaped
    response works.  Production use passes an
    ``openai.OpenAI(base_url=..., api_key=...)`` instance; tests
    pass a fake.
    """

    name = "openai-compat"

    def __init__(
        self,
        *,
        client: Any,
        model: str,
        max_tokens: int = _DEFAULT_MAX_TOKENS,
    ) -> None:
        self.client = client
        self.model = model
        self.max_tokens = max_tokens

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

        # OpenAI takes the system prompt as the first message in the
        # ``messages`` array, no separate ``system`` parameter.  No
        # explicit cache breakpoints; servers that support implicit
        # prefix caching (real OpenAI, some LiteLLM deployments) get
        # it for free, others pay full price each attempt.
        messages: list[dict] = [
            {"role": "system", "content": system_text},
            {"role": "user", "content": user_message},
        ]
        history: list[AttemptRecord] = []

        _progress("start", maxAttempts=max_attempts)

        for attempt in range(1, max_attempts + 1):
            _progress("model_request", attempt=attempt)

            try:
                response = self.client.chat.completions.create(
                    model=self.model,
                    max_tokens=self.max_tokens,
                    tools=[_VALIDATE_TOOL],
                    tool_choice="auto",
                    messages=messages,
                )
            except Exception as exc:
                if (
                    _is_recoverable_malformed_args_error(exc)
                    and attempt < max_attempts
                ):
                    _progress(
                        "malformed_args_recovery",
                        attempt=attempt,
                        error=preview(str(exc), 200),
                    )
                    history.append(
                        AttemptRecord(
                            attempt=attempt,
                            proof_text="",
                            outcome=ValidationOutcome(
                                ok=False,
                                error=f"server rejected malformed tool-call JSON: {exc}",
                            ),
                        )
                    )
                    messages = _strip_trailing_turn_with_synthetic_note(messages)
                    continue
                elapsed = int((time.monotonic() - started) * 1000)
                _progress(
                    "finish",
                    ok=False,
                    attempts=attempt - 1,
                    error=str(exc),
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

            choice = _first_choice(response)
            assistant_msg = _choice_message(choice)
            tool_calls = _tool_calls(assistant_msg)

            if not tool_calls:
                # Model emitted a text-only response (or nothing).
                # Treated as "gave up" -- mirror AnthropicBackend.
                elapsed = int((time.monotonic() - started) * 1000)
                _progress(
                    "finish",
                    ok=False,
                    attempts=attempt,
                    reason="no_tool_call",
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

            # Append the assistant turn.  We have to re-serialise
            # tool_calls into a JSON-safe shape because some clients
            # return Pydantic models that don't round-trip through
            # the request-side ``messages`` parameter.
            messages.append(
                {
                    "role": "assistant",
                    "content": _message_content(assistant_msg) or "",
                    "tool_calls": _serialize_tool_calls(tool_calls),
                }
            )

            valid_proof = None
            for tc in tool_calls:
                tc_id = _tool_call_id(tc)
                tc_name = _tool_call_function_name(tc)
                tc_args_raw = _tool_call_function_arguments(tc)

                if tc_name != VALIDATE_TOOL_NAME:
                    # Model called something we don't expose.  Tell
                    # it so via a tool message and let it retry.
                    messages.append(
                        {
                            "role": "tool",
                            "tool_call_id": tc_id,
                            "content": json.dumps(
                                {
                                    "ok": False,
                                    "error": (
                                        f"unknown tool {tc_name!r}; "
                                        f"only {VALIDATE_TOOL_NAME!r} is available"
                                    ),
                                }
                            ),
                        }
                    )
                    continue

                proof_text = _extract_proof_text(tc_args_raw)
                if proof_text is None:
                    messages.append(
                        {
                            "role": "tool",
                            "tool_call_id": tc_id,
                            "content": json.dumps(
                                {
                                    "ok": False,
                                    "error": "tool input missing required `proof_text`",
                                }
                            ),
                        }
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
                        "tool_call", attempt=attempt, proofPreview=""
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

                tool_payload = {
                    "ok": outcome.ok,
                    "error": outcome.error,
                }
                messages.append(
                    {
                        "role": "tool",
                        "tool_call_id": tc_id,
                        "content": json.dumps(tool_payload),
                    }
                )
                if outcome.ok and valid_proof is None:
                    valid_proof = proof_text

            if valid_proof is not None:
                elapsed = int((time.monotonic() - started) * 1000)
                _progress("finish", ok=True, attempts=attempt)
                return AgentResult(
                    ok=True,
                    proof=valid_proof,
                    attempts=attempt,
                    elapsed_ms=elapsed,
                    model=self.model,
                    history=tuple(history),
                )

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
# Response introspection -- duck-typed across openai's Pydantic models
# and dict-shaped fakes used in tests.
# ---------------------------------------------------------------------------


def _first_choice(response):
    choices = _attr(response, "choices", default=[]) or []
    if not choices:
        # Surface a structured error rather than crashing.
        raise RuntimeError("OpenAI response has no choices")
    return choices[0]


def _choice_message(choice):
    return _attr(choice, "message")


def _message_content(msg):
    return _attr(msg, "content")


def _tool_calls(msg):
    calls = _attr(msg, "tool_calls", default=None) or []
    return list(calls)


def _tool_call_id(tc) -> str:
    return _attr(tc, "id", default="") or ""


def _tool_call_function_name(tc) -> str:
    fn = _attr(tc, "function")
    return _attr(fn, "name", default="") or ""


def _tool_call_function_arguments(tc) -> str:
    """Return the JSON-string ``arguments`` field for a tool call."""
    fn = _attr(tc, "function")
    return _attr(fn, "arguments", default="") or ""


def _extract_proof_text(args_raw: str) -> Optional[str]:
    """Parse ``proof_text`` out of a tool-call ``arguments`` JSON string.

    OpenAI's tool-call arguments come back as a JSON-encoded string,
    not a parsed object; this is unlike Anthropic which yields a
    Python dict directly.  We do the parse once here.
    """
    if not args_raw:
        return None
    try:
        parsed = json.loads(args_raw)
    except (TypeError, ValueError):
        return None
    if not isinstance(parsed, dict):
        return None
    proof = parsed.get("proof_text")
    if not isinstance(proof, str):
        return None
    return proof


def _serialize_tool_calls(tool_calls) -> list[dict]:
    """Re-serialise a list of tool_call objects (Pydantic models or dicts)
    into a plain list of dicts safe to round-trip through the request.

    For ``validate_proof`` calls whose ``arguments`` aren't well-formed
    JSON containing ``proof_text``, we substitute a placeholder
    ``{"proof_text": ""}`` -- some servers (LiteLLM-fronted vLLM
    in particular) re-validate the message transcript on each
    request and reject malformed bytes from a prior turn.  See
    https://github.com/jsiek/deduce/issues/376.
    """
    out: list[dict] = []
    for tc in tool_calls:
        name = _tool_call_function_name(tc)
        args_raw = _tool_call_function_arguments(tc)
        out.append(
            {
                "id": _tool_call_id(tc),
                "type": "function",
                "function": {
                    "name": name,
                    "arguments": _normalize_args_for_request(name, args_raw),
                },
            }
        )
    return out


def _normalize_args_for_request(name: str, args_raw: str) -> str:
    """Replace malformed/missing ``validate_proof`` arguments with a
    placeholder so the next request's transcript is well-formed JSON.

    Only touches ``validate_proof`` calls -- unknown tools are passed
    through unchanged so the loop's existing unknown-tool error
    response still describes what the model actually did.
    """
    if name != VALIDATE_TOOL_NAME:
        return args_raw
    if _extract_proof_text(args_raw) is not None:
        return args_raw
    return json.dumps({"proof_text": ""})


def _is_recoverable_malformed_args_error(exc: BaseException) -> bool:
    """True if ``exc`` looks like a server-side 400 caused by malformed
    JSON inside a tool-call's ``arguments`` field.

    Matched by class name (``BadRequestError``) so this module doesn't
    need to import ``openai`` -- the same check works against the real
    SDK exception and the test fakes.
    """
    if type(exc).__name__ != "BadRequestError":
        return False
    msg = str(exc).lower()
    return any(marker in msg for marker in _RECOVERABLE_BAD_REQUEST_MARKERS)


def _strip_trailing_turn_with_synthetic_note(messages: list[dict]) -> list[dict]:
    """Walk back to the last ``role: assistant`` entry, drop it (and
    any tool messages that followed it), and replace it with a plain
    synthetic note pointing the model at what went wrong.

    Used after a recoverable malformed-args 400: the prior turn's
    tool_calls are what the server choked on, so we can't carry them
    forward into the next request.
    """
    cut = len(messages)
    for i in range(len(messages) - 1, -1, -1):
        if messages[i].get("role") == "assistant":
            cut = i
            break
    return messages[:cut] + [
        {"role": "assistant", "content": _MALFORMED_RETRY_NOTE}
    ]


def _attr(obj, name, default=None):
    """Read ``name`` off ``obj`` whether it's a dict or attribute object."""
    if obj is None:
        return default
    if isinstance(obj, dict):
        return obj.get(name, default)
    return getattr(obj, name, default)
