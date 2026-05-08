"""OpenAICompatBackend tests using a fake OpenAI-shaped client.

Mirrors test_anthropic_backend.py case-for-case so the two backends
have parallel coverage.  The wire shape differs (tool_calls array
on message vs tool_use blocks in content; role: tool vs user-role
result blocks) but the loop semantics are identical, so each test
asserts the same behavior using the OpenAI-shaped fakes.
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from typing import Any, Optional

import pytest

from tools.claude_fill_hole.agent import AgentResult
from tools.claude_fill_hole.openai_backend import OpenAICompatBackend
from tools.claude_fill_hole.validator import ValidationOutcome


# ---------------------------------------------------------------------------
# Fakes
# ---------------------------------------------------------------------------


@dataclass
class FakeFunction:
    name: str
    arguments: str  # JSON-encoded string per the OpenAI shape


@dataclass
class FakeToolCall:
    id: str
    function: FakeFunction
    type: str = "function"


@dataclass
class FakeMessage:
    role: str = "assistant"
    content: Optional[str] = None
    tool_calls: list = field(default_factory=list)


@dataclass
class FakeChoice:
    message: FakeMessage
    finish_reason: str = "tool_calls"
    index: int = 0


@dataclass
class FakeResponse:
    choices: list[FakeChoice]


class FakeChatCompletions:
    def __init__(self, scripted: list[FakeResponse]) -> None:
        self._scripted = scripted
        self.calls = 0
        self.last_kwargs: Optional[dict[str, Any]] = None

    def create(self, **kwargs):
        self.last_kwargs = kwargs
        if self.calls >= len(self._scripted):
            raise AssertionError(
                "fake client: loop made more API calls than scripted"
            )
        response = self._scripted[self.calls]
        self.calls += 1
        return response


class FakeChat:
    def __init__(self, scripted: list[FakeResponse]) -> None:
        self.completions = FakeChatCompletions(scripted)


class FakeClient:
    def __init__(self, scripted: list[FakeResponse]) -> None:
        self.chat = FakeChat(scripted)


class FakeValidator:
    def __init__(self, outcomes: list[ValidationOutcome]) -> None:
        self._outcomes = outcomes
        self.calls: list[str] = []

    def validate(self, proof_text: str) -> ValidationOutcome:
        self.calls.append(proof_text)
        idx = len(self.calls) - 1
        if idx >= len(self._outcomes):
            raise AssertionError(
                "fake validator: more validate() calls than scripted outcomes"
            )
        return self._outcomes[idx]


def _tool_call(proof: str, *, id_: str = "call_1") -> FakeToolCall:
    return FakeToolCall(
        id=id_,
        function=FakeFunction(
            name="validate_proof",
            arguments=json.dumps({"proof_text": proof}),
        ),
    )


def _response_with_tool_call(proof: str, *, id_: str = "call_1") -> FakeResponse:
    return FakeResponse(
        choices=[
            FakeChoice(
                message=FakeMessage(
                    role="assistant",
                    content=None,
                    tool_calls=[_tool_call(proof, id_=id_)],
                ),
                finish_reason="tool_calls",
            )
        ]
    )


_SYSTEM_TEXT = "stub system prompt"


def _backend(client: FakeClient) -> OpenAICompatBackend:
    return OpenAICompatBackend(client=client, model="Qwen3-Coder-Next")


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


def test_first_attempt_succeeds_returns_ok():
    client = FakeClient([_response_with_tool_call("reflexive")])
    validator = FakeValidator([ValidationOutcome(ok=True)])
    result = _backend(client).run(
        system_text=_SYSTEM_TEXT,
        user_message="goal: P = P",
        validator=validator,
        max_attempts=5,
    )
    assert result.ok is True
    assert result.proof == "reflexive"
    assert result.attempts == 1
    assert client.chat.completions.calls == 1


def test_third_attempt_succeeds_after_two_failures():
    client = FakeClient(
        [
            _response_with_tool_call("bad1", id_="call_1"),
            _response_with_tool_call("bad2", id_="call_2"),
            _response_with_tool_call("reflexive", id_="call_3"),
        ]
    )
    validator = FakeValidator(
        [
            ValidationOutcome(ok=False, error="goal mismatch"),
            ValidationOutcome(ok=False, error="undefined label"),
            ValidationOutcome(ok=True),
        ]
    )
    result = _backend(client).run(
        system_text=_SYSTEM_TEXT,
        user_message="goal: P = P",
        validator=validator,
        max_attempts=5,
    )
    assert result.ok is True
    assert result.proof == "reflexive"
    assert result.attempts == 3
    assert validator.calls == ["bad1", "bad2", "reflexive"]


def test_budget_exhausted_returns_failure():
    client = FakeClient(
        [
            _response_with_tool_call("bad1", id_="call_1"),
            _response_with_tool_call("bad2", id_="call_2"),
        ]
    )
    validator = FakeValidator(
        [
            ValidationOutcome(ok=False, error="err1"),
            ValidationOutcome(ok=False, error="err2"),
        ]
    )
    result = _backend(client).run(
        system_text=_SYSTEM_TEXT,
        user_message="goal: P",
        validator=validator,
        max_attempts=2,
    )
    assert result.ok is False
    assert result.proof is None
    assert result.attempts == 2
    assert "budget" in (result.error or "")
    assert len(result.history) == 2


def test_no_tool_call_returns_failure_immediately():
    """Model emits a text-only response. Treated as 'gave up'."""
    client = FakeClient(
        [
            FakeResponse(
                choices=[
                    FakeChoice(
                        message=FakeMessage(
                            role="assistant",
                            content="I don't know.",
                            tool_calls=[],
                        ),
                        finish_reason="stop",
                    )
                ]
            )
        ]
    )
    validator = FakeValidator([])
    result = _backend(client).run(
        system_text=_SYSTEM_TEXT,
        user_message="goal: P",
        validator=validator,
        max_attempts=5,
    )
    assert result.ok is False
    assert "no validate_proof" in (result.error or "")
    assert validator.calls == []


def test_malformed_tool_input_is_recoverable():
    """If the model emits invalid JSON or omits proof_text, the loop
    feeds that back via a tool message and gives the model another
    attempt."""
    client = FakeClient(
        [
            # First response: arguments with no proof_text key.
            FakeResponse(
                choices=[
                    FakeChoice(
                        message=FakeMessage(
                            role="assistant",
                            tool_calls=[
                                FakeToolCall(
                                    id="call_1",
                                    function=FakeFunction(
                                        name="validate_proof",
                                        arguments="{}",
                                    ),
                                )
                            ],
                        ),
                        finish_reason="tool_calls",
                    )
                ]
            ),
            _response_with_tool_call("reflexive", id_="call_2"),
        ]
    )
    validator = FakeValidator([ValidationOutcome(ok=True)])
    result = _backend(client).run(
        system_text=_SYSTEM_TEXT,
        user_message="goal: P = P",
        validator=validator,
        max_attempts=5,
    )
    assert result.ok is True
    assert result.attempts == 2
    assert validator.calls == ["reflexive"]


def test_unknown_tool_call_is_recoverable():
    """If the model invents a tool name, the loop tells it so and
    gives it another attempt."""
    client = FakeClient(
        [
            FakeResponse(
                choices=[
                    FakeChoice(
                        message=FakeMessage(
                            role="assistant",
                            tool_calls=[
                                FakeToolCall(
                                    id="call_1",
                                    function=FakeFunction(
                                        name="multiply",  # not validate_proof
                                        arguments=json.dumps(
                                            {"a": 1, "b": 2}
                                        ),
                                    ),
                                )
                            ],
                        ),
                        finish_reason="tool_calls",
                    )
                ]
            ),
            _response_with_tool_call("reflexive", id_="call_2"),
        ]
    )
    validator = FakeValidator([ValidationOutcome(ok=True)])
    result = _backend(client).run(
        system_text=_SYSTEM_TEXT,
        user_message="goal: P = P",
        validator=validator,
        max_attempts=5,
    )
    assert result.ok is True
    assert result.attempts == 2
    # Validator only ran on the second attempt -- the first never
    # got past the unknown-tool check.
    assert validator.calls == ["reflexive"]


def test_api_failure_is_reported_as_hard_error():
    """If client.chat.completions.create raises, the loop returns a
    structured failure with the exception message in error."""

    class ExplodingCompletions:
        def create(self, **kwargs):
            raise RuntimeError("connection refused")

    class ExplodingChat:
        def __init__(self):
            self.completions = ExplodingCompletions()

    class ExplodingClient:
        def __init__(self):
            self.chat = ExplodingChat()

    validator = FakeValidator([])
    result = OpenAICompatBackend(
        client=ExplodingClient(), model="Qwen3-Coder-Next"
    ).run(
        system_text=_SYSTEM_TEXT,
        user_message="goal: P",
        validator=validator,
        max_attempts=5,
    )
    assert result.ok is False
    assert "connection refused" in (result.error or "")


def test_progress_callback_fires_for_each_phase():
    events: list[tuple[str, dict]] = []

    def on_progress(event: str, **fields):
        events.append((event, fields))

    client = FakeClient([_response_with_tool_call("reflexive")])
    validator = FakeValidator([ValidationOutcome(ok=True)])
    _backend(client).run(
        system_text=_SYSTEM_TEXT,
        user_message="goal: P = P",
        validator=validator,
        max_attempts=5,
        on_progress=on_progress,
    )

    event_names = [e for e, _ in events]
    assert event_names[0] == "start"
    assert "model_request" in event_names
    assert "tool_call" in event_names
    assert "tool_result" in event_names
    assert event_names[-1] == "finish"


def test_dispatches_required_request_kwargs():
    """The fake client captures the kwargs the loop passes; assert
    the backend uses the right model, the validate_proof tool with
    OpenAI's function-wrapper shape, and tool_choice='auto'."""
    client = FakeClient([_response_with_tool_call("reflexive")])
    validator = FakeValidator([ValidationOutcome(ok=True)])
    _backend(client).run(
        system_text=_SYSTEM_TEXT,
        user_message="goal: P = P",
        validator=validator,
        max_attempts=5,
    )
    kwargs = client.chat.completions.last_kwargs
    assert kwargs["model"] == "Qwen3-Coder-Next"
    assert kwargs["tool_choice"] == "auto"
    # OpenAI tool definitions are wrapped in {type: "function", function: {...}}.
    tool_names = [t["function"]["name"] for t in kwargs["tools"]]
    assert tool_names == ["validate_proof"]
    # System text rides as the leading {role: "system"} message,
    # NOT as a separate parameter (that's the Anthropic shape).
    assert kwargs["messages"][0] == {
        "role": "system",
        "content": _SYSTEM_TEXT,
    }
    assert kwargs["messages"][1]["role"] == "user"


def test_works_with_dict_shaped_responses():
    """Belt and suspenders: real openai SDK returns Pydantic models
    with attribute access; some test setups (and some MCP clients)
    return plain dicts. Both should work."""
    response_dict = {
        "choices": [
            {
                "message": {
                    "role": "assistant",
                    "content": None,
                    "tool_calls": [
                        {
                            "id": "call_dict",
                            "type": "function",
                            "function": {
                                "name": "validate_proof",
                                "arguments": json.dumps(
                                    {"proof_text": "reflexive"}
                                ),
                            },
                        }
                    ],
                },
                "finish_reason": "tool_calls",
                "index": 0,
            }
        ]
    }
    client = FakeClient([response_dict])  # type: ignore[arg-type]
    validator = FakeValidator([ValidationOutcome(ok=True)])
    result = _backend(client).run(
        system_text=_SYSTEM_TEXT,
        user_message="goal: P = P",
        validator=validator,
        max_attempts=5,
    )
    assert result.ok is True
    assert result.proof == "reflexive"


# ---------------------------------------------------------------------------
# Defensive recovery for malformed tool-call arguments (issue #376)
# ---------------------------------------------------------------------------


class _CapturingChatCompletions:
    """Like FakeChatCompletions but records the messages list passed
    on every call so we can inspect transcript normalisation."""

    def __init__(self, scripted: list[FakeResponse]) -> None:
        self._scripted = scripted
        self.calls = 0
        self.messages_per_call: list[list[dict]] = []

    def create(self, **kwargs):
        self.messages_per_call.append([dict(m) for m in kwargs["messages"]])
        if self.calls >= len(self._scripted):
            raise AssertionError(
                "fake client: loop made more API calls than scripted"
            )
        response = self._scripted[self.calls]
        self.calls += 1
        return response


class _CapturingClient:
    def __init__(self, scripted: list[FakeResponse]) -> None:
        self.chat = type(
            "FakeChat", (), {"completions": _CapturingChatCompletions(scripted)}
        )()


def test_malformed_args_are_normalized_in_next_request_transcript():
    """Issue #376: when the model emits tool-call arguments without a
    valid `proof_text`, the next request's `messages` array must
    carry placeholder JSON (`{"proof_text": ""}`) rather than the
    original malformed bytes -- LiteLLM/vLLM in front of Qwen3-Coder
    re-validates the transcript and rejects malformed arguments with
    a 400 before the model gets to retry."""
    malformed_args = '{"proof_text": "unterminated'  # invalid JSON
    client = _CapturingClient(
        [
            FakeResponse(
                choices=[
                    FakeChoice(
                        message=FakeMessage(
                            role="assistant",
                            tool_calls=[
                                FakeToolCall(
                                    id="call_1",
                                    function=FakeFunction(
                                        name="validate_proof",
                                        arguments=malformed_args,
                                    ),
                                )
                            ],
                        ),
                        finish_reason="tool_calls",
                    )
                ]
            ),
            _response_with_tool_call("reflexive", id_="call_2"),
        ]
    )
    validator = FakeValidator([ValidationOutcome(ok=True)])
    result = OpenAICompatBackend(
        client=client, model="Qwen3-Coder-Next"
    ).run(
        system_text=_SYSTEM_TEXT,
        user_message="goal: P = P",
        validator=validator,
        max_attempts=5,
    )
    assert result.ok is True
    assert result.attempts == 2

    # Inspect the transcript of the second request: the assistant
    # turn from attempt 1 must have placeholder arguments, NOT the
    # original malformed bytes.
    second_request_messages = client.chat.completions.messages_per_call[1]
    assistant_turns = [
        m for m in second_request_messages if m.get("role") == "assistant"
    ]
    assert len(assistant_turns) >= 1
    serialized_args = assistant_turns[-1]["tool_calls"][0]["function"]["arguments"]
    assert serialized_args != malformed_args
    parsed = json.loads(serialized_args)
    assert parsed == {"proof_text": ""}


def test_well_formed_args_are_passed_through_unchanged():
    """The normalisation must NOT touch arguments that already parse
    cleanly with a `proof_text` field -- otherwise the model loses
    its own context across turns."""
    good_args = json.dumps({"proof_text": "bad-but-well-formed"})
    client = _CapturingClient(
        [
            FakeResponse(
                choices=[
                    FakeChoice(
                        message=FakeMessage(
                            role="assistant",
                            tool_calls=[
                                FakeToolCall(
                                    id="call_1",
                                    function=FakeFunction(
                                        name="validate_proof",
                                        arguments=good_args,
                                    ),
                                )
                            ],
                        ),
                        finish_reason="tool_calls",
                    )
                ]
            ),
            _response_with_tool_call("reflexive", id_="call_2"),
        ]
    )
    validator = FakeValidator(
        [
            ValidationOutcome(ok=False, error="goal mismatch"),
            ValidationOutcome(ok=True),
        ]
    )
    OpenAICompatBackend(client=client, model="Qwen3-Coder-Next").run(
        system_text=_SYSTEM_TEXT,
        user_message="goal: P = P",
        validator=validator,
        max_attempts=5,
    )
    second_request_messages = client.chat.completions.messages_per_call[1]
    assistant_turns = [
        m for m in second_request_messages if m.get("role") == "assistant"
    ]
    serialized_args = assistant_turns[-1]["tool_calls"][0]["function"]["arguments"]
    assert serialized_args == good_args


class _FakeBadRequestError(Exception):
    """Mimics openai.BadRequestError for tests -- the backend matches
    by class name, not by importing openai, so this works without the
    real SDK installed."""


_FakeBadRequestError.__name__ = "BadRequestError"


class _FlakyChatCompletions:
    """Returns a scripted response, raises on the second call, then
    returns a scripted response on the third call."""

    def __init__(
        self,
        scripted: list[FakeResponse],
        raise_on_call: int,
        exception: Exception,
    ) -> None:
        self._scripted = scripted
        self.calls = 0
        self._raise_on_call = raise_on_call
        self._exception = exception
        self.messages_per_call: list[list[dict]] = []

    def create(self, **kwargs):
        self.messages_per_call.append([dict(m) for m in kwargs["messages"]])
        self.calls += 1
        if self.calls == self._raise_on_call:
            raise self._exception
        idx = self.calls - 1 if self.calls < self._raise_on_call else self.calls - 2
        return self._scripted[idx]


class _FlakyClient:
    def __init__(
        self,
        scripted: list[FakeResponse],
        raise_on_call: int,
        exception: Exception,
    ) -> None:
        self.chat = type(
            "FakeChat",
            (),
            {
                "completions": _FlakyChatCompletions(
                    scripted, raise_on_call, exception
                )
            },
        )()


def test_recoverable_bad_request_continues_loop():
    """Issue #376: when client.chat.completions.create raises a
    BadRequestError that mentions malformed JSON in arguments, the
    loop should record it as a failed attempt, replace the trailing
    assistant turn with a synthetic note, and try again -- not bail
    out as a hard error."""
    exc = _FakeBadRequestError(
        "Error code: 400 - {'error': {'message': "
        "'litellm.BadRequestError: Hosted_vllmException - "
        "{\"error\":{\"message\":\"Unterminated string starting at: "
        "line 1 column 16 (char 15)\"}}'}}"
    )
    client = _FlakyClient(
        scripted=[
            _response_with_tool_call("bad1", id_="call_1"),  # call 1
            _response_with_tool_call("reflexive", id_="call_2"),  # call 3
        ],
        raise_on_call=2,
        exception=exc,
    )
    validator = FakeValidator(
        [
            ValidationOutcome(ok=False, error="goal mismatch"),
            ValidationOutcome(ok=True),
        ]
    )
    result = OpenAICompatBackend(
        client=client, model="Qwen3-Coder-Next"
    ).run(
        system_text=_SYSTEM_TEXT,
        user_message="goal: P = P",
        validator=validator,
        max_attempts=5,
    )
    assert result.ok is True
    assert result.proof == "reflexive"
    assert client.chat.completions.calls == 3

    # The third request's transcript should have a synthetic
    # assistant note replacing the prior failed turn -- no
    # tool_calls in that assistant entry.
    third_request_messages = client.chat.completions.messages_per_call[2]
    assistant_turns = [
        m for m in third_request_messages if m.get("role") == "assistant"
    ]
    assert any(
        "tool_calls" not in m and "malformed" in (m.get("content") or "").lower()
        for m in assistant_turns
    )

    # History should record both the malformed-args recovery and the
    # subsequent successful attempt.
    assert len(result.history) >= 2
    recovery_record = next(
        (h for h in result.history if "server rejected" in (h.outcome.error or "")),
        None,
    )
    assert recovery_record is not None


def test_non_recoverable_bad_request_still_returns_hard_error():
    """A BadRequestError unrelated to malformed arguments (e.g.
    auth/quota) must NOT be silently retried -- bail out as before."""
    exc = _FakeBadRequestError("invalid api key")

    class _AlwaysRaise:
        def __init__(self):
            self.calls = 0
            self.messages_per_call = []

        def create(self, **kwargs):
            self.calls += 1
            self.messages_per_call.append([dict(m) for m in kwargs["messages"]])
            raise exc

    raising = _AlwaysRaise()
    client = type(
        "FakeClient2",
        (),
        {"chat": type("FakeChat2", (), {"completions": raising})()},
    )()
    validator = FakeValidator([])
    result = OpenAICompatBackend(
        client=client, model="Qwen3-Coder-Next"
    ).run(
        system_text=_SYSTEM_TEXT,
        user_message="goal: P",
        validator=validator,
        max_attempts=5,
    )
    assert result.ok is False
    assert "invalid api key" in (result.error or "")
    # Loop should not have looped on this error.
    assert raising.calls == 1


def test_recoverable_bad_request_on_last_attempt_does_not_loop():
    """If the malformed-args 400 lands on the final attempt of the
    budget, there's no retry left -- return failure cleanly rather
    than continuing past max_attempts."""
    exc = _FakeBadRequestError(
        "Error code: 400 - litellm.BadRequestError: "
        "Unterminated string at line 1 column 16"
    )

    class _RaiseOnce:
        def __init__(self):
            self.calls = 0

        def create(self, **kwargs):
            self.calls += 1
            raise exc

    raising = _RaiseOnce()
    client = type(
        "FakeClient3",
        (),
        {"chat": type("FakeChat3", (), {"completions": raising})()},
    )()
    validator = FakeValidator([])
    result = OpenAICompatBackend(
        client=client, model="Qwen3-Coder-Next"
    ).run(
        system_text=_SYSTEM_TEXT,
        user_message="goal: P",
        validator=validator,
        max_attempts=1,
    )
    assert result.ok is False
    assert "API call failed" in (result.error or "")
    assert raising.calls == 1
