"""Agent-loop tests using a fake Anthropic client.

The loop's contract: drive ``client.messages.create`` repeatedly,
extract ``tool_use`` blocks, splice the proof_text through the
validator, append tool_result messages, and stop on the first
ok=True. These tests exercise that contract without burning API
credits.

Fake client + fake validator are both small, hand-rolled stand-ins.
The ``Block`` / ``FakeResponse`` dataclasses match the duck-typing
shape ``agent.py`` reads through (``block.type`` / ``block.id`` /
``block.input``).
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Optional

import pytest

from tools.claude_fill_hole.agent import AgentResult, run as run_agent
from tools.claude_fill_hole.validator import ValidationOutcome


# ---------------------------------------------------------------------------
# Fakes
# ---------------------------------------------------------------------------


@dataclass
class Block:
    type: str
    id: str = ""
    input: dict = field(default_factory=dict)
    text: str = ""


@dataclass
class FakeResponse:
    content: list[Block]
    stop_reason: str = "tool_use"


class FakeMessages:
    def __init__(self, scripted: list[FakeResponse]) -> None:
        self._scripted = scripted
        self.calls = 0
        self.last_kwargs: Optional[dict[str, Any]] = None

    def create(self, **kwargs):
        self.last_kwargs = kwargs
        if self.calls >= len(self._scripted):
            raise AssertionError(
                "fake client: agent loop made more API calls than scripted"
            )
        response = self._scripted[self.calls]
        self.calls += 1
        return response


class FakeClient:
    def __init__(self, scripted: list[FakeResponse]) -> None:
        self.messages = FakeMessages(scripted)


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


def _tool_use(proof: str, *, id_: str = "tu_1") -> Block:
    return Block(type="tool_use", id=id_, input={"proof_text": proof})


def _system() -> list[dict]:
    return [{"type": "text", "text": "stub system prompt"}]


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


def test_first_attempt_succeeds_returns_ok():
    client = FakeClient(
        [FakeResponse(content=[_tool_use("reflexive")])]
    )
    validator = FakeValidator([ValidationOutcome(ok=True)])
    result = run_agent(
        client=client,
        system=_system(),
        user_message="goal: P = P",
        validator=validator,
    )
    assert result.ok is True
    assert result.proof == "reflexive"
    assert result.attempts == 1
    assert client.messages.calls == 1


def test_third_attempt_succeeds_after_two_failures():
    client = FakeClient(
        [
            FakeResponse(content=[_tool_use("bad1", id_="tu_1")]),
            FakeResponse(content=[_tool_use("bad2", id_="tu_2")]),
            FakeResponse(content=[_tool_use("reflexive", id_="tu_3")]),
        ]
    )
    validator = FakeValidator(
        [
            ValidationOutcome(ok=False, error="goal mismatch (bad1)"),
            ValidationOutcome(ok=False, error="undefined label (bad2)"),
            ValidationOutcome(ok=True),
        ]
    )
    result = run_agent(
        client=client,
        system=_system(),
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
            FakeResponse(content=[_tool_use("bad1", id_="tu_1")]),
            FakeResponse(content=[_tool_use("bad2", id_="tu_2")]),
        ]
    )
    validator = FakeValidator(
        [
            ValidationOutcome(ok=False, error="err1"),
            ValidationOutcome(ok=False, error="err2"),
        ]
    )
    result = run_agent(
        client=client,
        system=_system(),
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
    """Model emits a text-only response (no tool_use blocks). Treated
    as 'gave up' -- not a hard error, but no proof to apply."""
    client = FakeClient(
        [
            FakeResponse(
                content=[Block(type="text", text="I don't know.")],
                stop_reason="end_turn",
            )
        ]
    )
    validator = FakeValidator([])
    result = run_agent(
        client=client,
        system=_system(),
        user_message="goal: P",
        validator=validator,
        max_attempts=5,
    )
    assert result.ok is False
    assert "no validate_proof" in (result.error or "")
    assert validator.calls == []


def test_malformed_tool_input_is_recoverable():
    """If the model omits ``proof_text``, the loop tells it so via a
    tool_result and gives it another attempt."""
    client = FakeClient(
        [
            FakeResponse(content=[Block(type="tool_use", id="tu_1", input={})]),
            FakeResponse(content=[_tool_use("reflexive", id_="tu_2")]),
        ]
    )
    validator = FakeValidator([ValidationOutcome(ok=True)])
    result = run_agent(
        client=client,
        system=_system(),
        user_message="goal: P = P",
        validator=validator,
        max_attempts=5,
    )
    assert result.ok is True
    assert result.attempts == 2
    # Validator was only called for the second attempt -- the
    # first never made it past the tool-input check.
    assert validator.calls == ["reflexive"]


def test_api_failure_is_reported_as_hard_error():
    """If client.messages.create raises, the loop returns a structured
    failure with the exception message in error."""

    class ExplodingMessages:
        def create(self, **kwargs):
            raise RuntimeError("network exploded")

    class ExplodingClient:
        def __init__(self):
            self.messages = ExplodingMessages()

    validator = FakeValidator([])
    result = run_agent(
        client=ExplodingClient(),
        system=_system(),
        user_message="goal: P",
        validator=validator,
        max_attempts=5,
    )
    assert result.ok is False
    assert result.proof is None
    assert "network exploded" in (result.error or "")


def test_progress_callback_fires_for_each_phase():
    events: list[tuple[str, dict]] = []

    def on_progress(event: str, **fields):
        events.append((event, fields))

    client = FakeClient(
        [FakeResponse(content=[_tool_use("reflexive")])]
    )
    validator = FakeValidator([ValidationOutcome(ok=True)])
    run_agent(
        client=client,
        system=_system(),
        user_message="goal: P = P",
        validator=validator,
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
    the agent uses adaptive thinking, an effort level, the
    validate_proof tool, and prompt-cached system content."""
    client = FakeClient(
        [FakeResponse(content=[_tool_use("reflexive")])]
    )
    validator = FakeValidator([ValidationOutcome(ok=True)])
    run_agent(
        client=client,
        system=_system(),
        user_message="goal: P = P",
        validator=validator,
    )
    kwargs = client.messages.last_kwargs
    assert kwargs["thinking"] == {"type": "adaptive"}
    assert kwargs["output_config"] == {"effort": "high"}
    assert kwargs["model"] == "claude-opus-4-7"
    tool_names = [t["name"] for t in kwargs["tools"]]
    assert tool_names == ["validate_proof"]
    # System block is passed through unchanged.
    assert kwargs["system"] == _system()
