"""AnthropicBackend tests using a fake Anthropic client.

The loop's contract: drive ``client.messages.create`` repeatedly,
extract ``tool_use`` blocks, splice the proof_text through the
validator, append tool_result messages, and stop on the first
ok=True.  These tests exercise that contract without burning API
credits.

Fake client + fake validator are both small, hand-rolled stand-ins.
The ``Block`` / ``FakeResponse`` dataclasses match the duck-typing
shape ``anthropic_backend.py`` reads through (``block.type`` /
``block.id`` / ``block.input``).
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Optional

import pytest

from tools.claude_fill_hole.agent import AgentResult
from tools.claude_fill_hole.anthropic_backend import AnthropicBackend
from tools.claude_fill_hole.validator import QueryOutcome, ValidationOutcome


# ---------------------------------------------------------------------------
# Fakes
# ---------------------------------------------------------------------------


@dataclass
class Block:
    type: str
    id: str = ""
    name: str = ""  # tool name when type == "tool_use"
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


def _tool_use(proof: str, *, id_: str = "tu_1",
              name: str = "validate_proof") -> Block:
    return Block(type="tool_use", id=id_, name=name,
                 input={"proof_text": proof})


class FakeQuerier:
    """Mock HoleQuerier: returns scripted QueryOutcomes per call."""

    def __init__(self, outcomes: list[QueryOutcome]) -> None:
        self._outcomes = outcomes
        self.calls: list[str] = []

    def query(self, proof_text: str) -> QueryOutcome:
        self.calls.append(proof_text)
        idx = len(self.calls) - 1
        if idx >= len(self._outcomes):
            raise AssertionError(
                "fake querier: more query() calls than scripted outcomes"
            )
        return self._outcomes[idx]


_SYSTEM_TEXT = "stub system prompt"


def _backend(client: FakeClient) -> AnthropicBackend:
    return AnthropicBackend(client=client)


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


def test_first_attempt_succeeds_returns_ok():
    client = FakeClient([FakeResponse(content=[_tool_use("reflexive")])])
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
    result = _backend(client).run(
        system_text=_SYSTEM_TEXT,
        user_message="goal: P",
        validator=validator,
        max_attempts=5,
    )
    assert result.ok is False
    assert "no tool call" in (result.error or "")
    assert validator.calls == []


def test_malformed_tool_input_is_recoverable():
    """If the model omits ``proof_text``, the loop tells it so via a
    tool_result and gives it another attempt."""
    client = FakeClient(
        [
            FakeResponse(
                content=[Block(type="tool_use", id="tu_1",
                               name="validate_proof", input={})]
            ),
            FakeResponse(content=[_tool_use("reflexive", id_="tu_2")]),
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
    result = AnthropicBackend(client=ExplodingClient()).run(
        system_text=_SYSTEM_TEXT,
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

    client = FakeClient([FakeResponse(content=[_tool_use("reflexive")])])
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
    the backend uses adaptive thinking, an effort level, the
    validate_proof tool, and a system block with cache_control."""
    client = FakeClient([FakeResponse(content=[_tool_use("reflexive")])])
    validator = FakeValidator([ValidationOutcome(ok=True)])
    _backend(client).run(
        system_text=_SYSTEM_TEXT,
        user_message="goal: P = P",
        validator=validator,
        max_attempts=5,
    )
    kwargs = client.messages.last_kwargs
    assert kwargs["thinking"] == {"type": "adaptive"}
    assert kwargs["output_config"] == {"effort": "high"}
    assert kwargs["model"] == "claude-opus-4-7"
    tool_names = [t["name"] for t in kwargs["tools"]]
    assert tool_names == ["validate_proof"]
    # The backend wraps the system_text with a cache_control breakpoint.
    assert kwargs["system"] == [
        {
            "type": "text",
            "text": _SYSTEM_TEXT,
            "cache_control": {"type": "ephemeral"},
        }
    ]


# ---------------------------------------------------------------------------
# query_goal tool tests.
#
# Three things worth pinning down:
#   1) When ``querier`` is passed, the API receives BOTH tools.
#   2) A query_goal call doesn't burn a validate_proof attempt.
#   3) The loop interleaves correctly: query, then validate, then stop.
# ---------------------------------------------------------------------------


def _query_use(proof: str, *, id_: str = "tu_q1",
               name: str = "query_goal") -> Block:
    return Block(type="tool_use", id=id_, name=name,
                 input={"proof_text": proof})


def test_querier_exposes_both_tools_to_api():
    """When a querier is passed, both validate_proof and query_goal
    are advertised in the request's tools array."""
    client = FakeClient([FakeResponse(content=[_tool_use("reflexive")])])
    validator = FakeValidator([ValidationOutcome(ok=True)])
    querier = FakeQuerier([])
    _backend(client).run(
        system_text=_SYSTEM_TEXT,
        user_message="goal: P = P",
        validator=validator,
        max_attempts=5,
        querier=querier,
    )
    tool_names = [t["name"] for t in client.messages.last_kwargs["tools"]]
    assert tool_names == ["validate_proof", "query_goal"]


def test_query_goal_call_does_not_burn_validate_attempt():
    """The model calls query_goal first, sees the goal, then commits
    a validate_proof.  attempts on the result reflects ONLY the
    validate_proof call -- query_goal is free."""
    client = FakeClient(
        [
            FakeResponse(content=[_query_use("?", id_="tu_q1")]),
            FakeResponse(content=[_tool_use("reflexive", id_="tu_v1")]),
        ]
    )
    validator = FakeValidator([ValidationOutcome(ok=True)])
    querier = FakeQuerier(
        [QueryOutcome(ok=True, goal="P = P", givens=())]
    )
    result = _backend(client).run(
        system_text=_SYSTEM_TEXT,
        user_message="goal: P = P",
        validator=validator,
        max_attempts=5,
        querier=querier,
    )
    assert result.ok is True
    assert result.proof == "reflexive"
    # Two API turns (one query, one validate) but only one validate attempt.
    assert result.attempts == 1
    assert client.messages.calls == 2
    assert querier.calls == ["?"]
    assert validator.calls == ["reflexive"]


def test_query_goal_failure_is_reported_to_model_and_loop_continues():
    """If the querier returns ok=False, the loop hands the error to
    the model as a tool_result and lets it try again -- it doesn't
    fail the whole run."""
    client = FakeClient(
        [
            FakeResponse(content=[_query_use("no_marker", id_="tu_q1")]),
            FakeResponse(content=[_tool_use("reflexive", id_="tu_v1")]),
        ]
    )
    validator = FakeValidator([ValidationOutcome(ok=True)])
    querier = FakeQuerier(
        [QueryOutcome(ok=False, error="proof_text contains no `?'")]
    )
    result = _backend(client).run(
        system_text=_SYSTEM_TEXT,
        user_message="goal: P = P",
        validator=validator,
        max_attempts=5,
        querier=querier,
    )
    assert result.ok is True
    assert result.attempts == 1
    assert querier.calls == ["no_marker"]


def test_query_goal_unavailable_when_querier_is_none():
    """Without a querier, the tools array contains only validate_proof,
    and a model that tries to call query_goal anyway gets an
    unknown-tool error back (does NOT crash the loop).

    We script the model to call query_goal first; the loop should
    surface 'unknown tool' and let the model recover with
    validate_proof on the next turn."""
    client = FakeClient(
        [
            FakeResponse(content=[_query_use("?", id_="tu_q1")]),
            FakeResponse(content=[_tool_use("reflexive", id_="tu_v1")]),
        ]
    )
    validator = FakeValidator([ValidationOutcome(ok=True)])
    result = _backend(client).run(
        system_text=_SYSTEM_TEXT,
        user_message="goal: P = P",
        validator=validator,
        max_attempts=5,
        querier=None,
    )
    assert result.ok is True
    # Only validate_proof should appear in the tools list.
    tool_names = [t["name"] for t in client.messages.last_kwargs["tools"]]
    assert tool_names == ["validate_proof"]
