"""Round-trip tests for the stdin/stdout JSON shapes."""

from __future__ import annotations

import json

from tools.claude_fill_hole.schema import (
    HoleFillRequest,
    HoleFillResponse,
    LemmaInfo,
    Given,
    ValidationAttempt,
    progress_event,
    request_from_json,
    response_to_json,
)


def test_request_from_json_minimum_fields() -> None:
    raw = json.dumps(
        {
            "file": "/tmp/proof.pf",
            "holeRange": {
                "start": {"line": 3, "character": 2},
                "end": {"line": 3, "character": 3},
            },
            "goal": "P = P",
            "givens": [],
            "lemmasInScope": [],
            "fingerprint": "sha256:abc",
        }
    )
    req = request_from_json(raw)
    assert isinstance(req, HoleFillRequest)
    assert req.file == "/tmp/proof.pf"
    assert req.hole_range.start.line == 3
    assert req.hole_range.start.character == 2
    assert req.hole_range.end.character == 3
    assert req.goal == "P = P"
    assert req.givens == ()
    assert req.lemmas_in_scope == ()
    assert req.fingerprint == "sha256:abc"
    assert req.content is None
    assert req.surrounding_excerpt is None


def test_request_from_json_full_payload() -> None:
    raw = json.dumps(
        {
            "file": "/tmp/proof.pf",
            "holeRange": {
                "start": {"line": 5, "character": 2},
                "end": {"line": 5, "character": 3},
            },
            "goal": "Q",
            "givens": [
                {"label": "pP", "formula": "P"},
                {"label": None, "formula": "anonymous"},
            ],
            "lemmasInScope": [
                {"name": "h", "kind": "lemma", "signature": "h: true"},
            ],
            "fingerprint": "fp",
            "content": "theorem t: ...\n",
            "surroundingExcerpt": "  ?\n",
        }
    )
    req = request_from_json(raw)
    assert req.givens == (
        Given(label="pP", formula="P"),
        Given(label=None, formula="anonymous"),
    )
    assert req.lemmas_in_scope == (
        LemmaInfo(name="h", kind="lemma", signature="h: true"),
    )
    assert req.content == "theorem t: ...\n"
    assert req.surrounding_excerpt == "  ?\n"


def test_response_to_json_success_round_trip() -> None:
    response = HoleFillResponse(
        ok=True,
        fingerprint="fp",
        attempts=2,
        elapsed_ms=1234,
        model="claude-opus-4-7",
        proof="reflexive",
        validations=(
            ValidationAttempt(
                attempt=1,
                ok=False,
                proof_preview="apply ...",
                error_tail="goal mismatch",
            ),
            ValidationAttempt(
                attempt=2,
                ok=True,
                proof_preview="reflexive",
                error_tail=None,
            ),
        ),
    )
    raw = response_to_json(response)
    decoded = json.loads(raw)
    assert decoded["ok"] is True
    assert decoded["fingerprint"] == "fp"
    assert decoded["attempts"] == 2
    assert decoded["elapsedMs"] == 1234
    assert decoded["model"] == "claude-opus-4-7"
    assert decoded["proof"] == "reflexive"
    assert "error" not in decoded
    assert decoded["validations"][0]["proofPreview"] == "apply ..."
    assert decoded["validations"][1]["errorTail"] is None


def test_response_to_json_failure_includes_error() -> None:
    response = HoleFillResponse(
        ok=False,
        fingerprint="fp",
        attempts=5,
        elapsed_ms=42,
        model="claude-opus-4-7",
        proof=None,
        error="budget exhausted",
        validations=(),
    )
    decoded = json.loads(response_to_json(response))
    assert decoded["ok"] is False
    assert decoded["error"] == "budget exhausted"
    assert "proof" not in decoded


def test_progress_event_is_one_line_json() -> None:
    line = progress_event("tool_call", attempt=2, proofPreview="abc")
    assert "\n" not in line
    decoded = json.loads(line)
    assert decoded == {
        "event": "tool_call",
        "attempt": 2,
        "proofPreview": "abc",
    }
