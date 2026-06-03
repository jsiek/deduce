"""Stdin/stdout JSON contract for the hole-fill sidecar.

Mirrors the shapes documented in docs/hole-fill-plan.md (Phase 2,
"stdin / stdout contract"). The dataclasses here are the bridge
between the LSP-shaped request emacs sends in and the result the
sidecar writes back; they are NOT load-bearing for the agent loop
itself, just for the CLI boundary.

Coordinates are LSP-shaped (0-indexed line/character) so emacs can
forward the ``deduce/holeContextAt`` response unchanged.
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from typing import Optional, cast


@dataclass(frozen=True)
class LspPosition:
    line: int
    character: int


@dataclass(frozen=True)
class LspRange:
    start: LspPosition
    end: LspPosition


@dataclass(frozen=True)
class Given:
    label: Optional[str]
    formula: str


@dataclass(frozen=True)
class LemmaInfo:
    name: str
    kind: str  # SymbolKind.value -- "theorem", "lemma", "postulate", ...
    signature: str


@dataclass(frozen=True)
class HoleFillRequest:
    """The JSON object emacs (or any other client) writes to stdin."""

    file: str
    hole_range: LspRange
    goal: str
    givens: tuple[Given, ...]
    lemmas_in_scope: tuple[LemmaInfo, ...]
    fingerprint: str
    # Path to the file's content. If not provided, the sidecar reads
    # ``file`` from disk -- but for unsaved-buffer cases the LSP
    # adapter will pass ``content`` directly so we don't have to.
    content: Optional[str] = None
    # Optional surrounding-source excerpt to include in the prompt
    # (~30 lines around the hole). The sidecar can compute this on
    # its own from ``content`` + ``hole_range``; clients can also
    # provide a precomputed slice.
    surrounding_excerpt: Optional[str] = None


@dataclass(frozen=True)
class ValidationAttempt:
    """One ``validate_proof`` invocation in the agent loop."""

    attempt: int
    ok: bool
    proof_preview: str  # first ~80 chars
    error_tail: Optional[str]  # last ~4kB of stderr on failure


@dataclass(frozen=True)
class HoleFillResponse:
    """The JSON object the sidecar writes to stdout on completion."""

    ok: bool
    fingerprint: str  # echoed back from the request
    attempts: int
    elapsed_ms: int
    model: str
    # The validated proof text on success; absent on failure.
    proof: Optional[str] = None
    # Top-level error message on hard failure (no answer after
    # max_attempts, missing API key, etc.); ``None`` on success.
    error: Optional[str] = None
    # One entry per ``validate_proof`` call. Cheap to include even
    # on success -- the sidecar always reports the trace.
    validations: tuple[ValidationAttempt, ...] = field(default_factory=tuple)


# ---------------------------------------------------------------------------
# JSON serialisation
# ---------------------------------------------------------------------------
#
# The wire format uses camelCase for fields that match LSP shapes
# (``holeRange``, ``lemmasInScope``, etc.) and snake_case otherwise --
# this is what the hole-fill plan documents and what emacs expects.
# Python identifiers are snake_case so we explicitly map both ways.


_REQUEST_FIELD_MAP = {
    # JSON key -> dataclass field name
    "file": "file",
    "holeRange": "hole_range",
    "goal": "goal",
    "givens": "givens",
    "lemmasInScope": "lemmas_in_scope",
    "fingerprint": "fingerprint",
    "content": "content",
    "surroundingExcerpt": "surrounding_excerpt",
}


def request_from_json(text: str) -> HoleFillRequest:
    raw: object = json.loads(text)
    return _request_from_dict(_expect_object(raw, "request"))


def _request_from_dict(raw: dict[str, object]) -> HoleFillRequest:
    range_raw = _expect_object(raw["holeRange"], "holeRange")
    start_raw = _expect_object(range_raw["start"], "holeRange.start")
    end_raw = _expect_object(range_raw["end"], "holeRange.end")
    hole_range = LspRange(
        start=LspPosition(
            line=_expect_int(start_raw["line"], "holeRange.start.line"),
            character=_expect_int(
                start_raw["character"], "holeRange.start.character"
            ),
        ),
        end=LspPosition(
            line=_expect_int(end_raw["line"], "holeRange.end.line"),
            character=_expect_int(end_raw["character"], "holeRange.end.character"),
        ),
    )
    givens = tuple(
        _given_from_object(given_raw, i)
        for i, given_raw in enumerate(_expect_list(raw.get("givens", []), "givens"))
    )
    lemmas = tuple(
        _lemma_from_object(lemma_raw, i)
        for i, lemma_raw in enumerate(
            _expect_list(raw.get("lemmasInScope", []), "lemmasInScope")
        )
    )
    return HoleFillRequest(
        file=_expect_str(raw["file"], "file"),
        hole_range=hole_range,
        goal=_expect_str(raw["goal"], "goal"),
        givens=givens,
        lemmas_in_scope=lemmas,
        fingerprint=_expect_str(raw.get("fingerprint", ""), "fingerprint"),
        content=_optional_str(raw.get("content"), "content"),
        surrounding_excerpt=_optional_str(
            raw.get("surroundingExcerpt"), "surroundingExcerpt"
        ),
    )


def _given_from_object(value: object, index: int) -> Given:
    raw = _expect_object(value, f"givens[{index}]")
    return Given(
        label=_optional_str(raw.get("label"), f"givens[{index}].label"),
        formula=_expect_str(raw["formula"], f"givens[{index}].formula"),
    )


def _lemma_from_object(value: object, index: int) -> LemmaInfo:
    raw = _expect_object(value, f"lemmasInScope[{index}]")
    return LemmaInfo(
        name=_expect_str(raw["name"], f"lemmasInScope[{index}].name"),
        kind=_expect_str(raw.get("kind", "theorem"), f"lemmasInScope[{index}].kind"),
        signature=_expect_str(
            raw.get("signature", ""), f"lemmasInScope[{index}].signature"
        ),
    )


def _expect_object(value: object, field: str) -> dict[str, object]:
    if not isinstance(value, dict):
        raise TypeError(f"{field} must be an object")
    raw = cast(dict[object, object], value)
    out: dict[str, object] = {}
    for key, item in raw.items():
        if not isinstance(key, str):
            raise TypeError(f"{field} keys must be strings")
        out[key] = item
    return out


def _expect_list(value: object, field: str) -> list[object]:
    if not isinstance(value, list):
        raise TypeError(f"{field} must be a list")
    return cast(list[object], value)


def _expect_str(value: object, field: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{field} must be a string")
    return value


def _optional_str(value: object, field: str) -> Optional[str]:
    if value is None:
        return None
    return _expect_str(value, field)


def _expect_int(value: object, field: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"{field} must be an integer")
    return value


def response_to_json(response: HoleFillResponse) -> str:
    """Serialise a HoleFillResponse to JSON with the wire-format keys."""
    out: dict[str, object] = {
        "ok": response.ok,
        "fingerprint": response.fingerprint,
        "attempts": response.attempts,
        "elapsedMs": response.elapsed_ms,
        "model": response.model,
        "validations": [
            {
                "attempt": v.attempt,
                "ok": v.ok,
                "proofPreview": v.proof_preview,
                "errorTail": v.error_tail,
            }
            for v in response.validations
        ],
    }
    if response.proof is not None:
        out["proof"] = response.proof
    if response.error is not None:
        out["error"] = response.error
    return json.dumps(out)


def progress_event(event: str, **fields: object) -> str:
    """One NDJSON line for the stderr progress channel.

    The sidecar emits events of kind ``start``, ``model_request``,
    ``tool_call``, ``tool_result``, ``finish`` -- emacs parses them
    line-by-line to drive its mode-line indicator.
    """
    payload: dict[str, object] = {"event": event}
    payload.update(fields)
    return json.dumps(payload)
