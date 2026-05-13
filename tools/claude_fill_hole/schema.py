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
from typing import Any, Optional


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
    raw = json.loads(text)
    return _request_from_dict(raw)


def _request_from_dict(raw: dict[str, Any]) -> HoleFillRequest:
    range_raw = raw["holeRange"]
    hole_range = LspRange(
        start=LspPosition(
            line=int(range_raw["start"]["line"]),
            character=int(range_raw["start"]["character"]),
        ),
        end=LspPosition(
            line=int(range_raw["end"]["line"]),
            character=int(range_raw["end"]["character"]),
        ),
    )
    givens = tuple(
        Given(label=g.get("label"), formula=g["formula"])
        for g in raw.get("givens", [])
    )
    lemmas = tuple(
        LemmaInfo(
            name=lemma["name"],
            kind=lemma.get("kind", "theorem"),
            signature=lemma.get("signature", ""),
        )
        for lemma in raw.get("lemmasInScope", [])
    )
    return HoleFillRequest(
        file=raw["file"],
        hole_range=hole_range,
        goal=raw["goal"],
        givens=givens,
        lemmas_in_scope=lemmas,
        fingerprint=raw.get("fingerprint", ""),
        content=raw.get("content"),
        surrounding_excerpt=raw.get("surroundingExcerpt"),
    )


def response_to_json(response: HoleFillResponse) -> str:
    """Serialise a HoleFillResponse to JSON with the wire-format keys."""
    out: dict[str, Any] = {
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


def progress_event(event: str, **fields: Any) -> str:
    """One NDJSON line for the stderr progress channel.

    The sidecar emits events of kind ``start``, ``model_request``,
    ``tool_call``, ``tool_result``, ``finish`` -- emacs parses them
    line-by-line to drive its mode-line indicator.
    """
    payload: dict[str, Any] = {"event": event}
    payload.update(fields)
    return json.dumps(payload)
