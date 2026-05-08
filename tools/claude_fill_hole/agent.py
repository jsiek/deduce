"""Backend-agnostic types and abstract base for the agent loop.

The actual tool-use loop lives in per-backend modules
(``anthropic_backend.py``, ``openai_backend.py``).  This module only
defines the shared shapes -- ``AgentResult``, ``AttemptRecord``, the
``Backend`` ABC, and the schema of the single tool we expose to the
model.

Why a backend split?  Anthropic and OpenAI tool-use APIs are
structurally similar (request -> tool_use blocks -> tool_result
blocks -> repeat) but their wire shapes differ enough that a single
implementation would be a tangle of "if anthropic: ... else: ..."
branches.  Two small concrete backends are clearer.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import Callable, Optional

from .validator import Validator, ValidationOutcome


# What we tell the model the tool does.  Kept brief; the SCAFFOLD
# in ``prompt.py`` already explains the iteration model.  The shape
# below is the JSON-Schema spelling Anthropic uses; OpenAI wraps the
# same dict in ``{"type": "function", "function": {...}}`` -- each
# backend handles the wrapping at its own boundary.
VALIDATE_TOOL_NAME = "validate_proof"
VALIDATE_TOOL_DESCRIPTION = (
    "Splice the given proof text into the file at the hole and run "
    "the Deduce checker. Returns {ok, error}. Call repeatedly to "
    "iterate; first valid proof wins."
)
VALIDATE_TOOL_PARAMETERS = {
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


# Type alias for the progress callback.  Matches what __main__.py uses
# to write NDJSON events to stderr; backends call back through this so
# they stay decoupled from the protocol layer.
ProgressFn = Callable[..., None]


class Backend(ABC):
    """A model-driver for the validate_proof tool-use loop.

    Subclasses encapsulate the SDK client + provider-specific knobs
    (model id, sampling parameters, prompt-caching shape).  The
    ``run`` method is the only public surface the protocol layer
    needs.
    """

    #: Short name for diagnostic output; e.g. "anthropic" or
    #: "openai-compat".  Used in progress events and the response's
    #: ``model`` field when the actual model id isn't useful on its
    #: own.
    name: str = "backend"

    #: Model id this backend will use (subclasses set this in
    #: ``__init__``).  Surfaced in ``AgentResult.model`` so the
    #: protocol layer can echo it back to the caller.
    model: str = ""

    @abstractmethod
    def run(
        self,
        *,
        system_text: str,
        user_message: str,
        validator: Validator,
        max_attempts: int,
        on_progress: Optional[ProgressFn] = None,
    ) -> AgentResult:
        """Drive the validate_proof tool-use loop until ok or budget exhausted.

        ``system_text`` is the rendered system prompt as plain text;
        the backend wraps it in whatever shape its SDK expects (e.g.
        Anthropic's text-block list with ``cache_control``, or
        OpenAI's leading ``{"role": "system", "content": ...}``).

        ``user_message`` is the first user turn carrying the
        per-request bits (goal, givens, lemmas, surrounding source).

        ``validator`` runs each candidate proof.  The first call
        that returns ``ok=True`` ends the loop.

        ``on_progress`` is an optional NDJSON-shaped callback the
        protocol layer uses to stream status to emacs over stderr.
        """


# ---------------------------------------------------------------------------
# Helpers shared across backends
# ---------------------------------------------------------------------------


def preview(s: str, n: int = 80) -> str:
    """Truncate ``s`` to at most ``n`` chars for use in progress events."""
    if len(s) <= n:
        return s
    return s[:n] + "..."
