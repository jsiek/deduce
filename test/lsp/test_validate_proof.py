"""Acceptance tests for ``lsp.query.validate_proof_at`` (Phase 5 / Step 3).

The hole-fill sidecar's ``validate_proof`` tool calls this on each
candidate proof Claude produces. The function splices the candidate
into the source at the hole's range and re-runs the checker; v0
just delegates to ``check_file``, so prelude reuse works but
in-file caching does not until the incremental-checking work lands.

The tests pin the contract the sidecar depends on: valid proofs
return ``ok=True``, invalid proofs return ``ok=False`` with the
checker's message, stale ranges are rejected cleanly, and the
function is stateless (idempotent + rolls back failed attempts).
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from lsp.query import (  # noqa: E402
    Position,
    Range,
    ValidationResult,
    hole_context_at,
    validate_proof_at,
)


SOURCE_WITH_HOLE = (
    "theorem t: all P:bool. P = P\n"
    "proof\n"
    "  arbitrary P:bool\n"
    "  ?\n"
    "end\n"
)

# The `?` sits at line 4, column 3 (1-indexed); the range is 1-char.
HOLE_RANGE = Range(
    start=Position(line=4, column=3),
    end=Position(line=4, column=4),
)


def test_valid_proof_returns_ok() -> None:
    """A proof that completes the goal yields ok=True with no error."""
    result = validate_proof_at(
        "test.pf", SOURCE_WITH_HOLE, HOLE_RANGE, "reflexive"
    )
    assert isinstance(result, ValidationResult)
    assert result.ok is True
    assert result.error is None


def test_invalid_proof_returns_error_with_message() -> None:
    """A proof that does not check yields ok=False with the checker's
    message. The text doesn't have to match exactly -- just be
    non-empty and mention something useful."""
    # The hole's goal is `P` (not `P = P`); a bare reference to an
    # undefined label is a clear, unambiguous failure that doesn't
    # reduce to anything trivial.
    source = (
        "theorem t: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  suppose pP: P\n"
        "  ?\n"
        "end\n"
    )
    hole = Range(
        start=Position(line=5, column=3),
        end=Position(line=5, column=4),
    )
    result = validate_proof_at(
        "test.pf", source, hole, "qZ"
    )
    assert result.ok is False
    assert result.error is not None
    assert len(result.error) > 0


def test_range_not_on_question_mark_is_rejected() -> None:
    """Range that doesn't cover a `?` token is rejected cleanly --
    catches stale hole_ranges from async callers without splicing
    in a random location."""
    # Range covering `arbitrary` instead of `?`.
    bad_range = Range(
        start=Position(line=3, column=3),
        end=Position(line=3, column=4),
    )
    result = validate_proof_at(
        "test.pf", SOURCE_WITH_HOLE, bad_range, "reflexive"
    )
    assert result.ok is False
    assert result.error is not None
    assert "?" in result.error


def test_range_out_of_bounds_is_rejected() -> None:
    """Range whose offsets fall past EOF is rejected cleanly."""
    out_of_bounds = Range(
        start=Position(line=999, column=1),
        end=Position(line=999, column=2),
    )
    result = validate_proof_at(
        "test.pf", SOURCE_WITH_HOLE, out_of_bounds, "reflexive"
    )
    assert result.ok is False
    assert result.error is not None


def test_two_valid_calls_in_a_row_each_succeed() -> None:
    """Idempotency: a successful validation doesn't leak state that
    breaks the next call. Same input both times must return the same
    result."""
    a = validate_proof_at(
        "test.pf", SOURCE_WITH_HOLE, HOLE_RANGE, "reflexive"
    )
    b = validate_proof_at(
        "test.pf", SOURCE_WITH_HOLE, HOLE_RANGE, "reflexive"
    )
    assert a.ok is True
    assert b.ok is True


def test_failed_call_does_not_break_subsequent_call() -> None:
    """Rollback: a failed validation leaves the pipeline in a state
    where the next valid call still succeeds. Regression check on
    the prelude-snapshot machinery -- if a checker exception
    pollutes the cached state, the next call would fail too."""
    bad = validate_proof_at(
        "test.pf", SOURCE_WITH_HOLE, HOLE_RANGE, "definitely_undefined_label"
    )
    assert bad.ok is False
    good = validate_proof_at(
        "test.pf", SOURCE_WITH_HOLE, HOLE_RANGE, "reflexive"
    )
    assert good.ok is True


def test_round_trip_with_hole_context_at() -> None:
    """End-to-end shape: hole_context_at returns a hole_range that
    validate_proof_at can use directly. Sidecar's exact call pattern."""
    ctx = hole_context_at(
        "test.pf", SOURCE_WITH_HOLE, Position(line=4, column=3)
    )
    assert ctx is not None
    result = validate_proof_at(
        "test.pf", SOURCE_WITH_HOLE, ctx.hole_range, "reflexive"
    )
    assert result.ok is True


def test_validates_against_givens_in_scope() -> None:
    """Sanity check that splicing actually places the proof at the
    hole (not somewhere else): a proof that needs an in-scope
    hypothesis succeeds, and the same text spliced where the
    hypothesis isn't bound would fail."""
    source = (
        "theorem t: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  suppose pP: P\n"
        "  ?\n"
        "end\n"
    )
    hole = Range(
        start=Position(line=5, column=3),
        end=Position(line=5, column=4),
    )
    result = validate_proof_at("test.pf", source, hole, "pP")
    assert result.ok is True
