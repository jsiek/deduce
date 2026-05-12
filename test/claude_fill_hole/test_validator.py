"""Validator tests against a real ``deduce.py``.

These tests fork the actual checker (the SubprocessValidator's job is
to do exactly that). They're slower than the schema/agent tests but
catch the kind of integration errors a mock would miss: tempfile
placement vs. relative imports, --no-stdlib propagation, error
truncation, exit-code handling.

Each test uses an isolated tempdir as both ``deduce_root`` (so
relative imports start there) and the request file's parent (so the
hidden tempfile lands somewhere we control).
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]

from tools.claude_fill_hole.validator import (  # noqa: E402
    HoleQuerier,
    SubprocessValidator,
)


SOURCE_WITH_HOLE = (
    "theorem t: all P:bool. P = P\n"
    "proof\n"
    "  arbitrary P:bool\n"
    "  ?\n"
    "end\n"
)


def _hole_offsets(source: str) -> tuple[int, int]:
    """Find the byte offsets of the single ``?`` in ``source``."""
    idx = source.index("?")
    return idx, idx + 1


@pytest.fixture
def make_validator(tmp_path):
    """Factory: build a SubprocessValidator pointed at deduce.py with
    a tempfile path inside ``tmp_path``."""
    def _build(source: str = SOURCE_WITH_HOLE, **overrides) -> SubprocessValidator:
        file_path = tmp_path / "proof.pf"
        file_path.write_text(source)
        start, end = _hole_offsets(source)
        kwargs = {
            "file_path": str(file_path),
            "content": source,
            "hole_start_offset": start,
            "hole_end_offset": end,
            "deduce_cmd": (sys.executable, str(REPO_ROOT / "deduce.py")),
            "deduce_root": str(REPO_ROOT),
            "no_stdlib": True,
            "timeout_seconds": 60.0,
        }
        kwargs.update(overrides)
        return SubprocessValidator(**kwargs)
    return _build


def test_valid_proof_returns_ok(make_validator):
    """``reflexive`` completes the goal ``P = P``."""
    v = make_validator()
    outcome = v.validate("reflexive")
    assert outcome.ok is True
    assert outcome.error is None


def test_invalid_proof_carries_checker_message(make_validator):
    """An undefined identifier is rejected with a non-empty error."""
    v = make_validator()
    # Use a goal where `.` won't trivially work, then pass an
    # undefined label.
    source = (
        "theorem t: all P:bool. if P then P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  suppose pP: P\n"
        "  ?\n"
        "end\n"
    )
    start, end = _hole_offsets(source)
    v = make_validator(source=source)
    # Re-init the cached fields with the new source
    v.content = source
    v.hole_start_offset = start
    v.hole_end_offset = end

    outcome = v.validate("definitely_undefined_label")
    assert outcome.ok is False
    assert outcome.error
    assert isinstance(outcome.error, str)
    assert len(outcome.error) > 0


def test_oversized_proof_text_is_rejected_locally(make_validator):
    """A proof_text past the byte cap is rejected without spawning
    deduce.py — the cap is meant to bound parser DOS."""
    v = make_validator(max_proof_text_bytes=128)
    huge = "x " * 200  # ~400 bytes
    outcome = v.validate(huge)
    assert outcome.ok is False
    assert outcome.error and "exceeds" in outcome.error


def test_tempfile_is_cleaned_up_on_success(make_validator, tmp_path):
    v = make_validator()
    v.validate("reflexive")
    leftover = list(tmp_path.glob(".*.fillhole.*.pf"))
    assert leftover == [], f"tempfile not cleaned: {leftover}"


def test_tempfile_is_cleaned_up_on_failure(make_validator, tmp_path):
    v = make_validator()
    v.validate("definitely_undefined_label")
    leftover = list(tmp_path.glob(".*.fillhole.*.pf"))
    assert leftover == []


def test_two_validate_calls_in_a_row_are_independent(make_validator):
    """Idempotency: two valid calls each succeed; the cleanup of the
    first doesn't leave state that breaks the second."""
    v = make_validator()
    a = v.validate("reflexive")
    b = v.validate("reflexive")
    assert a.ok is True
    assert b.ok is True


def test_failed_call_doesnt_break_subsequent_call(make_validator):
    """Rollback: a failing validate doesn't poison the next one."""
    v = make_validator()
    bad = v.validate("definitely_undefined_label")
    assert bad.ok is False
    good = v.validate("reflexive")
    assert good.ok is True


def test_missing_deduce_cmd_returns_structured_error(make_validator):
    """Bad executable -> structured error, not a Python crash."""
    v = make_validator(deduce_cmd=("/no/such/program",))
    outcome = v.validate("reflexive")
    assert outcome.ok is False
    assert outcome.error is not None


# ---------------------------------------------------------------------------
# HoleQuerier tests.
#
# A handful are pure-Python (rejecting bad input before invoking the
# pipeline); the integration-shaped one bootstraps the deduce env and
# exercises a real `lsp.query.hole_context_at' round-trip on a tiny
# in-memory `.pf' source.
# ---------------------------------------------------------------------------


@pytest.fixture
def make_querier(tmp_path):
    def _build(source: str = SOURCE_WITH_HOLE, **overrides) -> HoleQuerier:
        file_path = tmp_path / "proof.pf"
        file_path.write_text(source)
        start, end = _hole_offsets(source)
        kwargs = {
            "file_path": str(file_path),
            "content": source,
            "hole_start_offset": start,
            "hole_end_offset": end,
            "prelude": (),
        }
        kwargs.update(overrides)
        return HoleQuerier(**kwargs)
    return _build


def test_query_rejects_proof_text_without_question_mark(make_querier):
    """``query_goal`` is for inspecting partial proofs; a complete
    proof_text with no ``?`` is a misuse and should be rejected
    locally without invoking the pipeline."""
    q = make_querier()
    outcome = q.query("reflexive")
    assert outcome.ok is False
    assert outcome.error and "?" in outcome.error
    # No goal/givens on failure.
    assert outcome.goal is None
    assert outcome.givens == ()


def test_query_rejects_oversized_proof_text(make_querier):
    """Same byte-cap as the validator; meant to bound runaway model output."""
    q = make_querier(max_proof_text_bytes=128)
    huge = "?" + "x " * 200  # has a `?' but is too long
    outcome = q.query(huge)
    assert outcome.ok is False
    assert outcome.error and "exceeds" in outcome.error


def _bootstrap_deduce_env_for_tests() -> None:
    """Bootstrap the deduce env so HoleQuerier's in-process call to
    ``lsp.query.hole_context_at`` can resolve imports.

    Mirrors what __main__.py does at startup.  Idempotent.
    """
    if str(REPO_ROOT) not in sys.path:
        sys.path.insert(0, str(REPO_ROOT))
    sys.setrecursionlimit(10000)
    # parser.py reads `Deduce.lark' relative to dirname(sys.argv[0]);
    # under pytest, argv[0] is the pytest runner so the parser can't
    # find the grammar.  Point it at deduce.py in REPO_ROOT.
    sys.argv = [str(REPO_ROOT / "deduce.py")] + sys.argv[1:]
    from abstract_syntax import (  # noqa: E402
        add_import_directory,
        init_import_directories,
    )
    from flags import set_quiet_mode  # noqa: E402

    set_quiet_mode(True)
    init_import_directories()
    lib_dir = REPO_ROOT / "lib"
    if lib_dir.is_dir():
        add_import_directory(str(lib_dir))


def test_query_returns_goal_at_hole_in_simple_proof(make_querier):
    """Round-trip: feed a simple file with one ``?`` and ask the
    querier to report the goal at that ``?``.

    The fixture file has goal ``P = P`` after ``arbitrary P:bool``;
    asking with ``proof_text = "?"`` should report exactly that goal.
    """
    _bootstrap_deduce_env_for_tests()
    q = make_querier()  # default SOURCE_WITH_HOLE: P = P after arbitrary
    outcome = q.query("?")
    assert outcome.ok is True, f"expected ok, got error: {outcome.error}"
    # The goal contains "P = P" (or some slight whitespace variant).
    assert outcome.goal is not None
    assert "P = P" in outcome.goal.replace(" ", "") or "P=P" in outcome.goal.replace(" ", "")


def test_query_finds_first_question_mark_after_splice(make_querier):
    """When proof_text contains multiple ``?``s, the querier reports
    on the FIRST one located AT OR AFTER the hole's start offset.
    """
    _bootstrap_deduce_env_for_tests()
    # Source has only one hole; we splice in a partial proof with
    # the first `?' at the case-zero branch.
    source = (
        "union UN { z  s(UN) }\n"
        "theorem t: all n:UN. n = n\n"
        "proof\n"
        "  ?\n"
        "end\n"
    )
    q = make_querier(source=source)
    outcome = q.query("induction UN\ncase z { ? }\ncase s(n') suppose IH: n' = n' { ? }\n")
    assert outcome.ok is True, f"expected ok, got error: {outcome.error}"
    # First `?' after the splice point is in the `case z' branch;
    # its goal should mention z = z.
    assert outcome.goal is not None
    assert "z" in outcome.goal
