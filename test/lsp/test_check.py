"""Acceptance test for ``lsp.query.check`` (Phase 1 / Step 3).

For every ``test/should-error/*.pf`` fixture, verifies that ``check``
returns a single ``Diagnostic`` with ``Severity.ERROR`` whose start
line and column match the location reported in the sibling ``.err``
fixture. For a sample of ``test/should-validate/`` files, verifies
``check`` returns an empty list.

The .err files are produced by running ``deduce.py`` and capturing
stdout, so they contain the same location text the user sees today;
this test pins the new structured ``Diagnostic.range`` to that text,
catching any regression where the LSP/MCP boundary reports a
different line than the CLI does.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from lsp.query import Diagnostic, Position, Severity, check  # noqa: E402

ERROR_DIR = REPO_ROOT / "test" / "should-error"
PASS_DIR = REPO_ROOT / "test" / "should-validate"


# Matches Deduce's location header anywhere in a .err file. Some parse
# errors print the source excerpt first, then the header on a later
# line, so we scan instead of inspecting just the first line.
_LOC_HEADER_RE = re.compile(
    r"(?P<path>[^\s:]+):(?P<line>\d+)\.(?P<col>\d+)-(?P<eline>\d+)\.(?P<ecol>\d+):"
)


def _expected_positions(err_path: Path) -> list[Position]:
    """Pull every ``file:L.C-L.C:`` location out of a .err file.

    Some fixtures print just one location; parse errors print a trace
    (broader context, then the specific failure); structural errors
    like overload clashes print the primary location followed by a
    referential one (e.g. "previously defined here"). The Diagnostic's
    ``e.location`` matches *some* of these, depending on which path
    raised; we accept any match.
    """
    text = err_path.read_text()
    return [
        Position(line=int(m.group("line")), column=int(m.group("col")))
        for m in _LOC_HEADER_RE.finditer(text)
    ]


def _error_pf_files() -> list[Path]:
    return sorted(p for p in ERROR_DIR.glob("*.pf"))


# A handful of should-validate files; the full corpus is already
# covered by test_library.py at the CheckResult level. These confirm
# the query API's empty-list contract.
_SAMPLE_VALID = [
    "after.pf",
    "all-elim-tlet.pf",
    "ImportTests.pf",
    "ListTests.pf",
    "NatTests.pf",
]


@pytest.mark.parametrize("pf_path", _error_pf_files(), ids=lambda p: p.name)
def test_check_reports_error_at_expected_location(pf_path: Path) -> None:
    err_path = pf_path.with_suffix(pf_path.suffix + ".err")
    expected_positions = _expected_positions(err_path)
    if not expected_positions:
        pytest.skip(f"{err_path.name} has no parseable location header")

    content = pf_path.read_text()
    diagnostics = check(str(pf_path), content)

    assert isinstance(diagnostics, list)
    # Step 11 (multi-error collection) means a single .pf file can
    # produce more than one diagnostic — the .err fixture pins only
    # the first error (the one CLI prints), but cascading errors
    # downstream of it now surface too. The test still asserts the
    # primary error from the .err fixture appears, while permitting
    # extras.
    assert len(diagnostics) >= 1, (
        f"{pf_path.name}: expected at least 1 diagnostic, got 0"
    )

    for diag in diagnostics:
        assert isinstance(diag, Diagnostic)
        assert diag.severity is Severity.ERROR
        assert diag.message, f"{pf_path.name}: diagnostic message is empty"

    starts = [d.range.start for d in diagnostics]
    assert any(s in expected_positions for s in starts), (
        f"{pf_path.name}: no Diagnostic matches any location in "
        f"{err_path.name}. Expected one of "
        f"{[f'{p.line}.{p.column}' for p in expected_positions]}, "
        f"got {[f'{s.line}.{s.column}' for s in starts]}"
    )


@pytest.mark.parametrize("name", _SAMPLE_VALID)
def test_check_returns_empty_for_valid_files(name: str) -> None:
    path = PASS_DIR / name
    content = path.read_text()
    diagnostics = check(str(path), content)
    assert diagnostics == [], (
        f"{name} should validate but check returned {len(diagnostics)} "
        f"diagnostic(s): {[d.message for d in diagnostics]}"
    )


# --------------------------------------------------------------------------
# Incomplete-proof diagnostic shape (issue #335)
# --------------------------------------------------------------------------
#
# When the file has a `?', `check' produces a Diagnostic whose message
# is a *one-line* "incomplete proof; goal: <formula>" summary.  The
# goal/givens block lives in `goal_at''s `*Deduce Goal*' buffer
# instead (one keystroke away, `C-c C-g'); the diagnostic message
# itself lands in space-constrained UI (echo area, mode-line,
# underline tooltip) where multi-line content gets truncated.


def test_incomplete_proof_diagnostic_is_single_line() -> None:
    """The diagnostic message fits on one line for the echo area."""
    src = (
        "theorem t: all P:bool, Q:bool. if P then if Q then P\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  assume H1: P\n"
        "  assume H2: Q\n"
        "  ?\n"
        "end\n"
    )
    diags = check("test.pf", src)
    assert len(diags) == 1
    msg = diags[0].message
    # No newlines -- echo-area-friendly.
    assert "\n" not in msg, (
        f"diagnostic message should be single-line; got:\n{msg}"
    )
    # The message announces the kind of error and the goal.
    assert "incomplete proof" in msg
    assert "P" in msg  # the goal formula
    # The verbose CLI prose (Advice text, Givens block, tabs) must NOT
    # appear -- those belong in the *Deduce Goal* buffer.
    assert "Advice:" not in msg
    assert "Givens:" not in msg
    assert "\t" not in msg


def test_incomplete_proof_diagnostic_includes_goal_formula() -> None:
    """The single-line message names the goal so the user can
    triage without opening *Deduce Goal*."""
    src = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  ?\n"
        "end\n"
    )
    diags = check("test.pf", src)
    assert len(diags) == 1
    msg = diags[0].message
    # Goal text is rendered into the message somewhere after the
    # "incomplete proof" prefix.
    assert msg.startswith("incomplete proof")
    assert "P = P" in msg or "(all P:bool. P = P)" in msg


# --------------------------------------------------------------------------
# Multi-error collection (Step 11)
# --------------------------------------------------------------------------
#
# The pipeline used to short-circuit on the first error/hole, so the
# editor only ever drew one underline. Step 11 threads an ErrorSink
# through ``check_deduce`` so each top-level statement that fails (and
# each ``?`` in its own theorem) gets its own Diagnostic. These tests
# pin that contract directly.


def test_check_reports_multiple_holes() -> None:
    """Two independent theorems, each with a `?`, produce two
    diagnostics — one per hole, at distinct lines."""
    src = (
        "theorem t1: all P:bool. P = P\n"
        "proof\n"
        "  ?\n"
        "end\n"
        "theorem t2: all Q:bool. Q or not Q\n"
        "proof\n"
        "  ?\n"
        "end\n"
    )
    diags = check("test.pf", src)
    assert len(diags) == 2, (
        f"expected 2 diagnostics (one per hole), got {len(diags)}: "
        f"{[d.message for d in diags]}"
    )
    assert all(d.severity is Severity.ERROR for d in diags)
    assert all("incomplete proof" in d.message for d in diags)
    lines = sorted(d.range.start.line for d in diags)
    assert lines == [3, 7], (
        f"expected holes at lines 3 and 7, got {lines}"
    )


def test_check_reports_multiple_holes_within_one_proof() -> None:
    """Sibling subproofs in a single theorem each report their own
    hole. Covers the four sibling-independent recursion sites in
    ``check_proof_of``: PTuple (``?, ?``), proof-by-cases on ``or``,
    switch on ``bool``, switch on a union.
    """
    # PTuple: each conjunct of ``P and Q`` has its own ?
    src_tuple = (
        "theorem t: all P:bool, Q:bool. P and Q\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  ?, ?\n"
        "end\n"
    )
    diags = check("test.pf", src_tuple)
    assert len(diags) == 2, (
        f"PTuple: expected 2 holes, got {len(diags)}: "
        f"{[d.message for d in diags]}"
    )

    # Switch on bool: each arm has its own ?
    src_switch_bool = (
        "theorem t: all P:bool. P or not P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  switch P {\n"
        "    case true { ? }\n"
        "    case false { ? }\n"
        "  }\n"
        "end\n"
    )
    diags = check("test.pf", src_switch_bool)
    assert len(diags) == 2, (
        f"switch on bool: expected 2 holes, got {len(diags)}: "
        f"{[d.message for d in diags]}"
    )

    # Proof-by-cases on `or`: each arm has its own ?
    src_cases = (
        "theorem t: all P:bool, Q:bool. if P or Q then true\n"
        "proof\n"
        "  arbitrary P:bool, Q:bool\n"
        "  suppose prem: P or Q\n"
        "  cases prem\n"
        "  case p { ? }\n"
        "  case q { ? }\n"
        "end\n"
    )
    diags = check("test.pf", src_cases)
    assert len(diags) == 2, (
        f"cases on or: expected 2 holes, got {len(diags)}: "
        f"{[d.message for d in diags]}"
    )


def test_check_reports_proof_error_plus_hole_independently() -> None:
    """A proof-checking error in one theorem doesn't suppress a hole
    in an unrelated later theorem. The first theorem misuses
    ``reflexive`` (which proves equalities) on a non-equality goal;
    the second is just an incomplete proof. Both should appear.
    """
    src = (
        "theorem broken: all P:bool. P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  reflexive\n"               # reflexive on a non-equality
        "end\n"
        "theorem hole: all Q:bool. Q = Q\n"
        "proof\n"
        "  ?\n"
        "end\n"
    )
    diags = check("test.pf", src)
    assert len(diags) >= 2, (
        f"expected at least 2 diagnostics, got {len(diags)}: "
        f"{[d.message for d in diags]}"
    )
    # The hole at line 8 must appear regardless of the first
    # theorem's failed proof.
    assert any(d.range.start.line == 8 for d in diags), (
        f"expected a diagnostic on line 8 (the hole), got "
        f"{[(d.range.start.line, d.message[:40]) for d in diags]}"
    )
