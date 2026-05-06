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
    assert len(diagnostics) == 1, (
        f"{pf_path.name}: expected 1 diagnostic, got {len(diagnostics)}"
    )

    diag = diagnostics[0]
    assert isinstance(diag, Diagnostic)
    assert diag.severity is Severity.ERROR

    actual = diag.range.start
    assert actual in expected_positions, (
        f"{pf_path.name}: Diagnostic at {actual.line}.{actual.column} "
        f"doesn't match any location in {err_path.name} "
        f"({[f'{p.line}.{p.column}' for p in expected_positions]})"
    )
    assert diag.message, f"{pf_path.name}: diagnostic message is empty"


@pytest.mark.parametrize("name", _SAMPLE_VALID)
def test_check_returns_empty_for_valid_files(name: str) -> None:
    path = PASS_DIR / name
    content = path.read_text()
    diagnostics = check(str(path), content)
    assert diagnostics == [], (
        f"{name} should validate but check returned {len(diagnostics)} "
        f"diagnostic(s): {[d.message for d in diagnostics]}"
    )
