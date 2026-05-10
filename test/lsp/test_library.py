"""Acceptance test for ``lsp.library.check_file`` (Phase 1 / Step 1).

For every file in ``test/should-validate`` and ``test/should-error``,
verifies that the library API returns the same outcome (ok vs. error)
that ``test-deduce.py`` produces by shelling out to ``deduce.py``.

The session/state fixtures live in ``conftest.py`` so the Step 3
acceptance test can share them.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from lsp.library import CheckResult, check_file  # noqa: E402

PASS_DIR = REPO_ROOT / "test" / "should-validate"
ERROR_DIR = REPO_ROOT / "test" / "should-error"
LIB_DIR = REPO_ROOT / "lib"


def _pf_files(d: Path) -> list[Path]:
    return sorted(p for p in d.glob("*.pf"))


@pytest.mark.parametrize("path", _pf_files(PASS_DIR), ids=lambda p: p.name)
def test_should_validate(path: Path) -> None:
    result = check_file(str(path), prelude=())
    assert isinstance(result, CheckResult)
    assert result.ok, (
        f"{path.name} should validate but check_file returned an error:\n"
        f"{result.error_message}"
    )
    assert result.error_message is None
    assert result.exception is None
    assert result.ast is not None
    assert result.module_name == path.stem


@pytest.mark.parametrize("path", _pf_files(ERROR_DIR), ids=lambda p: p.name)
def test_should_error(path: Path) -> None:
    result = check_file(str(path), prelude=())
    assert isinstance(result, CheckResult)
    assert not result.ok, (
        f"{path.name} should produce an error but check_file returned ok"
    )
    assert result.error_message is not None
    assert result.error_message != ""
    assert result.exception is not None
    assert result.module_name == path.stem


@pytest.mark.parametrize("path", _pf_files(LIB_DIR), ids=lambda p: p.name)
def test_lib_collect_errors_no_false_positives(path: Path) -> None:
    """Regression test for issue #400: ``check_file(..., collect_errors=True)``
    on a stdlib file must agree with ``deduce.py`` -- speculative
    iff-application and PTuple goal-directed-then-synthesis attempts
    used to leak failed-probe errors into the sink even when the
    enclosing rule recovered."""
    result = check_file(str(path), collect_errors=True, prelude=())
    assert result.ok, (
        f"{path.name} should validate but collect_errors mode reported "
        f"{len(result.errors)} error(s); first:\n{result.error_message}"
    )
    assert result.errors == []
