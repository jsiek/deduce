"""Acceptance test for ``lsp.library.check_file`` (Phase 1 / Step 1).

For every file in ``test/should-validate`` and ``test/should-error``,
verifies that the library API returns the same outcome (ok vs. error)
that ``test-deduce.py`` produces by shelling out to ``deduce.py``.

This is an in-process test, so it has to manually scrub the module-level
caches in ``proof_checker`` and ``abstract_syntax`` between calls --
those are global today and Step 6 of the plan will replace this hack
with a proper state-isolation mechanism. Until then, ``_reset_state``
below is the source of truth for what state crosses call boundaries.
"""

from __future__ import annotations

import os
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

# Make sys.argv[0] point at deduce.py so the parser's set_deduce_directory
# resolution works the same way the CLI sets it up.
sys.argv = [str(REPO_ROOT / "deduce.py")]

import abstract_syntax  # noqa: E402
import proof_checker  # noqa: E402
from abstract_syntax import (  # noqa: E402
    add_import_directory,
    init_import_directories,
)
from flags import set_quiet_mode  # noqa: E402
from lsp.library import CheckResult, check_file  # noqa: E402

PASS_DIR = REPO_ROOT / "test" / "should-validate"
ERROR_DIR = REPO_ROOT / "test" / "should-error"
LIB_DIR = REPO_ROOT / "lib"
TEST_IMPORTS_DIR = REPO_ROOT / "test" / "test-imports"


def _reset_state() -> None:
    """Clear the module-level caches the pipeline accumulates per file.

    These are the same globals Step 6 of the LSP plan needs to lift; the
    list below is the working inventory. If a future change to the
    checker adds another cache, this test will likely start being flaky
    in CI -- add the new global here.
    """
    abstract_syntax.uniquified_modules.clear()
    abstract_syntax._predicate_decls_by_unique_name.clear()
    abstract_syntax.collected_imports.clear()
    abstract_syntax.reduce_only.clear()
    abstract_syntax.reduced_defs.clear()
    proof_checker.imported_modules.clear()
    proof_checker.checked_modules.clear()
    proof_checker.dirty_files.clear()
    proof_checker.modules.clear()


@pytest.fixture(scope="session", autouse=True)
def _set_up_globals():
    """Mirror what deduce.py's ``__main__`` does once at startup."""
    set_quiet_mode(True)
    init_import_directories()
    add_import_directory(str(LIB_DIR))
    add_import_directory(str(TEST_IMPORTS_DIR))
    sys.setrecursionlimit(10000)
    yield


@pytest.fixture(autouse=True)
def _reset_between_tests():
    _reset_state()
    yield
    _reset_state()


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
    assert result.module_name == path.stem
