"""Shared pytest fixtures for the lsp/ test suite.

The Deduce pipeline keeps a lot of module-level state in
``proof_checker`` and ``abstract_syntax`` (caches keyed by module name,
counters, sets of "already checked" modules, etc.). The CLI doesn't
care because each invocation runs in a fresh process, but the in-process
tests below run many checks back-to-back. ``_reset_state`` is the
working inventory of those globals; Step 6 of the LSP plan replaces
this hack with proper per-call isolation.
"""

import sys
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

# Make sys.argv[0] point at deduce.py so set_deduce_directory resolves
# imports the same way the CLI does. Has to happen before any test
# module imports the pipeline.
sys.argv = [str(REPO_ROOT / "deduce.py")]

import abstract_syntax  # noqa: E402
import proof_checker  # noqa: E402
from abstract_syntax import (  # noqa: E402
    add_import_directory,
    init_import_directories,
)
from flags import set_quiet_mode  # noqa: E402


LIB_DIR = REPO_ROOT / "lib"
TEST_IMPORTS_DIR = REPO_ROOT / "test" / "test-imports"


def _reset_state() -> None:
    """Clear the module-level caches the pipeline accumulates per file.

    If a future change to the checker adds another cache, the in-process
    tests will go flaky -- add the new global here.
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
    """Mirror what ``deduce.py``'s ``__main__`` does once at startup."""
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
