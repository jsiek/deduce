"""Shared pytest fixtures for the lsp/ test suite.

Phase 1 / Step 6 moved per-call state isolation into ``check_file``
itself, so the heavy-handed ``_reset_state`` fixture this file used
to declare is gone. Tests now rely on ``check_file`` to restore the
post-prelude snapshot before each call.

The session-scoped ``_set_up_globals`` fixture remains: it mirrors
what ``deduce.py`` does once at process start (enabling quiet mode,
adding ``lib/`` and ``test/test-imports/`` to the import path,
bumping the recursion limit). All test modules in this directory
inherit it automatically.

Tests that need to force a fresh bootstrap call ``reset_prelude_cache``
explicitly; ordinary tests rely on ``check_file`` to restore state.
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

from abstract_syntax import (  # noqa: E402
    add_import_directory,
    init_import_directories,
)
from flags import set_quiet_mode  # noqa: E402


LIB_DIR = REPO_ROOT / "lib"
TEST_IMPORTS_DIR = REPO_ROOT / "test" / "test-imports"


@pytest.fixture(scope="session", autouse=True)
def _set_up_globals():
    """Mirror what ``deduce.py``'s ``__main__`` does once at startup."""
    set_quiet_mode(True)
    init_import_directories()
    add_import_directory(str(LIB_DIR))
    add_import_directory(str(TEST_IMPORTS_DIR))
    sys.setrecursionlimit(10000)
    yield
