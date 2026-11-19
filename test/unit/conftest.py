"""Shared pytest config for the unit/ test suite.

Puts the repository root on ``sys.path`` so individual test modules
can do plain ``import abstract_syntax`` etc. without each one
recomputing the path.
"""

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from collections.abc import Iterator  # noqa: E402

import pytest  # noqa: E402

import abstract_syntax as ast  # noqa: E402

# Unique names for UInt's ``Binary`` constructors, as declaring them in
# module UInt would register them.
UINT_NAMES = ('bzero.0', 'dub_inc.0', 'inc_dub.0')


@pytest.fixture
def uint_names() -> Iterator[tuple[str, str, str]]:
    """Register ``UINT_NAMES`` as module UInt's constructors for one test."""
    saved = dict(ast.library_names)
    for name in UINT_NAMES:
        ast.register_library_name('UInt', name)
    yield UINT_NAMES
    ast.library_names.clear()
    ast.library_names.update(saved)
