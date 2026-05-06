"""Acceptance test for Step 6 (in-process prelude caching + state
isolation).

The plan's acceptance criteria, verbatim:

    (a) call ``check`` on the same file twice in one process, results
        identical;
    (b) ``check(A); check(B); check(A)`` -- third call matches first.

Plus a few extras that verify the new caching machinery actually
caches (rather than silently bootstrapping every time) and that the
public ``reset_prelude_cache`` helper works as documented.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

import lsp.library as _library  # noqa: E402
from lsp.library import reset_prelude_cache  # noqa: E402
from lsp.query import check  # noqa: E402


VALID_FILE = REPO_ROOT / "test" / "should-validate" / "after.pf"
ERROR_FILE_A = REPO_ROOT / "test" / "should-error" / "advice_and.pf"
ERROR_FILE_B = REPO_ROOT / "test" / "should-error" / "advice_or.pf"


def _diags(path: Path):
    return check(str(path), path.read_text())


# --------------------------------------------------------------------------
# Plan acceptance criterion (a): same file, two calls -> identical
# --------------------------------------------------------------------------


def test_check_is_idempotent_on_valid_file():
    d1 = _diags(VALID_FILE)
    d2 = _diags(VALID_FILE)
    assert d1 == [], f"{VALID_FILE.name} should validate"
    assert d2 == d1, "same input should produce same diagnostics"


def test_check_is_idempotent_on_error_file():
    d1 = _diags(ERROR_FILE_A)
    d2 = _diags(ERROR_FILE_A)
    assert d1, f"{ERROR_FILE_A.name} should produce a diagnostic"
    assert d2 == d1, (
        f"same input should produce same diagnostics; "
        f"got {d1[0]} vs {d2[0]}"
    )


# --------------------------------------------------------------------------
# Plan acceptance criterion (b): A; B; A -> first and third match
# --------------------------------------------------------------------------


def test_interleaved_checks_dont_pollute_each_other():
    da_first = _diags(ERROR_FILE_A)
    db = _diags(ERROR_FILE_B)
    da_second = _diags(ERROR_FILE_A)

    # Sanity: A and B really are different fixtures, otherwise the
    # interleaving check is meaningless.
    assert da_first != db, "A and B should produce different diagnostics"

    # The acceptance criterion: state from B did not bleed into A.
    assert da_second == da_first, (
        "third call's diagnostic differs from the first -- state from "
        f"the intervening B call leaked. Got: {da_first} vs {da_second}"
    )


# --------------------------------------------------------------------------
# Caching machinery actually caches
# --------------------------------------------------------------------------


def test_same_prelude_reuses_snapshot():
    """Two ``check`` calls with the same (empty) prelude should share
    a single snapshot, not bootstrap twice."""
    reset_prelude_cache()
    assert _library._prelude_snapshot is None

    _diags(VALID_FILE)
    snap_after_first = _library._prelude_snapshot
    assert snap_after_first is not None, "first call should populate snapshot"

    _diags(VALID_FILE)
    assert _library._prelude_snapshot is snap_after_first, (
        "second call with same prelude should reuse the snapshot"
    )


def test_reset_prelude_cache_forces_rebootstrap():
    """``reset_prelude_cache`` should drop the snapshot so the next
    call bootstraps from scratch."""
    _diags(VALID_FILE)
    assert _library._prelude_snapshot is not None

    reset_prelude_cache()
    assert _library._prelude_snapshot is None
    assert _library._prelude_key is None

    _diags(VALID_FILE)
    assert _library._prelude_snapshot is not None, (
        "after reset, the next call should rebootstrap and re-snapshot"
    )


# --------------------------------------------------------------------------
# State containers are restored, not just cleared
# --------------------------------------------------------------------------


def test_uniquified_modules_resets_between_calls():
    """A user file's module entry from one call should not survive
    into the next call's view of the cache.

    Specifically, the ``uniquified_modules`` cache from
    ``abstract_syntax`` should hold the same set of entries before
    and after each ``check_file`` call (modulo the prelude entries,
    which are part of the snapshot)."""
    import abstract_syntax

    reset_prelude_cache()
    _diags(VALID_FILE)
    after_first = set(abstract_syntax.uniquified_modules.keys())

    _diags(VALID_FILE)
    after_second = set(abstract_syntax.uniquified_modules.keys())

    assert after_first == after_second, (
        f"uniquified_modules drifted between identical calls: "
        f"first={after_first}, second={after_second}"
    )
