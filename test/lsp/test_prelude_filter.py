"""Acceptance test for issue #365.

When the user file imports a prelude module with `using` or `hiding`,
the prelude's auto-injected unfiltered import for that same module is
suppressed so the user's filter actually narrows the visible names.
"""

from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from lsp.library import check_file  # noqa: E402


PRELUDE = ("Base", "Option", "NatDefs", "NatAdd", "NatMonus", "NatMult",
           "NatLess", "NatEvenOdd", "NatDiv", "NatPowLog", "NatSum",
           "Pair", "Nat")


def _check(content: str):
    return check_file(
        "__test__.pf", prelude=PRELUDE, content=content,
    )


def test_unfiltered_prelude_import_brings_all_names():
    result = _check("define _ : Nat = gcd(suc(zero), suc(suc(zero)))\n")
    assert result.ok, f"baseline (no user filter) should validate: {result.error_message}"


def test_user_using_excludes_other_prelude_names():
    """`import Nat using equal_refl` should make `gcd` undefined."""
    src = "import Nat using equal_refl\n\ndefine _ : Nat = gcd(suc(zero), suc(suc(zero)))\n"
    result = _check(src)
    assert not result.ok, "expected gcd to be undefined under filtered prelude"
    assert "gcd" in (result.error_message or "")


def test_user_using_admits_named_prelude_name():
    """`import Nat using gcd` should still allow gcd."""
    src = "import Nat using gcd\n\ndefine _ : Nat = gcd(suc(zero), suc(suc(zero)))\n"
    result = _check(src)
    assert result.ok, f"expected gcd to be available: {result.error_message}"


def test_user_hiding_excludes_named_prelude_name():
    """`import Nat hiding gcd` should make gcd undefined."""
    src = "import Nat hiding gcd\n\ndefine _ : Nat = gcd(suc(zero), suc(suc(zero)))\n"
    result = _check(src)
    assert not result.ok, "expected gcd to be hidden"
    assert "gcd" in (result.error_message or "")
