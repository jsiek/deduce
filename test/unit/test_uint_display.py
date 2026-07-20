"""Unit tests for UInt value display (issue #1062).

A ``UInt`` value that reduces to zero is the bare nullary constructor
``bzero`` (a ``ResolvedVar``), while every nonzero value is a ``Call``
(``inc_dub``/``dub_inc`` tree). Both must print as decimals in the
default display mode; only ``--verbose`` shows the raw binary form.
"""

from __future__ import annotations

from collections.abc import Iterator

import pytest
from lark.tree import Meta

import abstract_syntax as ast
from flags import set_unique_names, set_verbose


@pytest.fixture(autouse=True)
def _reset_display_flags() -> Iterator[None]:
    set_unique_names(False)
    set_verbose(False)
    yield
    set_unique_names(False)
    set_verbose(False)


@pytest.mark.parametrize("n", [0, 1, 2, 3, 255, 1000])
def test_uint_value_prints_as_decimal(n: int) -> None:
    # Regression: zero used to print as ``bzero`` because the bare
    # constructor never reaches the ``Call.__str__`` UInt branch.
    assert str(ast.intToUInt(Meta(), n)) == str(n)


def test_uint_zero_stays_raw_under_verbose() -> None:
    set_verbose(True)
    assert str(ast.intToUInt(Meta(), 0)) == "bzero"


def test_uint_zero_prints_decimal_under_unique_names() -> None:
    # Nonzero UInt values already ignore --unique-names and print as
    # decimals; zero must be consistent with them.
    set_unique_names(True)
    assert str(ast.intToUInt(Meta(), 0)) == "0"


def test_bzero_pattern_constructor_stays_bzero() -> None:
    # The value-sugar must not leak into pattern/constructor position:
    # `case 0` would reparse as the Nat `zero` pattern, not the Binary
    # `bzero` constructor. A resolved `bzero` pattern constructor (as the
    # induction/predicate machinery builds) must print as `bzero`.
    pat = ast.PatternCons(Meta(), ast.ResolvedVar(Meta(), None, "bzero"), [])
    assert str(pat) == "bzero"
