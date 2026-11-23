"""Unit tests for numeric-literal builders (issues #1021, #1025).

Covers the compact binary builder ``intToUInt`` (correctness and its
O(log n) depth), the compact unary ``Numeral`` that ``intToNat``
builds, and the ``check_nat_literal_size`` guard that turns an
oversized ``Nat`` literal into a clean located ``ParseError`` instead of
a mid-check recursion crash.
"""

from __future__ import annotations

import pytest
from lark.tree import Meta

import abstract_syntax as ast
from error import ParseError
from flags import MAX_NAT_LITERAL


def _uint_depth(term: object) -> int:
    """Nesting depth of a UInt constructor stack (bzero/inc_dub/dub_inc)."""
    depth = 0
    while isinstance(term, ast.Call):
        term = term.args[0]
        depth += 1
    return depth


@pytest.mark.parametrize(
    "n", [0, 1, 2, 3, 4, 5, 17, 255, 256, 1000, 1024, 4000, 10**6, 10**9]
)
def test_int_to_uint_round_trips(n: int, uint_names: tuple[str, str, str]) -> None:
    term = ast.intToUInt(Meta(), n, *uint_names)
    assert ast.uintToInt(term) == n


def test_int_to_uint_is_logarithmic_depth(uint_names: tuple[str, str, str]) -> None:
    # A unary builder would be depth == value; the binary builder is
    # O(log n), so a billion must nest well under a hundred deep.
    assert _uint_depth(ast.intToUInt(Meta(), 10**9, *uint_names)) < 64


def test_check_nat_literal_size_accepts_up_to_max() -> None:
    ast.check_nat_literal_size(Meta(), MAX_NAT_LITERAL)
    ast.check_nat_literal_size(Meta(), 0)


@pytest.mark.parametrize("n", [MAX_NAT_LITERAL + 1, 100000])
def test_check_nat_literal_size_rejects_oversized(n: int) -> None:
    with pytest.raises(ParseError, match="too large"):
        ast.check_nat_literal_size(Meta(), n)


def test_uint_literal_has_no_size_limit() -> None:
    assert ast.natToInt(ast.mkUIntLit(Meta(), 10**9).args[0]) == 10**9


def _chain(n: int) -> ast.Term:
    """``suc^n(zero)`` built one call at a time."""
    term: ast.Term = ast.mkZero(Meta())
    for _ in range(n):
        term = ast.mkSuc(Meta(), term)
    return term


def test_nat_literal_is_a_numeral() -> None:
    # A literal stores its number (#1025): `natToInt` and `==` take
    # constant time even for a billion.
    big = ast.intToNat(Meta(), 10**9)
    assert isinstance(big, ast.Numeral)
    assert ast.natToInt(big) == 10**9
    assert big == ast.intToNat(Meta(), 10**9)
    assert big != ast.intToNat(Meta(), 10**9 + 1)


def test_numeral_is_its_suc_chain() -> None:
    # To code that takes it apart, a numeral is `suc(suc(suc(zero)))`.
    three = ast.intToNat(Meta(), 3)
    assert three == _chain(3) and _chain(3) == three
    assert three != _chain(2) and _chain(4) != three
    assert ast.base_name(three.rator.get_name()) == 'suc'
    assert three.args == [ast.intToNat(Meta(), 2)]
    assert str(three) == str(_chain(3)) == 'suc(suc(suc(zero)))'
    assert ast.intToNat(Meta(), 0) == ast.mkZero(Meta())
