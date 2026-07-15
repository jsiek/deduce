"""Unit tests for numeric-literal builders (issue #1021).

Covers the compact binary builder ``intToUInt`` (correctness and its
O(log n) depth) and the ``check_literal_size`` guard that turns an
oversized literal into a clean located ``ParseError`` instead of a
mid-check recursion crash.
"""

from __future__ import annotations

import pytest
from lark.tree import Meta

import abstract_syntax as ast
from error import ParseError
from flags import MAX_LITERAL


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
def test_int_to_uint_round_trips(n: int) -> None:
    term = ast.intToUInt(Meta(), n)
    assert ast.uintToInt(term) == n


def test_int_to_uint_is_logarithmic_depth() -> None:
    # A unary builder would be depth == value; the binary builder is
    # O(log n), so a billion must nest well under a hundred deep.
    assert _uint_depth(ast.intToUInt(Meta(), 10**9)) < 64


def test_check_literal_size_accepts_up_to_max() -> None:
    ast.check_literal_size(Meta(), MAX_LITERAL)
    ast.check_literal_size(Meta(), -MAX_LITERAL)
    ast.check_literal_size(Meta(), 0)


@pytest.mark.parametrize("n", [MAX_LITERAL + 1, 100000, -(MAX_LITERAL + 1)])
def test_check_literal_size_rejects_oversized(n: int) -> None:
    with pytest.raises(ParseError, match="too large"):
        ast.check_literal_size(Meta(), n)
