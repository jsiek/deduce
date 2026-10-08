"""Rat's `rzero` prints as `rat(+0)` as a value but as itself in a pattern
(#1207)."""
from typing import Iterator

import pytest
from lark.tree import Meta

import abstract_syntax as ast


@pytest.fixture
def rzero() -> Iterator[str]:
    # Register a stdlib Rat constructor, as declaring module Rat does.
    name = "rzero.test"
    ast.rat_constructors.add(name)
    yield name
    ast.rat_constructors.discard(name)


def test_rzero_value_prints_as_rat_zero(rzero: str) -> None:
    assert str(ast.ResolvedVar(Meta(), None, rzero)) == "rat(+0)"


def test_rzero_pattern_constructor_stays_rzero(rzero: str) -> None:
    pat = ast.PatternCons(Meta(), ast.ResolvedVar(Meta(), None, rzero), [])
    assert str(pat) == "rzero"
