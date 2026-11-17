"""Printed terms reparse to the same term (#1283): the printer drops
parentheses the grammar doesn't need, but keeps the ones it does."""
from pathlib import Path

import pytest

import rec_desc_parser
from abstract_syntax import Conditional, IfThen, Term, Theorem


def _parse(formula: str) -> Term:
    rec_desc_parser.set_deduce_directory(str(Path.cwd()))
    rec_desc_parser.set_filename("<print-parens-test>")
    rec_desc_parser.init_parser()
    # Array updates and field access are experimental imperative syntax.
    ast = rec_desc_parser.parse(f"module Test\ntheorem t: {formula} proof ? end\n",
                                experimental_imperative=True)
    return next(stmt for stmt in ast if isinstance(stmt, Theorem)).what


@pytest.mark.parametrize("formula", [
    "(if c then a else b)[i] = a",
    "(if c then a else b).f = a",
    "if c then (if p then q) else r",
])
def test_needed_parentheses_are_printed(formula):
    assert str(_parse(formula)) == formula


def test_pretty_printed_conditional_groups_an_implication_in_its_then_branch():
    term = _parse("if c then (if p then q) else r")
    assert isinstance(term, Conditional) and isinstance(term.thn, IfThen)
    assert _parse(term.pretty_print(0, True)) == term
