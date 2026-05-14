from pathlib import Path

import parser as lalr_parser
import rec_desc_parser
from abstract_syntax import Call, Theorem, Var


def _parse_theorem_formula(parser_module, formula):
    parser_module.set_deduce_directory(str(Path.cwd()))
    parser_module.set_filename("<parser-associativity-test>")
    parser_module.init_parser()
    ast = parser_module.parse(f"module Test\ntheorem t: {formula} proof ? end\n")
    theorem = next(stmt for stmt in ast if isinstance(stmt, Theorem))
    return theorem.what


def _name(term):
    assert isinstance(term, Var)
    return str(term.name)


def _shape(term):
    if isinstance(term, Var):
        return _name(term)
    assert isinstance(term, Call)
    return (_name(term.rator), tuple(_shape(arg) for arg in term.args))


def test_lalr_groups_additive_chains_left_like_recursive_descent():
    formula = "s + a + fromNat(i) = x"
    assert _shape(_parse_theorem_formula(lalr_parser, formula)) == _shape(
        _parse_theorem_formula(rec_desc_parser, formula)
    ) == (
        "=",
        (
            (
                "+",
                (
                    ("+", ("s", "a")),
                    ("fromNat", ("i",)),
                ),
            ),
            "x",
        ),
    )


def test_lalr_groups_multiplicative_chains_left_like_recursive_descent():
    formula = "x * y * z = w"
    assert _shape(_parse_theorem_formula(lalr_parser, formula)) == _shape(
        _parse_theorem_formula(rec_desc_parser, formula)
    ) == (
        "=",
        (
            ("*", (("*", ("x", "y")), "z")),
            "w",
        ),
    )
