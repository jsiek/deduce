"""Hand-built tests for the Term.typeof policy invariants."""

import sys
from pathlib import Path

from lark.tree import Meta

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

import abstract_syntax as ast  # noqa: E402


def _m() -> Meta:
    return Meta()


def _type_var(name: str) -> ast.Var:
    return ast.Var(_m(), None, name)


def test_substitute_rewrites_typeof_annotation() -> None:
    original_type = ast.ArrayType(_m(), _type_var("T"))
    term = ast.Var(_m(), original_type, "x")

    out = term.substitute({"T": ast.IntType(_m())})

    assert isinstance(out, ast.Var)
    assert out.name == "x"
    assert out.typeof == ast.ArrayType(_m(), ast.IntType(_m()))
    assert term.typeof == original_type


def test_reduce_leaves_typeof_annotation_unchanged() -> None:
    original_type = ast.ArrayType(_m(), _type_var("T"))
    term = ast.Int(_m(), original_type, 7)

    out = term.reduce({})

    assert isinstance(out, ast.Int)
    assert out.value == 7
    assert out.typeof is original_type
    assert out.typeof == ast.ArrayType(_m(), _type_var("T"))


def test_equality_ignores_typeof_annotation() -> None:
    assert ast.Int(_m(), ast.IntType(_m()), 7) == ast.Int(
        _m(), ast.BoolType(_m()), 7
    )
    assert ast.Var(_m(), ast.IntType(_m()), "x") == ast.Var(
        _m(), ast.BoolType(_m()), "x"
    )
