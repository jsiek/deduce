"""Tests for ``Env.import_env`` (issue #1250): how an importer's env takes
in the env an imported module was processed in."""

from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from lark.tree import Meta  # noqa: E402

from abstract_syntax import Env  # noqa: E402
from abstract_syntax.env import (  # noqa: E402
    AssociativeBinding, AutoEquationBinding,
)


def _env(module: str, **entries: object) -> Env:
    env = Env().declare_module(module)
    env.dict.update(entries)
    return env


def test_importer_keeps_its_module_and_tracing_and_gains_bindings():
    importer = _env("User", tracing={"user_f"}, a_1="mine")
    module = _env("M", tracing={"m_f"}, b_2="theirs", a_1="mine")
    merged = importer.import_env(module)
    assert merged.get_current_module() == "User"
    assert merged.dict["tracing"] == {"user_f"}
    assert (merged.dict["a_1"], merged.dict["b_2"]) == ("mine", "theirs")
    assert "b_2" not in importer.dict  # the importer's env is unchanged


def test_auto_rules_combine_without_duplicates():
    # Two modules that both import Base share Base's rule objects.
    base_rule, a_rule, b_rule, fallback = object(), object(), object(), object()
    loc = Meta()
    a_auto = AutoEquationBinding(loc, {"f": [base_rule, a_rule]}, [fallback], module="A")
    b_auto = AutoEquationBinding(loc, {"f": [base_rule], "g": [b_rule]}, [fallback], module="B")
    merged = _env("User", __auto__=a_auto).import_env(_env("B", __auto__=b_auto))
    auto = merged.dict["__auto__"]
    assert auto.equations == {"f": [base_rule, a_rule], "g": [b_rule]}
    assert auto.fallback_equations == [fallback]
    assert a_auto.equations == {"f": [base_rule, a_rule]}  # not mutated


def test_induction_schemes_union_with_the_importers_winning():
    merged = _env("User", __inductive__={"T": "mine"}).import_env(
        _env("M", __inductive__={"T": "theirs", "U": "u"})
    )
    assert merged.dict["__inductive__"] == {"T": "mine", "U": "u"}


def test_associativity_declarations_stay_newest_first():
    loc = Meta()
    shared, mine, theirs = ([], "Nat", "p"), ([], "UInt", "q"), ([], "Int", "r")
    ours = AssociativeBinding(loc, "+", [mine, shared], module="User")
    other = AssociativeBinding(loc, "+", [theirs, shared], module="M")
    merged = _env("User", **{"__associative_+": ours}).import_env(
        _env("M", **{"__associative_+": other})
    )
    assert merged.dict["__associative_+"].types == [theirs, mine, shared]
