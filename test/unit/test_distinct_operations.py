"""`distinct_operations` (#1294): instances of a where function that
would print alike but pass different operations print them."""
from __future__ import annotations

from lark.tree import Meta

import abstract_syntax as ast


def _var(name: str) -> ast.Term:
    return ast.Var(Meta(), None, name)


def _inst(subject: ast.Term, op: str) -> ast.TermInst:
    return ast.TermInst(Meta(), None, subject, [ast.IntType(Meta())], True,
                        dicts=[_var(op)])


def test_alike_instances_show_their_operations() -> None:
    plus, times = _inst(_var("msum"), "plus"), _inst(_var("msum"), "times")
    with ast.distinct_operations([plus, times]):
        assert (str(plus), str(times)) == ("@msum<int>{plus}", "@msum<int>{times}")
    assert str(plus) == str(times) == "msum"


def test_one_instance_prints_as_usual() -> None:
    plus = _inst(_var("msum"), "plus")
    with ast.distinct_operations([plus, plus]):
        assert str(plus) == "msum"


def test_nested_instances_keep_their_keys() -> None:
    # Outer instances whose subjects are instances: (inner A, X),
    # (inner B, X), and (inner A, Y). Showing the inner operations must
    # not change the outer instances' keys, or (inner A, X) and
    # (inner A, Y) would print alike.
    inner_a, inner_b = _inst(_var("f"), "a"), _inst(_var("f"), "b")
    outers = [_inst(inner_a, "x"), _inst(inner_b, "x"), _inst(inner_a, "y")]
    with ast.distinct_operations(outers):
        shown = [str(o) for o in outers]
    assert len(set(shown)) == 3, shown
