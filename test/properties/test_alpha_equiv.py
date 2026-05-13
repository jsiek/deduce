"""Property-based tests for the alpha_equiv helper and the four binder
__eq__ methods (Lambda / All / Some / TLet) that delegate to it.

These tests assert the *equivalence-relation* axioms (reflexivity,
symmetry, transitivity) plus a few alpha-renaming sanity checks that
the old substitute-based __eq__ silently got wrong --
``Lambda(x, Var(x)) == Lambda(x, Var(x))`` returned False before this
refactor because substituting ``{x: ResolvedVar(x)}`` produced a body
whose ResolvedVar(x) compared unequal to the other side's Var(x).
"""

import sys
from pathlib import Path

from hypothesis import HealthCheck, given, settings, strategies as st
from lark.tree import Meta

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from abstract_syntax import (  # noqa: E402
    All,
    Bool,
    BoolType,
    Call,
    FunctionType,
    Int,
    IntType,
    Lambda,
    Some,
    TLet,
    Var,
    alpha_equiv,
)


NAMES = ["x", "y", "z"]


def _m() -> Meta:
    return Meta()


var_st = st.builds(lambda v: Var(_m(), None, v), st.sampled_from(NAMES))
int_st = st.builds(lambda n: Int(_m(), None, n), st.integers(-5, 5))
bool_st = st.builds(lambda b: Bool(_m(), None, b), st.booleans())
leaf_st = st.one_of(var_st, int_st, bool_st)


# Full grammar including binders. Now usable as the comparison
# subject thanks to the alpha-equiv refactor.
term_st = st.recursive(
    leaf_st,
    lambda children: st.one_of(
        st.builds(
            lambda v, body: Lambda(_m(), None, [(v, None)], body),
            st.sampled_from(NAMES),
            children,
        ),
        st.builds(
            lambda v, body: All(_m(), None, (v, IntType(_m())), (0, 1), body),
            st.sampled_from(NAMES),
            children,
        ),
        st.builds(
            lambda v, body: Some(_m(), None, [(v, IntType(_m()))], body),
            st.sampled_from(NAMES),
            children,
        ),
        st.builds(
            lambda v, rhs, body: TLet(_m(), None, v, rhs, body),
            st.sampled_from(NAMES),
            children,
            children,
        ),
        st.builds(
            lambda rator, args: Call(_m(), None, rator, args),
            children,
            st.lists(children, min_size=1, max_size=2),
        ),
    ),
    max_leaves=6,
)


def _rename_in_var(t, old, new):
    """Substitute Var(old) -> Var(new) in a term, *not* respecting
    binders. Used only to build alpha-renamed test inputs where the
    caller has already ensured ``old`` is free."""
    if isinstance(t, Var) and t.name == old:
        return Var(_m(), None, new)
    if isinstance(t, Call):
        return Call(_m(), None, _rename_in_var(t.rator, old, new),
                    [_rename_in_var(a, old, new) for a in t.args])
    return t


# ---------- equivalence-relation axioms ----------------------------------


@given(term_st)
def test_alpha_equiv_reflexive(t):
    assert alpha_equiv(t, t)
    assert t == t


@given(term_st, term_st)
def test_alpha_equiv_symmetric(a, b):
    assert alpha_equiv(a, b) == alpha_equiv(b, a)


@settings(suppress_health_check=[HealthCheck.too_slow])
@given(term_st, term_st, term_st)
def test_alpha_equiv_transitive(a, b, c):
    if alpha_equiv(a, b) and alpha_equiv(b, c):
        assert alpha_equiv(a, c)


# ---------- alpha-renaming preservation ----------------------------------


@given(st.sampled_from(NAMES))
def test_lambda_same_binder_self_reference(x):
    # The bug fixed by this refactor:
    # Lambda(x, Var(x)) == Lambda(x, Var(x)) used to be False.
    body = Call(_m(), None, Var(_m(), None, x), [Int(_m(), None, 0)])
    l1 = Lambda(_m(), None, [(x, None)], body)
    l2 = Lambda(_m(), None, [(x, None)], body)
    assert l1 == l2


@given(st.sampled_from(NAMES), st.sampled_from(NAMES))
def test_lambda_alpha_renaming(x, y):
    # Lambda(x, Var(x)) == Lambda(y, Var(y))
    l_x = Lambda(_m(), None, [(x, None)], Var(_m(), None, x))
    l_y = Lambda(_m(), None, [(y, None)], Var(_m(), None, y))
    assert l_x == l_y


@given(st.sampled_from(NAMES), st.sampled_from(NAMES))
def test_all_alpha_renaming(x, y):
    all_x = All(_m(), None, (x, IntType(_m())), (0, 1), Var(_m(), None, x))
    all_y = All(_m(), None, (y, IntType(_m())), (0, 1), Var(_m(), None, y))
    assert all_x == all_y


@given(st.sampled_from(NAMES), st.sampled_from(NAMES))
def test_some_alpha_renaming(x, y):
    some_x = Some(_m(), None, [(x, IntType(_m()))], Var(_m(), None, x))
    some_y = Some(_m(), None, [(y, IntType(_m()))], Var(_m(), None, y))
    assert some_x == some_y


@given(st.sampled_from(NAMES), st.sampled_from(NAMES), int_st)
def test_tlet_alpha_renaming(x, y, rhs):
    tlet_x = TLet(_m(), None, x, rhs, Var(_m(), None, x))
    tlet_y = TLet(_m(), None, y, rhs, Var(_m(), None, y))
    assert tlet_x == tlet_y


# ---------- detection of real differences --------------------------------


def test_lambda_body_difference_detected():
    l1 = Lambda(_m(), None, [("x", None)], Int(_m(), None, 1))
    l2 = Lambda(_m(), None, [("x", None)], Int(_m(), None, 2))
    assert l1 != l2


def test_lambda_arity_difference_detected():
    l1 = Lambda(_m(), None, [("x", None)], Int(_m(), None, 0))
    l2 = Lambda(_m(), None, [("x", None), ("y", None)], Int(_m(), None, 0))
    assert l1 != l2


def test_capture_not_introduced():
    # Lambda(x, Var(y)) should NOT equal Lambda(y, Var(y)) -- the
    # free `y` in the LHS body is different from the bound `y` of
    # the RHS body. (Alpha-equiv on free names compares by name.)
    l1 = Lambda(_m(), None, [("x", None)], Var(_m(), None, "y"))
    l2 = Lambda(_m(), None, [("y", None)], Var(_m(), None, "y"))
    assert l1 != l2


def test_nested_lambda_shadowing():
    # Lambda(x, Lambda(y, Var(y))) == Lambda(a, Lambda(b, Var(b)))
    # under alpha-renaming.
    l1 = Lambda(_m(), None, [("x", None)],
                Lambda(_m(), None, [("y", None)], Var(_m(), None, "y")))
    l2 = Lambda(_m(), None, [("a", None)],
                Lambda(_m(), None, [("b", None)], Var(_m(), None, "b")))
    assert l1 == l2


def test_nested_lambda_inner_uses_outer():
    # Lambda(x, Lambda(y, Var(x))) renamed to Lambda(a, Lambda(b, Var(a))).
    l1 = Lambda(_m(), None, [("x", None)],
                Lambda(_m(), None, [("y", None)], Var(_m(), None, "x")))
    l2 = Lambda(_m(), None, [("a", None)],
                Lambda(_m(), None, [("b", None)], Var(_m(), None, "a")))
    assert l1 == l2
    # But Lambda(a, Lambda(b, Var(b))) is different.
    l3 = Lambda(_m(), None, [("a", None)],
                Lambda(_m(), None, [("b", None)], Var(_m(), None, "b")))
    assert l1 != l3


# ---------- FunctionType: the only Type-level binder ---------------------
#
# FunctionType binds `type_params` over its `param_types` and `return_type`.
# Before #491, `FunctionType.__eq__` ignored `type_params` entirely:
# fn<T> T -> T compared *equal* to fn<> Int -> Int (different arities) and
# fn<T> T -> T compared *equal* to fn<U> U -> U only by accident (the body
# references the bound name, which differs between sides). The parallel
# walk fixes both.


def _ft_id(tv):
    # fn<tv> tv -> tv  -- the polymorphic identity type, with binder
    # name `tv`. Constructed so the body references the bound name
    # through a Var, which is how the parser emits type-param uses.
    return FunctionType(_m(), [tv],
                        [Var(_m(), None, tv)],
                        Var(_m(), None, tv))


@given(st.sampled_from(NAMES), st.sampled_from(NAMES))
def test_function_type_alpha_renaming(x, y):
    # fn<x> x -> x == fn<y> y -> y -- alpha-renaming of the bound
    # type parameter.
    assert _ft_id(x) == _ft_id(y)


def test_function_type_type_params_arity_difference_detected():
    # The bug fixed by #491: previously, two FunctionTypes whose
    # param/return types were structurally equal but whose
    # `type_params` had different *lengths* compared equal.
    poly = _ft_id("T")
    mono = FunctionType(_m(), [],
                        [Var(_m(), None, "T")],
                        Var(_m(), None, "T"))
    assert poly != mono


def test_function_type_capture_not_introduced():
    # fn<x> y -> y  vs  fn<y> y -> y. The first has `y` free, the
    # second has `y` bound. Alpha-equiv must distinguish them.
    free_y = FunctionType(_m(), ["x"],
                          [Var(_m(), None, "y")],
                          Var(_m(), None, "y"))
    bound_y = FunctionType(_m(), ["y"],
                           [Var(_m(), None, "y")],
                           Var(_m(), None, "y"))
    assert free_y != bound_y


def test_function_type_param_count_difference_detected():
    f1 = FunctionType(_m(), [], [IntType(_m())], IntType(_m()))
    f2 = FunctionType(_m(), [], [IntType(_m()), IntType(_m())], IntType(_m()))
    assert f1 != f2


def test_function_type_return_type_difference_detected():
    f1 = FunctionType(_m(), [], [IntType(_m())], IntType(_m()))
    f2 = FunctionType(_m(), [], [IntType(_m())], BoolType(_m()))
    assert f1 != f2


def test_function_type_two_params_alpha_renamed():
    # fn<A, B> A -> B  ==  fn<X, Y> X -> Y  (parallel renaming of two binders)
    f1 = FunctionType(_m(), ["A", "B"],
                      [Var(_m(), None, "A")],
                      Var(_m(), None, "B"))
    f2 = FunctionType(_m(), ["X", "Y"],
                      [Var(_m(), None, "X")],
                      Var(_m(), None, "Y"))
    assert f1 == f2
    # But swapping the order of usage breaks the equivalence:
    # fn<X, Y> Y -> X is *not* the same as fn<A, B> A -> B.
    f3 = FunctionType(_m(), ["X", "Y"],
                      [Var(_m(), None, "Y")],
                      Var(_m(), None, "X"))
    assert f1 != f3


def test_function_type_nested_in_lambda_annotation():
    # The Lambda annotation `fn<T> T -> T` is alpha-renamable inside
    # the type position of a Lambda binder.
    l1 = Lambda(_m(), None, [("f", _ft_id("T"))], Int(_m(), None, 0))
    l2 = Lambda(_m(), None, [("f", _ft_id("U"))], Int(_m(), None, 0))
    assert l1 == l2


# Add a FunctionType generator to the pool. Bodies reference either
# a bound type-param or an outer free name -- both shapes exercise
# the binding-env lookup. We use `IntType` / `BoolType` as
# non-variable leaves so the generator can terminate without forcing
# a type variable in every position.

type_leaf_st = st.one_of(
    st.builds(lambda: IntType(_m())),
    st.builds(lambda: BoolType(_m())),
    st.builds(lambda v: Var(_m(), None, v), st.sampled_from(NAMES)),
)


function_type_st = st.recursive(
    type_leaf_st,
    lambda children: st.builds(
        lambda tps, pts, rt: FunctionType(_m(), tps, pts, rt),
        st.lists(st.sampled_from(NAMES), min_size=0, max_size=2, unique=True),
        st.lists(children, min_size=0, max_size=2),
        children,
    ),
    max_leaves=5,
)


@given(function_type_st)
def test_function_type_reflexive(t):
    assert t == t
    assert alpha_equiv(t, t)


@given(function_type_st, function_type_st)
def test_function_type_symmetric(a, b):
    assert (a == b) == (b == a)


@settings(suppress_health_check=[HealthCheck.too_slow])
@given(function_type_st, function_type_st, function_type_st)
def test_function_type_transitive(a, b, c):
    if a == b and b == c:
        assert a == c
