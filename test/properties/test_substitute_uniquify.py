"""Property-based tests for AST.substitute and AST.uniquify.

These tests build small terms via Hypothesis strategies and assert
invariants that should hold for any term in the generated subset.
The generator covers Var, Int, Bool, Call, and Lambda.

Lambda equality is only well-defined post-uniquify (Lambda.__eq__
substitutes bodies with ResolvedVar, which compares False against the
pre-uniquify Var — see abstract_syntax.py:1024). So the substitute
properties use the Lambda-free sub-grammar (Var, Int, Bool, Call),
and the uniquify properties use the full grammar but never compare
Lambda nodes structurally.
"""

import sys
from pathlib import Path

import pytest
from hypothesis import HealthCheck, given, settings, strategies as st
from lark.tree import Meta

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from abstract_syntax import (  # noqa: E402
    AST,
    Bool,
    Call,
    Int,
    Lambda,
    UniquifyContext,
    Var,
    reset_reduced_defs,
)


NAMES = ["x", "y", "z"]
ABSENT_KEY = "__never_in_generated_terms__"


def _m() -> Meta:
    return Meta()


var_st = st.builds(lambda v: Var(_m(), None, v), st.sampled_from(NAMES))
int_st = st.builds(lambda n: Int(_m(), None, n), st.integers(-5, 5))
bool_st = st.builds(lambda b: Bool(_m(), None, b), st.booleans())

leaf_st = st.one_of(var_st, int_st, bool_st)


lambda_free_term_st = st.recursive(
    leaf_st,
    lambda children: st.builds(
        lambda rator, args: Call(_m(), None, rator, args),
        children,
        st.lists(children, min_size=1, max_size=3),
    ),
    max_leaves=6,
)

term_with_binders_st = st.recursive(
    leaf_st,
    lambda children: st.one_of(
        st.builds(
            lambda v, body: Lambda(_m(), None, [(v, None)], body),
            st.sampled_from(NAMES),
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


def _walk(node):
    if isinstance(node, AST):
        yield node
        for fld in node.__dataclass_fields__:
            yield from _walk_value(getattr(node, fld))


def _walk_value(v):
    if isinstance(v, AST):
        yield from _walk(v)
    elif isinstance(v, (list, tuple)):
        for x in v:
            yield from _walk_value(x)


def _fresh_uniquify_env():
    # `overwrite` requires the sentinel `"no overload"` key. Free vars
    # in the generated terms are pre-seeded so undefined-var errors
    # don't fire.
    return {
        "no overload": {},
        "x": ["x.seed"],
        "y": ["y.seed"],
        "z": ["z.seed"],
    }


@pytest.fixture(autouse=True)
def _reset_reduced_defs():
    reset_reduced_defs()
    yield


# ---------- substitute ---------------------------------------------------


@given(lambda_free_term_st)
def test_substitute_empty_is_identity(t):
    assert t.substitute({}) == t


@given(lambda_free_term_st, lambda_free_term_st)
def test_substitute_absent_key_is_identity(t, replacement):
    assert t.substitute({ABSENT_KEY: replacement}) == t


@given(lambda_free_term_st, st.sampled_from(NAMES))
def test_substitute_var_with_itself_is_identity(t, name):
    self_var = Var(_m(), None, name)
    assert t.substitute({name: self_var}) == t


@given(lambda_free_term_st, st.sampled_from(NAMES))
def test_var_substitute_hit_returns_replacement(t, name):
    assert Var(_m(), None, name).substitute({name: t}) == t


@given(int_st, lambda_free_term_st)
def test_int_substitute_is_stable(n, replacement):
    assert n.substitute({"x": replacement}) == n


@given(bool_st, lambda_free_term_st)
def test_bool_substitute_is_stable(b, replacement):
    assert b.substitute({"x": replacement}) == b


# ---------- copy ---------------------------------------------------------


@given(lambda_free_term_st)
def test_copy_is_equal_but_distinct(t):
    c = t.copy()
    assert c == t
    assert c is not t


@given(lambda_free_term_st)
def test_copy_is_idempotent(t):
    assert t.copy().copy() == t


@given(lambda_free_term_st)
def test_substitute_does_not_mutate_input(t):
    before = str(t)
    t.substitute({"x": Int(_m(), None, 999)})
    assert str(t) == before


@given(
    lambda_free_term_st,
    st.sampled_from(NAMES),
    st.sampled_from(NAMES),
    lambda_free_term_st,
)
def test_substitute_composition(t, k1, k2, replacement):
    # For lambda-free terms (no binders to capture):
    #   t.subst({k1: u}).subst({k2: v}) == t.subst({k1: u.subst({k2:v}), k2: v})
    # when k1 != k2. Composition law under the assumption that no
    # binders shadow the keys — which is automatic here.
    if k1 == k2:
        return
    u = Var(_m(), None, k2)  # references k2 so sub2 has work to do
    v = replacement
    left = t.substitute({k1: u}).substitute({k2: v})
    right = t.substitute({k1: u.substitute({k2: v}), k2: v})
    assert left == right


# ---------- uniquify ----------------------------------------------------


@settings(suppress_health_check=[HealthCheck.too_slow])
@given(term_with_binders_st)
def test_uniquify_produces_distinct_binder_names(t):
    out = t.uniquify(_fresh_uniquify_env(), UniquifyContext())
    binder_names = [
        x for n in _walk(out) if isinstance(n, Lambda) for (x, _) in n.vars
    ]
    assert len(binder_names) == len(set(binder_names)), (
        f"duplicate binders after uniquify: {binder_names}"
    )


@settings(suppress_health_check=[HealthCheck.too_slow])
@given(term_with_binders_st)
def test_uniquify_is_deterministic(t):
    out1 = t.uniquify(_fresh_uniquify_env(), UniquifyContext())
    out2 = t.uniquify(_fresh_uniquify_env(), UniquifyContext())
    assert str(out1) == str(out2)


@settings(suppress_health_check=[HealthCheck.too_slow])
@given(term_with_binders_st)
def test_uniquify_does_not_mutate_input(t):
    before = str(t)
    t.uniquify(_fresh_uniquify_env(), UniquifyContext())
    after = str(t)
    assert before == after


@settings(suppress_health_check=[HealthCheck.too_slow])
@given(term_with_binders_st)
def test_uniquify_eliminates_plain_var(t):
    out = t.uniquify(_fresh_uniquify_env(), UniquifyContext())
    assert not any(isinstance(n, Var) for n in _walk(out))
