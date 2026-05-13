"""Property-based tests for the post-uniquify AST shape.

After ``uniquify_deduce`` runs, every variable reference is an
``OverloadedVar`` (or, post-typecheck, a ``ResolvedVar``) with a
mangled name like ``"x.S0"``; pre-uniquify ``Var`` no longer appears.
The companion tests in [`test_substitute_uniquify.py`](test_substitute_uniquify.py)
and [`test_typeof.py`](test_typeof.py) generate pre-uniquify shapes
only, which leaves the post-uniquify substitute / equality / reduce
paths unexercised — exactly the paths most of the recent bug fixes
(#480, #484, #490) lived on.

These tests pin down the invariants that the post-uniquify forms
must satisfy in isolation:

* Phase isolation: a pre-uniquify ``Var`` never compares equal to a
  post-uniquify ``OverloadedVar`` / ``ResolvedVar`` with the same
  underlying name.
* ``substitute`` never silently downgrades the post-uniquify form
  (an ``OverloadedVar`` miss stays ``OverloadedVar``, a ``ResolvedVar``
  miss stays ``ResolvedVar``).
* ``copy`` produces an independent ``resolved_names`` list on
  ``OverloadedVar`` — mutating one side does not affect the other.
* ``Lambda`` alpha-equivalence and ``substitute`` work on the
  post-uniquify body shape, which #490 made well-defined but the
  prior generator could not exercise.
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
    OverloadedVar,
    ResolvedVar,
    Term,
    Var,
    alpha_equiv,
    reset_reduced_defs,
)


# Pool of post-uniquify names. ``generate_name`` would produce shapes
# like ``"x.S0"`` / ``"y.S1"``; we use the same ``base.suffix`` shape
# so ``base_name`` and the str-rendering helpers behave the same.
POST_NAMES = ["x.S0", "y.S1", "z.S2"]


def _m() -> Meta:
    return Meta()


# ---------- Post-uniquify generators ------------------------------------

ovar_st = st.builds(
    lambda n: OverloadedVar(_m(), None, [n]),
    st.sampled_from(POST_NAMES),
)
rvar_st = st.builds(
    lambda n: ResolvedVar(_m(), None, n),
    st.sampled_from(POST_NAMES),
)
int_st = st.builds(lambda n: Int(_m(), None, n), st.integers(-5, 5))
bool_st = st.builds(lambda b: Bool(_m(), None, b), st.booleans())

post_leaf_st = st.one_of(ovar_st, rvar_st, int_st, bool_st)

post_term_st = st.recursive(
    post_leaf_st,
    lambda children: st.builds(
        lambda rator, args: Call(_m(), None, rator, list(args)),
        children,
        st.lists(children, min_size=1, max_size=3),
    ),
    max_leaves=6,
)


# Lambda body generator: keeps the body in the post-uniquify shape so
# that ``Lambda.__eq__`` (which delegates to ``_alpha_equiv_lambda``)
# is well-defined.
def _lambda_with_binder(binder, body):
    return Lambda(_m(), None, [(binder, None)], body)


post_lambda_st = st.builds(
    _lambda_with_binder,
    st.sampled_from(POST_NAMES),
    post_term_st,
)


def _walk(node):
    if isinstance(node, AST):
        yield node
        for fld in node.__dataclass_fields__:
            if fld == 'typeof':
                continue
            yield from _walk_value(getattr(node, fld))


def _walk_value(v):
    if isinstance(v, AST):
        yield from _walk(v)
    elif isinstance(v, (list, tuple)):
        for x in v:
            yield from _walk_value(x)


@pytest.fixture(autouse=True)
def _reset_reduced_defs():
    reset_reduced_defs()
    yield


# ---------- Phase isolation --------------------------------------------


@given(st.sampled_from(POST_NAMES))
def test_var_never_equals_overloaded_var(name):
    # Pre- and post-uniquify references must compare unequal even when
    # they nominally refer to the same identifier.
    pre = Var(_m(), None, name)
    post = OverloadedVar(_m(), None, [name])
    assert pre != post
    assert post != pre


@given(st.sampled_from(POST_NAMES))
def test_var_never_equals_resolved_var(name):
    pre = Var(_m(), None, name)
    post = ResolvedVar(_m(), None, name)
    assert pre != post
    assert post != pre


@given(st.sampled_from(POST_NAMES))
def test_overloaded_and_resolved_var_cross_equal_on_chosen_name(name):
    # Documented symmetry between the two post-uniquify forms (see
    # [abstract_syntax.py:990](../../abstract_syntax.py) /
    # [abstract_syntax.py:1088](../../abstract_syntax.py)).
    ov = OverloadedVar(_m(), None, [name])
    rv = ResolvedVar(_m(), None, name)
    assert ov == rv
    assert rv == ov


@given(st.sampled_from(POST_NAMES), st.sampled_from(POST_NAMES))
def test_overloaded_var_equality_uses_chosen_name_only(name1, name2):
    # ``OverloadedVar.__eq__`` compares ``resolved_names[0]`` only.
    # Trailing candidates don't matter for equality.
    ov1 = OverloadedVar(_m(), None, [name1, "extra.S99"])
    ov2 = OverloadedVar(_m(), None, [name2])
    assert (ov1 == ov2) == (name1 == name2)


# ---------- substitute never downgrades the post-uniquify form ---------


@given(post_term_st)
def test_substitute_miss_preserves_post_uniquify_class(t):
    # The key is not in ``POST_NAMES``, so every reference inside ``t``
    # is a miss. Every variable reference in the result must stay
    # post-uniquify (``OverloadedVar`` / ``ResolvedVar``) — never
    # silently degraded to the pre-uniquify ``Var``.
    s = t.substitute({"__never__.S999": Int(_m(), None, 0)})
    for n in _walk(s):
        if type(n) is Var:
            pytest.fail(f"pre-uniquify Var appeared in substituted output: {n}")


@given(st.sampled_from(POST_NAMES))
def test_overloaded_var_miss_stays_overloaded_var(name):
    ov = OverloadedVar(_m(), None, [name])
    s = ov.substitute({"__never__.S999": Int(_m(), None, 0)})
    assert isinstance(s, OverloadedVar)
    assert s.resolved_names == [name]


@given(st.sampled_from(POST_NAMES))
def test_resolved_var_miss_stays_resolved_var(name):
    # The specific invariant called out in #492: a ``ResolvedVar``
    # under ``substitute`` must never reintroduce an ``OverloadedVar``.
    rv = ResolvedVar(_m(), None, name)
    s = rv.substitute({"__never__.S999": Int(_m(), None, 0)})
    assert isinstance(s, ResolvedVar)
    assert not isinstance(s, OverloadedVar)
    assert s.name == name


# ---------- substitute hit returns the replacement ---------------------


@given(st.sampled_from(POST_NAMES), int_st)
def test_overloaded_var_hit_returns_replacement(name, replacement):
    ov = OverloadedVar(_m(), None, [name])
    assert ov.substitute({name: replacement}) is replacement


@given(st.sampled_from(POST_NAMES), int_st)
def test_resolved_var_hit_returns_replacement(name, replacement):
    rv = ResolvedVar(_m(), None, name)
    assert rv.substitute({name: replacement}) is replacement


# ---------- copy independence ------------------------------------------


@given(st.sampled_from(POST_NAMES))
def test_overloaded_var_copy_has_independent_name_list(name):
    # ``OverloadedVar.copy`` wraps ``resolved_names`` in ``list(...)``
    # so later mutation on one side cannot leak into the other.
    ov = OverloadedVar(_m(), None, [name, "alt.S77"])
    c = ov.copy()
    assert c.resolved_names == ov.resolved_names
    ov.resolved_names.append("mutated.S88")
    assert "mutated.S88" not in c.resolved_names


# ---------- Lambda body under substitute (post-uniquify shape) ----------


@given(st.sampled_from(POST_NAMES), st.sampled_from(POST_NAMES))
def test_lambda_alpha_renaming_post_uniquify(x, y):
    # The post-uniquify analogue of the alpha-renaming sanity check in
    # [test_alpha_equiv.py](test_alpha_equiv.py). ``Lambda(x, OV(x)) ==
    # Lambda(y, OV(y))`` under alpha-renaming, regardless of the
    # mangled suffix.
    l1 = Lambda(_m(), None, [(x, None)], OverloadedVar(_m(), None, [x]))
    l2 = Lambda(_m(), None, [(y, None)], OverloadedVar(_m(), None, [y]))
    assert l1 == l2


@given(st.sampled_from(POST_NAMES), st.sampled_from(POST_NAMES))
def test_lambda_self_reference_resolved_var(x, y):
    l1 = Lambda(_m(), None, [(x, None)], ResolvedVar(_m(), None, x))
    l2 = Lambda(_m(), None, [(y, None)], ResolvedVar(_m(), None, y))
    assert l1 == l2


@given(st.sampled_from(POST_NAMES))
def test_lambda_substitute_miss_leaves_body_unchanged(x):
    # Substituting with a key that doesn't appear anywhere in a
    # ``Lambda`` (neither binder nor body) is structurally a no-op:
    # the resulting Lambda has the same binder and a body equal to
    # the original.
    lam = Lambda(_m(), None, [(x, None)], Int(_m(), None, 42))
    other = "other.S999"
    assert other not in POST_NAMES
    s = lam.substitute({other: Int(_m(), None, 0)})
    assert isinstance(s, Lambda)
    assert s.body == Int(_m(), None, 42)
    assert s.vars[0][0] == x


@given(st.sampled_from(POST_NAMES))
def test_lambda_substitute_rewrites_free_body_reference(x):
    # ``Lambda(x.S0, OV(other.S999))`` with ``{other.S999: Int(7)}``
    # must rewrite the body to ``Int(7)`` (the reference is free
    # w.r.t. the binder). This exercises ``substitute`` recursing
    # into a Lambda body in the post-uniquify shape — the case #490
    # made well-defined.
    other = "other.S999"
    assert other != x and other not in POST_NAMES
    body = OverloadedVar(_m(), None, [other])
    lam = Lambda(_m(), None, [(x, None)], body)
    repl = Int(_m(), None, 7)
    s = lam.substitute({other: repl})
    assert isinstance(s, Lambda)
    assert s.body == repl
    # Binder unchanged.
    assert s.vars[0][0] == x


@settings(suppress_health_check=[HealthCheck.too_slow])
@given(post_lambda_st)
def test_lambda_copy_equals_under_alpha_equiv(lam):
    c = lam.copy()
    assert lam == c
    assert alpha_equiv(lam, c)
    # And a fresh top-level rename of the binder also stays
    # alpha-equivalent. Build a copy with a different binder name
    # and the body rewritten via substitute, then verify alpha-equiv.
    old = lam.vars[0][0]
    new = "fresh.S101"
    assert new != old
    renamed_body = lam.body.substitute({old: OverloadedVar(_m(), None, [new])})
    renamed = Lambda(_m(), None, [(new, None)], renamed_body)
    assert lam == renamed


# ---------- composition: post-uniquify substitute interacts cleanly -----


@given(post_term_st)
def test_substitute_empty_is_identity_post_uniquify(t):
    assert t.substitute({}) == t


@given(post_term_st, st.sampled_from(POST_NAMES))
def test_post_uniquify_term_self_var_substitute_is_identity(t, name):
    # ``{name: OV([name])}`` is an identity-of-the-post-uniquify-form
    # substitution — every miss reuses self (via the
    # ``new_typeof is self.typeof`` short-circuit), every hit returns
    # the equal OverloadedVar. The whole term should be equal to the
    # input under post-uniquify equality.
    self_ref = OverloadedVar(_m(), None, [name])
    assert t.substitute({name: self_ref}) == t
