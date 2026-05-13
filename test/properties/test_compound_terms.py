"""Property-based tests for compound formulas, transparent wrappers,
and Recursive-function cross-class equality.

The substitute-side properties in
[`test_substitute_uniquify.py`](test_substitute_uniquify.py) only
cover ``Var`` / ``Int`` / ``Bool`` / ``Call``. The alpha-equiv tests
in [`test_alpha_equiv.py`](test_alpha_equiv.py) cover ``Some`` /
``All`` / ``Lambda`` / ``TLet`` but never substitute through them.
This file fills both gaps:

* Substitute-side identity properties on terms that include the
  remaining formula constructors (``And`` / ``Or`` / ``IfThen`` /
  ``All`` / ``Some``).
* ``TermInst`` and ``TAnnote`` wrap a subject term and unwrap on
  comparison — both directions of ``alpha_equiv`` should pierce
  through them.
* ``RecFun`` / ``GenRecFun`` compare by name across the post-uniquify
  variable forms; ``substitute`` on either is identity. The cross-class
  branches in [abstract_syntax.py:3435](../../abstract_syntax.py) and
  [abstract_syntax.py:3547](../../abstract_syntax.py) have no property
  coverage today.
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
    All,
    And,
    Bool,
    Call,
    GenRecFun,
    IfThen,
    Int,
    IntType,
    Or,
    OverloadedVar,
    PVar,
    RecFun,
    ResolvedVar,
    Some,
    TAnnote,
    TermInst,
    Var,
    alpha_equiv,
    reset_reduced_defs,
)


NAMES = ["x", "y", "z"]
ABSENT_KEY = "__never_in_compound_terms__"


def _m() -> Meta:
    return Meta()


# ---------- Leaf and compound generators --------------------------------

var_st = st.builds(lambda v: Var(_m(), None, v), st.sampled_from(NAMES))
int_st = st.builds(lambda n: Int(_m(), None, n), st.integers(-5, 5))
bool_st = st.builds(lambda b: Bool(_m(), None, b), st.booleans())
leaf_st = st.one_of(var_st, int_st, bool_st)


# Closed binder name pool — kept disjoint from ``NAMES`` so substitute
# keys can't accidentally hit a binder and produce capture-shaped
# weirdness. ``All`` / ``Some`` use these as their bound variable
# names.
BINDER_NAMES = ["b1", "b2", "b3"]


# Recursive compound generator covering the formula constructors that
# weren't exercised by ``lambda_free_term_st`` plus ``Call`` so we
# still build interesting nested terms. Bound names in ``All`` /
# ``Some`` are drawn from a disjoint pool to keep substitute behaviour
# predictable; the body strategy is the recursive ``children``, which
# may reference the binder by name — that's fine, we never substitute
# binder names below.
compound_term_st = st.recursive(
    leaf_st,
    lambda children: st.one_of(
        st.builds(
            lambda args: And(_m(), None, list(args)),
            st.lists(children, min_size=2, max_size=3),
        ),
        st.builds(
            lambda args: Or(_m(), None, list(args)),
            st.lists(children, min_size=2, max_size=3),
        ),
        st.builds(
            lambda p, c: IfThen(_m(), None, p, c),
            children,
            children,
        ),
        st.builds(
            lambda v, body: All(_m(), None, (v, IntType(_m())), (0, 1), body),
            st.sampled_from(BINDER_NAMES),
            children,
        ),
        st.builds(
            lambda v, body: Some(_m(), None, [(v, IntType(_m()))], body),
            st.sampled_from(BINDER_NAMES),
            children,
        ),
        st.builds(
            lambda rator, args: Call(_m(), None, rator, list(args)),
            children,
            st.lists(children, min_size=1, max_size=2),
        ),
    ),
    max_leaves=6,
)


# A wrapped-term generator nests zero-or-more ``TermInst`` / ``TAnnote``
# wrappers around a compound term. Both wrappers are documented as
# transparent for equality and alpha-equivalence.
def _wrap_term_inst(t):
    return TermInst(_m(), None, t, [IntType(_m())])


def _wrap_tannote(t):
    return TAnnote(_m(), None, t, IntType(_m()))


wrapped_term_st = st.recursive(
    compound_term_st,
    lambda children: st.one_of(
        st.builds(_wrap_term_inst, children),
        st.builds(_wrap_tannote, children),
    ),
    max_leaves=3,
)


@pytest.fixture(autouse=True)
def _reset_reduced_defs():
    reset_reduced_defs()
    yield


# ---------- substitute identity properties on compound formulas --------


@settings(suppress_health_check=[HealthCheck.too_slow])
@given(compound_term_st)
def test_substitute_empty_is_identity_compound(t):
    assert t.substitute({}) == t


@settings(suppress_health_check=[HealthCheck.too_slow])
@given(compound_term_st, leaf_st)
def test_substitute_absent_key_is_identity_compound(t, replacement):
    assert t.substitute({ABSENT_KEY: replacement}) == t


@settings(suppress_health_check=[HealthCheck.too_slow])
@given(compound_term_st, st.sampled_from(NAMES))
def test_substitute_self_var_is_identity_compound(t, name):
    # ``{name: Var(name)}`` is the identity substitution for pre-uniquify
    # Vars. Every node — formula constructors included — survives equal.
    self_var = Var(_m(), None, name)
    assert t.substitute({name: self_var}) == t


# ---------- TermInst / TAnnote: transparent wrappers --------------------


@given(compound_term_st)
def test_term_inst_alpha_equiv_unwraps(t):
    wrapped = TermInst(_m(), None, t, [IntType(_m())])
    assert alpha_equiv(wrapped, t)
    assert alpha_equiv(t, wrapped)


@given(compound_term_st)
def test_tannote_alpha_equiv_unwraps(t):
    wrapped = TAnnote(_m(), None, t, IntType(_m()))
    assert alpha_equiv(wrapped, t)
    assert alpha_equiv(t, wrapped)


@given(compound_term_st)
def test_nested_wrapper_alpha_equiv_unwraps(t):
    # TermInst around TAnnote around the term — both layers must unwrap.
    wrapped = TermInst(
        _m(), None,
        TAnnote(_m(), None, t, IntType(_m())),
        [IntType(_m())],
    )
    assert alpha_equiv(wrapped, t)
    assert alpha_equiv(t, wrapped)


@given(compound_term_st)
def test_term_inst_eq_unwraps(t):
    # TermInst.__eq__ falls through to subject comparison for any other
    # class — including formulas. This is what lets pattern matches over
    # post-typecheck ASTs ignore the wrapper.
    wrapped = TermInst(_m(), None, t, [IntType(_m())])
    assert wrapped == t


@given(compound_term_st)
def test_tannote_eq_unwraps(t):
    wrapped = TAnnote(_m(), None, t, IntType(_m()))
    assert wrapped == t


@settings(suppress_health_check=[HealthCheck.too_slow])
@given(wrapped_term_st, wrapped_term_st)
def test_alpha_equiv_wrappers_compose_symmetrically(t1, t2):
    # If the wrapped terms are alpha-equivalent in one direction, they
    # are in the other. Exercises the unwrap loop in ``_alpha_equiv``.
    assert alpha_equiv(t1, t2) == alpha_equiv(t2, t1)


# ---------- RecFun / GenRecFun cross-class equality --------------------

# Names follow the post-uniquify mangling so the cross-class equality
# corresponds to the shape that actually appears post-typecheck.
RECFUN_NAMES = ["foo.S0", "bar.S1", "baz.S2"]


def _make_recfun(name):
    return RecFun(_m(), name, [], [], IntType(_m()), [], visibility='public')


def _make_genrecfun(name):
    return GenRecFun(
        _m(), name, [], [], IntType(_m()),
        Int(_m(), None, 0), IntType(_m()),
        Int(_m(), None, 0), PVar(_m(), 'pv.S0'),
        visibility='public',
    )


@given(st.sampled_from(RECFUN_NAMES))
def test_recfun_equals_resolved_var_by_name(name):
    rf = _make_recfun(name)
    rv = ResolvedVar(_m(), None, name)
    assert rf == rv
    assert rv == rf


@given(st.sampled_from(RECFUN_NAMES))
def test_recfun_equals_overloaded_var_by_name(name):
    rf = _make_recfun(name)
    ov = OverloadedVar(_m(), None, [name])
    assert rf == ov
    assert ov == rf


@given(st.sampled_from(RECFUN_NAMES))
def test_recfun_equals_var_by_name(name):
    # RecFun is name-equal even to a pre-uniquify Var (the phase-
    # isolation rule is between Var <-> OverloadedVar / ResolvedVar
    # only; RecFun is exempt). Documented at
    # [abstract_syntax.py:3440](../../abstract_syntax.py).
    rf = _make_recfun(name)
    v = Var(_m(), None, name)
    assert rf == v
    assert v == rf


@given(st.sampled_from(RECFUN_NAMES))
def test_recfun_equals_term_inst_subject(name):
    rf = _make_recfun(name)
    rv = ResolvedVar(_m(), None, name)
    wrapped = TermInst(_m(), None, rv, [IntType(_m())])
    assert rf == wrapped
    assert wrapped == rf


@given(st.sampled_from(RECFUN_NAMES), st.sampled_from(RECFUN_NAMES))
def test_recfun_recfun_equality_by_name(n1, n2):
    rf1 = _make_recfun(n1)
    rf2 = _make_recfun(n2)
    assert (rf1 == rf2) == (n1 == n2)


@given(st.sampled_from(RECFUN_NAMES))
def test_recfun_substitute_is_identity(name):
    # ``RecFun.substitute`` returns self unconditionally — recursive
    # definitions can't be alpha-renamed at use sites without breaking
    # the global recursion link.
    rf = _make_recfun(name)
    assert rf.substitute({name: Int(_m(), None, 999)}) is rf
    assert rf.substitute({}) is rf


@given(st.sampled_from(RECFUN_NAMES))
def test_genrecfun_equals_resolved_var_by_name(name):
    gf = _make_genrecfun(name)
    rv = ResolvedVar(_m(), None, name)
    assert gf == rv
    assert rv == gf


@given(st.sampled_from(RECFUN_NAMES))
def test_genrecfun_equals_overloaded_var_by_name(name):
    gf = _make_genrecfun(name)
    ov = OverloadedVar(_m(), None, [name])
    assert gf == ov
    assert ov == gf


@given(st.sampled_from(RECFUN_NAMES))
def test_genrecfun_equals_var_by_name(name):
    gf = _make_genrecfun(name)
    v = Var(_m(), None, name)
    assert gf == v
    assert v == gf


@given(st.sampled_from(RECFUN_NAMES), st.sampled_from(RECFUN_NAMES))
def test_genrecfun_genrecfun_equality_by_name(n1, n2):
    gf1 = _make_genrecfun(n1)
    gf2 = _make_genrecfun(n2)
    assert (gf1 == gf2) == (n1 == n2)


@given(st.sampled_from(RECFUN_NAMES))
def test_genrecfun_substitute_is_identity(name):
    gf = _make_genrecfun(name)
    assert gf.substitute({name: Int(_m(), None, 999)}) is gf
    assert gf.substitute({}) is gf


# ---------- RecFun under alpha_equiv (cross-phase, free reference) ------


@given(st.sampled_from(RECFUN_NAMES))
def test_recfun_alpha_equiv_with_resolved_var(name):
    # The post-uniquify analogue: a free RecFun reference is alpha-
    # equivalent to a ResolvedVar with the same name (and similarly
    # for OverloadedVar). This is the cross-class branch in
    # ``_alpha_equiv_varref``.
    rf = _make_recfun(name)
    rv = ResolvedVar(_m(), None, name)
    ov = OverloadedVar(_m(), None, [name])
    assert alpha_equiv(rf, rv)
    assert alpha_equiv(rv, rf)
    assert alpha_equiv(rf, ov)
    assert alpha_equiv(ov, rf)


@given(st.sampled_from(RECFUN_NAMES))
def test_genrecfun_alpha_equiv_with_resolved_var(name):
    gf = _make_genrecfun(name)
    rv = ResolvedVar(_m(), None, name)
    ov = OverloadedVar(_m(), None, [name])
    assert alpha_equiv(gf, rv)
    assert alpha_equiv(rv, gf)
    assert alpha_equiv(gf, ov)
    assert alpha_equiv(ov, gf)
