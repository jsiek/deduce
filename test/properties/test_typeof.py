"""Property-based tests for the ``typeof`` annotation on Term subclasses.

The ``typeof`` field on ``Term`` is a cached type annotation populated
by the type checker. It is non-structural for equality and copy, but
``substitute`` *does* rewrite it via the ``on_typeof`` hook in
``Term.substitute`` / ``Term._map_children`` (see
[abstract_syntax.py:74](../../abstract_syntax.py) and
[abstract_syntax.py:315](../../abstract_syntax.py)).

#480 fixed a class of bugs where ``typeof`` was a post-hoc-assigned
attribute that disappeared after ``_map_children`` rebuilt the node;
#484 fixed inconsistencies where the substituted ``typeof`` would
silently drop. These tests cover the surviving invariant: after
``copy`` / ``substitute``, the ``typeof`` annotation on every node
that had one is the same type (or its substitution image).
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
    BoolType,
    Call,
    FunctionType,
    Int,
    IntType,
    Term,
    Var,
    reset_reduced_defs,
)


NAMES = ["x", "y", "z"]


def _m() -> Meta:
    return Meta()


# ---------- Type pool ----------------------------------------------------

# Closed types only (no type parameters, no free type variables). This
# keeps ``Type.substitute(sub)`` insensitive to the term-level
# substitutions we apply below, so the property reduces to "typeof is
# preserved" rather than "typeof is rewritten by the same substitution".
int_type_st = st.builds(lambda: IntType(_m()))
bool_type_st = st.builds(lambda: BoolType(_m()))
ground_type_st = st.one_of(int_type_st, bool_type_st)

type_st = st.recursive(
    ground_type_st,
    lambda children: st.builds(
        lambda params, ret: FunctionType(_m(), [], list(params), ret),
        st.lists(children, min_size=1, max_size=2),
        children,
    ),
    max_leaves=4,
)

# Each generated term gets either no typeof (the pre-typecheck shape)
# or one drawn from the pool.
optional_type_st = st.one_of(st.none(), type_st)


# ---------- Annotated term pool -----------------------------------------

annotated_var_st = st.builds(
    lambda v, ty: Var(_m(), ty, v),
    st.sampled_from(NAMES),
    optional_type_st,
)
annotated_int_st = st.builds(
    lambda n, ty: Int(_m(), ty, n),
    st.integers(-5, 5),
    optional_type_st,
)
annotated_bool_st = st.builds(
    lambda b, ty: Bool(_m(), ty, b),
    st.booleans(),
    optional_type_st,
)
annotated_leaf_st = st.one_of(annotated_var_st, annotated_int_st, annotated_bool_st)

annotated_term_st = st.recursive(
    annotated_leaf_st,
    lambda children: st.builds(
        lambda rator, args, ty: Call(_m(), ty, rator, list(args)),
        children,
        st.lists(children, min_size=1, max_size=3),
        optional_type_st,
    ),
    max_leaves=6,
)


def _walk(node):
    # Structural pre-order walk that skips the ``typeof`` field.
    # ``typeof`` is non-structural and its rewrites under substitute
    # are what we are testing on the node itself — recursing into it
    # here would also misalign the parallel walk in the Var-hit case,
    # since the replacement typically has a different (or absent)
    # typeof.
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


# ---------- copy preserves typeof ---------------------------------------


@given(annotated_term_st)
def test_copy_preserves_typeof(t):
    c = t.copy()
    for orig, copied in zip(_walk(t), _walk(c)):
        if isinstance(orig, Term):
            assert isinstance(copied, Term)
            assert copied.typeof == orig.typeof


# ---------- substitute preserves typeof (no key in term) ----------------


@given(annotated_term_st)
def test_substitute_empty_preserves_typeof(t):
    s = t.substitute({})
    for orig, after in zip(_walk(t), _walk(s)):
        if isinstance(orig, Term):
            assert isinstance(after, Term)
            assert after.typeof == orig.typeof


# ---------- substitute propagates typeof through Term.substitute ---------


@given(annotated_term_st, annotated_term_st)
def test_substitute_absent_key_preserves_typeof(t, replacement):
    # The substitution name never appears in the generated term, so
    # every node is rebuilt via ``_map_children`` (or, for VarRef, via
    # ``subst_typeof``). The cached ``typeof`` must survive.
    s = t.substitute({"__absent__": replacement})
    for orig, after in zip(_walk(t), _walk(s)):
        if isinstance(orig, Term):
            assert isinstance(after, Term)
            assert after.typeof == orig.typeof


@given(annotated_term_st, st.sampled_from(NAMES))
def test_substitute_self_var_preserves_typeof(t, name):
    # ``{name: Var(name, None)}`` is the identity substitution as far as
    # variable references are concerned. For non-VarRef nodes (whose
    # typeof goes through ``on_typeof``) the cached annotation must
    # survive. For ``Var(name)`` nodes that match the key, the result
    # is the replacement Var — so we skip that case in the comparison.
    self_var = Var(_m(), None, name)
    s = t.substitute({name: self_var})
    for orig, after in zip(_walk(t), _walk(s)):
        if not isinstance(orig, Term):
            continue
        if isinstance(orig, Var) and orig.name == name:
            # Substituted to ``self_var`` (typeof=None) — typeof is the
            # replacement's, not the original's.
            continue
        assert isinstance(after, Term)
        assert after.typeof == orig.typeof


# ---------- Var.substitute: hit case loses original typeof --------------


@given(type_st, type_st, st.sampled_from(NAMES))
def test_var_hit_takes_replacements_typeof(t1, t2, name):
    # A ``Var`` with ``typeof=t1`` that is hit by a substitution
    # returns the replacement (with the replacement's own typeof),
    # *not* the original ``Var`` with its annotation. This pins down
    # the documented behaviour in [abstract_syntax.py:916](../../abstract_syntax.py).
    original = Var(_m(), t1, name)
    replacement = Int(_m(), t2, 7)
    s = original.substitute({name: replacement})
    assert s.typeof == t2


# ---------- Var.substitute: miss case routes through subst_typeof -------


@given(type_st, st.sampled_from(NAMES))
def test_var_miss_keeps_own_typeof(t, name):
    # ``Var(name=foo, typeof=t)`` substituted with a key for ``bar``
    # rebuilds (or short-circuits to) a Var with the same typeof.
    other = "bar"
    assert other not in NAMES
    v = Var(_m(), t, name)
    s = v.substitute({other: Int(_m(), None, 0)})
    assert isinstance(s, Var)
    assert s.name == name
    assert s.typeof == t


# ---------- Type-side: substitute on closed types is identity-equal -----


@given(type_st)
def test_type_substitute_closed_is_identity_equal(ty):
    # The pool only generates closed types. Applying a term-level
    # substitution to one must leave it equal to itself. This is the
    # supporting invariant that makes the term-level properties above
    # behave as "typeof is preserved" rather than "rewritten".
    assert ty.substitute({"x": Int(_m(), None, 0)}) == ty


# ---------- typeof field survives _map_children -------------------------


@settings(suppress_health_check=[HealthCheck.too_slow])
@given(annotated_term_st)
def test_typeof_field_survives_map_children(t):
    # Hits the same code path as #480/#484: rebuild the term through
    # ``_map_children`` (here via ``copy``) and confirm every node's
    # ``typeof`` is still a Type (or None), not silently dropped.
    c = t.copy()
    for n in _walk(c):
        if isinstance(n, Term):
            assert n.typeof is None or isinstance(n.typeof, AST)
