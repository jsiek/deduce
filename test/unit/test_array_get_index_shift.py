"""Unit tests for the ArrayGet index-shift rule (issue #469).

The rule peels one leading ``node(...)`` off a ``MakeArray`` subject
when the position term has a positive constructor shape, rebuilding
the access with the decremented index.

These tests target the cases that cannot be reached from a ``.pf``
source file outside the ``UInt`` module, because ``UInt`` is an
``opaque union`` and so its constructors (``bzero``, ``dub_inc``,
``inc_dub``) are not visible to user code.  In particular, the
``inc_dub(symbolic)`` decrement path -- whose predecessor is the
private library helper ``dub`` and so is reachable only via a name
lookup in ``env`` -- has no other coverage.
"""

from __future__ import annotations

from lark.tree import Meta

import abstract_syntax as ast


def _meta() -> Meta:
    return Meta()


def _int_ty() -> ast.IntType:
    return ast.IntType(_meta())


def _array_ty() -> ast.ArrayType:
    return ast.ArrayType(_meta(), _int_ty())


def _term_binding() -> ast.TermBinding:
    # The bindings themselves are only looked up by name
    # (`base_to_unique`); their `typ` / `defn` content is unused by
    # the index-shift rule, so a placeholder type is fine.
    return ast.TermBinding(_meta(), module='UInt', typ=_int_ty())


def _make_env_with_uint_helpers() -> ast.Env:
    """Build a minimal `Env` with uniquified UInt constructor and
    helper names registered.  The rule looks these up via
    `base_to_unique`; their bindings only need to be present.
    """
    env = ast.Env()
    for unique_name in ('bzero.0', 'dub_inc.0', 'inc_dub.0', 'dub.0'):
        env.dict[unique_name] = _term_binding()
    return env


def _node_ctor() -> ast.TermInst:
    return ast.TermInst(
        _meta(), None,
        ast.ResolvedVar(_meta(), None, 'node.0'),
        [_int_ty()], False,
    )


def _node(hd: ast.Term, tl: ast.Term) -> ast.Call:
    return ast.Call(_meta(), None, _node_ctor(), [hd, tl])


def _call_resolved(name: str, args: list[ast.Term]) -> ast.Call:
    return ast.Call(
        _meta(), None,
        ast.ResolvedVar(_meta(), None, name),
        args,
    )


def _build_array_get(position: ast.Term) -> ast.ArrayGet:
    x = ast.Var(_meta(), None, 'x')
    xs = ast.Var(_meta(), None, 'xs')
    make_array = ast.MakeArray(_meta(), _array_ty(), _node(x, xs))
    return ast.ArrayGet(_meta(), _int_ty(), make_array, position)


def _assert_peeled_to(reduced: ast.Term, expected_index_base: str,
                      expected_index_arg_name: str) -> None:
    """The reduced term should be ``array(xs)[<expected_index>]`` where
    ``<expected_index>`` is a Call to a function/constructor whose base
    name matches `expected_index_base`, applied to the single Var
    `expected_index_arg_name`.
    """
    assert isinstance(reduced, ast.ArrayGet), \
        f'expected ArrayGet, got {type(reduced).__name__}: {reduced}'
    assert isinstance(reduced.subject, ast.MakeArray), \
        f'expected MakeArray, got {type(reduced.subject).__name__}: {reduced.subject}'
    inner = reduced.subject.subject
    assert isinstance(inner, ast.Var) and inner.name == 'xs', \
        f'expected the tail Var `xs`, got {inner}'
    pos = reduced.position
    assert isinstance(pos, ast.Call), \
        f'expected the decremented position to be a Call, got {pos}'
    rator_name = pos.rator.name if hasattr(pos.rator, 'name') else None
    assert rator_name is not None and ast.base_name(rator_name) == expected_index_base, \
        f'expected position rator base name {expected_index_base!r}, got {rator_name!r}'
    assert len(pos.args) == 1
    arg = pos.args[0]
    assert isinstance(arg, ast.Var) and arg.name == expected_index_arg_name, \
        f'expected position arg Var({expected_index_arg_name!r}), got {arg}'


def test_inc_dub_symbolic_falls_back_to_dub_call():
    """`array(node(x, xs))[inc_dub(i')]` reduces to
    `array(xs)[dub(i')]` when `i'` is symbolic.  The rule's
    `_uint_double` helper has no structural shape to peel and so
    falls back to building a `Call` to the library `dub` helper
    that it finds in `env`.
    """
    env = _make_env_with_uint_helpers()
    iprime = ast.Var(_meta(), None, "iprime")
    inc_dub_iprime = _call_resolved('inc_dub.0', [iprime])
    reduced = _build_array_get(inc_dub_iprime).reduce(env)
    _assert_peeled_to(reduced,
                      expected_index_base='dub',
                      expected_index_arg_name='iprime')


def test_dub_inc_symbolic_peels_structurally():
    """`array(node(x, xs))[dub_inc(i')]` reduces structurally to
    `array(xs)[inc_dub(i')]` without needing the `dub` fallback.
    """
    env = _make_env_with_uint_helpers()
    iprime = ast.Var(_meta(), None, "iprime")
    dub_inc_iprime = _call_resolved('dub_inc.0', [iprime])
    reduced = _build_array_get(dub_inc_iprime).reduce(env)
    _assert_peeled_to(reduced,
                      expected_index_base='inc_dub',
                      expected_index_arg_name='iprime')


def test_inc_dub_symbolic_without_dub_in_env_does_not_reduce():
    """When the lib `dub` helper is not in env, the rule has nothing
    to fall back to and must leave the access unreduced -- the proof
    checker's existing equality and rewriting machinery has to take
    over from there.
    """
    env = _make_env_with_uint_helpers()
    del env.dict['dub.0']
    iprime = ast.Var(_meta(), None, "iprime")
    inc_dub_iprime = _call_resolved('inc_dub.0', [iprime])
    array_get = _build_array_get(inc_dub_iprime)
    reduced = array_get.reduce(env)
    # No peeling: the subject's list-spine is still `node(x, xs)` and
    # the position is still `inc_dub(iprime)`.
    assert isinstance(reduced, ast.ArrayGet)
    assert isinstance(reduced.subject, ast.MakeArray)
    inner = reduced.subject.subject
    assert isinstance(inner, ast.Call), \
        f'expected the list-spine to still be a node-Call, got {inner}'
    assert ast.base_name(inner.rator.subject.name) == 'node'
    pos = reduced.position
    assert isinstance(pos, ast.Call)
    assert ast.base_name(pos.rator.name) == 'inc_dub'
