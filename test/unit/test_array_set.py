"""Unit tests for the `ArraySet` read-over-write model (issue #1118, Phase 2i).

`ArraySet(a, i, v)` is the verifier-only functional update representing the
mutable array `a` with index `i` set to `v`. Its semantics live in
`ArrayGet.reduce` (read-over-write) and `ArrayLength.reduce` (a write preserves
length). These pin those reductions directly, without the checker or stdlib.
"""

from lark.tree import Meta

from abstract_syntax import (
    ArrayGet, ArrayLength, ArraySet, Call, Env, ResolvedVar,
)


def _meta() -> Meta:
  m = Meta()
  m.empty = False
  m.filename = 'test.pf'
  m.line = 1
  m.column = 1
  m.start_pos = 0
  m.end_line = 1
  m.end_column = 2
  m.end_pos = 1
  return m


def _env() -> Env:
  return Env({'__current_module__': 'test'})


def _rv(name: str) -> ResolvedVar:
  return ResolvedVar(_meta(), None, name)


def _nat(n: int):
  # A post-uniquify `Nat` literal `suc(...suc(zero))`. `isNat` (and so the
  # concrete-index read-over-write) recognizes only the resolved `zero`/`suc`
  # constructors, not the pre-uniquify `Var` form `intToNat` builds.
  t = _rv('zero')
  for _ in range(n):
    t = Call(_meta(), None, _rv('suc'), [t])
  return t


def _set(subject, pos, val) -> ArraySet:
  return ArraySet(_meta(), None, subject, pos, val)


def _get(subject, pos) -> ArrayGet:
  return ArrayGet(_meta(), None, subject, pos)


def test_read_after_write_same_symbolic_index_is_the_written_value() -> None:
  # a[i] := v  then  a[i]  ==  v, even when `i` is symbolic.
  read = _get(_set(_rv('a'), _rv('i'), _rv('v')), _rv('i'))
  assert read.reduce(_env()) == _rv('v')


def test_read_after_write_distinct_concrete_index_keeps_prior_value() -> None:
  # a[0] := v  then  a[1]  reads through the write to the prior array `a[1]`.
  read = _get(_set(_rv('a'), _nat(0), _rv('v')),
              _nat(1))
  reduced = read.reduce(_env())
  assert isinstance(reduced, ArrayGet)
  assert reduced.subject == _rv('a')
  assert reduced.position == _nat(1)


def test_read_after_write_distinct_symbolic_index_stays_symbolic() -> None:
  # a[i] := v  then  a[j]  cannot be simplified without knowing i vs j, so it
  # stays an unresolved read over the update (sound: no false read-through).
  update = _set(_rv('a'), _rv('i'), _rv('v'))
  read = _get(update, _rv('j'))
  reduced = read.reduce(_env())
  assert isinstance(reduced, ArrayGet)
  assert isinstance(reduced.subject, ArraySet)


def test_repeated_writes_compose_last_write_wins() -> None:
  # a[i] := v ; a[i] := w  then  a[i]  ==  w.
  inner = _set(_rv('a'), _rv('i'), _rv('v'))
  outer = _set(inner, _rv('i'), _rv('w'))
  assert _get(outer, _rv('i')).reduce(_env()) == _rv('w')


def test_repeated_writes_earlier_index_survives_a_later_distinct_write() -> None:
  # a[0] := v ; a[1] := w  then  a[0]  ==  v (the later write is at a distinct
  # concrete index, so it is transparent to the read at index 0).
  inner = _set(_rv('a'), _nat(0), _rv('v'))
  outer = _set(inner, _nat(1), _rv('w'))
  assert _get(outer, _nat(0)).reduce(_env()) == _rv('v')


def test_length_is_preserved_across_a_write() -> None:
  # length(a[i := v]) reduces to length(a): a write does not change length.
  update = _set(_rv('a'), _rv('i'), _rv('v'))
  reduced = ArrayLength(_meta(), None, update).reduce(_env())
  assert reduced == ArrayLength(_meta(), None, _rv('a'))


def test_length_is_preserved_across_repeated_writes() -> None:
  inner = _set(_rv('a'), _rv('i'), _rv('v'))
  outer = _set(inner, _rv('j'), _rv('w'))
  reduced = ArrayLength(_meta(), None, outer).reduce(_env())
  assert reduced == ArrayLength(_meta(), None, _rv('a'))
