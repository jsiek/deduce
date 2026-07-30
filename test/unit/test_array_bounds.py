"""Unit tests for mutable-array read typing and array-bounds obligations
(issue #1117, Phase 2h).

Two halves, both exercised without the CLI or the stdlib:

  * ``type_synth_term`` on an ``ArrayGet`` distinguishes the pure ``[T]`` path
    (unchanged) from the mutable ``[T]!`` path (element type + index check);
  * ``imperative_verifier`` builds and deduplicates the ``i < length(a)``
    bounds obligation for a mutable-array read.
"""

from lark.tree import Meta

from abstract_syntax import (
    ArrayGet, ArrayLength, ArrayType, BoolType, Call, Env, MutableArrayType,
    ResolvedVar,
)
from checker_types import type_synth_term
from error import IncompleteProof, UserError
from imperative_verifier import (
    ArrayBoundsObligations, ImperativeObligation, ObligationKind,
    array_bounds_goal,
)


def _meta(start: int = 0, end: int = 1) -> Meta:
  m = Meta()
  m.empty = False
  m.filename = 'test.pf'
  m.line = 3
  m.column = 5
  m.start_pos = start
  m.end_line = 3
  m.end_column = 6
  m.end_pos = end
  return m


def _env() -> Env:
  return Env({'__current_module__': 'test'})


def _rv(name: str) -> ResolvedVar:
  return ResolvedVar(_meta(), None, name)


def _uint_type() -> ResolvedVar:
  # A stand-in for the `UInt` type: `_check_array_index_type` only inspects the
  # type's base name, so a bare `UInt` reference is enough here -- no stdlib.
  return ResolvedVar(_meta(), None, 'UInt')


def _typing_env() -> Env:
  # A bare env with array/scalar term vars -- no stdlib needed because the
  # ArrayGet path only reads the subject's `typeof` and (for the mutable path)
  # the index's `typeof`.
  env = _env()
  env = env.declare_term_var(_meta(), 'marr',
                             MutableArrayType(_meta(), BoolType(_meta())))
  env = env.declare_term_var(_meta(), 'parr',
                             ArrayType(_meta(), BoolType(_meta())))
  env = env.declare_term_var(_meta(), 'idx', _uint_type())
  env = env.declare_term_var(_meta(), 'flag', BoolType(_meta()))
  return env


def _read(subject: str = 'marr', index: str = 'idx',
          start: int = 0, end: int = 5) -> ArrayGet:
  return ArrayGet(_meta(start, end), None, _rv(subject), _rv(index))


# --- ArrayType vs MutableArrayType typing -----------------------------------

def test_mutable_read_has_element_type() -> None:
  ret = type_synth_term(_read('marr', 'idx'), _typing_env(), None, [])
  assert isinstance(ret, ArrayGet)
  assert ret.typeof == BoolType(_meta())


def test_pure_read_is_unchanged_and_skips_index_check() -> None:
  # The pure `[T]` path never checked the index type; a `bool` index that the
  # mutable path rejects must still be accepted here so pure-array behavior is
  # unchanged.
  ret = type_synth_term(_read('parr', 'flag'), _typing_env(), None, [])
  assert isinstance(ret, ArrayGet)
  assert ret.typeof == BoolType(_meta())


def test_mutable_read_rejects_non_integer_index() -> None:
  try:
    type_synth_term(_read('marr', 'flag'), _typing_env(), None, [])
    assert False, 'expected a UserError for a bool index'
  except UserError as e:
    assert 'index must be' in str(e)


def test_read_of_non_array_is_rejected() -> None:
  try:
    type_synth_term(_read('flag', 'idx'), _typing_env(), None, [])
    assert False, 'expected a UserError for a non-array subject'
  except UserError as e:
    assert 'expected an array' in str(e)


# --- bounds-obligation construction -----------------------------------------

def test_bounds_goal_is_index_less_than_length() -> None:
  goal = array_bounds_goal(_read('marr', 'idx'))
  assert isinstance(goal, Call)
  assert isinstance(goal.rator, ResolvedVar) and goal.rator.get_name() == '<'
  index, length = goal.args
  assert index == _rv('idx')
  assert isinstance(length, ArrayLength) and length.subject == _rv('marr')


def test_recording_a_read_yields_one_array_bounds_obligation() -> None:
  collector = ArrayBoundsObligations()
  collector.record(_read())
  obligations = collector.obligations()
  assert len(obligations) == 1
  ob = obligations[0]
  assert isinstance(ob, ImperativeObligation)
  assert ob.kind is ObligationKind.ARRAY_BOUNDS
  # Source-located at the read.
  assert ob.location.start_pos == 0 and ob.location.end_pos == 5


def test_duplicate_source_access_is_recorded_once() -> None:
  collector = ArrayBoundsObligations()
  collector.record(_read(start=0, end=5))
  collector.record(_read(start=0, end=5))   # same source access
  collector.record(_read(start=6, end=11))  # a distinct access
  assert len(collector.obligations()) == 2


# --- discharge --------------------------------------------------------------

def test_in_bounds_read_verifies_when_precondition_supplies_the_bound() -> None:
  collector = ArrayBoundsObligations()
  collector.record(_read(),
                   givens=[('pre', array_bounds_goal(_read()))])
  collector.obligations()[0].discharge(_env())  # returns normally


def test_missing_bounds_evidence_reports_array_bounds_diagnostic() -> None:
  collector = ArrayBoundsObligations()
  collector.record(_read())
  try:
    collector.obligations()[0].discharge(_env())
    assert False, 'expected an IncompleteProof'
  except IncompleteProof as e:
    assert 'array bounds' in str(e)
    assert 'test.pf:3.5' in str(e)
