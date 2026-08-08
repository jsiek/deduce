"""Unit tests for mutable-array read typing and array-bounds obligations
(issue #1117, Phase 2h; issue #1166).

Two halves, both exercised without the CLI or the stdlib:

  * ``type_synth_term`` on an ``ArrayGet`` distinguishes the pure ``[T]`` path
    (unchanged) from the mutable ``[T]!`` path (element type + index check);
  * ``imperative_verifier`` builds, deduplicates, and discharges the
    ``i < length(a)`` bounds obligation for a mutable-array read. The goal's
    ``<``/``length`` operators are *resolved* against the scope (not bare
    names), so the obligation discharges from a ``requires i < length(a)``
    premise that carries the same resolved operators (issue #1166).
"""

from lark.tree import Meta

from abstract_syntax import (
    ArrayGet, ArrayLength, ArrayType, BoolType, Call, Env, FunctionType,
    MutableArrayType, OverloadedVar, ResolvedVar, base_name,
)
from checker_types import type_check_formula, type_synth_term
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
  # type's base name, and the `<`/`length` signatures below only compare it by
  # equality, so a bare `UInt` reference is enough here -- no stdlib.
  return ResolvedVar(_meta(), None, 'UInt')


def _typing_env() -> Env:
  # A bare env with array/scalar term vars plus resolved `<` and `length`
  # operators. No stdlib is needed: the ArrayGet path only reads the subject's
  # `typeof` and (for the mutable path) the index's `typeof`, and the
  # bounds-goal path only needs a `<` (UInt, UInt) -> bool and a `length`
  # returning the index type in scope. The operators carry uniquified-style
  # names (`<.op`, `length.op`) so a bare-name `<` is visibly distinct from
  # the resolved one a real premise would carry (issue #1166).
  env = _env()
  env = env.declare_term_var(_meta(), 'marr',
                             MutableArrayType(_meta(), BoolType(_meta())))
  env = env.declare_term_var(_meta(), 'parr',
                             ArrayType(_meta(), BoolType(_meta())))
  env = env.declare_term_var(_meta(), 'idx', _uint_type())
  env = env.declare_term_var(_meta(), 'flag', BoolType(_meta()))
  env = env.declare_term_var(
      _meta(), '<.op',
      FunctionType(_meta(), [], [_uint_type(), _uint_type()],
                   BoolType(_meta())))
  env = env.declare_term_var(
      _meta(), 'length.op',
      FunctionType(_meta(), [], [_uint_type()], _uint_type()))
  return env


def _read(subject: str = 'marr', index: str = 'idx',
          start: int = 0, end: int = 5) -> ArrayGet:
  return ArrayGet(_meta(start, end), None, _rv(subject), _rv(index))


def _typed_read(subject: str = 'marr', index: str = 'idx',
                start: int = 0, end: int = 5,
                env: Env | None = None) -> ArrayGet:
  # An `ArrayGet` whose subject/position carry resolved types, the shape the
  # verifier hands to `array_bounds_goal`.
  ret = type_synth_term(_read(subject, index, start, end),
                        env or _typing_env(), None, [])
  assert isinstance(ret, ArrayGet)
  return ret


def _user_premise(env: Env) -> object:
  # How a `requires idx < length(marr)` clause type-checks: a surface `<` call
  # over `length(marr)`, resolved against `env`. `array_bounds_goal` must build
  # an identical formula for the obligation to discharge from this premise.
  call = Call(_meta(), None, OverloadedVar(_meta(), None, ['<.op']),
              [_rv('idx'),
               Call(_meta(), None, OverloadedVar(_meta(), None, ['length.op']),
                    [_rv('marr')])])
  return type_check_formula(call, env)


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
  env = _typing_env()
  goal = array_bounds_goal(_typed_read(env=env), env)
  assert isinstance(goal, Call)
  assert isinstance(goal.rator, ResolvedVar) and goal.rator.get_name() == '<.op'
  index, length = goal.args
  assert index == _rv('idx')
  assert isinstance(length, ArrayLength) and length.subject == _rv('marr')


def test_bounds_goal_resolves_the_less_than_operator() -> None:
  # The regression for #1166: the goal's `<` must be the *resolved* operator a
  # user premise carries, not a bare-name `ResolvedVar('<')`.
  env = _typing_env()
  goal = array_bounds_goal(_typed_read(env=env), env)
  assert isinstance(goal, Call)
  assert base_name(goal.rator.get_name()) == '<'
  assert goal.rator.get_name() != '<'
  # It matches exactly the formula a type-checked `requires idx < length(marr)`
  # premise produces.
  assert goal == _user_premise(env)


def test_bounds_goal_needs_operators_in_scope() -> None:
  try:
    array_bounds_goal(_typed_read(env=_typing_env()), _env())
    assert False, 'expected a UserError when `<`/`length` are out of scope'
  except UserError as e:
    assert '`length` and `<`' in str(e)


def test_recording_a_read_yields_one_array_bounds_obligation() -> None:
  env = _typing_env()
  collector = ArrayBoundsObligations()
  collector.record(_typed_read(env=env), env)
  obligations = collector.obligations()
  assert len(obligations) == 1
  ob = obligations[0]
  assert isinstance(ob, ImperativeObligation)
  assert ob.kind is ObligationKind.ARRAY_BOUNDS
  # Source-located at the read.
  assert ob.location.start_pos == 0 and ob.location.end_pos == 5


def test_duplicate_source_access_is_recorded_once() -> None:
  env = _typing_env()
  collector = ArrayBoundsObligations()
  collector.record(_typed_read(start=0, end=5, env=env), env)
  collector.record(_typed_read(start=0, end=5, env=env), env)   # same access
  collector.record(_typed_read(start=6, end=11, env=env), env)  # distinct
  assert len(collector.obligations()) == 2


# --- discharge --------------------------------------------------------------

def test_in_bounds_read_verifies_when_precondition_supplies_the_bound() -> None:
  # The resolved goal discharges from a `requires idx < length(marr)` premise
  # that carries the *same* resolved operators -- the case #1166 was about.
  env = _typing_env()
  collector = ArrayBoundsObligations()
  collector.record(_typed_read(env=env), env,
                   givens=[('pre', _user_premise(env))])
  collector.obligations()[0].discharge(env)  # returns normally


def test_bare_name_less_than_does_not_discharge_from_a_resolved_premise() -> None:
  # Pins the bug: a goal built with a bare-name `<` (the pre-#1166 shape) does
  # NOT discharge from a premise carrying the resolved `<`, even though both
  # read `idx < length(marr)` on the surface.
  env = _typing_env()
  bare_goal = Call(_meta(), None, ResolvedVar(_meta(), None, '<'),
                   [_rv('idx'),
                    ArrayLength(_meta(), None, _rv('marr'))])
  ob = ImperativeObligation(_meta(), bare_goal, ObligationKind.ARRAY_BOUNDS,
                            givens=[('pre', _user_premise(env))])
  try:
    ob.discharge(env)
    assert False, 'expected an IncompleteProof for a bare-name `<` goal'
  except IncompleteProof:
    pass


def test_missing_bounds_evidence_reports_array_bounds_diagnostic() -> None:
  env = _typing_env()
  collector = ArrayBoundsObligations()
  collector.record(_typed_read(env=env), env)
  try:
    collector.obligations()[0].discharge(env)
    assert False, 'expected an IncompleteProof'
  except IncompleteProof as e:
    assert 'array bounds' in str(e)
    assert 'test.pf:3.5' in str(e)
