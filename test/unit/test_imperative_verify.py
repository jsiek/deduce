"""Unit tests for straight-line procedure verification (issue #1115, Phase 2f).

`checker_pipeline.proc_obligations` performs forward symbolic execution over a
`_proc_verifiable` procedure and returns the verification conditions it
generates (without discharging them), so the weakest-precondition formulas can
be pinned here without the CLI or the stdlib. `verify_proc` then discharges
what it returns -- exercised at the end for one provable and one false goal.
"""

from lark.tree import Meta

from abstract_syntax import (
    BoolType, Env, ImpAssert, ImpAssign, ImpIf, ImpReturn, ImpVar, LValueVar,
    MutableArrayType, ResolvedVar,
)
from abstract_syntax.declarations import ProcDecl, ProcParam, ProcSpec
from abstract_syntax.literals import mkEqual
from checker_pipeline import _proc_verifiable, proc_obligations, verify_proc
from error import IncompleteProof
from imperative_verifier import ObligationKind


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


def _bool() -> BoolType:
  return BoolType(_meta())


def _param(name: str) -> ProcParam:
  return ProcParam(_meta(), name, _bool())


def _proc(name: str, params: list[ProcParam], return_type: object,
          specs: list[ProcSpec], body: list[object],
          result_name: object = None) -> ProcDecl:
  return ProcDecl(_meta(), name, [], params, return_type, specs, body, [],
                  result_name)


# --- weakest-precondition formulas ------------------------------------------

def test_identity_postcondition_is_reflexive() -> None:
  # proc identity(x: bool) -> bool  ensures result = x  { return x }
  decl = _proc('identity', [_param('x')], _bool(),
               [ProcSpec(_meta(), 'ensures', mkEqual(_meta(), _rv('result'),
                                                     _rv('x')))],
               [ImpReturn(_meta(), _rv('x'))], 'result')
  _env_out, obs = proc_obligations(decl, _env())
  assert len(obs) == 1
  assert obs[0].kind is ObligationKind.POSTCONDITION
  # `result` was substituted by the returned value `x`.
  assert str(obs[0].goal) == 'x = x'


def test_reassigned_local_reflects_the_last_write() -> None:
  # proc f(x, y) -> bool  ensures result = y  { var z := x  z := y  return z }
  decl = _proc('f', [_param('x'), _param('y')], _bool(),
               [ProcSpec(_meta(), 'ensures', mkEqual(_meta(), _rv('result'),
                                                     _rv('y')))],
               [ImpVar(_meta(), 'z', None, _rv('x')),
                ImpAssign(_meta(), LValueVar(_meta(), 'z'), _rv('y')),
                ImpReturn(_meta(), _rv('z'))], 'result')
  _env_out, obs = proc_obligations(decl, _env())
  # result = z = (last write) y, so the goal is `y = y`, not `x = y`.
  assert [str(o.goal) for o in obs] == ['y = y']


def test_multiple_requires_and_ensures_keep_their_locations() -> None:
  # Two `requires` become two entry givens; two `ensures` become two
  # obligations, each anchored at its own clause.
  post0 = _meta(100, 110)
  post1 = _meta(120, 130)
  decl = _proc('keep', [_param('x'), _param('y')], None,
               [ProcSpec(_meta(), 'requires', _rv('x')),
                ProcSpec(_meta(), 'requires', _rv('y')),
                ProcSpec(post0, 'ensures', _rv('x')),
                ProcSpec(post1, 'ensures', _rv('y'))],
               [])
  _env_out, obs = proc_obligations(decl, _env())
  assert [str(o.goal) for o in obs] == ['x', 'y']
  # Each obligation points at the ensures clause that produced it.
  assert obs[0].location.start_pos == 100
  assert obs[1].location.start_pos == 120
  # Both obligations carry both requires clauses as givens.
  assert [str(f) for (_l, f) in obs[0].givens] == ['x', 'y']
  assert [str(f) for (_l, f) in obs[1].givens] == ['x', 'y']


def test_assert_raises_a_goal_and_then_supplies_a_fact() -> None:
  # An `assert` becomes an ASSERTION obligation; its fact is then available as
  # a given to everything downstream (here the final postcondition).
  aloc = _meta(100, 110)
  decl = _proc('flow', [_param('x'), _param('y')], _bool(),
               [ProcSpec(_meta(), 'requires', mkEqual(_meta(), _rv('x'),
                                                      _rv('y'))),
                ProcSpec(_meta(), 'ensures', mkEqual(_meta(), _rv('result'),
                                                     _rv('y')))],
               [ImpAssert(aloc, mkEqual(_meta(), _rv('x'), _rv('y')), None),
                ImpReturn(_meta(), _rv('x'))], 'result')
  _env_out, obs = proc_obligations(decl, _env())
  assert [str(o.kind) for o in obs] == ['assertion', 'postcondition']
  assert obs[0].location.start_pos == 100
  # The assertion sees only the entry given; the postcondition also sees the
  # asserted fact.
  assert [str(f) for (_l, f) in obs[0].givens] == ['x = y']
  assert [str(f) for (_l, f) in obs[1].givens] == ['x = y', 'x = y']


def test_void_fall_through_checks_postconditions_without_a_result() -> None:
  # A procedure with no return value exits by falling off the end; its
  # postconditions must hold there and may not mention `result`.
  decl = _proc('noop', [_param('x')], None,
               [ProcSpec(_meta(), 'ensures', _rv('x'))], [])
  _env_out, obs = proc_obligations(decl, _env())
  assert [str(o.goal) for o in obs] == ['x']
  assert obs[0].kind is ObligationKind.POSTCONDITION


# --- the _proc_verifiable gate ----------------------------------------------

def test_straight_line_body_is_verifiable() -> None:
  decl = _proc('ok', [_param('x')], _bool(), [],
               [ImpVar(_meta(), 'y', None, _rv('x')),
                ImpReturn(_meta(), _rv('y'))], 'y')
  assert _proc_verifiable(decl)


def test_branch_defers_verification() -> None:
  decl = _proc('branchy', [_param('x')], None, [],
               [ImpIf(_meta(), _rv('x'), [], None)])
  assert not _proc_verifiable(decl)


def test_mutable_array_parameter_defers_verification() -> None:
  decl = _proc('sweep', [ProcParam(_meta(), 'a',
                                   MutableArrayType(_meta(), _bool()))],
               None, [], [])
  assert not _proc_verifiable(decl)


# --- discharge integration --------------------------------------------------

def test_verify_proc_accepts_a_provable_procedure() -> None:
  decl = _proc('identity', [_param('x')], _bool(),
               [ProcSpec(_meta(), 'ensures', mkEqual(_meta(), _rv('result'),
                                                     _rv('x')))],
               [ImpReturn(_meta(), _rv('x'))], 'result')
  verify_proc(decl, _env())  # returns normally; `x = x` discharges


def test_verify_proc_reports_a_false_postcondition() -> None:
  # ensures result = x, but the body returns a fresh `false`, so the
  # postcondition cannot be discharged and points at the ensures clause.
  from abstract_syntax import Bool
  post = _meta(100, 110)
  decl = _proc('wrong', [_param('x')], _bool(),
               [ProcSpec(post, 'ensures', mkEqual(_meta(), _rv('result'),
                                                  _rv('x')))],
               [ImpReturn(_meta(), Bool(_meta(), None, False))], 'result')
  try:
    verify_proc(decl, _env())
    assert False, 'expected an IncompleteProof'
  except IncompleteProof as e:
    assert 'postcondition' in str(e)
