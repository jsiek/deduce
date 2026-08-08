"""Unit tests for procedure verification (issues #1115 Phase 2f, #1116 Phase
2g).

`checker_pipeline.proc_obligations` performs path-sensitive forward symbolic
execution over a `_proc_verifiable` procedure and returns the verification
conditions it generates (without discharging them), so the weakest-precondition
formulas can be pinned here without the CLI or the stdlib. `verify_proc` then
discharges what it returns -- exercised at the end for one provable and one
false goal.
"""

from lark.tree import Meta

from abstract_syntax import (
    Bool, BoolType, Env, ImpAssert, ImpAssign, ImpAssume, ImpIf, ImpReturn,
    ImpVar, ImpWhile, LValueIndex, LValueVar, MutableArrayType, ResolvedVar,
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


def test_if_generates_a_postcondition_per_branch_with_the_condition() -> None:
  # Phase 2g (issue #1116): an `if` splits verification into two paths. Each
  # branch's `return` discharges the postcondition on its own path, carrying
  # the branch condition (then) or its negation (else) as a given.
  decl = _proc('pick', [_param('x')], _bool(),
               [ProcSpec(_meta(), 'ensures', mkEqual(_meta(), _rv('result'),
                                                     _rv('x')))],
               [ImpIf(_meta(), _rv('x'),
                      [ImpReturn(_meta(), _rv('x'))],
                      [ImpReturn(_meta(), _rv('x'))])],
               'result')
  _env_out, obs = proc_obligations(decl, _env())
  assert [str(o.kind) for o in obs] == ['postcondition', 'postcondition']
  # `result` is `x` on both paths, so each goal is `x = x`.
  assert [str(o.goal) for o in obs] == ['x = x', 'x = x']
  # The then-path sees the condition; the else-path sees its negation.
  assert [str(f) for (_l, f) in obs[0].givens] == ['x']
  assert [str(f) for (_l, f) in obs[1].givens] == ['not x']


def test_elseless_if_skips_the_missing_branch() -> None:
  # A missing `else` is `skip`: the continuation is still checked on the
  # else-path, with the negated condition as a given. Here the void proc's
  # postcondition is checked on both the then-path (given `x`) and the
  # fall-through else-path (given `not x`).
  decl = _proc('guard', [_param('x')], None,
               [ProcSpec(_meta(), 'ensures', _rv('x'))],
               [ImpIf(_meta(), _rv('x'),
                      [ImpAssert(_meta(), _rv('x'), None)], None)])
  _env_out, obs = proc_obligations(decl, _env())
  # then-path: the `assert` obligation, then the postcondition; else-path: just
  # the postcondition.
  assert [str(o.kind) for o in obs] == \
      ['assertion', 'postcondition', 'postcondition']
  assert [str(f) for (_l, f) in obs[0].givens] == ['x']
  assert [str(f) for (_l, f) in obs[-1].givens] == ['not x']


def test_assume_supplies_a_downstream_given() -> None:
  # Phase 2g (issue #1116): `assume P` raises no obligation but adds `P` as a
  # given for the statements that follow it (here the later `assert`).
  decl = _proc('assumed', [_param('x')], None, [],
               [ImpAssume(_meta(), _rv('x')),
                ImpAssert(_meta(), _rv('x'), None)])
  _env_out, obs = proc_obligations(decl, _env())
  assert [str(o.kind) for o in obs] == ['assertion']
  assert [str(f) for (_l, f) in obs[0].givens] == ['x']


def test_locals_remain_in_the_discharge_environment() -> None:
  # The returned discharge environment carries the body's locals, not just the
  # parameters, so an attached inline-assert proof (`assert P by <proof>`) can
  # reference a local even though goals and givens are substituted down to
  # parameters. Regression for the PR #1165 review (P2).
  decl = _proc('p', [_param('x')], None, [],
               [ImpVar(_meta(), 'y', None, _rv('x')),
                ImpAssert(_meta(), _rv('x'), None)])
  env_out, _obs = proc_obligations(decl, _env())
  assert 'x' in env_out.dict
  assert 'y' in env_out.dict


def test_branch_locals_reach_the_discharge_environment() -> None:
  # A local declared inside a branch is likewise gathered into the discharge
  # environment (uniquify keeps its name distinct, so no clash with same-named
  # locals on other paths).
  decl = _proc('q', [_param('x')], None, [],
               [ImpIf(_meta(), _rv('x'),
                      [ImpVar(_meta(), 'y', None, _rv('x'))], None)])
  env_out, _obs = proc_obligations(decl, _env())
  assert 'y' in env_out.dict


def test_void_fall_through_checks_postconditions_without_a_result() -> None:
  # A procedure with no return value exits by falling off the end; its
  # postconditions must hold there and may not mention `result`.
  decl = _proc('noop', [_param('x')], None,
               [ProcSpec(_meta(), 'ensures', _rv('x'))], [])
  _env_out, obs = proc_obligations(decl, _env())
  assert [str(o.goal) for o in obs] == ['x']
  assert obs[0].kind is ObligationKind.POSTCONDITION


# --- loops (Phase 2l, issue #1121) ------------------------------------------

def _echo_loop() -> ProcDecl:
  # proc echo(x, go) -> bool  ensures result = x {
  #   var y := x  while go invariant y = x { y := y }  return y }
  inv_loc = _meta(100, 110)
  return _proc('echo', [_param('x'), _param('go')], _bool(),
               [ProcSpec(_meta(), 'ensures', mkEqual(_meta(), _rv('result'),
                                                     _rv('x')))],
               [ImpVar(_meta(), 'y', None, _rv('x')),
                ImpWhile(_meta(), _rv('go'),
                         [mkEqual(inv_loc, _rv('y'), _rv('x'))], [], None,
                         [ImpAssign(_meta(), LValueVar(_meta(), 'y'),
                                    _rv('y'))]),
                ImpReturn(_meta(), _rv('y'))], 'result')


def test_loop_emits_entry_preservation_and_exit_obligations() -> None:
  # Entry checks the invariant in the pre-loop state (`y = x` with `y := x`, so
  # `x = x`); preservation checks it after one havoced iteration (`y = x` with
  # the invariant and loop condition as givens); the exit continuation
  # discharges the postcondition over the havoced state with the invariant and
  # the negated condition as givens.
  _env_out, obs = proc_obligations(_echo_loop(), _env())
  assert [str(o.kind) for o in obs] == \
      ['loop invariant on entry', 'loop invariant preservation',
       'postcondition']
  assert [str(o.goal) for o in obs] == ['x = x', 'y = x', 'y = x']
  # Entry has no givens; preservation and exit carry the invariant plus the
  # (positive / negated) loop condition.
  assert [str(f) for (_l, f) in obs[0].givens] == []
  assert [str(f) for (_l, f) in obs[1].givens] == ['y = x', 'go']
  assert [str(f) for (_l, f) in obs[2].givens] == ['y = x', 'not go']


def test_loop_entry_and_preservation_point_at_the_invariant() -> None:
  # Both invariant obligations are anchored at the invariant annotation the
  # user wrote, so a failure points there rather than at the loop header.
  _env_out, obs = proc_obligations(_echo_loop(), _env())
  assert obs[0].location.start_pos == 100
  assert obs[1].location.start_pos == 100


def test_loop_invariants_keep_their_individual_locations() -> None:
  # Two invariants become two entry obligations (and two preservation
  # obligations), each anchored at its own annotation.
  loc0, loc1 = _meta(100, 110), _meta(120, 130)
  decl = _proc('two', [_param('x'), _param('z'), _param('go')], None, [],
               [ImpVar(_meta(), 'a', None, _rv('x')),
                ImpVar(_meta(), 'b', None, _rv('z')),
                ImpWhile(_meta(), _rv('go'),
                         [mkEqual(loc0, _rv('a'), _rv('x')),
                          mkEqual(loc1, _rv('b'), _rv('z'))], [], None,
                         [ImpAssign(_meta(), LValueVar(_meta(), 'a'), _rv('a')),
                          ImpAssign(_meta(), LValueVar(_meta(), 'b'),
                                    _rv('b'))])])
  _env_out, obs = proc_obligations(decl, _env())
  entry = [o for o in obs if o.kind is ObligationKind.LOOP_ENTRY]
  assert [o.location.start_pos for o in entry] == [100, 120]
  assert [str(o.goal) for o in entry] == ['x = x', 'z = z']


def test_loop_havocs_assigned_locals_but_retains_the_rest() -> None:
  # A local the loop assigns (`y`) is havoced -- after the loop it stands for
  # an arbitrary value, so returning it yields the symbolic `y`. A local the
  # loop never assigns (`kept`) keeps its pre-loop value `x`.
  def loop_returning(name: str) -> ProcDecl:
    return _proc('r', [_param('x'), _param('go')], _bool(),
                 [ProcSpec(_meta(), 'ensures', mkEqual(_meta(), _rv('result'),
                                                       _rv('x')))],
                 [ImpVar(_meta(), 'kept', None, _rv('x')),
                  ImpVar(_meta(), 'y', None, _rv('x')),
                  ImpWhile(_meta(), _rv('go'), [], [], None,
                           [ImpAssign(_meta(), LValueVar(_meta(), 'y'),
                                      _rv('y'))]),
                  ImpReturn(_meta(), _rv(name))], 'result')
  _e0, kept_obs = proc_obligations(loop_returning('kept'), _env())
  assert [str(o.goal) for o in kept_obs] == ['x = x']  # retained
  _e1, y_obs = proc_obligations(loop_returning('y'), _env())
  assert [str(o.goal) for o in y_obs] == ['y = x']     # havoced


def test_sequential_loop_drops_stale_givens_about_a_reassigned_local() -> None:
  # A given an earlier loop exports about a local (its invariant `y`) must not
  # be carried past a *later* loop that havocs the same local; otherwise the
  # second loop's continuation could reuse the stale fact. Here the second loop
  # reassigns `y` with no invariant, so after it `y` carries no given and the
  # postcondition `result = y` cannot be proved -- the obligation's givens
  # mention neither the stale `y` invariant nor `y`.
  decl = _proc('two_loops', [_param('go1'), _param('go2')], _bool(),
               [ProcSpec(_meta(), 'ensures', _rv('y_res'))],
               [ImpVar(_meta(), 'y', None, Bool(_meta(), None, True)),
                ImpWhile(_meta(), _rv('go1'), [_rv('y')], [], None,
                         [ImpAssign(_meta(), LValueVar(_meta(), 'y'),
                                    _rv('y'))]),
                ImpWhile(_meta(), _rv('go2'), [], [], None,
                         [ImpAssign(_meta(), LValueVar(_meta(), 'y'),
                                    Bool(_meta(), None, False))]),
                ImpReturn(_meta(), _rv('y'))], 'y_res')
  _env_out, obs = proc_obligations(decl, _env())
  post = [o for o in obs if o.kind is ObligationKind.POSTCONDITION]
  assert len(post) == 1
  # The stale `y` from loop 1's exit invariant is gone (loop 2 havocs `y`);
  # only the `y`-free negated loop conditions survive, so the postcondition `y`
  # is unprovable (as it should be).
  givens = [str(f) for (_l, f) in post[0].givens]
  assert givens == ['not go1', 'not go2']
  assert not any('y' == g for g in givens)


def test_loop_established_and_preserved_proofs_drive_combined_obligations() -> \
    None:
  # A user `established`/`preserved` proof covers the whole invariant
  # conjunction, so it produces one combined obligation per phase (carrying the
  # proof) instead of one per invariant.
  from abstract_syntax import PTrue
  decl = _proc('proved', [_param('x'), _param('go')], None, [],
               [ImpVar(_meta(), 'a', None, _rv('x')),
                ImpVar(_meta(), 'b', None, _rv('x')),
                ImpWhile(_meta(), _rv('go'),
                         [mkEqual(_meta(), _rv('a'), _rv('x')),
                          mkEqual(_meta(), _rv('b'), _rv('x'))], [], None,
                         [ImpAssign(_meta(), LValueVar(_meta(), 'a'), _rv('a')),
                          ImpAssign(_meta(), LValueVar(_meta(), 'b'),
                                    _rv('b'))],
                         PTrue(_meta()), PTrue(_meta()))])
  _env_out, obs = proc_obligations(decl, _env())
  entry = [o for o in obs if o.kind is ObligationKind.LOOP_ENTRY]
  preserve = [o for o in obs if o.kind is ObligationKind.LOOP_PRESERVATION]
  assert len(entry) == 1 and entry[0].proof is not None
  assert len(preserve) == 1 and preserve[0].proof is not None
  # The single preservation goal is the conjunction of both invariants (in the
  # havoced state, so the invariant variables `a`/`b` stay symbolic).
  assert str(preserve[0].goal) == '((a = x) and (b = x))'


# --- the _proc_verifiable gate ----------------------------------------------

def test_straight_line_body_is_verifiable() -> None:
  decl = _proc('ok', [_param('x')], _bool(), [],
               [ImpVar(_meta(), 'y', None, _rv('x')),
                ImpReturn(_meta(), _rv('y'))], 'y')
  assert _proc_verifiable(decl)


def test_branch_is_verifiable() -> None:
  # Phase 2g (issue #1116): an `if` over otherwise-verifiable statements is now
  # itself verifiable (was deferred in Phase 2f). A missing `else` is `skip`.
  decl = _proc('branchy', [_param('x')], None, [],
               [ImpIf(_meta(), _rv('x'), [], None)])
  assert _proc_verifiable(decl)


def test_branch_with_unmodeled_statement_defers() -> None:
  # `_stmt_verifiable` recurses into branch bodies, so a still-unmodeled
  # construct nested inside a branch defers the whole proc. A `call` statement
  # remains unmodeled, so the `case _` fall-through fires.
  from abstract_syntax import ImpCall
  call = ImpCall(_meta(), _rv('x'))
  decl = _proc('callish', [_param('x')], None, [],
               [ImpIf(_meta(), _rv('x'), [call], None)])
  assert not _proc_verifiable(decl)


def test_branch_assigning_to_a_parameter_defers() -> None:
  # `_assigns_to_a_parameter` recurses into branches, so a parameter assignment
  # nested in a branch still defers (entry/exit ambiguity, #1120).
  decl = _proc('sneaky_branch', [_param('x')], None,
               [ProcSpec(_meta(), 'ensures', _rv('x'))],
               [ImpIf(_meta(), _rv('x'),
                      [ImpAssign(_meta(), LValueVar(_meta(), 'x'),
                                 Bool(_meta(), None, True))], None)])
  assert not _proc_verifiable(decl)


def test_mutable_array_parameter_no_longer_defers_verification() -> None:
  # Before #1118 a mutable-array parameter deferred the whole procedure; now
  # reads (#1117) and element writes (#1118) are modeled, so a procedure over
  # one is verifiable (here, trivially: empty body, no specs).
  decl = _proc('sweep', [ProcParam(_meta(), 'a',
                                   MutableArrayType(_meta(), _bool()))],
               None, [], [])
  assert _proc_verifiable(decl)


def test_frame_declaration_defers_verification() -> None:
  # Frame semantics (#1119) are not modeled yet, so a `reads`/`modifies`
  # clause defers verification (its subjects may name un-typeable constructs).
  decl = _proc('framed', [ProcParam(_meta(), 'a',
                                    MutableArrayType(_meta(), _bool()))],
               None, [ProcSpec(_meta(), 'modifies', [_rv('a')])], [])
  assert not _proc_verifiable(decl)


def test_local_state_loop_is_verifiable() -> None:
  # Phase 2l (issue #1121): a `while` whose body is straight-line local state
  # (a `var`/assignment, `assert`, `assume`) is verifiable.
  decl = _proc('counting', [_param('go')], None, [],
               [ImpVar(_meta(), 'y', None, _rv('go')),
                ImpWhile(_meta(), _rv('go'), [], [], None,
                         [ImpAssign(_meta(), LValueVar(_meta(), 'y'),
                                    _rv('y'))])])
  assert _proc_verifiable(decl)


def test_nested_loop_in_a_loop_body_defers() -> None:
  # A nested `while` is not a straight-line loop-body statement, so a loop
  # containing one is deferred (nested loops are a later slice).
  inner = ImpWhile(_meta(), _rv('go'), [], [], None, [])
  outer = ImpWhile(_meta(), _rv('go'), [], [], None, [inner])
  decl = _proc('nested', [_param('go')], None, [], [outer])
  assert not _proc_verifiable(decl)


def test_array_write_in_a_loop_body_defers() -> None:
  # A mutable-array element write inside a loop body is a later slice (#1128),
  # so a loop containing one is deferred.
  write = ImpAssign(_meta(), LValueIndex(_meta(), 'a', _rv('i')), _rv('v'))
  loop = ImpWhile(_meta(), _rv('go'), [], [], None, [write])
  decl = _proc('arr', [_param('go')], None, [], [loop])
  assert not _proc_verifiable(decl)


def test_loop_assigning_a_parameter_defers() -> None:
  # A loop that assigns a parameter defers for the same entry-vs-exit ambiguity
  # as a straight-line parameter assignment (#1120).
  loop = ImpWhile(_meta(), _rv('x'), [], [], None,
                  [ImpAssign(_meta(), LValueVar(_meta(), 'x'),
                             Bool(_meta(), None, True))])
  decl = _proc('loopassign', [_param('x')], None, [], [loop])
  assert not _proc_verifiable(decl)


def test_assignment_to_a_parameter_defers_verification() -> None:
  # Assigning to a parameter is permitted (parameters are locals), but a
  # postcondition mentioning it would be ambiguous between the entry and exit
  # value without an `old` snapshot, so verification is deferred rather than
  # checked against the entry value alone.
  from abstract_syntax import Bool
  decl = _proc('sneaky', [_param('x')], None,
               [ProcSpec(_meta(), 'ensures', _rv('x'))],
               [ImpAssign(_meta(), LValueVar(_meta(), 'x'),
                          Bool(_meta(), None, True))])
  assert not _proc_verifiable(decl)


def test_proof_block_defers_verification() -> None:
  # A `by <slot>` clause needs the out-of-line proof-block bindings, which are
  # out of scope for this slice, so a procedure that declares one is deferred.
  from abstract_syntax import PTrue
  from abstract_syntax.declarations import ProcProofEntry
  decl = ProcDecl(_meta(), 'slotted', [], [_param('x')], None, [],
                  [ImpReturn(_meta(), _rv('x'))],
                  [ProcProofEntry(_meta(), 'slot', PTrue(_meta()))], None)
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
