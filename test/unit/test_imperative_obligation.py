"""Unit tests for the imperative verification-obligation API (issue #1112).

These construct and discharge obligations directly, without running the CLI
or the rest of the pipeline -- the whole point of the API is that later
verifier slices can unit-test the formulas they generate in isolation.
"""

from lark.tree import Meta

from abstract_syntax import Bool, BoolType, Env, PTrue
from error import Diagnostic, ErrorSink, IncompleteProof, set_active_sink
from imperative_verifier import ImperativeObligation, ObligationKind


def _meta() -> Meta:
  m = Meta()
  m.empty = False
  m.filename = 'test.pf'
  m.line = 3
  m.column = 5
  m.start_pos = 0
  m.end_line = 3
  m.end_column = 6
  m.end_pos = 1
  return m


def _env() -> Env:
  return Env({'__current_module__': 'test'})


def _true() -> Bool:
  return Bool(_meta(), BoolType(_meta()), True)


def _false() -> Bool:
  return Bool(_meta(), BoolType(_meta()), False)


# --- construction is pure ---------------------------------------------------

def test_construction_runs_no_checking() -> None:
  # Building an obligation must not touch the checker or global state -- a
  # false goal is fine until someone calls discharge().
  ob = ImperativeObligation(_meta(), _false(), ObligationKind.ASSERTION)
  assert ob.kind is ObligationKind.ASSERTION
  assert ob.givens == []
  assert ob.proof is None


def test_obligation_kinds_have_readable_phrases() -> None:
  # The enum value doubles as the diagnostic phrase.
  assert str(ObligationKind.ARRAY_BOUNDS) == 'array bounds'
  assert str(ObligationKind.LOOP_PRESERVATION) == 'loop invariant preservation'
  # Every kind is a distinct, non-empty phrase.
  phrases = [str(k) for k in ObligationKind]
  assert len(phrases) == len(set(phrases))
  assert all(phrases)


def test_givens_formula_shape() -> None:
  loc = _meta()
  a, b = _true(), _false()
  # No givens -> `true` antecedent.
  none = ImperativeObligation(loc, _true(), ObligationKind.FRAME)
  assert isinstance(none.givens_formula(), Bool) and none.givens_formula().value
  # One given -> that formula verbatim.
  one = ImperativeObligation(loc, _true(), ObligationKind.FRAME,
                             givens=[('h', a)])
  assert one.givens_formula() is a
  # Many givens -> conjunction, in order.
  many = ImperativeObligation(loc, _true(), ObligationKind.FRAME,
                              givens=[('h1', a), ('h2', b)])
  assert many.givens_formula().args == [a, b]


def test_env_with_givens_installs_local_hypotheses() -> None:
  ob = ImperativeObligation(_meta(), _true(), ObligationKind.PRECONDITION,
                            givens=[('h', _false())])
  base = _env()
  extended = ob.env_with_givens(base)
  assert len(extended.local_proofs()) == 1
  # The base env is not mutated -- Env updates are functional.
  assert base.local_proofs() == []


# --- discharge: automatic ---------------------------------------------------

def test_trivial_true_goal_discharges() -> None:
  ob = ImperativeObligation(_meta(), _true(), ObligationKind.ASSERTION)
  ob.discharge(_env())  # returns normally


def test_false_goal_reports_source_located_incomplete_proof() -> None:
  loc = _meta()
  ob = ImperativeObligation(loc, _false(), ObligationKind.PRECONDITION)
  try:
    ob.discharge(_env())
    assert False, 'expected an IncompleteProof'
  except IncompleteProof as e:
    msg = str(e)
    assert 'test.pf:3.5' in msg            # source-located at the annotation
    assert 'precondition' in msg           # obligation kind is visible
    assert 'Goal:' in msg
    assert e.formula is ob.goal            # structured field for the LSP/MCP


def test_false_given_discharges_any_goal() -> None:
  # A contradictory hypothesis entails the goal via check_implies.
  ob = ImperativeObligation(_meta(), _false(), ObligationKind.LOOP_EXIT,
                            givens=[('h', _false())])
  ob.discharge(_env())  # returns normally


# --- discharge: attached proofs ---------------------------------------------

def test_attached_correct_proof_discharges() -> None:
  loc = _meta()
  ob = ImperativeObligation(loc, _true(), ObligationKind.ASSERTION,
                            proof=PTrue(loc))
  ob.discharge(_env())  # returns normally


def test_attached_wrong_proof_reports_diagnostic() -> None:
  loc = _meta()
  ob = ImperativeObligation(loc, _false(), ObligationKind.ASSERTION,
                            proof=PTrue(loc))
  try:
    ob.discharge(_env())
    assert False, 'expected a diagnostic'
  except Diagnostic:
    pass


# --- discharge: error-sink routing ------------------------------------------

def test_failure_records_into_active_sink_without_raising() -> None:
  sink = ErrorSink()
  prev = set_active_sink(sink)
  try:
    ImperativeObligation(_meta(), _false(),
                         ObligationKind.FRAME).discharge(_env())
  finally:
    set_active_sink(prev)
  assert len(sink) == 1
  assert isinstance(sink.errors[0], IncompleteProof)
