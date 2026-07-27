"""Source-located verification obligations for the imperative layer.

Issue #854 Phase 2c (#1112). Provides ONE representation and discharge path
for every imperative proof obligation (preconditions, postconditions,
assertions, array bounds, frames, loop entry / preservation / exit, and
decreases) so later verifier slices construct obligations instead of
hand-rolling goal/given plumbing and error presentation.

The representation is pure and CLI-independent: constructing an
``ImperativeObligation`` runs no proof checking and touches no global state,
so later slices can unit-test the formulas they generate without spinning up
the whole pipeline. ``discharge`` is the only method that reaches into the
checker, and it reuses the existing machinery rather than copying it:

  * an attached ``by`` proof is checked with ``check_proof_of``;
  * an unproved goal is attempted automatically -- ``reduce`` applies the
    ambient ``auto`` rewrite rules (the same normalization ``simplify`` uses)
    and ``check_implies`` decides whether the givens entail the goal;
  * when nothing discharges the goal, the standard source-located
    ``Goal:`` / ``Givens:`` incomplete-proof diagnostic is reported at the
    annotation that created the obligation.

There is NO statement-specific verification-condition generation here; that
is the job of the later Phase 2 slices that build obligations of these kinds.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import List, Optional, Tuple

from lark.tree import Meta

import style
from abstract_syntax import And, Bool, Env, Formula, Proof, is_true


class ObligationKind(Enum):
  """The provenance of an imperative proof obligation.

  The value doubles as the human-readable phrase shown in diagnostics, so a
  reader can tell a failed array-bounds check from a failed loop-invariant
  preservation without decoding an internal enum name."""

  PRECONDITION = 'precondition'
  POSTCONDITION = 'postcondition'
  ASSERTION = 'assertion'
  ARRAY_BOUNDS = 'array bounds'
  FRAME = 'frame'
  LOOP_ENTRY = 'loop invariant on entry'
  LOOP_PRESERVATION = 'loop invariant preservation'
  LOOP_EXIT = 'loop exit'
  DECREASES = 'decreases'

  def __str__(self) -> str:
    return self.value


@dataclass
class ImperativeObligation:
  """One imperative proof obligation.

  Attributes:
    location: the source annotation that created the obligation (a
      ``requires``/``ensures`` clause, an ``assert``, an array index, a
      loop's ``invariant``/``decreases``, ...). Diagnostics point here.
    goal: the ``Formula`` that must hold. Callers pass an already
      type-checked formula.
    kind: which sort of obligation this is (see ``ObligationKind``).
    givens: the facts in scope, as ``(label, formula)`` pairs in the order
      they were established. Discharge installs them as local proof
      hypotheses so an attached proof can cite them by ``label`` and the
      ``Givens:`` presentation lists them.
    proof: the optional ``by`` proof the user attached at ``location``.
  """

  location: Meta
  goal: Formula
  kind: ObligationKind
  givens: List[Tuple[str, Formula]] = field(default_factory=list)
  proof: Optional[Proof] = None

  def givens_formula(self) -> Formula:
    """The conjunction of the given hypotheses, or ``true`` when there are
    none -- the antecedent handed to ``check_implies`` for the automatic
    discharge attempt."""
    facts = [frm for (_label, frm) in self.givens]
    if len(facts) == 0:
      return Bool(self.location, None, True)
    if len(facts) == 1:
      return facts[0]
    return And(self.location, None, facts)

  def env_with_givens(self, env: Env) -> Env:
    """``env`` extended with each given as a local proof hypothesis."""
    proof_env = env
    for (label, frm) in self.givens:
      proof_env = proof_env.declare_local_proof_var(self.location, label, frm)
    return proof_env

  def discharge(self, env: Env) -> None:
    """Verify the obligation in ``env``.

    Returns normally when the goal is discharged. Otherwise reports a
    source-located diagnostic through the usual channels (raising in a CLI
    run, recording into the active error sink for the LSP/MCP multi-error
    path) -- an attached-proof failure surfaces the proof checker's own
    error; an unproved goal surfaces the ``Goal:`` / ``Givens:``
    incomplete-proof diagnostic."""
    proof_env = self.env_with_givens(env)
    if self.proof is not None:
      # Independent obligation: route any failure into the active error
      # sink (when one is installed) exactly like a top-level theorem.
      from checker_proofs import _try_check_proof_of
      _try_check_proof_of(self.proof, self.goal, proof_env)
      return
    if self._discharged_automatically(proof_env):
      return
    self._report_incomplete(proof_env)

  def _discharged_automatically(self, env: Env) -> bool:
    """Attempt to discharge the goal without a user proof: normalize with the
    ambient ``auto`` rules and ask ``check_implies`` whether the givens entail
    the result. Returns whether the goal was proved."""
    from checker_logic import check_implies
    from error import UserError

    reduced_goal = self.goal.reduce(env)
    if is_true(reduced_goal):
      return True
    antecedent = self.givens_formula().reduce(env)
    try:
      check_implies(self.location, antecedent, reduced_goal)
      return True
    except UserError:
      return False

  def _report_incomplete(self, env: Env) -> None:
    from checker_proofs import givens_str
    from error import add_incomplete

    add_incomplete(
        self.location,
        style.bold_red('incomplete proof') + '\n'
        + 'could not prove this ' + str(self.kind) + ' obligation\n'
        + style.orange('Goal:') + '\n\t' + str(self.goal)
        + givens_str(env),
        formula=self.goal, env=env)
