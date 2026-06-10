"""Proof checking and goal-directed tactic dispatch.

File charter:
- Put code here when it checks proof terms, checks proofs against goals,
  dispatches proof/tactic handler tables, produces proof advice, manages
  proof-time fresh names, or handles proof-local diagnostic collection.
- This module may call type checking and formula logic, but it should not own
  the implementation of term/type synthesis, predicate lowering, statement
  caching, or whole-file phase orchestration.
- When adding a new proof syntax form, place its handler and dispatch-table
  entry here unless the form is only an implementation detail of predicate
  lowering or custom induction generation.
"""

from typing import TYPE_CHECKING, TypeAlias, cast

from lark.tree import Meta

from abstract_syntax import (
    All, AllElim, AllElimTypes, AllIntro, And, ApplyDefsFact,
    ApplyDefsGoal, Bool, BoolType, Call, Cases,
    Constructor, Env, EvaluateFact, EvaluateGoal, Formula,
    FunctionType, Hole, IfThen, ImpIntro, IndCase, Induction,
    InductiveInfo, Lambda,
    ModusPonens, Omitted, Or, OverloadedVar, PAndElim, PAnnot,
    PExtensionality, PHelpUse, PHole, PInjective, PLet, PRecall,
    Pattern, PatternTerm, PReflexive, Proof, PSorry, PSymmetric, PTLetNew,
    PTransitive, PTrue,
    PTuple, PVar, PatternBool, PatternCons, ProofBinding, ResolvedVar,
    RewriteFact, RewriteGoal, RuleInduction, RuleInversion,
    SimplifyFact, SimplifyGoal, Some, SomeElim, SomeIntro, Suffices,
    SwitchProof, SwitchProofCase, TLet, Term, TermInst, Type, TypeInst, TypeType,
    Union, Var, VarRef, ViewBinding, ViewDecl, base_name, callable_name, formula_match,
    get_predicate_decl, get_type_name, is_constructor, is_equation,
    mkEqual, remove_mark, set_dont_reduce_opaque, set_reduce_all,
    get_reduce_only, set_reduce_only, split_equation, type_match, type_names,
)
from checker_common import *
from checker_logic import (
    apply_rewrites, check_implies, collect_all_if_then,
    expand_definitions, expand_residual_hint, ground_goal_evaluate_hint,
    instantiate, isolate_difference, pattern_to_term, rewrite,
)
from checker_types import (
    check_formula, check_pattern, check_type, type_check_term,
    lookup_union, type_first_letter, type_synth_term,
)
from error import (
    Diagnostic, IncompleteProof, InternalError, MatchFailed, UserError,
    add_diagnostic, add_incomplete, get_active_sink,
    incomplete_error, internal_error, match_failed,
    speculative_probe, user_error, warning, wrap_user_error,
)
from flags import get_target_hole_location, get_verbose
import style

# ``generate_conjunct_body`` is defined in ``checker_induction`` and injected
# into this module's namespace at runtime by the ``proof_checker`` facade
# (see ``proof_checker._link_modules``). The TYPE_CHECKING import avoids a
# static cycle with ``checker_induction`` (which imports
# ``generate_proof_name`` from this file) while still letting mypy resolve
# the symbol.
if TYPE_CHECKING:
    from checker_induction import generate_conjunct_body

CheckedFormula: TypeAlias = Term
Substitution: TypeAlias = dict[str, Term | Type]
TypeSubstitution: TypeAlias = dict[str, Type]
ViewMatch: TypeAlias = tuple[ViewDecl, Type, Type, list[Type]]

name_id = 0

# ---------------------------------------------------------------------------
# In-proof error collection
# ---------------------------------------------------------------------------
#
# ``check_deduce`` already collects one error per top-level statement.
# Inside a single proof, ``check_proof_of`` recurses; many of those
# recursions are sequential (each subproof's success is the parent's
# premise) but a handful are *sibling-independent*: each conjunct of
# a ``?, ?, ?`` tuple, each arm of a ``switch``, each case of an
# ``induction`` proves the same goal under different hypotheses with
# no value flowing between siblings. Catching and continuing at those
# loops surfaces every hole / failed subgoal in the proof, not just
# the first.
#
# Set by ``check_deduce`` for the duration of a single run with an
# error sink in scope; ``None`` otherwise (CLI / goal_at / MCP all
# leave it ``None`` and keep raise-on-first behaviour).  Mirrors the
# existing ``flags.target_hole_location`` pattern -- a module-level
# flag is how the rest of the checker plumbs run-wide context into
# ``check_proof_of`` without dragging an extra parameter through 50+
# recursive call sites.

def _try_check_proof_of(pf: Proof, frm: CheckedFormula, env: Env) -> None:
  """Call ``check_proof_of`` and, when an error sink is active, catch
  any raised exception, append it to the sink, and return normally so
  the surrounding sibling loop continues.

  Use this only at sibling-independent recursion sites (PTuple
  conjuncts, switch / induction / cases arms). At sequential sites a
  failure means the parent can't continue meaningfully -- stick with
  a plain ``check_proof_of`` call there.
  """
  try:
    check_proof_of(pf, frm, env)
  except Diagnostic as e:
    sink = get_active_sink()
    if sink is None:
      raise
    sink.add(e)

def generate_proof_name(name: str) -> str:
    """Allocate a fresh label/binder name at proof-check time.

    Uses ``proof_checker.name_id`` rather than a ``UniquifyContext`` —
    these are generated during proof checking (e.g. for synthesised
    induction-case bindings and rule-induction validators), not during
    the uniquify pass. Distinct counter so the names don't collide
    with the ones uniquify already minted."""
    global name_id
    ls = name.split('.')
    new_id = name_id
    name_id += 1
    return ls[0] + '.' + str(new_id)


# ---------------------------------------------------------------------------
# Per-statement cache
# ---------------------------------------------------------------------------
#

def _check_proof_recall(proof: PRecall, env: Env) -> CheckedFormula:
  loc = proof.location
  results = []
  for fact in proof.facts:
    new_fact = type_check_term(fact, BoolType(loc), env, None, [])
    if new_fact in env.local_proofs():
        results.append(new_fact)
    else:
        user_error(loc, 'Could not find a proof of\n\t' + str(new_fact) \
              + '\nin the current scope\n' \
              + style.orange('Givens:') + '\n' + env.proofs_str())
  if len(results) > 1:
      return And(loc, BoolType(loc), results)
  if len(results) == 1:
      return results[0]
  user_error(loc, 'expected some facts after `recall`')

def _check_proof_var(proof: PVar, env: Env) -> CheckedFormula:
  loc = proof.location
  try:
    formula = env.get_formula_of_proof_var(proof)
    if formula:
        return formula
    raise UserError('could not find given: ' + proof.name)
  except UserError as e:
    user_error(loc, str(e))

def _check_proof_true(proof: PTrue, env: Env) -> CheckedFormula:
  return Bool(proof.location, BoolType(proof.location), True)

def _check_proof_and_elim(proof: PAndElim, env: Env) -> CheckedFormula:
  loc = proof.location
  formula = check_proof(proof.subject, env)
  if isinstance(formula, TLet):
    formula = formula.reduceLets(env)

  match formula:
    case And(_, _, args):
      if proof.which >= len(args):
        user_error(loc, 'out of bounds, access to conjunct ' + str(proof.which) \
                   + ' but there are only ' + str(len(args)) + ' conjuncts' \
                   + ' in formula\n\t' + str(formula))
      return args[proof.which]
    case _:
      user_error(loc, 'expected a conjunction, not ' + str(formula))

def _check_proof_evaluate_fact(proof: EvaluateFact, env: Env) -> CheckedFormula:
  formula = check_proof(proof.subject, env)
  set_reduce_all(True)
  try:
    return formula.reduce(env)
  finally:
    set_reduce_all(False)

def _check_proof_apply_defs_fact(proof: ApplyDefsFact, env: Env) -> CheckedFormula:
  formula = check_proof(proof.subject, env)
  return expand_definitions(proof.location, formula, proof.definitions, env)

def _check_proof_rewrite_fact(proof: RewriteFact, env: Env) -> CheckedFormula:
  formula = check_proof(proof.subject, env)
  eqns = [check_proof(equation_proof, env)
          for equation_proof in proof.equations]
  red_formula = formula.reduce(env)
  return apply_rewrites(proof.location, red_formula, eqns, env,
                        display_formula=formula)

def _check_proof_simplify_fact(proof: SimplifyFact, env: Env) -> CheckedFormula:
  formula = check_proof(proof.subject, env)
  preds = [check_proof(given, env) for given in proof.givens]
  equations = [pred_to_equality(proof.location, p) for p in preds]
  eqns = [equation.reduce(env) for equation in equations]
  new_formula = apply_rewrites(proof.location, formula, eqns, env,
                               display_eqns=equations)
  return new_formula.reduce(env)

def _check_proof_hole(proof: PHole, env: Env) -> CheckedFormula:
  incomplete_error(proof.location, 'unfinished proof')

def _check_proof_sorry(proof: PSorry, env: Env) -> CheckedFormula:
  user_error(proof.location, "can't use sorry in context with unknown goal")

def _check_proof_help_use(proof: PHelpUse, env: Env) -> CheckedFormula:
  formula = check_proof(proof.proof, env)
  user_error(proof.location, proof_use_advice(proof.proof, formula, env))

def _check_proof_tlet_new(proof: PTLetNew, env: Env) -> CheckedFormula:
  new_rhs = type_synth_term(proof.rhs, env, None, [])
  body_env = env.define_term_var(proof.location, proof.var,
                                 new_rhs.typeof, new_rhs)
  return check_proof(proof.body, body_env)

def _check_proof_let(proof: PLet, env: Env) -> CheckedFormula:
  loc = proof.location
  new_frm = check_formula(proof.proved, env)
  match new_frm:
    case Hole(_, _):
      proved_formula = check_proof(proof.because, env)
      user_error(loc, "\nhave " + proof.label + ':\n\t' + str(proved_formula))
    case _:
      _try_check_proof_of(proof.because, new_frm, env)
      body_env = env.declare_local_proof_var(loc, proof.label,
                                             remove_mark(new_frm))
      return check_proof(proof.body, body_env)

def _check_proof_annot(proof: PAnnot, env: Env) -> CheckedFormula:
  loc = proof.location
  new_claim = check_formula(proof.claim, env)
  match new_claim:
    case Hole(_, _):
      proved_formula = check_proof(proof.body, env)
      user_error(loc, '\nconclude ' + str(proved_formula))
    case _:
      _try_check_proof_of(proof.body, new_claim, env)
      return remove_mark(new_claim)

def _check_proof_tuple(proof: PTuple, env: Env) -> CheckedFormula:
  loc = proof.location
  frms = [check_proof(pf, env) for pf in proof.args]
  return And(loc, BoolType(loc), frms)

def _check_proof_imp_intro(proof: ImpIntro, env: Env) -> CheckedFormula:
  loc = proof.location
  if proof.premise is not None:
      new_prem = check_formula(proof.premise, env)
  else:
      new_prem = None
  body_env = env.declare_local_proof_var(loc, proof.label, new_prem)
  conc = check_proof(proof.body, body_env)
  return IfThen(loc, BoolType(loc), new_prem, conc)

def _check_proof_all_intro(proof: AllIntro, env: Env) -> CheckedFormula:
  loc = proof.location
  body_env = env
  x, ty = proof.var
  checked_ty = check_type(ty, env)
  checked_var = (x, checked_ty)
  if isinstance(checked_ty, TypeType):
    body_env = body_env.declare_type(loc, x)
  else:
    body_env = body_env.declare_term_var(loc, x, checked_ty)
  formula = check_proof(proof.body, body_env)
  return All(loc, BoolType(loc), checked_var, proof.pos, formula)

def _check_proof_all_elim(proof: AllElim, env: Env) -> CheckedFormula:
  loc = proof.location
  allfrm = check_proof(proof.univ, env)

  if isinstance(allfrm, TLet):
    allfrm = allfrm.reduceLets(env)

  match allfrm:
    case All(_, _, var, _, _):
      sub: Substitution = {}
      _, ty = var
      try:
        new_arg = type_check_term(proof.arg, ty.substitute(sub), env, None, [])
        if isinstance(new_arg, TermInst):
            new_arg.inferred = False
      except UserError as e:
        if isinstance(ty, TypeType):
          user_error(loc, f"In instantiation of\n\t{str(proof.univ)} : {str(allfrm)}\n" \
                     + f"expected a type argument, but was given '{proof.arg}'")
        else:
          raise e
      if isinstance(ty, TypeType):
        user_error(loc, 'to instantiate:\n\t' + str(proof.univ)+' : '+str(allfrm) \
                   +'\nwith type arguments, instead write:\n\t' \
                   +str(proof.univ) + '<' + str(proof.arg) + '>\n')
    case _:
      user_error(loc, 'expected all formula to instantiate, not ' + str(allfrm) \
                 + '\n' + style.orange('Givens:') + '\n' + env.proofs_str())
  return instantiate(loc, allfrm, new_arg)

def _check_proof_all_elim_types(proof: AllElimTypes, env: Env) -> CheckedFormula:
  loc = proof.location
  allfrm = check_proof(proof.univ, env)

  if isinstance(allfrm, TLet):
    allfrm = allfrm.reduceLets(env)

  match allfrm:
    case All(_, _, vars, _, _):
      sub = {}
      var, ty = vars
      type_arg = check_type(proof.arg, env)
      if not isinstance(ty, TypeType):
        user_error(loc, 'unexpected term parameter ' + str(var) + ' in type instantiation')
      sub[var] = type_arg
    case _:
      user_error(loc, 'expected all formula to instantiate, not ' + str(allfrm))
  return instantiate(loc, allfrm, type_arg)

def _check_proof_modus_ponens(proof: ModusPonens, env: Env) -> CheckedFormula:
  loc = proof.location
  ifthen = check_proof(proof.implication, env)
  match ifthen:
    case IfThen() | All() | And():
      pass
    case _:
      ifthen = ifthen.reduce(env)
  match ifthen:
    case IfThen(loc2, tyof, prem, conc):
      _try_check_proof_of(proof.arg, prem, env)
      return conc.reduce(env)
    case And(loc2, tyof, _):
      vars, imps = collect_all_if_then(loc, ifthen, env)
      arg_frm = check_proof(proof.arg, env)
      rets = []
      for prem, conc in imps:
        try:
          with speculative_probe():
            check_proof_of(proof.arg, prem, env)
          rets.append(conc)
        except UserError:
          pass
      if len(rets) == 1: return rets[0]
      elif len(rets) > 1: return And(loc2, tyof, rets)
      else:
        user_error(loc, "could not prove that " +str(arg_frm) +
                   " implies at least one of\n\t"\
                   + "\n\t".join([str(p) for p, _ in imps])
                   + "\nfor application of \n\t"+str(ifthen)
                   + "\nto \n\t" + str(proof.arg) + ': ' + str(arg_frm))
    case All(loc2, tyof, _, _, _):
      (vars, imps) = collect_all_if_then(loc, ifthen, env)
      rets = []
      reasons = []
      arg_frm = check_proof(proof.arg, env)
      for prem, conc in imps:
        try:
          matching: dict[str, Term] = {}
          formula_match(loc, vars, prem, arg_frm, matching, env,
                        numeric_literals=True)
          type_vars = [x for x in vars if isinstance(x.typeof, TypeType)]
          term_vars = [x for x in vars if not isinstance(x.typeof, TypeType)]
          if len(type_vars) > 0:
            var_type = {x.name : x.typeof for x in term_vars}
            formula_matches = [(x,trm) for (x,trm) in matching.items()]
            for (x,trm) in formula_matches:
                if x in var_type.keys():
                  new_var_type = var_type[x].substitute(matching)
                  type_match(loc, type_vars, new_var_type, trm.typeof, matching)
          for x in vars:
            if x.name not in matching.keys():
              match_failed(loc, "could not deduce an instantiation for variable "\
                           + str(x) + '\n' \
                           + 'for application of\n\t' + str(ifthen) + '\n'\
                           + 'to\n\t' + str(proof.arg) + ': ' + str(arg_frm))
          rets.append(conc.substitute(matching).reduce(env))
        except MatchFailed as e:
          reasons.append(e)
      if len(rets) == 1: return rets[0]
      elif len(rets) > 1: return And(loc2, tyof, rets)
      else:
        user_error(loc, "could not deduce an instantiation for any of the variables "\
              + "for application of \n\t" + str(ifthen) + '\n'\
              + 'to\n\t' + str(proof.arg) + ': ' + str(arg_frm) + '\n'\
              + 'because:\n' + '\n\t'.join([str(e) for e in reasons]))
    case _:
      user_error(loc, "in 'apply', expected an if-then formula, not " + str(ifthen))

def _check_proof_injective(proof: PInjective, env: Env) -> CheckedFormula:
  loc = proof.location
  check_type(proof.constr, env)
  if not is_constructor(proof.constr.name, env):
    user_error(loc, 'in injective, expected a constructor, not\n\t' + base_name(proof.constr.name)
          + givens_str(env))
  formula = check_proof(proof.body, env)
  (a,b) = split_equation(loc, formula, env)
  match (a,b):
    case (Call(_, _, rator1, args1),
          Call(_, _, rator2, args2)) if len(args1) == len(args2):
      name1 = callable_name(rator1)
      name2 = callable_name(rator2)
      if name1 is None or name2 is None:
        user_error(loc, 'in injective, expected constructor calls, not '
              + str(formula))
      f1 = base_name(name1)
      f2 = base_name(name2)
      if f1 != f2:
        user_error(loc, 'in injective, ' + f1 + ' ≠ ' + f2)
      if str(proof.constr) != f1:
        user_error(loc, 'in injective, ' + str(proof.constr) + ' ≠ ' + f1)
      if not is_constructor(name1, env):
        user_error(loc, 'in injective, ' + name1 + ' not a constructor')
      boolty = BoolType(loc)
      eqs = [mkEqual(loc, arg1, arg2) for (arg1,arg2) in zip(args1, args2)]
      if len(eqs) > 1:
          return And(loc, boolty, eqs)
      elif len(eqs) == 1:
          return eqs[0]
      else:
          return Bool(loc, boolty, True)
    case _:
      user_error(loc, 'in injective, non-applicable formula: ' + str(formula))

def _check_proof_symmetric(proof: PSymmetric, env: Env) -> CheckedFormula:
  loc = proof.location
  frm = check_proof(proof.body, env)
  (a,b) = split_equation(loc, frm, env)
  return mkEqual(loc, b, a)

def _check_proof_transitive(proof: PTransitive, env: Env) -> CheckedFormula:
  loc = proof.location
  eq1 = check_proof(proof.first, env)
  eq2 = check_proof(proof.second, env)
  (a,b1) = split_equation(loc, eq1, env)
  (b2,c) = split_equation(loc, eq2, env)
  b1r = b1.reduce(env)
  b2r = b2.reduce(env)
  if b1r != b2r:
    user_error(loc, 'error in transitive,\nyou proved\n\t'
          + str(eq1) + '\nand\n\t' + str(eq2) + '\n' \
          + 'but the middle formulas do not match:\n\t' \
          + str(b1r) + '\n≠\n\t' + str(b2r))
  else:
    return mkEqual(loc, a, c)

_CHECK_PROOF_HANDLERS = {
  PRecall: _check_proof_recall,
  PVar: _check_proof_var,
  PTrue: _check_proof_true,
  PAndElim: _check_proof_and_elim,
  EvaluateFact: _check_proof_evaluate_fact,
  ApplyDefsFact: _check_proof_apply_defs_fact,
  RewriteFact: _check_proof_rewrite_fact,
  SimplifyFact: _check_proof_simplify_fact,
  PHole: _check_proof_hole,
  PSorry: _check_proof_sorry,
  PHelpUse: _check_proof_help_use,
  PTLetNew: _check_proof_tlet_new,
  PLet: _check_proof_let,
  PAnnot: _check_proof_annot,
  PTuple: _check_proof_tuple,
  ImpIntro: _check_proof_imp_intro,
  AllIntro: _check_proof_all_intro,
  AllElim: _check_proof_all_elim,
  AllElimTypes: _check_proof_all_elim_types,
  ModusPonens: _check_proof_modus_ponens,
  PInjective: _check_proof_injective,
  PSymmetric: _check_proof_symmetric,
  PTransitive: _check_proof_transitive,
}

def check_proof(proof: Proof, env: Env) -> CheckedFormula:
  if get_verbose():
    print('check_proof:')
    print('\t' + str(proof))
  handler = _CHECK_PROOF_HANDLERS.get(type(proof))
  if handler is not None:
    return cast(CheckedFormula, handler(proof, env))
  user_error(proof.location, goal_only_proof_error(proof))

# Tactic-keyword name used for each "goal-only" Proof class. These tactics
# transform the current goal rather than producing a proof of a formula, so
# they can only be checked by `check_proof_of`, not `check_proof`.
GOAL_ONLY_TACTIC_NAME = {
  ApplyDefsGoal: 'expand',
  RewriteGoal: 'replace',
  SimplifyGoal: 'simplify',
  EvaluateGoal: 'evaluate',
  Suffices: 'suffices',
  Induction: 'induction',
  RuleInduction: 'induction',
  RuleInversion: 'cases',
  Cases: 'cases',
  SwitchProof: 'switch',
}

def goal_only_proof_error(proof: Proof) -> str:
  """Error message for a proof that can only be used in goal-directed mode.

  Detects common user mistakes (e.g. chaining tactics with `|` as in
  ``replace eq | expand X``) and offers actionable advice instead of the
  internal phrase "need to be in goal-directed mode".
  """
  tactic = GOAL_ONLY_TACTIC_NAME.get(type(proof))
  if tactic is None:
    return 'a proof of a formula is expected here, not the tactic\n\t' \
        + str(proof)
  return '`' + tactic + '` is a goal-directed tactic — it transforms ' \
      + 'the current goal, but it does not by itself produce a proof of a ' \
      + 'formula. It cannot be used here.\n\n' \
      + 'If you wrote something like `replace eq | ' + tactic + ' ...` or ' \
      + '`expand f | ' + tactic + ' ...`, note that `|` separates ' \
      + 'arguments to the leading tactic, not a sequence of tactics. ' \
      + 'To run tactics in sequence, write them as separate proof steps:\n' \
      + '\treplace eq\n' \
      + '\t' + tactic + ' ...'

def get_type_args(ty: Type | VarRef) -> list[Type]:
  if isinstance(ty, VarRef):
    return []
  match ty:
    case TypeInst(_, ty, type_args):
      return cast(list[Type], type_args)
    case _:
      raise InternalError('unhandled case in get_type_args: ' + repr(ty))

label_count = 0

def reset_label() -> None:
    pass

def generate_label() -> str:
    global label_count
    l = 'label_' + str(label_count)
    label_count = label_count + 1
    return l
  
def proof_use_advice(proof: Proof, formula: CheckedFormula, env: Env) -> str:
    prefix = style.dark_green('Advice about using fact:') + '\n' \
        + '\t' + str(formula) + '\n\n'
    match formula:
      case Bool(loc, _, True):
        return prefix + '\tThe "true" fact is useless.\n'
      case Bool(loc, _, False):
        return prefix \
            + '\tUse this "false" fact to implicitly prove anything!\n'
      case And(loc, _, args):
        return prefix \
            + '\tUse this logical-and to implicitly prove any of its parts:\n' \
            + '\n'.join('\t\t' + str(arg) for arg in args)
      case Or(loc, _, args):
        reset_label()
        return prefix \
            + '\tUse this logical-or by proceeding with a "cases" statement:\n'\
            + '\t\tcases ' + str(proof) + '\n' \
            + '\n'.join(['\t\tcase ' + generate_label() + ' : ' + str(arg) \
                         + ' { ? }' for arg in args])
      case IfThen(loc, _, prem, conc):
        return prefix \
            + '\tApply this if-then formula to a proof of its premise:\n' \
            + '\t\t' + str(prem) + '\n' \
            + '\tto obtain a proof of its conclusion:\n' \
            + '\t\t' + str(conc) + '\n' \
            + '\tby using an apply-to statement:\n' \
            + '\t\tapply ' + str(proof) + ' to ?'
      case All(loc, _, var, (s, _), body):
        vars = [var]
        while s != 0:
          match body:
            case All(_, _, var2, (s, _), body):
              vars.append(var2)

        letters = []
        all_new_vars: Substitution = {}
        i = 65
        type_param = False
        for (x,ty) in vars:
          if isinstance(ty, TypeType):
              type_param = True
          letters.append(chr(i))
          all_new_vars[x] = ResolvedVar(loc,ty, chr(i))
          i = i + 1
        plural = 's' if len(vars) > 1 else ''
        pronoun = 'them' if len(vars) > 1 else 'it'
        
        if type_param:
            how = ' between `<` and `>` like so:\n' \
                + '\t\t ' + str(proof) + '<' + ', '.join(letters) + '>' + '\n'
        else:
            how = ' in square-brackets like so:\n' \
                + '\t\t ' + str(proof) + '[' + ', '.join(letters) + ']' + '\n'
        
        return prefix \
            + '\tInstantiate this all formula with your choice' + plural \
            + ' for ' + ', '.join([base_name(x) for (x,ty) in vars]) + '\n' \
            + '\tby writing ' + pronoun + how \
            + '\tto obtain a proof of:\n' \
            + '\t\t' + str(body.substitute(all_new_vars))
      case Some(loc, _, vars, body):
        letters = []
        some_new_vars: Substitution = {}
        i = 65
        for (x,ty) in vars:
            letters.append(chr(i))
            some_new_vars[x] = ResolvedVar(loc,ty, chr(i))
            i = i + 1
        new_body = body.substitute(some_new_vars)
        return prefix \
            + 'To use this "some" formula, proceed with:\n' \
            + '\tobtain ' + ', '.join(letters) + \
            ' where label: ' + str(new_body) + ' from ' + str(proof) +'\n' \
            + 'where ' + ', '.join(letters) \
            + (' are new names of your choice' if len(vars) > 1 \
               else ' is a new name of your choice' ) + ',\n' \
            + 'followed by a proof of the goal.'

      case Call(_, _, rator, [_, _]) if isinstance(rator, VarRef) and rator.get_name() == '=':
        return prefix \
            + '\tYou can use this equality in a replace statement:\n' \
            + '\t\treplace ' + str(proof) + '\n'
      case _:
        return 'Sorry, I have no advice for this kind of formula.'

def make_unique(name: str, env: Env) -> str:
    if name in env:
        return make_unique(name + "'", env)
    else:
        return name

def is_recursive(name: str, typ: Type | VarRef) -> bool:
    match typ:
      case OverloadedVar(_, _, rs):
        return bool(name == rs[0])
      case ResolvedVar(_, _, r):
        return bool(name == r)
      case TypeInst(_, ty, _):
        return is_recursive(name, ty)
      case _:
        return False

def update_all_head(r: Formula) -> Formula:
    match r:
      case All(loc2, tyof, var, (s, e), frm):
        if s == 0:  
          return All(loc2, tyof, var, (s, e-1), frm)
        else:
          return All(loc2, tyof, var, (s, e-1), update_all_head(frm))
      case _:
        return r

def gen_conjunct_advice(conjunct: Formula, arbs: list[str], ihs: list[str]) -> str:
  match conjunct:
    case All(_, _, (n, _), _, b):
      return gen_conjunct_advice(b, arbs + [base_name(n)], ihs)
    case IfThen(_, _, _, b):
      return gen_conjunct_advice(b, arbs, ihs + [f"IH{len(ihs)}"])
    case Call(_, _, _, [arg]):
      withs = ""
      if arbs:
        withs = "with " + ", ".join(arbs) + ". "
      assumes = ""
      if ihs:
        assumes = "assume " + ", ".join(ihs) +" "
      return f"\t\tcase {withs}{arg} {assumes} {'{'}\n\t\t\t?\n{'\t\t}'}"
  return ""

def gen_custom_induction_advice(conjuncts: list[Formula]) -> str:
  return "\n".join([gen_conjunct_advice(c, [], []) for c in conjuncts])

def _custom_induction_expected_cases(conjuncts: list[Formula]) -> str:
  return gen_custom_induction_advice(conjuncts).replace('\t\t', '\t')

def _custom_induction_case_hint(conjunct: Formula) -> str:
  return gen_conjunct_advice(conjunct, [], []).replace('\t\t', '\t')

def _switch_pattern_could_match_alts(pat: Pattern, alts: list[Constructor]) -> bool:
  """Heuristic: would ``pat`` plausibly match one of the union ``alts``?

  Used to detect whether a ``switch`` case is targeting the union's
  underlying constructors or the type's public (custom-induction) view.
  Patterns that are not :class:`PatternCons` (e.g. ``with m. 1 + m`` /
  numeric literal pseudo-patterns) never match constructors, and a
  :class:`PatternCons` matches when any candidate name overlaps with an
  alt name."""
  if not isinstance(pat, PatternCons):
    return False
  constr = pat.constructor
  if isinstance(constr, OverloadedVar):
    candidates = constr.resolved_names
  elif isinstance(constr, VarRef):
    candidates = [constr.get_name()]
  else:
    return False
  return any(alt.name in candidates for alt in alts)

def _proof_view_callable(loc: Meta, name: str, type_args: list[Type]) -> Term:
  rator: Term = ResolvedVar(loc, None, name)
  if type_args:
    rator = TermInst(loc, None, rator, type_args)
  return rator

def _proof_view_call(loc: Meta, name: str, arg: Term,
                     type_args: list[Type]) -> Call:
  return Call(loc, None, _proof_view_callable(loc, name, type_args), [arg])

def _bijective_view_for_source_type(loc: Meta, ty: Type, env: Env
                                    ) -> ViewMatch | None:
  for binding in env.dict.values():
    if not isinstance(binding, ViewBinding):
      continue
    view = binding.view
    if view.inverse is None:
      continue
    matching: dict[str, Type | VarRef | None] = {}
    try:
      type_match(loc, type_names(loc, view.type_params),
                 view.source, ty, matching)
    except MatchFailed:
      continue
    sub: Substitution = {
        name: value for name, value in matching.items()
        if value is not None
    }
    type_args = [cast(Type, sub[name]) for name in view.type_params]
    source_ty = cast(Type, view.source.substitute(sub))
    target_ty = cast(Type, view.target.substitute(sub))
    return view, source_ty, target_ty, type_args
  return None

def _view_switch_expected_cases(alts: list[Constructor], env: Env) -> str:
  lines = []
  for alt in alts:
    params = [make_unique(type_first_letter(ty) + str(i + 1), env)
              for i, ty in enumerate(alt.parameters)]
    line = '\tcase ' + base_name(alt.name)
    if params:
      line += '(' + ', '.join(params) + ')'
    line += ' {\n\t  ?\n\t}'
    lines.append(line)
  return '\n'.join(lines)

def _check_induction_via_custom_induction(
    loc: Meta,
    typ: Type,
    formula: All,
    cases: list[IndCase],
    custom_ind: InductiveInfo,
    env: Env,
    expected_cases: str | None = None,
) -> None:
  conjuncts = custom_ind["conjuncts"]
  fun_name = custom_ind["fun"]
  fun_ty = custom_ind['fun_ty']
  type_vars = custom_ind['tys']
  type_subst = {}

  types_elimmed = custom_ind["thm"]

  if len(cases) != len(conjuncts):
    plural = '' if len(conjuncts) == 1 else 's'
    if expected_cases is None:
      expected_cases = _custom_induction_expected_cases(conjuncts)
    add_diagnostic(loc, 'expected ' + str(len(conjuncts)) \
          + ' case' + plural + ' for custom induction on ' + str(typ) \
          + ', but have ' + str(len(cases)) \
          + '\nExpected cases:\n' + expected_cases \
          + givens_str(env))
    return

  if type_vars != []:
    match typ:
      case TypeInst(loc, _, params):
        assert len(type_vars) == len(params) # Enforced by match_induction_fun
        for k, v in zip(type_vars, params):
          type_subst[k] = v
          types_elimmed = AllElimTypes(loc, types_elimmed, v, (0, 1))
      case _:
        internal_error(loc, "Expected a type inst")

  pfun = Lambda(loc, fun_ty, [formula.var], formula.body)
  fun_var = ResolvedVar(loc, fun_ty, fun_name)

  annots = []

  for (conjunct, case) in zip(conjuncts, cases):
    conjunct = conjunct.substitute(type_subst)
    new_body = generate_conjunct_body(loc, conjunct, case, fun_var, type_subst, env)
    new_body = ApplyDefsGoal(loc, [fun_var], new_body)

    annot = PAnnot(loc, conjunct, new_body)
    annots.append(annot)

  new_pf = PTLetNew(loc, fun_name, pfun,
                    ApplyDefsFact(loc, [fun_var],
                                  ModusPonens(loc,
                                              AllElim(loc, types_elimmed,
                                                      fun_var,  (0, 1)),
                                              PTuple(loc, annots))))

  if get_verbose():
    print("Generated custom induction:")
    print(new_pf)

  _try_check_proof_of(new_pf, formula, env)

def _check_induction_via_view(loc: Meta, typ: Type,
                              formula: All,
                              cases: list[IndCase],
                              view: ViewDecl,
                              source_ty: Type,
                              target_ty: Type,
                              type_args: list[Type],
                              custom_ind: InductiveInfo | None,
                              env: Env) -> None:
  if custom_ind is None:
    add_diagnostic(loc, 'induction on `' + str(typ) + '` via view `'
          + base_name(view.name) + '` needs an induction theorem for `'
          + str(typ) + '` until view induction can prove recursive view '
          + 'cases directly.' + givens_str(env))
    return

  target_union = lookup_union(loc, target_ty, env)
  alts = target_union.alternatives
  if len(cases) != len(alts):
    plural = '' if len(alts) == 1 else 's'
    add_diagnostic(loc, 'expected ' + str(len(alts)) + ' view case'
          + plural + ' for induction on `' + str(typ) + '` via view `'
          + base_name(view.name) + '`, but have ' + str(len(cases))
          + '\nExpected cases:\n' + _view_switch_expected_cases(alts, env)
          + givens_str(env))
    return

  translated_cases = []
  cases_present: dict[str, bool] = {}
  for alt, indcase in zip(alts, cases):
    match indcase.pattern:
      case PatternCons(_, _, _):
        body_env = check_pattern(indcase.pattern, target_ty, env, cases_present)
        if indcase.pattern.constructor.name != alt.name:
          add_diagnostic(indcase.location, "expected a view case for "
                + str(base_name(alt.name)) + " not "
                + str(base_name(indcase.pattern.constructor.name))
                + givens_str(env))
          return
        pattern_term = pattern_to_term(indcase.pattern)
        checked_pattern = type_check_term(pattern_term, target_ty, body_env, None, [])
        out_term = type_check_term(
            _proof_view_call(loc, view.out, checked_pattern, type_args),
            source_ty, body_env, None, [])
        old_reduce_only = get_reduce_only()
        set_reduce_only(old_reduce_only + [ResolvedVar(loc, None, view.out)])
        try:
          out_term = cast(Term, out_term.reduce(body_env))
        finally:
          set_reduce_only(old_reduce_only)
        translated_cases.append(
            IndCase(indcase.location,
                    PatternTerm(indcase.pattern.location, out_term,
                                indcase.pattern.bindings()),
                    indcase.induction_hypotheses,
                    indcase.body))
      case _:
        add_diagnostic(indcase.location, 'expected a constructor pattern for '
              + 'induction on `' + str(typ) + '` via view `'
              + base_name(view.name) + '`'
              + '\nExpected cases:\n' + _view_switch_expected_cases(alts, env)
              + givens_str(env))
        return

  _check_induction_via_custom_induction(
      loc, typ, formula, translated_cases, custom_ind, env,
      expected_cases=_view_switch_expected_cases(alts, env))

def _check_switch_via_view(loc: Meta, new_subject: Term,
                           formula: CheckedFormula,
                           cases: list[SwitchProofCase],
                           ty: Type, view: ViewDecl,
                           target_ty: Type, type_args: list[Type],
                           env: Env) -> None:
  if not isinstance(new_subject, VarRef):
    add_diagnostic(loc, '`switch` on `' + str(ty) + '` through view '
          + '`' + base_name(view.name) + '` with a non-variable subject '
          + 'is not supported. Bind the subject first: `define n = '
          + str(new_subject) + '` and then `switch n`.'
          + givens_str(env))
    return

  target_union = lookup_union(loc, target_ty, env)
  alts = target_union.alternatives
  if len(cases) != len(alts):
    plural = '' if len(alts) == 1 else 's'
    add_diagnostic(loc, 'expected ' + str(len(alts)) + ' view case'
          + plural + ' in switch on `' + str(ty) + '` via view `'
          + base_name(view.name) + '`, but have ' + str(len(cases))
          + '\nExpected cases:\n' + _view_switch_expected_cases(alts, env)
          + givens_str(env))
    return

  for scase in cases:
    if scase.assumptions:
      add_diagnostic(scase.location, '`switch` on `' + str(ty)
            + '` via view `' + base_name(view.name) + '` does not bind '
            + 'case assumptions. The case goal is checked with `'
            + str(new_subject) + '` replaced by the view out-pattern.'
            + givens_str(env))
      return

  view_value_name = generate_proof_name('v')
  view_value = ResolvedVar(loc, target_ty, view_value_name)
  out_value = _proof_view_call(loc, view.out, view_value, type_args)
  view_formula_body = cast(
      CheckedFormula,
      formula.substitute({new_subject.get_name(): out_value}),
  )
  view_formula = All(loc, None, (view_value_name, target_ty), (0, 1),
                     view_formula_body)

  ind_cases = [
      IndCase(scase.location, scase.pattern, [], scase.body)
      for scase in cases
  ]
  prove_view_formula = PAnnot(loc, view_formula,
                              Induction(loc, target_ty, ind_cases))
  into_subject = _proof_view_call(loc, view.into, new_subject, type_args)
  prove_out_into = AllElim(loc, prove_view_formula, into_subject, (0, 1))

  try:
    with speculative_probe():
      check_proof_of(prove_out_into, formula, env)
      return
  except UserError:
    pass

  inverse: Proof = PVar(loc, cast(str, view.inverse))
  for type_arg in type_args:
    inverse = AllElimTypes(loc, inverse, type_arg, (0, 1))
  inverse_eq = AllElim(loc, inverse, new_subject, (0, 1))
  new_pf = RewriteGoal(loc, [PSymmetric(loc, inverse_eq)], prove_out_into)

  if get_verbose():
    print("Generated view switch:")
    print(new_pf)

  _try_check_proof_of(new_pf, formula, env)

def _check_switch_via_custom_induction(loc: Meta, new_subject: Term,
                                       formula: CheckedFormula,
                                       cases: list[SwitchProofCase],
                                       ty: Type, custom_ind: InductiveInfo,
                                       env: Env) -> None:
  """Discharge ``switch <subject> { ... }`` on a type whose union
  constructors are wrapped by a custom-induction (public) view, by
  reducing it to one application of the custom induction theorem.

  The motive is ``lambda x. formula[subject -> x]``, so each case body
  is checked against the goal with the subject replaced by the case
  pattern (matching the ``switch`` semantics for ``Var`` subjects).
  The induction hypothesis is auto-suppressed (named ``_``); the user
  doesn't write ``assume IH`` and doesn't get an IH in scope. The user
  also doesn't get the equation ``subject = pattern`` -- for the
  case-analysis-with-equation idiom, ``cases <T>_zero_or_*[<subject>]``
  is the right tool. We refuse non-``Var`` subjects on this path
  because the ``formula[subject -> x]`` substitution only works
  reliably when the subject is a variable name."""
  conjuncts = custom_ind["conjuncts"]
  fun_name = custom_ind["fun"]
  fun_ty = custom_ind['fun_ty']
  type_vars = custom_ind['tys']
  type_subst: TypeSubstitution = {}
  types_elimmed = cast(Proof, custom_ind["thm"])

  if not isinstance(new_subject, VarRef):
    add_diagnostic(loc, '`switch` on `' + str(ty) + '` with a non-variable'
          + ' subject is not supported (would need a case-analysis lemma'
          + ' to relate the subject to each case pattern). Bind the'
          + ' subject first: `define n = ' + str(new_subject)
          + '` and then `switch n`.'
          + givens_str(env))
    return

  if len(cases) != len(conjuncts):
    plural = '' if len(conjuncts) == 1 else 's'
    add_diagnostic(loc, 'expected ' + str(len(conjuncts))
          + ' case' + plural + ' in switch on `' + str(ty) + '`,'
          + ' but have ' + str(len(cases))
          + '\nExpected cases:\n' + _custom_induction_expected_cases(conjuncts)
          + givens_str(env))
    return

  for scase in cases:
    typed = [asm for asm in scase.assumptions if asm[1] is not None]
    if typed:
      add_diagnostic(scase.location, '`switch` on `' + str(ty) + '`'
            + ' (custom-induction view) does not bind an equation'
            + ' hypothesis. Use `cases <T>_zero_or_*[' + str(new_subject)
            + ']` (e.g. `cases uint_zero_or_add_one[' + str(new_subject)
            + ']` for `UInt`) when you need `' + str(new_subject)
            + ' = <pattern>` as a labelled hypothesis, or `induction '
            + str(ty) + '` when you also need the IH.'
            + givens_str(env))
      return

  if type_vars != []:
    match ty:
      case TypeInst(_, _, params):
        assert len(type_vars) == len(params)
        for k, v in zip(type_vars, params):
          type_subst[k] = v
          types_elimmed = AllElimTypes(loc, types_elimmed, v, (0, 1))
      case _:
        internal_error(loc, "expected a TypeInst for generic custom induction")

  fresh_x = generate_proof_name('x')
  motive_var = ResolvedVar(loc, ty, fresh_x)
  pfun_body = cast(Term, formula.substitute({new_subject.get_name(): motive_var}))
  pfun = Lambda(loc, fun_ty, [(fresh_x, ty)], pfun_body)
  fun_var = ResolvedVar(loc, fun_ty, fun_name)

  annots = []
  for (conjunct, scase) in zip(conjuncts, cases):
    conjunct = cast(Formula, conjunct.substitute(type_subst))
    ind_case = IndCase(scase.location, scase.pattern, [], scase.body)
    new_body = generate_conjunct_body(loc, conjunct, ind_case, fun_var,
                                      type_subst, env)
    new_body = ApplyDefsGoal(loc, [fun_var], new_body)
    annot = PAnnot(loc, conjunct, new_body)
    annots.append(annot)

  all_x_P = ModusPonens(loc,
                        AllElim(loc, types_elimmed, fun_var, (0, 1)),
                        PTuple(loc, annots))
  specialized = ApplyDefsFact(loc, [fun_var],
                              AllElim(loc, all_x_P, new_subject, (0, 1)))
  new_pf = PTLetNew(loc, fun_name, pfun, specialized)

  if get_verbose():
    print("Generated custom-view switch:")
    print(new_pf)

  _try_check_proof_of(new_pf, formula, env)

def proof_advice(formula: CheckedFormula, env: Env) -> str:
    prefix = style.dark_green('Advice:') + '\n'

    red_formula = formula.reduce(env)
    if formula != red_formula:
        prefix += '\tThis goal simplifies to\n\t\t' + str(red_formula) + '\n' \
            + '\tConsider using\n\t\tsimplify\n\n'
    
    match formula:
      case Bool(loc, _, True):
        return prefix + '\tYou can prove "true" with a period.\n'
      case Bool(loc, _, False):
        return prefix \
            + '\tProve "false" by proving a contradiction:\n' \
            + '\tif you prove both "P" and "not P", \n' \
            + '\tthen "contradict (recall not P), (recall P)" proves "false".\n'
      case And(loc, _, args):
        return prefix \
            + '\tProve this logical-and formula by proving each of its'\
            + ' parts,\n\tshown below, then combine the proofs with commas.\n' \
            + '\n'.join('\t\t' + str(arg) for arg in args)
      case Or(loc, _, args):
        return prefix \
            + '\tProve this logical-or formula by proving one of its parts:\n' \
            + '\n'.join('\t\t' + str(arg) for arg in args)
      case IfThen(loc, _, prem, conc):
        return prefix \
            + '\tProve this if-then formula with:\n' \
            + '\t\tassume label: ' + str(prem) + '\n' \
            + '\tfollowed by a proof of:\n' \
            + '\t\t' + str(conc)
      case All(loc, _, var, (s, _), body):
        pf = "arbitrary "
        cur = formula
        prev_s = s + 1 # This variable stops spillover into other alls

        while isinstance(cur, All) and cur.pos[0] >= 0 and cur.pos[0] < prev_s:
          pf += f"{base_name(cur.var[0])}:{cur.var[1]}{', ' if cur.pos[0] > 0 else ''}"
          prev_s = cur.pos[0]
          cur = cur.body

        arb_advice = prefix \
            + '\tProve this "all" formula with:\n' \
            + '\t\t' + pf + '\n' \
            + '\tfollowed by a proof of:\n' \
            + '\t\t' + str(cur)

        # NOTE: Maybe we shouldn't give induction advice for non recursively
        # defined unions. However right now we will because I haven't added
        # that check yet. Maybe even suggest a switch instead.
        
        var_x, var_ty = var
        match var_ty:
          # NOTE: These are the types that are handled in get_type_name, and
          # get_def_of_type_var
          case TypeInst() | Var() | OverloadedVar() | ResolvedVar():
            pass
          case _:
            return arb_advice # don't give induction advice for type variables

        # When foralls are generated, the def of type var is not in the environment?
        # Seems to be a problem with extensionality
        # I'm ok for now with just failing the match if this happens
        ty = None
        try:
          ty = env.get_def_of_type_var(get_type_name(var_ty))
        except Exception:
          pass

        match ty:
          case Union(_, name, _, alts):
            has_custom_ind = env.get_inductive(var_ty)

            if ty.visibility == 'opaque':
              binding = env.dict[name]
              if binding.location.filename != env.get_current_module() and not has_custom_ind:
                return arb_advice

            if len(alts) < 2:
              return arb_advice # Can't do induction if there's only one case
                
            ind_advice = '\n\n\tAlternatively, you can try induction with:\n' \
              +  '\t\tinduction ' + str(var_ty) + '\n'

            if has_custom_ind:
              # Do advice based on the theorem
              ind_advice += gen_custom_induction_advice(has_custom_ind["conjuncts"])
            else:
              # Do advice based on the alts of the union
              for alt in alts:
                match alt:
                  case Constructor(loc3, constr_name, param_types):
                    params = [make_unique(type_first_letter(ty)+str(i+1), env)\
                              for i,ty in enumerate(param_types)]
                    ind_advice += '\t\tcase ' + base_name(constr_name)
                    if len(param_types) > 0:
                      ind_advice += '(' + ', '.join(params) + ')'
                    num_recursive = sum([1 if is_recursive(name, ty) else 0 \
                                         for ty in param_types])
                    if num_recursive > 0:
                      rec_params =[(p,ty) for (p,ty) in zip(params,param_types)\
                                   if is_recursive(name, ty)]
                      ind_advice += ' assume '
                      ind_advice += ',\n\t\t\t'.join(['IH' + str(i+1) + ': ' \
                            + str(update_all_head(body.substitute({var_x: ResolvedVar(loc3, param_ty, param)}))) \
                            for i, (param,param_ty) in enumerate(rec_params)])

                    ind_advice += ' {\n\t\t  ?\n\t\t}\n'
                    
            return arb_advice + ind_advice
        
          case _:
            return arb_advice


      case Some(loc, _, vars, body):
        letters = []
        new_vars: Substitution = {}
        i = 65
        for (x,ty) in vars:
            letters.append(chr(i))
            new_vars[x] = ResolvedVar(loc,ty, chr(i))
            i = i + 1
        return prefix \
            + '\tProve this "some" formula with:\n' \
            + '\t\tchoose ' + ', '.join(letters) + '\n' \
            + '\twhere you replace ' + ', '.join(letters) \
            + ' with your choice(s),\n' \
            + '\tthen prove:\n' \
            + '\t\t' + str(body.substitute(new_vars))
      case Call(_, _, rator, [_, _]) if isinstance(rator, VarRef) and rator.get_name() == '=':
        return prefix \
            + '\tTo prove this equality, one of these statements might help:\n'\
            + '\t\texpand\n' \
            + '\t\treplace\n' \
            + '\t\tequations\n'
      case TLet(_, _, var, _, body):
        return proof_advice(body, env)
      case _:
        for (name, b) in env.dict.items():
            if isinstance(b, ProofBinding) and b.local and b.formula == formula:
                msg = '\nYou can conclude the proof with:\n'
                if base_name(name) == '_':
                    msg += '\trecall ' + str(formula)
                else:
                    msg += '\tconclude ' + str(formula) \
                        + ' by ' + base_name(name)                
                return msg

        return ''

def givens_str(env: Env) -> str:
    env_str = env.proofs_str()
    if len(env_str) > 0:
        givens = '\n' + style.orange('Givens:') + '\n' + env_str
    else:
        givens = ''
    return cast(str, givens)

def pred_to_equality(meta: Meta, pred: CheckedFormula) -> CheckedFormula:
    match pred:
      case IfThen(_, _, p, Bool(_, _, False)):
          return Call(meta, None, ResolvedVar(meta, None, '='),
                      [p , Bool(meta, None, False)])
      case _:
          return Call(meta, None, ResolvedVar(meta, None, '='),
                      [pred , Bool(meta, None, True)])

def _check_rule_induction(proof: RuleInduction, goal: CheckedFormula, env: Env) -> None:
  """See `_check_rule_inversion`: same shape, applies the
  `<pred>_rule_induction` theorem instead of the inversion theorem."""
  _check_rule_induction_or_inversion(proof, goal, env, is_inversion=False)

def _check_rule_inversion(proof: RuleInversion, goal: CheckedFormula, env: Env) -> None:
  """Desugar `rule inversion <pred> case <r1> { ... } ...` to
     `apply <pred>_rule_inversion[<motive>] to (<case_1>, ..., <case_k>)`.
  Same goal shape as `rule induction`, but each case proves the rule's
  *non*-augmented conjunct (premises in their original form, no
  motive's induction hypothesis paired with recursive premises)."""
  _check_rule_induction_or_inversion(proof, goal, env, is_inversion=True)

def _check_rule_induction_or_inversion(
    proof: RuleInduction | RuleInversion,
    goal: CheckedFormula,
    env: Env,
    is_inversion: bool,
) -> None:
  loc = proof.location
  pred_name_in = proof.hyp_name  # the predicate name after the keyword
  ri_cases = proof.cases
  keyword_phrase = 'rule inversion' if is_inversion else 'rule induction'

  # Strip outer `all` quantifiers and the `if pred(xs) then ...` from
  # the goal.
  binders = []
  rest = goal
  while isinstance(rest, All):
    binders.append(rest.var)
    rest = rest.body
  if not isinstance(rest, IfThen):
    user_error(loc, keyword_phrase + " expects a goal of the form "
          "'all xs. if <pred>(xs) then Q(xs)', got '" + str(goal) + "'")
  pred_call = rest.premise
  q_formula = rest.conclusion
  if not isinstance(pred_call, Call):
    user_error(loc, keyword_phrase + " expects the goal's premise to be a call "
          "to the predicate, got '" + str(pred_call) + "'")

  rator = pred_call.rator
  rator_callable_name = callable_name(rator)
  if rator_callable_name != pred_name_in:
    user_error(loc, keyword_phrase + " over '" + base_name(pred_name_in)
          + "' but the goal's premise is a call to '"
          + str(rator) + "'")
  pred_decl = get_predicate_decl(rator_callable_name)
  if pred_decl is None:
    user_error(loc, keyword_phrase + ": '" + base_name(rator_callable_name)
          + "' is not a predicate or relation declared with the "
          "'predicate' or 'relation' keyword")

  # The args of the goal's `pred(xs)` should be the binders' Vars, in
  # order. They give us the motive parameters.
  args = pred_call.args
  arg_names = []
  for a in args:
    if not isinstance(a, VarRef):
      user_error(loc, keyword_phrase + ": predicate arguments in the goal "
            "must be plain variables (got '" + str(a) + "')")
    arg_names.append(a.get_name())
  if len(set(arg_names)) != len(arg_names):
    user_error(loc, keyword_phrase + ": duplicate predicate argument vars in "
          "the goal (motive inference does not yet handle this)")

  arity = len(args)
  param_types = []
  if isinstance(pred_decl.signature, FunctionType):
    param_types = pred_decl.signature.param_types

  # Match user case names to predicate rule names.
  rule_unique_names = [r.name for r in pred_decl.rules]
  user_cases_by_rule = {}
  for c in ri_cases:
    if c.rule_name not in rule_unique_names:
      base = base_name(c.rule_name)
      user_error(c.location,
            keyword_phrase + ": '" + base
            + "' is not a rule of predicate '"
            + base_name(rator_callable_name) + "'")
    if c.rule_name in user_cases_by_rule:
      user_error(c.location,
            keyword_phrase + ": duplicate case for rule '"
            + base_name(c.rule_name) + "'")
    user_cases_by_rule[c.rule_name] = c
  missing = [base_name(rn) for rn in rule_unique_names
             if rn not in user_cases_by_rule]
  if missing:
    user_error(loc, keyword_phrase + ": missing case"
          + ('s' if len(missing) > 1 else '')
          + " for rule" + ('s' if len(missing) > 1 else '') + ": "
          + ', '.join(missing))

  # Build the motive as a lambda whose binders match the goal's outer
  # `all` binders (renaming if needed for cleanliness). The body is the
  # goal's `Q(xs)` with arg-vars left intact (since they're the lambda's
  # own binders).
  motive = Lambda(loc, None,
                  [(arg_names[i], param_types[i].copy())
                   for i in range(arity)],
                  q_formula.copy())

  thm_name = pred_decl.rule_inversion_name if is_inversion \
             else pred_decl.rule_induction_name
  thm_proof = PVar(loc, thm_name)
  with_motive = AllElim(loc, thm_proof, motive, (0, 1))
  case_proofs = [user_cases_by_rule[rn].body
                 for rn in rule_unique_names]
  if len(case_proofs) == 1:
    rules_proof = case_proofs[0]
  else:
    rules_proof = PTuple(loc, case_proofs)
  desugared = ModusPonens(loc, with_motive, rules_proof)

  _try_check_proof_of(desugared, goal, env)

def _check_proof_of_hole(proof: PHole, formula: CheckedFormula, env: Env) -> None:
  loc = proof.location
  new_formula = check_formula(remove_mark(formula), env)
  # Uncommented by i ran into a proof where I had to prove
  # (A = A or A = B) which should have just reduced to A = A
  # but it didn't.
  # new_formula = new_formula.reduce(env)
  target = get_target_hole_location()
  if target is not None and (loc.line, loc.column) != target:
    return
  advice = proof_advice(new_formula, env)
  givens = givens_str(env)
  if not givens:
    advice = advice.rstrip('\n')
  add_incomplete(loc, style.bold_red('incomplete proof') + '\n' \
                   + style.orange('Goal:') + '\n\t' + str(new_formula) + '\n'\
                   + advice \
                   + givens,
                   formula=new_formula, env=env)

def _check_proof_of_sorry(proof: PSorry, formula: CheckedFormula, env: Env) -> None:
  warning(proof.location, 'unfinished proof')

def _check_proof_of_reflexive(proof: PReflexive, formula: CheckedFormula, env: Env) -> None:
  match formula:
    case Call(_, _, rator, [lhs, rhs]) if isinstance(rator, VarRef) and rator.get_name() == '=':
      lhsNF = lhs.reduce(env)
      rhsNF = rhs.reduce(env)
      if lhsNF != rhsNF:
        (small_lhs, small_rhs) = isolate_difference(lhsNF, rhsNF)
        msg = 'error in proof by reflexive:\n'
        if small_lhs == lhsNF:
          msg = msg + str(lhsNF) + ' ≠ ' + str(rhsNF)
        else:
          msg = msg + str(small_lhs) + ' ≠ ' + str(small_rhs) + '\n' \
            + 'therefore\n' + str(lhsNF) + ' ≠ ' + str(rhsNF)
        user_error(proof.location, msg + '\n' + givens_str(env))
    case _:
      add_diagnostic(proof.location,
                     'reflexive proves an equality, not\n\t' \
                     + str(formula) \
                     + givens_str(env))

def _check_proof_of_symmetric(proof: PSymmetric, formula: CheckedFormula, env: Env) -> None:
  loc = proof.location
  (a,b) = split_equation(loc, formula, env)
  flip_formula = mkEqual(loc, b, a)
  _try_check_proof_of(proof.body, flip_formula, env)

def _check_proof_of_transitive(proof: PTransitive, formula: CheckedFormula, env: Env) -> None:
  loc = proof.location
  (a1,c) = split_equation(loc, formula, env)

  eq1 = check_proof(proof.first, env)
  (a2,b) = split_equation(loc, eq1, env)

  _try_check_proof_of(proof.second, mkEqual(loc, b, c), env)

  a1r = a1.reduce(env)
  a2r = a2.reduce(env)
  if remove_mark(a1r) != remove_mark(a2r):
    add_diagnostic(loc, 'for transitive, from proofs of\n'
          + '\t' + str(eq1) + '\n'
          + 'and\n'
          + '\t' + str(b) + ' = ' + str(c) + '\n'
          + 'the transitive rule concludes\n\t' + str(a2) + ' = ' + str(c) + '\n'
          + 'but that does not match the goal\n\t' + str(formula) + '\n'
          + givens_str(env))

def _check_proof_of_extensionality(proof: PExtensionality, formula: CheckedFormula, env: Env) -> None:
  loc = proof.location
  (lhs,rhs) = split_equation(loc, formula, env)
  match lhs.typeof:
    case FunctionType(_, [], typs, _):
      names = [generate_proof_name('x') for ty in typs]
      args = [ResolvedVar(loc, None, x) for x in names]
      call_lhs = Call(loc, None, lhs, args)
      call_rhs = Call(loc, None, rhs, args)
      formula = mkEqual(loc, call_lhs, call_rhs)
      for i, v in enumerate(reversed(list(zip(names, typs)))):
        formula = All(loc, None, v, (i, len(names)), formula)
      _try_check_proof_of(proof.body, formula, env)
    case FunctionType(_, ty_params, _, _):
      add_diagnostic(loc, 'extensionality expects function without any type parameters, not ' + str(len(ty_params))
            + givens_str(env))
    case _:
      add_diagnostic(loc, 'extensionality expects a function, not ' + str(lhs.typeof)
            + givens_str(env))

def _check_proof_of_evaluate_goal(proof: EvaluateGoal, formula: CheckedFormula, env: Env) -> None:
  loc = proof.location
  set_reduce_all(True)
  set_dont_reduce_opaque(True)
  red_formula = remove_mark(formula).reduce(env)
  set_reduce_all(False)
  set_dont_reduce_opaque(False)
  if red_formula != Bool(loc, None, True):
    add_diagnostic(loc, 'the goal did not evaluate to `true`, but instead:\n\t' \
          + str(red_formula)
          + givens_str(env))

def _missing_period_after_tactic(tactic_loc: Meta, body: Proof,
                                 residual: CheckedFormula,
                                 tactic: str, env: Env) -> bool:
  # When a tactic-style goal (`replace` / `expand` / `simplify`) has a
  # `PHole` body and the residual reduces to `true`, the user is one
  # period away from a valid proof. The generic `PHole` diagnostic
  # reports `Goal: true` with the equally generic advice "prove `true`
  # with a period," which is correct but doesn't point at the tactic
  # that produced the tautology -- in an `equations` chain especially,
  # the body location reads as the next step's boundary and the user
  # has to figure out which step is missing the period. Emit a
  # targeted hint anchored at the tactic itself and return `True` so
  # the caller skips the generic path.
  if not isinstance(body, PHole):
    return False
  reduced = remove_mark(residual).reduce(env)
  if not (isinstance(reduced, Bool) and reduced.value is True):
    return False
  add_incomplete(tactic_loc,
    style.bold_red('incomplete proof') + '\n'
    + 'the `' + tactic + '` already reduced the goal to `true`.\n'
    + style.dark_green('Advice:') + '\n'
    + '\tAdd a trailing `.` after `' + tactic
    + '` (e.g. `by ' + tactic + ' ... .`) to close this step.\n'
    + givens_str(env),
    formula=reduced, env=env)
  return True

def _check_proof_of_rewrite_goal(proof: RewriteGoal, formula: CheckedFormula, env: Env) -> None:
  loc = proof.location
  equations = [check_proof(proof, env) for proof in proof.equations]
  eqns = [equation.reduce(env) for equation in equations]
  new_formula = formula.reduce(env)
  new_formula = apply_rewrites(loc, new_formula, eqns, env,
                               display_formula=formula,
                               display_eqns=equations)
  if _missing_period_after_tactic(loc, proof.body, new_formula, 'replace', env):
    return
  _try_check_proof_of(proof.body, new_formula, env)

def _check_proof_of_simplify_goal(proof: SimplifyGoal, formula: CheckedFormula, env: Env) -> None:
  loc = proof.location
  preds = [check_proof(proof, env) for proof in proof.givens]
  equations = [pred_to_equality(loc, p) for p in preds]
  eqns = [equation.reduce(env) for equation in equations]
  new_formula = apply_rewrites(loc, formula, eqns, env,
                               display_eqns=equations)
  new_formula = new_formula.reduce(env)
  if _missing_period_after_tactic(loc, proof.body, new_formula, 'simplify', env):
    return
  _try_check_proof_of(proof.body, new_formula, env)

def _check_proof_of_apply_defs_goal(proof: ApplyDefsGoal, formula: CheckedFormula, env: Env) -> None:
  loc = proof.location
  new_formula = expand_definitions(loc, formula, proof.definitions, env)
  red_formula = new_formula.reduce(env)
  if _missing_period_after_tactic(loc, proof.body, red_formula, 'expand', env):
    return
  sink = get_active_sink()
  before_len = len(sink.errors) if sink is not None else 0
  try:
    _try_check_proof_of(proof.body, red_formula, env)
  except UserError as e:
    hint = expand_residual_hint(red_formula, proof.definitions, env,
                                original=formula)
    if hint:
      raise wrap_user_error(e, hint) from e
    raise
  # Sink path: _try_check_proof_of swallows the exception into the sink
  # and returns normally, so the except clause above never fires. Walk
  # any entries it added during this call and attach the same hint so
  # collect_errors mode (MCP / LSP) sees the helpful tail the CLI gets.
  if sink is not None and len(sink.errors) > before_len:
    hint = expand_residual_hint(red_formula, proof.definitions, env,
                                original=formula)
    if hint:
      for i in range(before_len, len(sink.errors)):
        entry = sink.errors[i]
        if isinstance(entry, UserError):
          sink.errors[i] = wrap_user_error(entry, hint)

def _check_proof_of_all_intro(proof: AllIntro, formula: CheckedFormula, env: Env) -> None:
  loc = proof.location
  var = proof.var
  body = proof.body
  x, ty = var
  checked_ty = check_type(ty, env)

  if isinstance(formula, TLet):
    formula = formula.reduceLets(env)

  match formula:
    case All(_, _, var2, (s, _), formula2):
      _, ty2 = var2
      if checked_ty != ty2:
        add_diagnostic(loc, "arbitrary expects " + base_name(x)
              + " to have type\n\t" + str(ty2)
              + "\nbut got type\n\t" + str(ty))
        return
      sub = {}
      sub[ var2[0] ] = OverloadedVar(loc, checked_ty, [ var[0] ])

      frm2 = formula2.substitute(sub)

      if s != 0:
        frm2 = update_all_head(frm2)

      body_env = env.declare_term_vars(loc, [(x, checked_ty)])
      _try_check_proof_of(body, frm2, body_env)
    case _:
      add_diagnostic(loc, 'arbitrary is proof of an all formula, not\n' \
            + str(formula)
            + givens_str(env))

def _check_proof_of_some_intro(proof: SomeIntro, formula: CheckedFormula, env: Env) -> None:
  loc = proof.location
  # room for improvement, if var has type annotation, could type_check the witness
  witnesses = [type_synth_term(trm, env, None, []) for trm in proof.witnesses]

  if isinstance(formula, TLet):
    formula = formula.reduceLets(env)

  match formula:
    case Some(_, _, vars, formula2):
      sub = {var[0]: trm for (var,trm) in zip(vars, witnesses) }
      body_frm = formula2.substitute(sub)
      _try_check_proof_of(proof.body, body_frm, env)
    case _:
      add_diagnostic(loc, "choose expects the goal to start with 'some', not " + str(formula)
            + givens_str(env))

def _check_proof_of_some_elim(proof: SomeElim, formula: CheckedFormula, env: Env) -> None:
  loc = proof.location
  someFormula = check_proof(proof.some, env)

  if isinstance(someFormula, TLet):
    someFormula = someFormula.reduceLets(env)

  match someFormula:
    case Some(loc2, _, vars, formula2):
      sub = {var[0]: ResolvedVar(loc2, None, x) for (var,x) in zip(vars,proof.witnesses)}
      witnessFormula = formula2.substitute(sub)

      witnesses_types = [(x,var[1]) for (var,x) in zip(vars,proof.witnesses)]
      body_env = env.declare_term_vars(loc, witnesses_types)
      if proof.prop:
        prop = check_formula(proof.prop, body_env)
        check_implies(loc, witnessFormula.reduce(env), prop.reduce(body_env))
      else:
        prop = witnessFormula
      body_env = body_env.declare_local_proof_var(loc, proof.label, prop)
      _try_check_proof_of(proof.body, formula, body_env)
    case _:
      add_diagnostic(loc, "obtain expects 'from' to be a proof of a 'some' formula, not " + str(someFormula)
            + givens_str(env))

def _check_proof_of_imp_intro(proof: ImpIntro, formula: CheckedFormula, env: Env) -> None:
  loc = proof.location

  if proof.premise is None:
    if isinstance(formula, TLet):
      formula = formula.reduceLets(env)

    match formula:
      case IfThen(_, _, prem, conc):
        body_env = env.declare_local_proof_var(loc, proof.label, prem)
        _try_check_proof_of(proof.body, conc, body_env)
      case _:
        add_diagnostic(proof.location, 'expected proof of ' + str(formula) + \
              '\n\tnot a proof of if-then: ' + str(proof)
              + givens_str(env))
    return

  new_prem1 = check_formula(proof.premise, env)
  match formula:
    case IfThen(_, _, prem2, conc):
      prem1_red = new_prem1.reduce(env)
      prem2_red = prem2.reduce(env)
      if prem1_red != prem2_red:
        (small1, small2) = isolate_difference(prem1_red, prem2_red)
        msg = str(prem1_red) + ' ≠ ' + str(prem2_red) + '\n' \
            + 'because\n' + str(small1) + ' ≠ ' + str(small2)
        add_diagnostic(loc, 'mismatch in premise:\n' + msg
            + givens_str(env))
      body_env = env.declare_local_proof_var(loc, proof.label, new_prem1)
      _try_check_proof_of(proof.body, conc, body_env)
    case _:
      add_diagnostic(proof.location, 'the assume statement is for if-then formula, not ' + str(formula)
            + givens_str(env))

def _check_proof_of_tlet_new(proof: PTLetNew, formula: CheckedFormula, env: Env) -> None:
  loc = proof.location
  new_rhs = type_synth_term(proof.rhs, env, None, [])
  body_env = env.define_term_var(loc, proof.var, new_rhs.typeof, new_rhs)
  equation = mkEqual(loc, new_rhs, ResolvedVar(loc, None, proof.var)).reduce(env)
  red_formula = formula.reduce(env)
  if get_verbose():
      print('define ' + str(proof.var) + '\n\trewrite with ' + str(equation) + '\n\tin ' \
            + str(red_formula))
  frm = rewrite(loc, red_formula, equation, env)
  new_body_env = Env({k: ProofBinding(b.location, \
                                      rewrite(loc, b.formula, equation, env), \
                                      b.local, module=env.get_current_module()) \
                      if isinstance(b, ProofBinding) else b \
                       for (k,b) in body_env.dict.items()})
  _try_check_proof_of(proof.body, frm, new_body_env)

def _check_proof_of_let(proof: PLet, formula: CheckedFormula, env: Env) -> None:
  loc = proof.location
  new_frm = check_formula(proof.proved, env)
  match new_frm:
    case Hole(_, _):
      proved_formula = check_proof(proof.because, env)
      warning(loc, "\nhave " + base_name(proof.label) + ':\n\t' + str(proved_formula))
      body_env = env.declare_local_proof_var(loc, proof.label, proved_formula)
    case _:
      _try_check_proof_of(proof.because, new_frm, env)
      body_env = env.declare_local_proof_var(loc, proof.label, remove_mark(new_frm))
  _try_check_proof_of(proof.body, formula, body_env)

def _check_proof_of_annot(proof: PAnnot, formula: CheckedFormula, env: Env) -> None:
  loc = proof.location
  new_claim = check_formula(proof.claim, env)
  match new_claim:
    case Hole(_, _):
      _try_check_proof_of(proof.body, formula, env)
      add_diagnostic(loc, '\nneed to show:\n\t' + str(formula)
            + givens_str(env))
    case _:
      claim_red = new_claim.reduce(env)
      formula_red = formula.reduce(env)
      check_implies(loc, remove_mark(claim_red).reduce(env),
                    remove_mark(formula_red).reduce(env))
      _try_check_proof_of(proof.body, claim_red, env)

def _check_proof_of_tuple(proof: PTuple, formula: CheckedFormula, env: Env) -> None:
  loc = proof.location
  try:
    with speculative_probe():
      red_formula = formula.reduce(env)
      match red_formula:
        case And(_, _, frms):
          for (frm,pf) in zip(frms, proof.args):
            check_proof_of(pf, frm, env)
          if len(proof.args) < len(frms):
            incomplete_error(loc, 'expected ' + str(len(frms)) + ' proofs but only got '\
                             + str(len(proof.args)))
        case _:
          user_error(loc, 'comma proves logical-and, not ' + str(red_formula))
  except IncompleteProof as ex:
    raise ex
  except UserError as ex1:
    try:
      with speculative_probe():
        form = check_proof(proof, env)
        form_red = form.reduce(env)
        formula_red = formula.reduce(env)
        check_implies(proof.location, form_red, remove_mark(formula_red))
    except UserError as ex2:
      add_diagnostic(loc, 'failed to prove: ' + str(formula) + '\n' \
            + '\tfirst tried each subproof in goal-directed mode, but:\n' \
            + str(ex1) + '\n' \
            + '\tthen tried synthesis mode, but:\n'\
            + str(ex2)
            + givens_str(env))

def _check_proof_of_cases(proof: Cases, formula: CheckedFormula, env: Env) -> None:
  loc = proof.location
  sub_frm = check_proof(proof.subject, env)

  # sub_red = sub_frm.reduce(env)
  sub_red = sub_frm
  if isinstance(sub_frm, TLet):
    sub_red = sub_frm.reduceLets(env)

  match sub_red:
    case Or(_, _, frms):
      if len(proof.cases) < len(frms):
          add_diagnostic(loc, "expected " + str(len(frms)) + " cases, not " + str(len(proof.cases))
                + givens_str(env))
      for (frm, (label,frm2,the_case)) in zip(frms, proof.cases):
        if frm2:
            new_frm2 = check_formula(frm2, env)
        if frm2 and (frm != new_frm2): # was frm != red_frm2
          add_diagnostic(loc, 'case ' + str(new_frm2) + '\ndoes not match alternative in goal: \n' + str(frm)
                + givens_str(env))
        body_env = env.declare_local_proof_var(loc, label, frm)
        _try_check_proof_of(the_case, formula, body_env)
    case _:
      add_diagnostic(proof.location, "expected 'or', not " + str(sub_red)
            + givens_str(env))

def _check_proof_of_suffices(proof: Suffices, formula: CheckedFormula, env: Env) -> None:
  loc = proof.location
  claim = proof.claim
  reason = proof.reason
  rest = proof.body
  evaluate = False

  match reason:
    case EvaluateGoal(_):
       evaluate = True

  if evaluate:
    new_claim = type_check_term(claim, BoolType(loc), env, None, [])
    set_reduce_all(True)
    set_dont_reduce_opaque(True)
    new_formula = formula.reduce(env)
    red_claim = new_claim.reduce(env)
    set_reduce_all(False)
    set_dont_reduce_opaque(False)

    match red_claim:
      case Omitted(_, _):
        _try_check_proof_of(rest, new_formula, env)
      case Hole(loc2, _):
        newer_formula = check_formula(new_formula, env)
        warning(loc, '\nsuffices to prove:\n\t' + str(newer_formula))
        check_proof_of(rest, newer_formula, env)
      case _:
        try:
          check_implies(loc, red_claim, new_formula)
        except UserError as e:
          raise wrap_user_error(e, '\n' + style.orange('Givens:') + '\n' + env.proofs_str()) from e
        _try_check_proof_of(rest, new_claim, env)
    return

  new_claim = type_check_term(claim, BoolType(loc), env, None, [])
  claim_red = new_claim.reduce(env)

  match claim_red:
    case Hole(loc2, _):
      proved_formula = check_proof(reason, env)
      match proved_formula:
        case IfThen(_, _, prem, conc):
          check_implies(loc, conc, formula)
          warning(loc2, '\nsuffices to prove:\n\t' + str(prem))
          _try_check_proof_of(rest, prem, env)
        case _:
          add_diagnostic(loc, 'expected a proof of an "if"-"then" formula, not ' + str(proved_formula)
                + givens_str(env))
    case Omitted(_, _):
      proved_formula = check_proof(reason, env)
      match proved_formula:
        case IfThen(_, _, prem, conc):
          check_implies(loc, conc, formula)
          _try_check_proof_of(rest, prem, env)
        case _:
          add_diagnostic(loc, 'expected a proof of an "if"-"then" formula, not ' + str(proved_formula)
                + givens_str(env))
    case _:
      imp = IfThen(loc, BoolType(loc), claim_red, formula).reduce(env)
      _try_check_proof_of(reason, imp, env)
      _try_check_proof_of(rest, claim_red, env)

def _check_proof_of_induction(proof: Induction, formula: CheckedFormula, env: Env) -> None:
  loc = proof.location
  typ = check_type(proof.typ, env)
  cases = proof.cases

  if isinstance(formula, TLet):
    formula = formula.reduceLets(env)
  match formula:
    case All(_, _, (_,ty), _, _):
      if typ != ty:
        add_diagnostic(loc, "type of induction: " + str(typ) \
              + "\ndoes not match the all-formula's type: " + str(ty)
              + givens_str(env))
    case _:
      add_diagnostic(loc, 'induction expected an all-formula, not ' + str(formula)
            + givens_str(env))

  # TODO: Allow for specification of what type to use
  custom_ind = env.get_inductive(typ)

  view_match = _bijective_view_for_source_type(loc, typ, env)
  if view_match is not None:
    view, source_ty, view_target_ty, view_type_args = view_match
    view_alts = lookup_union(loc, view_target_ty, env).alternatives
    if any(_switch_pattern_could_match_alts(c.pattern, view_alts)
           for c in cases):
      _check_induction_via_view(loc, typ, cast(All, formula), cases, view,
                                source_ty, view_target_ty, view_type_args,
                                custom_ind, env)
      return

  if custom_ind:
    if get_verbose():
      print(f"Using custom induction for type {typ}")
    _check_induction_via_custom_induction(loc, typ, cast(All, formula),
                                          cases, custom_ind, env)
  else:
    match env.get_def_of_type_var(get_type_name(typ)):
      case Union(_, name, typarams, alts):
        if len(cases) != len(alts):
          add_diagnostic(loc, 'expected ' + str(len(alts)) + ' cases for induction' \
                + ', but only have ' + str(len(cases))
                + givens_str(env))
        cases_present: dict[str, bool] = {}
        for (constr,indcase) in zip(alts, cases):
          check_pattern(indcase.pattern, typ, env, cases_present)
          if get_verbose():
              print('\nCase ' + str(indcase.pattern))
          if indcase.pattern.constructor.name != constr.name:
            add_diagnostic(indcase.location, "expected a case for " + str(base_name(constr.name)) \
                  + " not " + str(base_name(indcase.pattern.constructor.name))
                  + givens_str(env))
          if len(indcase.pattern.parameters) != len(constr.parameters):
            add_diagnostic(indcase.location, "expected " + str(len(constr.parameters)) \
                  + " arguments to " + base_name(constr.name) \
                  + " not " + str(len(indcase.pattern.parameters))
                  + givens_str(env))
          induction_hypotheses = [instantiate(loc, formula,
                                              ResolvedVar(loc,None, param))
                                  for (param, ty) in
                                  zip(indcase.pattern.parameters,
                                      constr.parameters)
                                  if is_recursive(name, ty)]
          body_env = env

          if len(typarams) > 0:
            sub = { T: ty for (T,ty) in zip(typarams, typ.arg_types)}
            parameter_types = [p.substitute(sub) for p in constr.parameters]
          else:
            parameter_types = constr.parameters
          body_env = body_env.declare_term_vars(loc,
                                                zip(indcase.pattern.parameters,
                                                    parameter_types),
                                                True)

          trm = pattern_to_term(indcase.pattern)
          new_trm = type_check_term(trm, typ, body_env, None, [])
          if isinstance(new_trm, TermInst):
              new_trm.inferred = False
          pre_goal = instantiate(loc, formula, new_trm)
          goal = check_formula(pre_goal, body_env)

          # fill the rest of the given induction_hypotheses with _ labels
          for i in range(len(indcase.induction_hypotheses), len(induction_hypotheses)):
            indcase.induction_hypotheses.append((generate_proof_name('_'), None))

          for ((x,frm1),frm2) in zip(indcase.induction_hypotheses, induction_hypotheses):
            if frm1 != None:
              new_frm1 = check_formula(frm1, body_env)
              if new_frm1 != frm2:
                (small_frm1,small_frm2) = isolate_difference(new_frm1, frm2)
                msg = 'incorrect induction hypothesis, expected\n' \
                    + str(frm2) + '\nbut got\n' + str(new_frm1) \
                    + '\nin particular\n' + str(small_frm1) + '\n≠\n' + str(small_frm2)
                add_diagnostic(frm1.location, msg
                      + givens_str(body_env))
            body_env = body_env.declare_local_proof_var(loc, x, frm2)

          _try_check_proof_of(indcase.body, goal, body_env)
      case blah:
        add_diagnostic(loc, "induction expected name of union, not " + str(typ)
              + '\nwhich resolves to\n' + str(blah) + '\nin ' + str(env))

def _check_proof_of_switch(proof: SwitchProof, formula: CheckedFormula, env: Env) -> None:
  loc = proof.location
  new_subject = type_synth_term(proof.subject, env, None, [])
  cases = proof.cases
  ty = new_subject.typeof
  match ty:
    case BoolType(_):
      # check exhaustiveness
      has_true_case = False
      has_false_case = False
      for scase in cases:
        match scase.pattern:
          case PatternBool(_, True):
            has_true_case = True
          case PatternBool(_, False):
            has_false_case = True
          case _:
            internal_error(loc, 'unhandled case in switch proof')
      if not has_true_case:
        add_diagnostic(loc, 'missing case for true'
            + givens_str(env))
      if not has_false_case:
        add_diagnostic(loc, 'missing case for false'
            + givens_str(env))

      # check each case
      for scase in cases:
        if not isinstance(scase.pattern, PatternBool):
          add_diagnostic(scase.location, "expected pattern 'true' or 'false' in switch on bool"
                + givens_str(env))

        subject_case = Bool(scase.location, BoolType(scase.location), True) if scase.pattern.value \
                       else Bool(scase.location, BoolType(scase.location), False)
        equation = mkEqual(scase.location, new_subject, subject_case)
        predicate = new_subject if scase.pattern.value \
                                else IfThen(loc, None, new_subject, Bool(loc, None, False))

        body_env = env

        if len(scase.assumptions) == 0:
              scase.assumptions.append((generate_proof_name('_'), None))

        assumptions = [(label, check_formula(asm, body_env) if asm else None) for (label,asm) in scase.assumptions]
        if len(assumptions) == 1:
          if assumptions[0][1] != None and assumptions[0][1] != predicate:
            subject_str = str(new_subject)
            msg = 'expected assumption\n' + str(predicate) \
                + '\nbut got\n' + str(assumptions[0][1]) \
                + '\n\nIn a `switch <expr>` where `<expr>` is a boolean,' \
                + ' `case true` introduces\nan assumption of formula `<expr>`' \
                + ' directly (here: `' + subject_str + '`), not' \
                + ' `<expr> = true`.\n`case false` introduces `not <expr>`.'
            add_diagnostic(scase.location, msg
                  + givens_str(env))
          body_env = body_env.declare_local_proof_var(loc, assumptions[0][0], predicate)

        if len(assumptions) > 1:
          add_diagnostic(scase.location, 'only one assumption is allowed in a switch case'
                + givens_str(env))
        frm = rewrite(loc, formula.reduce(env), equation.reduce(env), env)
        new_frm = frm.reduce(env)
        _try_check_proof_of(scase.body, new_frm, body_env)
    case TypeType(_):
      # As far as I know, it is not possible to switch on a type
      add_diagnostic(loc, "In 'switch' expected a term, got " + str(new_subject)
            + givens_str(env))
    case _:
      tname = get_type_name(ty)
      match env.get_def_of_type_var(tname):
        case Union(_, _, typarams, alts):
          # Prefer a bijective view when the cases are written against
          # the view target constructors. This is the public UInt path:
          # `case zero` / `case suc(m)` are handled by the view before
          # any custom-induction fallback is considered.
          view_match = _bijective_view_for_source_type(loc, ty, env)
          if view_match is not None:
            view, _, view_target_ty, view_type_args = view_match
            view_alts = lookup_union(loc, view_target_ty, env).alternatives
            if any(_switch_pattern_could_match_alts(c.pattern, view_alts)
                   for c in cases):
              _check_switch_via_view(loc, new_subject, formula, cases, ty,
                                     view, view_target_ty, view_type_args,
                                     env)
              return

          # If the type has a custom induction theorem and a case
          # misses both the view target constructors and the underlying
          # union constructors, fall back to the custom-induction path.
          # UInt keeps this hook as the support theorem for recursive
          # view induction and for legacy theorem-shaped cases such as
          # `case 0` / `case with m. 1 + m`.
          custom_ind = env.get_inductive(ty)
          if custom_ind is not None and any(
              not _switch_pattern_could_match_alts(c.pattern, alts)
              for c in cases):
            _check_switch_via_custom_induction(loc, new_subject, formula,
                                               cases, ty, custom_ind, env)
            return
          if len(cases) != len(alts):
            alt_name_list = [base_name(c.name) for c in alts]
            def case_pattern_name(p: object) -> str:
              if isinstance(p, PatternCons) and isinstance(p.constructor, Var):
                return cast(str, base_name(p.constructor.name))
              return str(p)
            present_names = [case_pattern_name(c.pattern) for c in cases]
            present_set = set(present_names)
            missing = [n for n in alt_name_list if n not in present_set]
            extras = [n for n in present_names if n not in set(alt_name_list)]
            suffix_parts = []
            if missing:
              suffix_parts.append('missing: ' + ', '.join(missing))
            if extras:
              suffix_parts.append('unexpected: ' + ', '.join(extras))
            if not suffix_parts:
              suffix_parts.append('got ' + str(len(cases)))
            add_diagnostic(loc, 'expected ' + str(len(alts)) + ' cases in switch ('
                  + ', '.join(alt_name_list) + '), ' + '; '.join(suffix_parts)
                  + givens_str(env))
          cases_present: dict[str, bool] = {}
          for (constr,scase) in zip(alts, cases):
            check_pattern(scase.pattern, ty, env, cases_present)
            if scase.pattern.constructor.name != constr.name:
              add_diagnostic(scase.location, "expected a case for " + str(constr) \
                    + " not " + str(scase.pattern.constructor)
                    + givens_str(env))
            if len(scase.pattern.parameters) != len(constr.parameters):
              add_diagnostic(scase.location, "expected " + str(len(constr.parameters)) \
                    + " arguments to " + base_name(constr.name) \
                    + " not " + str(len(scase.pattern.parameters))
                    + givens_str(env))
            subject_case = pattern_to_term(scase.pattern)
            body_env = env

            tyargs = get_type_args(ty)
            sub = {T:ty for (T,ty) in zip(typarams, tyargs)}
            constr_params = [ty.substitute(sub) for ty in constr.parameters]
            body_env = body_env.declare_term_vars(loc, zip(scase.pattern.parameters,
                                                           constr_params))

            new_subject_case = type_check_term(subject_case, ty, body_env, None, [])
            if isinstance(new_subject_case, TermInst):
                new_subject_case.inferred = False

            if len(scase.assumptions) == 0:
              scase.assumptions.append((generate_proof_name('_'), None))

            assumptions = [(label,check_formula(asm, body_env) if asm else None) for (label,asm) in scase.assumptions]
            if len(assumptions) == 1:
              assumption = mkEqual(scase.location, new_subject, subject_case)
              new_assumption = type_synth_term(assumption, body_env, None, [])
              if assumptions[0][1] != None:
                  case_assumption = type_synth_term(assumptions[0][1], body_env, None, [])
                  if case_assumption != new_assumption:
                      add_diagnostic(scase.location, 'in case, expected assume of\n' + str(new_assumption) \
                            + '\nnot\n' + str(case_assumption)
                            + givens_str(body_env))
              body_env = body_env.declare_local_proof_var(loc, assumptions[0][0], new_assumption)
            if len(assumptions) > 1:
              add_diagnostic(scase.location, 'only one assumption is allowed in a switch case'
                    + givens_str(body_env))

            if isinstance(new_subject, VarRef):
              frm = formula.substitute({new_subject.name: new_subject_case})
            else:
              frm = formula
            red_frm = frm.reduce(body_env)
            _try_check_proof_of(scase.body, red_frm, body_env)
        case _:
          add_diagnostic(loc, "switch expected union type or bool, not " + str(ty)
                + givens_str(env))

def _check_synthesized_proof_against_goal(
    proof: Proof,
    formula: CheckedFormula,
    env: Env,
) -> None:
  try:
    form = check_proof(proof, env)
    form_red = form.reduce(env)
    formula_red = remove_mark(formula).reduce(env)
    check_implies(proof.location, form_red, formula_red)
  except IncompleteProof as e:
    raise e
  except UserError as e:
    # It could be that form is never reduced, such as in a PHelpUse.
    # In that case, we don't give 'replace' advice.
    extra_advice = ''
    try:
      if is_equation(form_red):
        extra_advice = '\nDid you mean `replace ' + str(proof) + '`?'
      else:
        extra_advice = ground_goal_evaluate_hint(form_red, formula_red, env)
    finally:
      raise wrap_user_error(e, extra_advice) from e

def _check_proof_of_goal_agnostic(proof: Proof, formula: CheckedFormula, env: Env) -> None:
  return _check_synthesized_proof_against_goal(proof, formula, env)

_GOAL_AGNOSTIC_PROOF_TYPES = {
  PRecall,
  PVar,
  PTrue,
  PAndElim,
  EvaluateFact,
  ApplyDefsFact,
  RewriteFact,
  SimplifyFact,
  PHelpUse,
  AllElim,
  AllElimTypes,
  ModusPonens,
  PInjective,
}

_CHECK_PROOF_OF_GOAL_AGNOSTIC_HANDLERS = {
  proof_type: _check_proof_of_goal_agnostic
  for proof_type in _GOAL_AGNOSTIC_PROOF_TYPES
}

_CHECK_PROOF_OF_HANDLERS = {
  **_CHECK_PROOF_OF_GOAL_AGNOSTIC_HANDLERS,
  PHole: _check_proof_of_hole,
  PSorry: _check_proof_of_sorry,
  PReflexive: _check_proof_of_reflexive,
  PSymmetric: _check_proof_of_symmetric,
  PTransitive: _check_proof_of_transitive,
  PExtensionality: _check_proof_of_extensionality,
  EvaluateGoal: _check_proof_of_evaluate_goal,
  RewriteGoal: _check_proof_of_rewrite_goal,
  SimplifyGoal: _check_proof_of_simplify_goal,
  ApplyDefsGoal: _check_proof_of_apply_defs_goal,
  AllIntro: _check_proof_of_all_intro,
  SomeIntro: _check_proof_of_some_intro,
  SomeElim: _check_proof_of_some_elim,
  ImpIntro: _check_proof_of_imp_intro,
  PTLetNew: _check_proof_of_tlet_new,
  PLet: _check_proof_of_let,
  PAnnot: _check_proof_of_annot,
  PTuple: _check_proof_of_tuple,
  Cases: _check_proof_of_cases,
  Induction: _check_proof_of_induction,
  SwitchProof: _check_proof_of_switch,
  Suffices: _check_proof_of_suffices,
  RuleInduction: _check_rule_induction,
  RuleInversion: _check_rule_inversion,
}

def check_proof_of(proof: Proof, formula: CheckedFormula, env: Env) -> None:
  if get_verbose():
    print('check_proof_of: ' + str(formula) + '?')
    print('\t' + str(proof))
  handler = _CHECK_PROOF_OF_HANDLERS.get(type(proof))
  if handler is not None:
    return handler(proof, formula, env)
  match proof:
    case _:
      return _check_synthesized_proof_against_goal(proof, formula, env)
