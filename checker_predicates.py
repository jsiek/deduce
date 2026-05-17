"""Predicate/relation validation and lowering.

File charter:
- Put code here when it validates predicate signatures or rules, checks
  predicate strict positivity, decomposes predicate premises, or builds the
  generated derivation unions, intro theorems, validators, rule induction, or
  rule inversion declarations.
- Keep the decision about when generated declarations enter the main pipeline
  in ``checker_pipeline.py``; this module should build and validate predicate
  artifacts, not run the whole checker over them.
- Predicate-generated proof AST construction belongs here when it is part of
  lowering predicates. General proof tactic behavior belongs in
  ``checker_proofs.py``.
"""

from dataclasses import dataclass
from typing import Any

from lark.tree import Meta

from abstract_syntax import (
    All,
    AllElim,
    AllIntro,
    And,
    ApplyDefsFact,
    ApplyDefsGoal,
    Bool,
    BoolType,
    Call,
    Constructor,
    Declaration,
    Define,
    Env,
    Formula,
    FunCase,
    FunctionType,
    Generic,
    IfThen,
    ImpIntro,
    IndCase,
    Induction,
    Lambda,
    ModusPonens,
    Or,
    OverloadedVar,
    PAndElim,
    PLet,
    PReflexive,
    PTrue,
    PTuple,
    PVar,
    PatternCons,
    Predicate,
    Proof,
    RecFun,
    ResolvedVar,
    RewriteGoal,
    Rule,
    Some,
    SomeElim,
    SomeIntro,
    Switch,
    SwitchCase,
    Term,
    Theorem,
    Type,
    TypeInst,
    Union,
    VarRef,
    base_name,
    callable_name,
)
from checker_common import *
from checker_proofs import generate_proof_name
from checker_types import check_type
from edit_distance import edit_distance
from error import user_error, warning

# Predicate / relation validation (phase 2: shape, arity, strict positivity)
# ============================================================
#
# Validates an inductively defined predicate or relation. The Predicate AST
# already went through uniquify, so any free variable in a rule's body has
# already been caught by Var.uniquify with its own did-you-mean message.
# What's left for us:
#
# 1. Signature shape: 'fn ... -> bool' (arity ≥ 1) or 'bool' (arity 0).
# 2. Each rule's conclusion is a call to the predicate, with the right arity.
# 3. Strict positivity: the predicate may not appear in a "negative" position
#    of any rule's premise — under 'not', or to the left of an inner '->'.
#    The predicate at the top of the *outer* implication's conclusion (i.e.
#    the rule's main conclusion) is always positive and is not flagged.
# 4. A soft style hint when the keyword and arity disagree (predicate of
#    arity ≥ 2 → suggest 'relation', and vice versa).
#
# Error messages name the rule (`In rule 'NAME' of predicate 'FOO': ...`) so
# the user can locate which rule misfired without re-reading the whole block.

def _validate_predicate_signature(sig: Any, name: str, keyword: str, env: Env) -> tuple[int, list[Type], Any]:
  checked_sig = check_type(sig, env)
  if isinstance(checked_sig, BoolType):
    return 0, [], checked_sig
  if isinstance(checked_sig, FunctionType):
    if not isinstance(checked_sig.return_type, BoolType):
      user_error(checked_sig.return_type.location,
            "the result type of a " + keyword + " must be 'bool', not '"
            + str(checked_sig.return_type) + "'")
    return len(checked_sig.param_types), checked_sig.param_types, checked_sig
  user_error(sig.location,
        "the type of " + keyword + " '" + base_name(name)
        + "' must be 'bool' or 'fn ... -> bool', not '" + str(sig) + "'")

def _predicate_style_hint(loc: Meta, name: str, keyword: str, arity: int) -> None:
  if keyword == 'predicate' and arity >= 2:
    warning(loc,
            "style hint: '" + base_name(name) + "' has arity "
            + str(arity) + "; consider 'relation' instead of 'predicate' "
            "for n-ary relations.")
  elif keyword == 'relation' and arity == 1:
    warning(loc,
            "style hint: '" + base_name(name) + "' has arity 1; consider "
            "'predicate' instead of 'relation' for unary properties.")

def _decompose_rule_body(formula: Any) -> tuple[Any, Any]:
  """Strip outer 'all' quantifiers, then split optional 'if prem then conc'.
  Returns (binders, premise_or_None, conclusion). The conclusion is whatever
  is left after stripping 'all's and an optional outermost implication."""
  while isinstance(formula, All):
    formula = formula.body
  if isinstance(formula, IfThen):
    return formula.premise, formula.conclusion
  return None, formula

def _validate_predicate_rule_shape(rule: Any, pred_name: str, keyword: str, arity: int, env: Env) -> None:
  _, concl = _decompose_rule_body(rule.formula)
  if not isinstance(concl, Call):
    user_error(concl.location,
          "in rule '" + base_name(rule.name) + "' of " + keyword + " '"
          + base_name(pred_name) + "': the rule's conclusion must apply '"
          + base_name(pred_name) + "', but found '" + str(concl) + "'")
  rator = concl.rator
  rator_callable_name = callable_name(rator)
  if rator_callable_name != pred_name:
    suggestion = ''
    if rator_callable_name is not None:
      base_rator = base_name(rator_callable_name)
      base_pred = base_name(pred_name)
      if edit_distance(base_rator, base_pred) <= max(2, len(base_pred) // 5):
        suggestion = " (did you mean '" + base_pred + "'?)"
    user_error(concl.location,
          "in rule '" + base_name(rule.name) + "' of " + keyword + " '"
          + base_name(pred_name) + "': the rule's conclusion must apply '"
          + base_name(pred_name) + "', but it applies '" + str(rator)
          + "'" + suggestion)
  if len(concl.args) != arity:
    plural = 's' if arity != 1 else ''
    user_error(concl.location,
          keyword + " '" + base_name(pred_name) + "' takes " + str(arity)
          + " argument" + plural + ", but rule '" + base_name(rule.name)
          + "' applies it to " + str(len(concl.args)))

def _check_predicate_strict_positivity(rule: Any, pred_name: str, keyword: str, env: Env) -> None:
  premise, _concl = _decompose_rule_body(rule.formula)
  if premise is None:
    return
  _walk_pred_premise(premise, pred_name, keyword, rule, forbidden=False)

def _walk_pred_premise(formula: Any, pred_name: str, keyword: str, rule: Any, forbidden: bool) -> None:
  """Walk a premise looking for occurrences of the predicate. The
  `forbidden` flag flips on under 'not' / 'if/then' premises and stays on
  through subsequent nesting (sticky semantics, matching the union check)."""
  match formula:
    case Call(loc, _, rator, args):
      ratname = None
      if isinstance(rator, VarRef):
        ratname = rator.get_name()
      if forbidden and ratname == pred_name:
        user_error(loc,
              keyword + " '" + base_name(pred_name) + "' must not occur "
              "in a negative position (under 'not' or to the left of an "
              "inner 'then') of its own introduction rules; this would "
              "make the definition circular and inconsistent.\n"
              "In rule '" + base_name(rule.name) + "'.")
      for a in args:
        _walk_pred_premise(a, pred_name, keyword, rule, forbidden)
    case OverloadedVar(loc, _, rns):
      ref = rns[0]
      if forbidden and ref == pred_name:
        user_error(loc,
              keyword + " '" + base_name(pred_name) + "' must not occur "
              "in a negative position of its own introduction rules.\n"
              "In rule '" + base_name(rule.name) + "'.")
    case IfThen(loc, _, prem, conc):
      _walk_pred_premise(prem, pred_name, keyword, rule, forbidden=True)
      _walk_pred_premise(conc, pred_name, keyword, rule, forbidden)
    case And(loc, _, parts):
      for a in parts:
        _walk_pred_premise(a, pred_name, keyword, rule, forbidden)
    case Or(loc, _, parts):
      for a in parts:
        _walk_pred_premise(a, pred_name, keyword, rule, forbidden)
    case All(loc, _, _, _, body):
      _walk_pred_premise(body, pred_name, keyword, rule, forbidden)
    case Some(loc, _, _, body):
      _walk_pred_premise(body, pred_name, keyword, rule, forbidden)
    case _:
      pass

# --- translation -------------------------------------------------------
#
# Lower a validated `Predicate` to a derivation-tree encoding:
#
#   1. A `union <Pred>Deriv { D_<rule_1>(...) ; D_<rule_2>(...) ; ... }`
#      whose constructors mirror the rules. Each constructor takes the
#      rule's outer `all`-bound variables and one sub-derivation per
#      *recursive* premise (a premise of the form `<pred>(...)`).
#   2. A `recursive is_<pred>_deriv(<Pred>Deriv, T1, ..., Tn) -> bool`
#      that pattern-matches on the derivation and returns true exactly
#      when the derivation justifies that the predicate holds for the
#      given arguments. Each case asserts the conclusion's args, the
#      rule's non-recursive premises, and the validator on each
#      sub-derivation.
#   3. A `define <pred>(x1,...,xn) := some d. is_<pred>_deriv(d, x1,...,xn)`.
#   4. A `postulate <rule_name> : <rule's formula>` per rule.
#
# This encoding is the same one Coq uses internally: the predicate is the
# image of `is_*_deriv` under existential elimination on a strictly
# positive `union`. Because both `induction` (over the derivation `union`)
# and `switch` (on a derivation, for inversion) are existing primitives
# in Deduce, both elimination forms are cheap to add as user-facing sugar
# in follow-up commits.
#
# Limitations of this v1 translation:
#   * Rule premises must be a (possibly empty) conjunction of atoms.
#     Disjunctive premises (`if A or B then ...`) and nested implications
#     are rejected with a clear error pointing at the offending premise.
#   * Higher-order recursive premises (`all m. if Q(m) then pred(m)`) are
#     also rejected — the derivation constructor would need to carry a
#     function `fn ... -> <Pred>Deriv`, which is fine in Deduce but adds
#     enough complexity to defer to a later commit.

@dataclass
class _PremiseInfo:
  atom: Any                     # the premise atom, copied
  is_recursive: bool
  orig_idx: int                 # index in the original conjunction (for PAndElim)
  sub_deriv_name: Any           # str if recursive (the obtain'd witness), else None
  deriv_label: Any              # str if recursive (the obtain'd proof label), else None
  rec_args: Any                 # list[Term] if recursive (atom.args), else None

@dataclass
class _RuleTranslation:
  rule: Any                     # the original Rule
  bound_vars: list[Any]         # [(name, type)] outer all-bound
  premise_top: Any              # the original premise formula (or None)
  premises: list[_PremiseInfo]  # list of _PremiseInfo, in original order
  conclusion_args: list[Any]    # the rule conclusion's args, copied
  conclusion_loc: Any           # location of the conclusion (for proof spans)
  validator_arg_names: list[str]  # fresh names for the validator's arity-many extra params

  @property
  def recursive_premises(self) -> list[_PremiseInfo]:
    return [p for p in self.premises if p.is_recursive]

  @property
  def non_recursive_premises(self) -> list[_PremiseInfo]:
    return [p for p in self.premises if not p.is_recursive]

def _flatten_and(formula: Any) -> list[Any]:
  if isinstance(formula, And):
    return list(formula.args)
  return [formula]

def _is_recursive_atom(atom: Any, pred_name: str) -> bool:
  if not isinstance(atom, Call):
    return False
  rator = atom.rator
  if not isinstance(rator, VarRef):
    return False
  rname = rator.get_name()
  return bool(rname == pred_name)

def _premise_too_complex(prem: Any) -> bool:
  # Anything whose top is something we don't peel away in `_flatten_and`
  # signals a premise shape we won't translate yet. Bare atoms, calls,
  # and conjunctions of those are fine.
  if isinstance(prem, (IfThen, Or, All, Some)):
    return True
  if isinstance(prem, And):
    return any(_premise_too_complex(p) for p in prem.args)
  return False

def _decompose_rule_for_translation(rule: Any, pred_name: str, keyword: str) -> _RuleTranslation:
  formula = rule.formula
  bound_vars = []
  while isinstance(formula, All):
    bound_vars.append(formula.var)
    formula = formula.body
  if isinstance(formula, IfThen):
    premise = formula.premise
    conclusion = formula.conclusion
  else:
    premise = None
    conclusion = formula

  premises = []
  if premise is not None:
    if _premise_too_complex(premise):
      user_error(premise.location,
            "in rule '" + base_name(rule.name) + "' of " + keyword + " '"
            + base_name(pred_name) + "': v1 of the predicate translation "
            "supports only a conjunction of atoms as the rule's premise. "
            "Disjunctive, implicational, or quantified premises will be "
            "supported in a later commit.")
    for idx, atom in enumerate(_flatten_and(premise)):
      if _is_recursive_atom(atom, pred_name):
        premises.append(_PremiseInfo(
          atom=atom.copy(), is_recursive=True, orig_idx=idx,
          sub_deriv_name=generate_proof_name('d'),
          deriv_label=generate_proof_name('deriv'),
          rec_args=[a.copy() for a in atom.args]))
      else:
        premises.append(_PremiseInfo(
          atom=atom.copy(), is_recursive=False, orig_idx=idx,
          sub_deriv_name=None, deriv_label=None, rec_args=None))

  if not isinstance(conclusion, Call):
    user_error(conclusion.location,
          "expected a Call in conclusion of rule '"
          + base_name(rule.name) + "' (validation should have caught this)")
  conclusion_args = [a.copy() for a in conclusion.args]
  validator_arg_names = [generate_proof_name('m') for _ in conclusion_args]

  return _RuleTranslation(rule=rule,
                          bound_vars=bound_vars,
                          premise_top=premise,
                          premises=premises,
                          conclusion_args=conclusion_args,
                          conclusion_loc=conclusion.location,
                          validator_arg_names=validator_arg_names)

def _build_predicate_translation(decl: Any, param_types: list[Any]) -> list[Any]:
  loc = decl.location
  pred_name = decl.name
  typarams = decl.type_params
  rules = decl.rules
  keyword = decl.original_keyword
  arity = len(param_types)
  base_pred = base_name(pred_name)

  rule_translations = [_decompose_rule_for_translation(r, pred_name, keyword)
                       for r in rules]

  # 1. Build the derivation union.
  deriv_union_name = generate_proof_name(base_pred + 'Deriv')
  constr_names = [generate_proof_name('D_' + base_name(r.name)) for r in rules]

  # The type-arg-applied form of the derivation type, used both as the
  # type of sub-derivations inside constructors and as the existential's
  # binder type below. For arity 0 type params, just a Var; otherwise a
  # TypeInst over the type-param vars.
  if typarams:
    deriv_type_inst = TypeInst(
      loc,
      ResolvedVar(loc, None, deriv_union_name),
      [ResolvedVar(loc, None, t) for t in typarams])
  else:
    deriv_type_inst = ResolvedVar(loc, None, deriv_union_name)

  constructors = []
  for cname, rt in zip(constr_names, rule_translations):
    fields = [t.copy() for (_, t) in rt.bound_vars] + \
             [deriv_type_inst.copy() for _ in rt.recursive_premises]
    constructors.append(Constructor(rt.rule.location, cname, fields))
  deriv_union = Union(loc, deriv_union_name, list(typarams), constructors,
                      visibility='public')

  # 2. Build the validator.
  is_deriv_name = generate_proof_name('is_' + base_pred + '_deriv')
  fun_cases = []
  for cname, rt in zip(constr_names, rule_translations):
    pat_param_names = [v for (v, _) in rt.bound_vars] + \
                      [p.sub_deriv_name for p in rt.recursive_premises]
    pattern = PatternCons(
      rt.rule.location,
      ResolvedVar(rt.rule.location, None, cname),
      pat_param_names)

    clauses = []
    # m_i = conclusion_args[i]
    for (m, c) in zip(rt.validator_arg_names, rt.conclusion_args):
      clauses.append(
        Call(rt.rule.location, BoolType(rt.rule.location),
             ResolvedVar(rt.rule.location, None, '='),
             [ResolvedVar(rt.rule.location, None, m), c.copy()]))
    # non-recursive premises verbatim
    for p in rt.non_recursive_premises:
      clauses.append(p.atom.copy())
    # recursive premise validators
    for p in rt.recursive_premises:
      args = [ResolvedVar(rt.rule.location, None, p.sub_deriv_name)] + \
             [a.copy() for a in p.rec_args]
      clauses.append(
        Call(rt.rule.location, BoolType(rt.rule.location),
             ResolvedVar(rt.rule.location, None, is_deriv_name),
             args))

    if not clauses:
      body = Bool(rt.rule.location, BoolType(rt.rule.location), True)
    elif len(clauses) == 1:
      body = clauses[0]
    else:
      body = And(rt.rule.location, BoolType(rt.rule.location), clauses)

    fun_cases.append(FunCase(
      rt.rule.location,
      ResolvedVar(rt.rule.location, None, is_deriv_name),
      pattern, list(rt.validator_arg_names), body))

  validator_param_types = [deriv_type_inst.copy()] + \
                          [t.copy() for t in param_types]
  has_any_recursive = any(len(rt.recursive_premises) > 0
                          for rt in rule_translations)
  if has_any_recursive:
    validator = RecFun(loc, is_deriv_name, list(typarams),
                       validator_param_types, BoolType(loc), fun_cases,
                       visibility=decl.visibility)
  else:
    # Deduce's `recursive` requires at least one recursive call. When no
    # rule has a recursive premise, lower the validator to a plain `fun`
    # whose body is a `switch` on the derivation. The cases match the
    # `fun_cases` we already built — we just rebuild them as switch cases
    # with the m_i parameters captured by the lambda.
    d_param_name = generate_proof_name('d')
    d_param_var = ResolvedVar(loc, None, d_param_name)
    switch_cases = []
    for fc in fun_cases:
      switch_cases.append(SwitchCase(fc.location, fc.pattern, fc.body))
    switch_term = Switch(loc, BoolType(loc), d_param_var, switch_cases)
    fun_params = [(d_param_name, deriv_type_inst.copy())] + \
                 [(m, t.copy()) for (m, t) in
                  zip(rule_translations[0].validator_arg_names
                      if rule_translations else [], param_types)]
    fun_body = Lambda(loc, None, fun_params, switch_term)
    if typarams:
      fun_body = Generic(loc, None, list(typarams), fun_body)
    validator_typ = FunctionType(loc, list(typarams),
                                 validator_param_types, BoolType(loc))
    validator = Define(loc, is_deriv_name, validator_typ, fun_body,
                       visibility=decl.visibility)

  # 3. Build the predicate's `define` body: fun args { some d. is_*_deriv(d, args) }
  arg_var_names = [generate_proof_name('x') for _ in range(arity)]
  arg_vars = [ResolvedVar(loc, None, x) for x in arg_var_names]
  d_name = generate_proof_name('d')
  is_deriv_call = Call(loc, BoolType(loc),
                       ResolvedVar(loc, None, is_deriv_name),
                       [ResolvedVar(loc, None, d_name)] + arg_vars)
  some_body = Some(loc, BoolType(loc),
                   [(d_name, deriv_type_inst.copy())], is_deriv_call)
  if arity > 0:
    define_body = Lambda(loc, None,
                         [(x, t.copy())
                          for (x, t) in zip(arg_var_names, param_types)],
                         some_body)
  else:
    define_body = some_body
  if typarams:
    define_body = Generic(loc, None, list(typarams), define_body)

  define_decl = Define(loc, pred_name, decl.signature.copy(), define_body,
                       visibility=decl.visibility)

  # 4. Synthesised intro theorems. For each rule we build a Theorem whose
  # statement is the user's rule formula and whose proof:
  #   * `arbitrary` over the bound vars,
  #   * `assume` the premise (if any),
  #   * for each recursive premise, `obtain` the underlying derivation,
  #   * `expand` the predicate, `choose` the rule's derivation
  #     constructor, `expand` the validator, then prove the resulting
  #     conjunction with reflexivity for argument equalities, hypothesis
  #     access for non-recursive premises, and the obtained labels for
  #     recursive premise validators.
  pred_var = lambda l: ResolvedVar(l, None, pred_name)
  is_deriv_var = lambda l: ResolvedVar(l, None, is_deriv_name)
  intro_theorems = []
  for cname, rt in zip(constr_names, rule_translations):
    intro_theorems.append(
      _build_intro_theorem(rt, pred_name, pred_var, is_deriv_var, cname))

  # 5. Synthesised rule-induction and rule-inversion theorems.
  rule_ind_theorem = _build_rule_induction_theorem(
    decl, param_types, rule_translations, constr_names,
    pred_var, is_deriv_var, deriv_type_inst, is_inversion=False)
  rule_inv_theorem = _build_rule_induction_theorem(
    decl, param_types, rule_translations, constr_names,
    pred_var, is_deriv_var, deriv_type_inst, is_inversion=True)

  return [deriv_union, validator, define_decl] + intro_theorems + \
         [rule_ind_theorem, rule_inv_theorem]

def _build_intro_theorem(rt: _RuleTranslation, pred_name: str, pred_var: Any, is_deriv_var: Any, constr_name: str) -> Theorem:
  """Build a `Theorem` for one rule's intro lemma."""
  loc = rt.rule.location
  hyp_label = generate_proof_name('hyp')
  n_premises = len(rt.premises)

  # Constructor witness: D_<rule>(<bound vars>, <obtained derivation labels>)
  constr_args = [ResolvedVar(loc, None, name) for (name, _) in rt.bound_vars] \
                + [ResolvedVar(loc, None, p.sub_deriv_name)
                   for p in rt.recursive_premises]
  if constr_args:
    constr_witness = Call(loc, None,
                          ResolvedVar(loc, None, constr_name),
                          constr_args)
  else:
    constr_witness = ResolvedVar(loc, None, constr_name)

  # The proof of the validator-body conjunction. Order matches the
  # validator: m_i = c_i for each conclusion arg, then non-recursive
  # premises (in original order), then recursive validators (in original
  # order).
  conjunct_proofs = []
  for _ in rt.conclusion_args:
    conjunct_proofs.append(PReflexive(loc))
  for p in rt.non_recursive_premises:
    if n_premises == 1:
      conjunct_proofs.append(PVar(loc, hyp_label))
    else:
      conjunct_proofs.append(PAndElim(loc, p.orig_idx, PVar(loc, hyp_label)))
  for p in rt.recursive_premises:
    conjunct_proofs.append(PVar(loc, p.deriv_label))

  if not conjunct_proofs:
    inner_proof = PTrue(loc)
  elif len(conjunct_proofs) == 1:
    inner_proof = conjunct_proofs[0]
  else:
    inner_proof = PTuple(loc, conjunct_proofs)

  # expand is_<pred>_deriv to reduce the validator call
  inner_proof = ApplyDefsGoal(loc, [is_deriv_var(loc)], inner_proof)
  # choose the rule's constructor as the existential witness
  inner_proof = SomeIntro(loc, [constr_witness], inner_proof)
  # expand the predicate to expose the existential
  inner_proof = ApplyDefsGoal(loc, [pred_var(loc)], inner_proof)

  # For each recursive premise (innermost-first), wrap in a SomeElim that
  # binds the derivation. Walk in reverse so the first premise ends up as
  # the outermost obtain.
  for p in reversed(rt.recursive_premises):
    is_deriv_call = Call(loc, BoolType(loc), is_deriv_var(loc),
                         [ResolvedVar(loc, None, p.sub_deriv_name)]
                         + [a.copy() for a in p.rec_args])
    if n_premises == 1:
      atom_proof = PVar(loc, hyp_label)
    else:
      atom_proof = PAndElim(loc, p.orig_idx, PVar(loc, hyp_label))
    some_proof = ApplyDefsFact(loc, [pred_var(loc)], atom_proof)
    inner_proof = SomeElim(loc, [p.sub_deriv_name], p.deriv_label,
                           is_deriv_call, some_proof, inner_proof)

  # If there's a premise, wrap in ImpIntro
  if rt.premise_top is not None:
    inner_proof = ImpIntro(loc, hyp_label, rt.premise_top.copy(), inner_proof)

  # Wrap with AllIntro for each bound var (innermost first)
  n_bound = len(rt.bound_vars)
  for i, (vname, vty) in enumerate(reversed(rt.bound_vars)):
    inner_proof = AllIntro(loc, (vname, vty.copy()), (i, n_bound),
                           inner_proof)

  return Theorem(rt.rule.location, rt.rule.name, rt.rule.formula.copy(),
                 inner_proof, False)

# --- rule-induction theorem generator ----------------------------------
#
# For each predicate, generate a theorem `<pred>_rule_induction` that
# states the rule-induction principle. The proof generalises to
# "all d. all xs. if is_<pred>_deriv(d, xs) then M(xs)" and inducts on
# the derivation `union`. Once `rule induction` proof-form sugar lands
# in a follow-up commit, this theorem is the workhorse it desugars to.

def _build_rule_induction_theorem(decl: Any, param_types: list[Any], rule_translations: list[_RuleTranslation],
                                  constr_names: list[str], pred_var: Any, is_deriv_var: Any,
                                  deriv_type_inst: Any, is_inversion: bool = False) -> Theorem:
  """Build the `<pred>_rule_induction` (or `_rule_inversion`) theorem.

  When `is_inversion` is True, generate the strictly weaker inversion
  principle: rule premises are *not* augmented with the motive's
  induction hypothesis, and the per-case premise tuple omits the
  matching `M(<rec args>)` entries. The proof still inducts on the
  derivation `union` (we just don't use the induction hypotheses)."""
  loc = decl.location
  pred_name = decl.name
  base_name(pred_name)
  arity = len(param_types)

  # The theorem's uniquified name was pre-registered in env during
  # Predicate.uniquify so user code referencing `<pred>_rule_induction`
  # (or `_rule_inversion`) resolves correctly.
  thm_name = decl.rule_inversion_name if is_inversion \
             else decl.rule_induction_name

  motive_name = generate_proof_name('M')
  if arity > 0:
    motive_type = FunctionType(loc, [], [t.copy() for t in param_types],
                               BoolType(loc))
  else:
    motive_type = BoolType(loc)

  def motive_var(l: Meta) -> ResolvedVar:
    return ResolvedVar(l, None, motive_name)

  def apply_motive(args: list[Any], l: Meta = loc) -> Any:
    if args:
      return Call(l, BoolType(l), motive_var(l), args)
    return motive_var(l)

  def apply_pred(args: list[Any], l: Meta = loc) -> Any:
    if args:
      return Call(l, BoolType(l), pred_var(l), args)
    return pred_var(l)

  def wrap_alls(formula: Any, vars_with_types: list[Any]) -> Any:
    n = len(vars_with_types)
    out = formula
    for i, (vname, vty) in enumerate(reversed(vars_with_types)):
      out = All(loc, BoolType(loc), (vname, vty.copy()), (i, n), out)
    return out

  def wrap_all_intros(proof: Any, vars_with_types: list[Any]) -> Any:
    n = len(vars_with_types)
    out = proof
    for i, (vname, vty) in enumerate(reversed(vars_with_types)):
      out = AllIntro(loc, (vname, vty.copy()), (i, n), out)
    return out

  # ---- statement ----------------------------------------------------------
  rule_conjuncts = []
  for rt in rule_translations:
    if rt.premises:
      augmented = []
      for p in rt.premises:
        augmented.append(p.atom.copy())
        if p.is_recursive and not is_inversion:
          augmented.append(apply_motive([a.copy() for a in p.rec_args]))
      aug_premise = augmented[0] if len(augmented) == 1 \
                    else And(loc, BoolType(loc), augmented)
      conj_inner = IfThen(loc, BoolType(loc), aug_premise,
                          apply_motive([a.copy()
                                        for a in rt.conclusion_args]))
    else:
      conj_inner = apply_motive([a.copy() for a in rt.conclusion_args])
    conj_inner = wrap_alls(conj_inner, list(rt.bound_vars))
    rule_conjuncts.append(conj_inner)

  if not rule_conjuncts:
    rules_hyp_formula = Bool(loc, BoolType(loc), True)
  elif len(rule_conjuncts) == 1:
    rules_hyp_formula = rule_conjuncts[0]
  else:
    rules_hyp_formula = And(loc, BoolType(loc), rule_conjuncts)

  outer_arg_names = [generate_proof_name('x') for _ in range(arity)]
  outer_arg_types_pairs = list(zip(outer_arg_names, param_types))
  pred_call_outer = apply_pred([ResolvedVar(loc, None, x)
                                for x in outer_arg_names])
  main_conc = IfThen(loc, BoolType(loc), pred_call_outer,
                     apply_motive([ResolvedVar(loc, None, x)
                                   for x in outer_arg_names]))
  main_conc = wrap_alls(main_conc, outer_arg_types_pairs)

  full_statement = All(
    loc, BoolType(loc), (motive_name, motive_type), (0, 1),
    IfThen(loc, BoolType(loc), rules_hyp_formula, main_conc))

  # ---- proof body --------------------------------------------------------
  rules_hyp_label = generate_proof_name('rules_hyp')
  helper_label = generate_proof_name('helper')

  # helper formula: all d. all ms. if is_<pred>_deriv(d, ms) then M(ms)
  helper_d_name = generate_proof_name('d')
  helper_m_names = [generate_proof_name('m') for _ in range(arity)]
  helper_m_pairs = list(zip(helper_m_names, param_types))
  helper_validator_call = Call(
    loc, BoolType(loc), is_deriv_var(loc),
    [ResolvedVar(loc, None, helper_d_name)] +
    [ResolvedVar(loc, None, m) for m in helper_m_names])
  helper_inner = IfThen(loc, BoolType(loc), helper_validator_call,
                        apply_motive([ResolvedVar(loc, None, m)
                                      for m in helper_m_names]))
  helper_inner = wrap_alls(helper_inner, helper_m_pairs)
  helper_formula = All(loc, BoolType(loc),
                       (helper_d_name, deriv_type_inst.copy()), (0, 1),
                       helper_inner)

  # ---- per-case proofs ---------------------------------------------------
  ind_cases = []
  for rule_idx, (cname, rt) in enumerate(zip(constr_names, rule_translations)):
    ind_cases.append(_build_rule_induction_case(
      cname, rt, rule_idx, len(rule_translations), pred_var, is_deriv_var,
      apply_motive, apply_pred, rules_hyp_label, arity, param_types,
      wrap_alls, wrap_all_intros, is_inversion))

  helper_proof = Induction(loc, deriv_type_inst.copy(), ind_cases)

  # ---- final assembly ----------------------------------------------------
  final_d_name = generate_proof_name('d')
  final_deriv_label = generate_proof_name('deriv')
  pred_h_label = generate_proof_name('pred_h')

  pred_h_validator = Call(
    loc, BoolType(loc), is_deriv_var(loc),
    [ResolvedVar(loc, None, final_d_name)] +
    [ResolvedVar(loc, None, x) for x in outer_arg_names])

  helper_at_d = AllElim(loc, PVar(loc, helper_label),
                        ResolvedVar(loc, None, final_d_name),
                        (0, 1))
  applied = helper_at_d
  for i, x in enumerate(outer_arg_names):
    applied = AllElim(loc, applied, ResolvedVar(loc, None, x), (i, arity))
  use_helper = ModusPonens(loc, applied, PVar(loc, final_deriv_label))

  pred_h_expanded = ApplyDefsFact(loc, [pred_var(loc)],
                                  PVar(loc, pred_h_label))
  obtain_proof = SomeElim(loc, [final_d_name], final_deriv_label,
                          pred_h_validator, pred_h_expanded, use_helper)

  imp_inner = ImpIntro(loc, pred_h_label, pred_call_outer.copy(),
                       obtain_proof)
  imp_inner = wrap_all_intros(imp_inner, outer_arg_types_pairs)

  proof_body = PLet(loc, helper_label, helper_formula, helper_proof,
                    imp_inner)
  proof_body = ImpIntro(loc, rules_hyp_label, rules_hyp_formula.copy(),
                        proof_body)
  proof_body = AllIntro(loc, (motive_name, motive_type.copy()), (0, 1),
                        proof_body)

  return Theorem(loc, thm_name, full_statement, proof_body, False)

def _build_rule_induction_case(constr_name: str, rt: _RuleTranslation, rule_idx: int, n_rules: int,
                               pred_var: Any, is_deriv_var: Any, apply_motive: Any,
                               apply_pred: Any, rules_hyp_label: str, arity: int,
                               param_types: list[Any], wrap_alls: Any, wrap_all_intros: Any,
                               is_inversion: bool = False) -> IndCase:
  """Build one ind_case for the helper's `induction <Deriv>`.

  The case proves: all m1,...,mn. if is_<pred>_deriv(C(<bound>, <subs>), ms)
                                  then M(ms)
  by:
    arbitrary ms;
    assume dh : is_<pred>_deriv(C(...), ms)
    have dh_u := expand is_<pred>_deriv in dh   -- conjunction
    extract m_i = arg_i, recursive validator hits, non-rec premises
    replace each m_i = arg_i in the goal
    rebuild the (M-augmented) premise tuple expected by the rule's
      conjunct of rules_hyp
    apply rules_hyp's conjunct to that
  """
  loc = rt.rule.location
  bound_var_names = [v for (v, _) in rt.bound_vars]
  sub_deriv_names = [p.sub_deriv_name for p in rt.recursive_premises]

  pat_param_names = list(bound_var_names) + list(sub_deriv_names)
  pattern = PatternCons(loc, ResolvedVar(loc, None, constr_name),
                        pat_param_names)

  case_ih_labels = [generate_proof_name('IH') for _ in rt.recursive_premises]
  ind_hyps = []
  for ih_label, p in zip(case_ih_labels, rt.recursive_premises):
    ih_m_names = [generate_proof_name('m') for _ in range(arity)]
    ih_m_vars = [ResolvedVar(loc, None, m) for m in ih_m_names]
    ih_validator = Call(
      loc, BoolType(loc), is_deriv_var(loc),
      [ResolvedVar(loc, None, p.sub_deriv_name)] + ih_m_vars)
    ih_inner = IfThen(loc, BoolType(loc), ih_validator,
                      apply_motive(ih_m_vars))
    ih_inner = wrap_alls(ih_inner, list(zip(ih_m_names, param_types)))
    ind_hyps.append((ih_label, ih_inner))

  m_names = [generate_proof_name('m') for _ in range(arity)]
  m_vars = [ResolvedVar(loc, None, m) for m in m_names]
  m_pairs = list(zip(m_names, param_types))

  constr_args = [ResolvedVar(loc, None, n) for n in bound_var_names] + \
                [ResolvedVar(loc, None, n) for n in sub_deriv_names]
  if constr_args:
    constr_term = Call(loc, None,
                       ResolvedVar(loc, None, constr_name),
                       constr_args)
  else:
    constr_term = ResolvedVar(loc, None, constr_name)

  dh_label = generate_proof_name('dh')
  dh_formula = Call(loc, BoolType(loc), is_deriv_var(loc),
                    [constr_term] + m_vars)

  num_eq = arity
  num_nr = len(rt.non_recursive_premises)
  num_rec = len(rt.recursive_premises)
  total_conjuncts = num_eq + num_nr + num_rec

  dh_unfolded_label = generate_proof_name('dh_u')
  # If total_conjuncts == 1 the validator body isn't a conjunction; we use
  # the unfolded fact directly and conjunct extraction is a no-op.
  def conj_proof(idx: int) -> Any:
    if total_conjuncts == 1:
      return PVar(loc, dh_unfolded_label)
    return PAndElim(loc, idx, PVar(loc, dh_unfolded_label))

  # Equality conjuncts: m_i = arg_i. We later `replace` each in the goal.
  eq_proofs = [conj_proof(i) for i in range(num_eq)]

  # Recursive validator hits: indices [num_eq + num_nr ... total_conjuncts)
  rec_validator_proofs = [conj_proof(num_eq + num_nr + i)
                          for i in range(num_rec)]

  # Non-recursive premise atoms: indices [num_eq ... num_eq + num_nr)
  nr_proofs_by_orig_idx = {}
  nr_iter = iter(rt.non_recursive_premises)
  for offset in range(num_nr):
    p = next(nr_iter)
    nr_proofs_by_orig_idx[p.orig_idx] = conj_proof(num_eq + offset)

  rec_validator_by_orig_idx = {}
  rec_iter_idx = 0
  for p in rt.premises:
    if p.is_recursive:
      rec_validator_by_orig_idx[p.orig_idx] = (
        rec_validator_proofs[rec_iter_idx], p)
      rec_iter_idx += 1

  # Build the rules_hyp conjunct proof and the augmented-premise tuple.
  # Rules_hyp's conjunct for this rule has shape
  #   all <bound>. if <augmented premise> then M(<concl args>)
  # Instantiate with the bound vars; modus-ponens with the rebuilt premise.

  # PVar(rules_hyp), narrowed to this rule's conjunct.
  if n_rules == 1:
    conj_of_rules_hyp = PVar(loc, rules_hyp_label)
  else:
    conj_of_rules_hyp = PAndElim(loc, rule_idx, PVar(loc, rules_hyp_label))

  # Instantiate with each bound var.
  applied = conj_of_rules_hyp
  n_bound = len(rt.bound_vars)
  for i, (bv, _) in enumerate(rt.bound_vars):
    applied = AllElim(loc, applied,
                      ResolvedVar(loc, None, bv), (i, n_bound))

  # Build the augmented-premise tuple (in original order):
  #   for each premise atom (orig_idx in rt.premises):
  #     if non-recursive: use its expanded validator conjunct (proof of the
  #       atom verbatim).
  #     if recursive: produce a proof of `<atom> and M(<rec_args>)`:
  #       - <atom> = pred(rec_args). Construct via:
  #           expand pred; choose <sub_deriv_name>; <validator hit>.
  #       - M(rec_args) via the IH:
  #           apply IH[rec_args]... to <validator hit>.
  if rt.premises:
    augmented_proof_parts = []
    for p in rt.premises:
      if p.is_recursive:
        validator_proof, p_info = rec_validator_by_orig_idx[p.orig_idx]
        # Proof of pred(rec_args): expand pred; choose sub_deriv; validator_proof
        atom_proof = ApplyDefsGoal(
          loc, [pred_var(loc)],
          SomeIntro(loc,
                    [ResolvedVar(loc, None, p_info.sub_deriv_name)],
                    validator_proof))
        augmented_proof_parts.append(atom_proof)
        if not is_inversion:
          # Proof of M(rec_args): apply IH[rec_args]... to validator_proof
          ih_idx = list(rt.recursive_premises).index(p_info)
          ih_label = case_ih_labels[ih_idx]
          ih_applied = PVar(loc, ih_label)
          for k, ra in enumerate(p_info.rec_args):
            ih_applied = AllElim(loc, ih_applied, ra.copy(), (k, arity))
          m_proof = ModusPonens(loc, ih_applied, validator_proof)
          augmented_proof_parts.append(m_proof)
      else:
        # Non-recursive: the atom's proof is the validator's matching conjunct.
        augmented_proof_parts.append(nr_proofs_by_orig_idx[p.orig_idx])

    if len(augmented_proof_parts) == 1:
      premise_tuple = augmented_proof_parts[0]
    else:
      premise_tuple = PTuple(loc, augmented_proof_parts)

    final_apply = ModusPonens(loc, applied, premise_tuple)
  else:
    final_apply = applied

  # Replace each m_i with arg_i (so the goal M(m_1,...,m_n) becomes
  # M(arg_1,...,arg_n) which `final_apply` proves).
  if eq_proofs:
    body = RewriteGoal(loc, list(eq_proofs), final_apply)
  else:
    body = final_apply

  # Have dh_unfolded := expand validator in dh, with the right shape.
  if total_conjuncts == 1:
    dh_unfolded_formula = _build_validator_body_formula(
      rt, m_vars, is_deriv_var, pred_var, loc)
  else:
    dh_unfolded_formula = _build_validator_body_formula(
      rt, m_vars, is_deriv_var, pred_var, loc)

  body = PLet(loc, dh_unfolded_label, dh_unfolded_formula,
              ApplyDefsFact(loc, [is_deriv_var(loc)], PVar(loc, dh_label)),
              body)
  body = ImpIntro(loc, dh_label, dh_formula, body)
  body = wrap_all_intros(body, m_pairs)

  return IndCase(loc, pattern, ind_hyps, body)

def _build_validator_body_formula(rt: _RuleTranslation, m_vars: list[Any], is_deriv_var: Any, pred_var: Any, loc: Meta) -> Any:
  """The conjunction the validator-body unfolds to for this rule."""
  clauses = []
  for (m_var, c) in zip(m_vars, rt.conclusion_args):
    clauses.append(Call(loc, BoolType(loc),
                        ResolvedVar(loc, None, '='),
                        [m_var, c.copy()]))
  for p in rt.non_recursive_premises:
    clauses.append(p.atom.copy())
  for p in rt.recursive_premises:
    clauses.append(Call(
      loc, BoolType(loc), is_deriv_var(loc),
      [ResolvedVar(loc, None, p.sub_deriv_name)] +
      [a.copy() for a in p.rec_args]))
  if not clauses:
    return Bool(loc, BoolType(loc), True)
  if len(clauses) == 1:
    return clauses[0]
  return And(loc, BoolType(loc), clauses)
