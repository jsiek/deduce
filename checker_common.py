"""Shared imports for the checker split.

File charter:
- Keep only common imports, type aliases, and narrowly shared constants needed
  by several checker modules during the facade transition.
- Do not add checker behavior, mutable checker state, or phase-specific helper
  functions here; those belong in the module that owns the phase.
- If a helper starts here because it is genuinely shared, move it out once a
  clearer owner emerges. This file should keep the split mechanically simple,
  not become a second monolith.
"""

# The checking process for programs & proofs has the following steps:
#
# 0. uniquify:
#    Rename all variables to have unique names.
#
# 1. process_declarations:
#    Collects the type environment for the top-level statements, usually
#    from their declared types. (Except for define's without types.)
#
# 2. type_check_stmt:
#    Type check the bodies of functions using the type environment.
#    Perform overload resolution using the types.
#
# 3. collect_env:
#    Collects the proofs (mapping proof labels to their formulas
#              and runtime environment mapping variables to values)
#    and the values (mapping names to their values, for defines a functions)
#    into an environment.
#
# 4. check_proofs:
#    Check that the proofs follow the rules of logic,
#    run the print and assert statements,
#    reduce some formulas and terms automatically.

from dataclasses import dataclass
from typing import List, Optional, Tuple, cast
from lark.tree import Meta

from abstract_syntax import (
    All, AllElim, AllElimTypes, AllIntro, And, ApplyDefsFact,
    ApplyDefsGoal, Array, ArrayGet, ArrayType, Assert, Associative,
    Auto, Bool, BoolType, Call, Cases, Conditional,
    Constructor, Declaration, Define, Env, EvaluateFact, EvaluateGoal,
    Export, Formula, FunCase, FunctionType, GenRecFun, Generic,
    GenericUnknownInst, Hole, IfThen, ImpIntro, Import, IndCase,
    Induction, Inductive, Int, IntType, Lambda, MakeArray,
    Mark, MarkException, Module, ModusPonens, Omitted, Or,
    OverloadType, OverloadedVar, PAndElim, PAnnot, PExtensionality, PHelpUse,
    PHole, PInjective, PLet, PRecall, PReflexive, PSorry,
    PSymmetric, PTLetNew, PTransitive, PTrue, PTuple, PVar,
    Pattern, PatternBool, PatternCons, PatternTerm, Postulate, Predicate, Print,
    ProofBinding, RecFun, ResolvedVar, RewriteFact, RewriteGoal, Rule,
    RuleInduction, RuleInversion, SimplifyFact, SimplifyGoal, Some,
    SomeElim, SomeIntro, Statement, Suffices, Switch, SwitchCase, SwitchProof,
    TAnnote, TLet, Term, TermInst, Theorem, Trace, Type, TypeInst, TypeType,
    Union, Var, VarRef, ViewDecl, ViewRecFun, alpha_equiv, base_name,
    check_post_typecheck_invariants, count_marks, find_file, find_mark,
    callable_name, formula_match, formulas_equal_modulo_numeric_literals, get_num_rewrites,
    get_predicate_decl, get_reduced_defs,
    get_type_name, isUInt, is_associative, is_constructor, is_equation,
    is_true, mkEqual, name2str, print_theorems, remove_mark,
    replace_mark, reset_num_rewrites, reset_reduced_defs, rewrite_aux,
    set_dont_reduce_opaque, set_eval_all, set_reduce_all, split_equation,
    type_match, type_names, uintToInt, uniquify_deduce as uniquify_deduce,
)
from edit_distance import edit_distance
from error import (
    Diagnostic,
    ErrorSink,
    IncompleteProof,
    InternalError,
    MatchFailed,
    UserError,
    add_diagnostic,
    add_incomplete,
    error_header,
    get_active_sink,
    incomplete_error,
    internal_error,
    match_failed,
    set_active_sink,
    speculative_probe,
    user_error,
    warning,
    wrap_user_error,
)
from flags import (
    VerboseLevel,
    get_check_imports,
    get_debugger,
    get_quiet_mode,
    get_target_hole_location,
    get_verbose,
    print_verbose,
    set_verbose,
)
from pathlib import Path
import style


def switch_pattern_could_match_alts(
    pat: Pattern, alts: list[Constructor]
) -> bool:
  """Return whether a switch pattern could name one of a union's constructors.

  This is a heuristic used when deciding whether switch cases target a union's
  direct constructors or a public view exposed for that union.
  """
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


def gen_conjunct_advice(conjunct: Formula, arbs: list[str], ihs: list[str]) -> str:
  """Render one custom-induction conjunct as a suggested ``case`` skeleton.

  Used to build the "Expected a case shaped like ..." advice shown when a
  custom induction proof is missing or malformed. Shared by ordinary proof
  dispatch (``checker_proofs``) and custom-induction body generation
  (``checker_induction``). Unrecognized conjunct shapes yield the empty
  string so advice generation never crashes while a user error is being
  assembled.
  """
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

def custom_induction_expected_cases(conjuncts: list[Formula]) -> str:
  return gen_custom_induction_advice(conjuncts).replace('\t\t', '\t')

def custom_induction_case_hint(conjunct: Formula) -> str:
  return gen_conjunct_advice(conjunct, [], []).replace('\t\t', '\t')


def view_call(loc: Meta, name: str, arg: Term,
              type_args: Optional[List[Type]] = None) -> Call:
  """Build a single-argument call to view function ``name`` applied to ``arg``.

  Shared by view checking (``checker_pipeline``, ``checker_types``) and view
  proof generation (``checker_proofs``). When ``type_args`` is non-empty the
  operator is instantiated with a ``TermInst``; otherwise it is a bare
  ``ResolvedVar``.
  """
  rator: Term = ResolvedVar(loc, None, name)
  if type_args:
    rator = TermInst(loc, None, rator, type_args)
  return Call(loc, None, rator, [arg])
