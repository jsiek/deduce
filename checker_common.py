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
    PatternBool, PatternCons, PatternTerm, Postulate, Predicate, Print,
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
