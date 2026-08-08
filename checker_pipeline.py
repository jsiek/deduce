"""Top-level checker phases and whole-file orchestration.

File charter:
- Put code here when it sequences checker phases over statements: declaration
  processing, statement type checking, environment collection, proof-check
  scheduling, import/module bookkeeping, and the public ``check_deduce`` entry.
- Keep phase internals in their owners: term/type rules in ``checker_types.py``,
  proof tactic rules in ``checker_proofs.py``, predicate lowering in
  ``checker_predicates.py``, formula rewrites in ``checker_logic.py``, and
  cache mechanics in ``checker_cache.py``.
- This module may coordinate those services and maintain pipeline state, but it
  should not become the home for new local rules unless the rule is truly about
  phase ordering or statement-level orchestration.
"""

from dataclasses import dataclass
from typing import TYPE_CHECKING, Callable, List, Optional, Tuple, cast

from lark.tree import Meta

if TYPE_CHECKING:
    from imperative_verifier import ImperativeObligation

from abstract_syntax import (
    All, And, Array, ArrayGet, ArraySet, Assert, AST, Associative, Auto, Bool,
    Call, Conditional, Constructor, Declaration, Define, Env, Export,
    Formula, FunCase, FunctionType, GenRecFun, Generic, GenericUnknownInst,
    Hole, IfThen, ImpAlloc, ImpAssert, ImpAssign, ImpAssume, ImpCallExpr,
    ImpIf, ImpReturn, ImpStmt, ImpVar, ImpWhile, Import, Inductive, Lambda,
    LValueField, LValueIndex, LValueVar, MakeArray, Module,
    MutableArrayType, ObjectDecl,
    ObjectField, ObserverDecl, Omitted, Or, OverloadType, OverloadedVar, PSorry, PVar,
    PatternBool, PatternCons, Postulate, Predicate, Print, ProcDecl, ProcParam,
    ProcSpec, Proof, RecFun, ResolvedVar, ResourceDecl, Rule, Some,
    Statement, Switch, SwitchCase, TAnnote, TermBinding, TLet, Term, TermInst, Theorem,
    Trace, Type, TypeAlias, TypeInst, TypeType, Union, Var, VarRef, VerboseLevel,
    ViewDecl, ViewRecFun, alpha_equiv, base_name, callable_name,
    check_post_typecheck_invariants, find_file, full_reduce, mkEqual,
    print_theorems, type_match, type_names,
)
from checker_cache import (
    _collect_defined_names, _collect_referenced_names, _hash_ast,
    _is_global_barrier, _record_hit, _record_miss, _stmt_cache,
)
from checker_common import *
from checker_predicates import (
    _build_predicate_translation, _check_predicate_strict_positivity,
    _predicate_style_hint, _validate_predicate_rule_shape,
    _validate_predicate_signature,
)
from checker_induction import match_induction
from checker_logic import pattern_to_term
from checker_proofs import _try_check_proof_of, generate_proof_name
from checker_types import (
    _check_array_index_type, check_constructor_pattern, check_formula,
    check_no_recfun_escape, check_pattern, check_strict_positivity, check_type,
    dirty_files, get_recursive_call_count, infer_param_polarities, is_modified,
    lookup_union, reset_recursive_call_count, type_check_formula,
    type_check_term, type_synth_term,
)
from error import (
    Diagnostic, ErrorSink, MatchFailed, error_header, get_active_sink,
    get_active_warning_sink, internal_error, set_active_sink, user_error,
    warning,
)
from flags import (
    get_check_imports, get_debugger, get_quiet_mode,
    get_target_hole_location, get_verbose, set_verbose,
)

imported_modules: set[str] = set()
checked_modules: set[str] = set()

Substitution = dict[str, Term | Type | RecFun | GenRecFun]
TypeMatching = dict[str, Type | VarRef | None]
ViewInfo = tuple[ViewDecl, Type, Type]
PatternCoverage = dict[str, bool]
ParamTypes = list[tuple[str, Type]]

def check_proc_signature(decl: ProcDecl, env: Env) -> tuple[Statement, Env]:
  # Phase 2b (issue #1111): type-check a procedure's signature -- its type
  # parameters, ordinary and ghost parameter types, optional return type, and
  # `requires`/`ensures`/`reads`/`modifies`/`decreases` spec clauses -- and
  # register the checked signature in `Env` so later `call` resolution finds
  # it. The body and proof slots are left to later slices. Duplicate proc
  # names are already rejected in `uniquify`.
  loc = decl.location
  type_env = env.declare_type_vars(loc, decl.type_params)

  # Parameter types. Duplicate parameter names are already rejected in
  # `uniquify` (before any binding is created), so they never reach here.
  checked_params: list[ProcParam] = []
  param_pairs: list[tuple[str, Type]] = []
  for p in decl.params:
    checked_ty = check_type(p.typ, type_env)
    checked_params.append(ProcParam(p.location, p.name, checked_ty, p.ghost))
    param_pairs.append((p.name, checked_ty))

  # `requires`, `reads`, `modifies`, and `decreases` see the parameters.
  param_env = type_env.declare_term_vars(loc, param_pairs)

  checked_return = None
  if decl.return_type is not None:
    checked_return = check_type(decl.return_type, type_env)

  # Postconditions additionally see `result`, bound to the return type.
  post_env = param_env
  if checked_return is not None and decl.result_name is not None:
    post_env = param_env.declare_term_var(loc, decl.result_name,
                                          checked_return, local=True)

  checked_specs: list[ProcSpec] = []
  seen_post_labels: set[str] = set()
  for spec in decl.specs:
    match spec.keyword:
      case 'requires':
        value = check_formula(cast(Term, spec.value), param_env)
        checked_specs.append(ProcSpec(spec.location, 'requires', value))
      case 'ensures':
        if spec.label is not None:
          if base_name(spec.label) in seen_post_labels:
            user_error(spec.location,
                       'duplicate postcondition label: '
                       + base_name(spec.label))
          seen_post_labels.add(base_name(spec.label))
        value = check_formula(cast(Term, spec.value), post_env)
        checked_specs.append(ProcSpec(spec.location, 'ensures', value,
                                      spec.label))
      case 'decreases':
        value = type_synth_term(cast(Term, spec.value), param_env, None, [])
        checked_specs.append(ProcSpec(spec.location, 'decreases', value))
      case _:  # 'reads' | 'modifies'
        # Frame expressions are checked structurally only: `uniquify` has
        # already resolved their subject names, but the footprint/heap
        # semantics needed to type a mutable-array read (`a[i]`, #1117) or a
        # `footprint(...)` (#1126) are later slices, so the frame list passes
        # through unchanged here.
        checked_specs.append(ProcSpec(spec.location, spec.keyword,
                                      spec.value))

  checked_decl = ProcDecl(loc, decl.name, decl.type_params, checked_params,
                          checked_return, checked_specs, decl.body,
                          decl.proof_block, decl.result_name,
                          visibility=decl.visibility)
  new_env = env.declare_proc(loc, decl.name, decl.type_params, checked_params,
                             checked_return, checked_specs, decl.visibility)
  return checked_decl, new_env

# Phase 2d (issue #1113): imperative statement forms whose *typing* is not yet
# modeled by the verifier. Procedure calls, allocations, mutable-array reads
# and writes, field writes, and `assert`/`assume`/loop obligations are all
# later slices (#1116-#1122); a body that uses any of them is left untouched
# here (and keeps emitting the Phase 1m "not verified" warning) rather than
# risk a spurious type error. Straight-line bodies over ordinary local `var`,
# assignment, `return`, and `if` are type-checked in full.
def _imp_stmt_unmodeled(s: ImpStmt) -> bool:
  # Field access (`s.rhs`/`s.lhs`) rather than positional matching: `ImpVar`
  # and `ImpAssign` hold their right-hand side at different positions, so a
  # shared positional pattern would silently read the wrong field.
  match s:
    case ImpVar():
      return isinstance(s.rhs, (ImpCallExpr, ImpAlloc))
    case ImpAssign():
      # Local-variable assignment (`x := e`) and mutable-array element writes
      # (`a[i] := v`, #1118) are modeled; object field writes (`p.f := v`)
      # and call/allocation right-hand sides are later slices.
      return isinstance(s.rhs, (ImpCallExpr, ImpAlloc)) \
          or isinstance(s.lhs, LValueField)
    case ImpIf(_, _, then_body, else_body):
      return _block_unmodeled(then_body) \
          or (else_body is not None and _block_unmodeled(else_body))
    case ImpReturn() | ImpAssert() | ImpAssume():
      return False
    case ImpWhile():
      # A local-state `while` (Phase 2l, #1116/#1121) is modeled as long as its
      # body is: a body that writes an array or calls a procedure keeps the
      # whole loop -- and so the procedure -- deferred.
      return _block_unmodeled(s.body)
    case _:
      # `call` statements.
      return True

def _block_unmodeled(stmts: list[ImpStmt]) -> bool:
  return any(_imp_stmt_unmodeled(s) for s in stmts)

def _declares_frame(decl: ProcDecl) -> bool:
  # Whether the procedure declares a `reads`/`modifies` frame. Frame semantics
  # and enforcement are #1119 (Phase 2j); until then a frame-declaring
  # procedure is not modeled (its body is neither type-checked nor verified) --
  # the frame subjects can name constructs this slice cannot type
  # (`footprint(p)`, object fields).
  return any(spec.keyword in ('reads', 'modifies') for spec in decl.specs)

def _proc_body_unmodeled(decl: ProcDecl) -> bool:
  # Mutable-array parameters are typeable now that reads (#1117) and element
  # writes (#1118) are modeled, so a proc is deferred only when it declares a
  # frame (#1119, not yet modeled) or its body uses a statement form
  # `_imp_stmt_unmodeled` still flags (calls, allocations, field writes,
  # `while`).
  return _declares_frame(decl) or _block_unmodeled(decl.body)

def _stmt_always_returns(s: ImpStmt) -> bool:
  match s:
    case ImpReturn():
      return True
    case ImpIf(_, _, then_body, else_body):
      return else_body is not None \
          and _block_always_returns(then_body) \
          and _block_always_returns(else_body)
    case _:
      return False

def _block_always_returns(stmts: list[ImpStmt]) -> bool:
  # Conservatively decide whether a block must execute a `return`. Only `true`
  # when we are certain, so a body that can fall off the end is never mistaken
  # for one that returns (the missing-return diagnostic stays sound; richer
  # path analysis is a later slice). Any statement that always returns makes
  # the whole block always return -- everything after it is unreachable.
  return any(_stmt_always_returns(s) for s in stmts)

def _array_write_element_type(loc: Meta, lhs: LValueIndex,
                              env: Env) -> Type:
  # The element type of the mutable array a write `a[i] := v` targets, after
  # checking that `a` names a mutable-array binding in scope. Shared by body
  # type-checking and verification so both agree on what a write means.
  binding = env.dict.get(lhs.array)
  if not isinstance(binding, TermBinding):
    user_error(loc, 'assignment to undefined array: ' + base_name(lhs.array))
  if not isinstance(binding.typ, MutableArrayType):
    user_error(loc, 'cannot index-assign to ' + base_name(lhs.array)
               + ' because it is not a mutable array; it has type '
               + str(binding.typ))
  return binding.typ.elt_type

def _type_check_array_write(loc: Meta, lhs: LValueIndex, rhs: Term,
                            env: Env) -> None:
  # A mutable-array element write `a[i] := v` (#1118): the index must be a
  # `UInt` (as for a read, #1117) and the value must have the element type.
  elt_type = _array_write_element_type(loc, lhs, env)
  new_index = type_synth_term(lhs.index, env, None, [])
  _check_array_index_type(new_index)
  type_check_term(rhs, elt_type, env, None, [])

def _type_check_imp_stmt(s: ImpStmt, env: Env,
                         return_type: Optional[Type]) -> Env:
  # Returns the environment as seen by the *following* statement in the same
  # block: a `var` extends it with the new local; everything else leaves it
  # unchanged. `Env` is functional, so nested `if` blocks type-check against a
  # value derived from `env` without leaking their locals back out.
  match s:
    case ImpVar(loc, name, type_annot, rhs, _):
      if type_annot is not None:
        var_ty = check_type(type_annot, env)
        type_check_term(cast(Term, rhs), var_ty, env, None, [])
      else:
        var_ty = type_synth_term(cast(Term, rhs), env, None, []).typeof
      return env.declare_term_var(loc, name, var_ty, local=True)
    case ImpAssign(loc, lhs, rhs):
      if isinstance(lhs, LValueIndex):
        _type_check_array_write(loc, lhs, cast(Term, rhs), env)
        return env
      target = cast(LValueVar, lhs)
      binding = env.dict.get(target.name)
      if not isinstance(binding, TermBinding):
        user_error(loc, 'assignment to undefined variable: '
                   + base_name(target.name))
      if not binding.local:
        user_error(loc, 'cannot assign to ' + base_name(target.name)
                   + ' because it is not a local variable')
      type_check_term(cast(Term, rhs), binding.typ, env, None, [])
      return env
    case ImpIf(loc, cond, then_body, else_body):
      type_check_formula(cond, env)
      _type_check_imp_block(then_body, env, return_type)
      if else_body is not None:
        _type_check_imp_block(else_body, env, return_type)
      return env
    case ImpReturn(loc, value):
      if return_type is None:
        user_error(loc, 'this procedure has no return type, so it may not '
                   + 'return a value')
      else:
        type_check_term(value, return_type, env, None, [])
      return env
    case ImpAssert(loc, formula, _):
      # The asserted formula must be a `bool`; the obligation that it actually
      # holds is discharged later in `verify_proc` (Phase 2f).
      type_check_formula(formula, env)
      return env
    case ImpAssume(loc, formula):
      # `assume` is proof-only: the formula must be a `bool`, and it becomes a
      # given for the statements that follow (see `proc_obligations`). It has
      # no runtime effect, so it never contributes to the state.
      type_check_formula(formula, env)
      return env
    case ImpWhile(loc, cond, invariants, _, _, body, _, _, _):
      # Phase 2l (#1121): the loop condition and each invariant must be a
      # `bool`, and the body type-checks against the enclosing environment
      # (its own locals stay block-scoped, matching uniquify). The `decreases`
      # measure is left for the termination slice (#1122).
      type_check_formula(cond, env)
      for inv in invariants:
        type_check_formula(inv, env)
      _type_check_imp_block(body, env, return_type)
      return env
    case _:
      return env

def _type_check_imp_block(stmts: list[ImpStmt], env: Env,
                          return_type: Optional[Type]) -> None:
  for s in stmts:
    env = _type_check_imp_stmt(s, env, return_type)

# Phase 2e (issue #1114): ghost-variable noninterference. `ghost` parameters
# and `ghost var` locals are proof-only, so Phase 6 can erase them without
# changing runtime behavior -- which is sound only if ghost data never
# influences runtime behavior. `imp_ghost_dependencies` is the core dependency
# predicate: the ghost names a term references. A runtime context whose result
# is nonempty would let proof-only data flow into runtime behavior and is
# rejected. Runtime data flowing *into* a ghost binding (and ghost bindings
# referencing each other) stays valid, so ghost contexts are never checked.
#
# This pass is purely syntactic -- it depends on uniquified names, not on
# types -- so unlike `type_check_proc_body` it runs on EVERY proc body,
# including ones deferred by `_proc_body_unmodeled`; otherwise the guarantee
# could be bypassed just by adding an unmodeled construct (e.g. a mutable-array
# parameter would defer the whole body and let a `return g` slip through).
# Contexts that need infrastructure not yet built are deliberately skipped: a
# `call`'s argument positions cannot be classified runtime-vs-ghost until call
# resolution knows which callee parameters are ghost (#1124/#1125), and a
# `call`/`new` right-hand side likewise, so those are left to their own slices.
# Proof-only contexts (`assert`/`assume`, loop invariants, decreases) may
# freely mention ghost data and are never checked.
def imp_ghost_dependencies(node: object, ghost_names: set[str]) -> set[str]:
  return _referenced_names(node) & ghost_names

def _reject_ghost_flow(loc: Meta, node: object, ghost_names: set[str],
                       context: str) -> None:
  refs = imp_ghost_dependencies(node, ghost_names)
  if refs:
    named = ', '.join(sorted(base_name(g) for g in refs))
    noun = 'ghost variables ' if len(refs) > 1 else 'ghost variable '
    user_error(loc, context + ' may not depend on ' + noun + named
               + ' because ghost data is proof-only and cannot influence '
               + 'runtime behavior')

def _lvalue_is_ghost(lhs: LValueVar | LValueIndex | LValueField,
                     ghost_names: set[str]) -> bool:
  # A write target is ghost exactly when the variable/array/object it names is
  # a ghost binding (mutable arrays are runtime today, so an indexed/field
  # write is normally a runtime context). Attribute access, not positional
  # matching: each `LValue*` dataclass leads with `location`, and the naming
  # field lives at a different position in each, so a positional pattern would
  # silently bind the wrong field.
  match lhs:
    case LValueVar():
      return lhs.name in ghost_names
    case LValueIndex():
      return lhs.array in ghost_names
    case _:
      return cast(LValueField, lhs).subject in ghost_names

def _ghost_check_stmt(s: ImpStmt, ghost_names: set[str]) -> None:
  # `ghost_names` grows in place as ghost locals come into scope; nested blocks
  # get a copy (see `_ghost_check_block`) so a branch/loop-local ghost
  # declaration does not leak out.
  match s:
    case ImpVar(loc, name, _, rhs, ghost):
      if ghost:
        ghost_names.add(name)
      elif not isinstance(rhs, (ImpCallExpr, ImpAlloc)):
        _reject_ghost_flow(loc, rhs, ghost_names,
                           "the initializer of runtime variable '"
                           + base_name(name) + "'")
    case ImpAssign(loc, lhs, rhs):
      if not _lvalue_is_ghost(lhs, ghost_names) \
         and not isinstance(rhs, (ImpCallExpr, ImpAlloc)):
        if isinstance(lhs, LValueIndex):
          _reject_ghost_flow(loc, lhs.index, ghost_names,
                             'an array index of a runtime assignment')
        _reject_ghost_flow(loc, rhs, ghost_names,
                           "a runtime assignment to '" + str(lhs) + "'")
    case ImpIf(loc, cond, then_body, else_body):
      _reject_ghost_flow(loc, cond, ghost_names, 'a branch condition')
      _ghost_check_block(then_body, ghost_names)
      if else_body is not None:
        _ghost_check_block(else_body, ghost_names)
    case ImpWhile(loc, cond, _, _, _, body, _, _, _):
      _reject_ghost_flow(loc, cond, ghost_names, 'a loop condition')
      _ghost_check_block(body, ghost_names)
    case ImpReturn(loc, value):
      _reject_ghost_flow(loc, value, ghost_names, 'a return value')
    case _:
      # `assert`/`assume` are proof-only; `call` argument classification is a
      # later slice (see the pass note above).
      pass

def _ghost_check_block(stmts: list[ImpStmt], ghost_names: set[str]) -> None:
  ghost_names = set(ghost_names)
  for s in stmts:
    _ghost_check_stmt(s, ghost_names)

def check_ghost_noninterference(decl: ProcDecl) -> None:
  _ghost_check_block(decl.body, {p.name for p in decl.params if p.ghost})

def type_check_proc_body(decl: ProcDecl, env: Env) -> None:
  # Phase 2d (issue #1113): type-check a procedure's straight-line body --
  # annotated and inferred local `var` declarations, assignments to local
  # variables, and `return` -- with lexical block scope. Bodies that use
  # constructs not yet modeled (see `_proc_body_unmodeled`) are deferred to
  # later slices. No specifications are proved here.
  if _proc_body_unmodeled(decl):
    return
  loc = decl.location
  type_env = env.declare_type_vars(loc, decl.type_params)
  param_pairs = [(p.name, p.typ) for p in decl.params]
  body_env = type_env.declare_term_vars(loc, param_pairs, local=True)
  _type_check_imp_block(decl.body, body_env, decl.return_type)
  if decl.return_type is not None and not _block_always_returns(decl.body):
    user_error(loc, "procedure '" + base_name(decl.name)
               + "' declares return type " + str(decl.return_type)
               + ' but may finish without returning a value')

# --- Phase 2f/2g/2i (issues #1115, #1116, #1118): procedure verification -----
# A procedure is *verifiable* by these slices when its body is built from local
# state and finite branching: local `var` declarations, assignments to a local
# variable or a mutable-array element (`a[i] := v`, #1118), `assert`, `assume`,
# `if`/`else` (recursively verifiable), and `return`, all with ordinary-term
# right-hand sides. Loops (`while`), procedure calls, allocations, and object
# field writes are later slices, so a body using any of them stays deferred
# (and keeps the Phase 1m warning).
def _loop_body_verifiable(s: ImpStmt) -> bool:
  # Phase 2l (#1121): the body of a verifiable local-state `while` is
  # straight-line local state -- local `var`/assignment (ordinary right-hand
  # sides), `assert`, and `assume`. Branching, nested loops, `return`, calls,
  # and mutable-array element writes inside a loop body are later slices
  # (array loops are #1128), so a loop containing any of them keeps the whole
  # procedure deferred.
  match s:
    case ImpVar():
      return not isinstance(s.rhs, (ImpCallExpr, ImpAlloc))
    case ImpAssign():
      return isinstance(s.lhs, LValueVar) \
          and not isinstance(s.rhs, (ImpCallExpr, ImpAlloc))
    case ImpAssert() | ImpAssume():
      return True
    case _:
      return False

def _stmt_verifiable(s: ImpStmt) -> bool:
  match s:
    case ImpVar():
      return not isinstance(s.rhs, (ImpCallExpr, ImpAlloc))
    case ImpAssign():
      return isinstance(s.lhs, (LValueVar, LValueIndex)) \
          and not isinstance(s.rhs, (ImpCallExpr, ImpAlloc))
    case ImpAssert() | ImpAssume() | ImpReturn():
      return True
    case ImpIf(_, _, then_body, else_body):
      return all(_stmt_verifiable(t) for t in then_body) \
          and (else_body is None
               or all(_stmt_verifiable(t) for t in else_body))
    case ImpWhile():
      return all(_loop_body_verifiable(t) for t in s.body)
    case _:
      # `call` statements.
      return False

def _assigns_to_a_parameter(decl: ProcDecl) -> bool:
  # Parameters are declared as locals, so the body checker permits assigning to
  # one. Without an entry-state/`old` snapshot (a later slice, #1120) a
  # postcondition mentioning a reassigned parameter is ambiguous between its
  # entry and exit value, so such a procedure is deferred rather than verified
  # against the entry value alone. `if` branches nest, so the scan recurses.
  param_names = {p.name for p in decl.params}
  def assigns(stmts: list[ImpStmt]) -> bool:
    for s in stmts:
      match s:
        case ImpAssign() if isinstance(s.lhs, LValueVar) \
                and s.lhs.name in param_names:
          return True
        case ImpIf(_, _, then_body, else_body):
          if assigns(then_body) \
             or (else_body is not None and assigns(else_body)):
            return True
        case ImpWhile():
          if assigns(s.body):
            return True
    return False
  return assigns(decl.body)

def _body_has_array_write(stmts: list[ImpStmt]) -> bool:
  # Whether the body performs a mutable-array element write `a[i] := v`
  # anywhere, recursing into `if` branches.
  for s in stmts:
    match s:
      case ImpAssign() if isinstance(s.lhs, LValueIndex):
        return True
      case ImpIf(_, _, then_body, else_body):
        if _body_has_array_write(then_body) \
           or (else_body is not None and _body_has_array_write(else_body)):
          return True
  return False

def _array_write_aliasing_risk(decl: ProcDecl) -> bool:
  # Phase 2i (#1118) models a write `a[i] := v` as a functional update of the
  # verifier state keyed by the *handle name* `a`, which is sound only when no
  # two handles can denote the same underlying array. The heap model that
  # resolves aliasing by array identity + dynamic frames is a later phase (see
  # docs/imperative-verification-plan.md, "One heap model"; frames are #1119).
  # Until then a writing procedure is deferred whenever more than one mutable-
  # array handle is reachable, because a write through one could be observed
  # through an alias. The chosen end-state is the Dafny-style identity-keyed
  # heap with dynamic frames (docs/imperative-verification-plan.md, "Aliasing
  # and identity"), landing with modifies-frame enforcement in #1119; this
  # deferral is the interim restriction until then. Reachable handles are the
  # mutable-array parameters plus
  # any local that copies a handle (`var y := a`); element reads (`var y :=
  # a[i]`) and lengths are scalars, not handles. Allocation (`new`) is out of
  # scope for this slice, so those are the only sources.
  array_params = {p.name for p in decl.params
                  if isinstance(p.typ, MutableArrayType)}
  if not array_params or not _body_has_array_write(decl.body):
    return False
  if len(array_params) > 1:
    return True

  def copies_a_handle(stmts: list[ImpStmt]) -> bool:
    for s in stmts:
      match s:
        case ImpVar() if isinstance(s.rhs, VarRef) \
                and s.rhs.get_name() in array_params:
          return True
        case ImpIf(_, _, then_body, else_body):
          if copies_a_handle(then_body) \
             or (else_body is not None and copies_a_handle(else_body)):
            return True
    return False
  return copies_a_handle(decl.body)

def _proc_verifiable(decl: ProcDecl) -> bool:
  # Frame semantics (#1119) are not modeled yet, so a frame-declaring proc is
  # deferred rather than verified against an unenforced frame.
  if _declares_frame(decl):
    return False
  # Aliasing between mutable-array handles is not modeled yet (#1118 keys the
  # verifier state by handle name); defer a writing proc with more than one
  # reachable array handle. See `_array_write_aliasing_risk`.
  if _array_write_aliasing_risk(decl):
    return False
  # An out-of-line `proof ... end` block supplies proof slots cited by
  # `by <slot>` clauses. Installing those slot bindings is out of scope for
  # this slice, so a procedure that declares one is deferred (an inline
  # `assert P by <proof>` with no proof block is still verified). #1115
  if decl.proof_block:
    return False
  if _assigns_to_a_parameter(decl):
    return False
  return all(_stmt_verifiable(s) for s in decl.body)

def _proc_givens(decl: ProcDecl) -> list[tuple[str, Formula]]:
  # Entry givens: every `requires` clause, in source order. Repeated clauses
  # are conjoined by the obligation's `givens_formula`. The generated
  # `requiresN` labels (like the `assertN`/`assumeN`/`ifN` labels
  # `proc_obligations` generates) are internal: they drive auto-discharge and
  # the `Givens:` presentation, but are deliberately not citable by name from a
  # manual inline proof (uniquify, which resolves proof `PVar`s, runs before
  # these are created). Binding in-scope givens for manual imperative proofs is
  # the proof-slot/context work of Phase 2n (#1123); keeping auto-labeled facts
  # available only to automation (not by a fabricated name) matches #1125.
  givens: list[tuple[str, Formula]] = []
  for spec in decl.specs:
    if spec.keyword == 'requires':
      givens.append(('requires' + str(len(givens)), cast(Formula, spec.value)))
  return givens

def _proc_postconditions(decl: ProcDecl, state: 'Substitution',
                         result: Optional[Term]) -> list[tuple[Meta, Formula]]:
  # One goal per `ensures` clause, anchored at that clause's own location so a
  # failure points at the postcondition the user wrote. Each clause is
  # evaluated in the exit state: `state` rewrites every mutated binding to its
  # symbolic value (so a written mutable-array parameter `a` becomes its
  # `ArraySet` update, #1118), and `result` (the symbolic returned value, or
  # None for a fall-through with no return value) is substituted for the bound
  # `result` name. Both happen in ONE pass -- `result` is already a value over
  # the exit state, so a combined substitution avoids rewriting inside it twice
  # (which would re-expand a mutated array handle unboundedly).
  sub: Substitution = dict(state)
  if result is not None and decl.result_name is not None:
    sub[decl.result_name] = result
  posts: list[tuple[Meta, Formula]] = []
  for spec in decl.specs:
    if spec.keyword != 'ensures':
      continue
    frm = cast(Formula, cast(Formula, spec.value).substitute(sub))
    posts.append((spec.location, frm))
  return posts

def _collect_array_gets(node: object, out: list[ArrayGet]) -> list[ArrayGet]:
  # Every `ArrayGet` subterm of `node`, in a generic structural walk (the AST's
  # `_map_children` visits each child field, including list elements, without
  # enumerating constructors). Used to raise a bounds obligation per executed
  # mutable-array read (#1118, and the design's "all array accesses are in
  # bounds" goal).
  if isinstance(node, ArrayGet):
    out.append(node)
  if isinstance(node, AST):
    def visit(child: AST) -> AST:
      _collect_array_gets(child, out)
      return child
    node._map_children(visit)
  return out

def _array_bounds_obligation(aloc: Meta, array_name: str,
                             arr_binding: TermBinding, index: Term,
                             givens: list[tuple[str, Formula]],
                             env: Env) -> 'ImperativeObligation':
  # The in-bounds obligation `i < length(a)` for a mutable-array write `a[i]`
  # (#1118). The goal is built by `index_in_bounds_goal`, shared with the read
  # path so both resolve `<`/`length` identically (#1166). `length` is
  # invariant under writes, so the base array handle -- not any symbolic write
  # state -- is used as the `length` argument regardless of earlier writes.
  from imperative_verifier import (
      ImperativeObligation, ObligationKind, index_in_bounds_goal)
  base_handle = OverloadedVar(arr_binding.location, arr_binding.typ,
                              [array_name])
  goal = index_in_bounds_goal(aloc, base_handle, index, env)
  return ImperativeObligation(aloc, goal, ObligationKind.ARRAY_BOUNDS,
                              givens=list(givens))

def proc_obligations(decl: ProcDecl,
                     env: Env) -> tuple[Env, list['ImperativeObligation']]:
  # Phase 2f/2g (issues #1115, #1116): the verification conditions of a
  # `_proc_verifiable` procedure, by path-sensitive forward symbolic execution.
  # `state` maps each local variable to its current value as a term over the
  # parameters, so substituting it into an assertion, returned expression, or
  # branch condition yields a goal or given mentioning only parameters.
  #
  # `if` splits the current path in two: the then-path carries the condition as
  # a given, the else-path its negation (a missing `else` is `skip`), and both
  # continue through the statements that follow the `if`. A `return` ends its
  # path (discharging the postconditions with the returned value); a path that
  # falls off the end discharges the postconditions with `result` unbound. Each
  # path keeps its own `state`/`givens`, so a fact asserted or assumed on one
  # branch is not visible on the other, and never before the statement itself.
  #
  # Obligations are emitted in path/source order, with per-path given labels
  # derived from `len(givens)`, so the ordering is deterministic. Pure w.r.t.
  # proof checking -- it only builds formulas -- so it can be unit-tested in
  # isolation from `verify_proc`, which discharges what it returns.
  #
  # Returns the environment obligations discharge in: the parameters plus every
  # local declared anywhere in the body. Goals and givens are substituted
  # through `state` and so mention only parameters, but an attached inline-
  # assert proof (`assert P by <proof>`) is stored unchanged and may reference a
  # body local in an intermediate step, so the locals must stay in scope for it
  # to type-check. Uniquify makes every local name globally unique, so gathering
  # them across all branch paths introduces no clashes.
  from imperative_verifier import ImperativeObligation, ObligationKind
  loc = decl.location
  type_env = env.declare_type_vars(loc, decl.type_params)
  base_env = type_env.declare_term_vars(
      loc, [(p.name, p.typ) for p in decl.params], local=True)
  obligations: list[ImperativeObligation] = []
  local_bindings: dict[str, tuple[Meta, Type]] = {}

  def emit_posts(result: Optional[Term], state: Substitution,
                 givens: list[tuple[str, Formula]]) -> None:
    for (post_loc, goal) in _proc_postconditions(decl, state, result):
      obligations.append(
          ImperativeObligation(post_loc, goal, ObligationKind.POSTCONDITION,
                               givens=list(givens)))

  PathEnd = Callable[[Substitution, list[tuple[str, Formula]], Env], None]

  def walk(stmts: list[ImpStmt], state: Substitution,
           givens: list[tuple[str, Formula]], cur_env: Env,
           on_end: PathEnd) -> None:
    def symbolic(rhs: Term, typ: Type) -> Term:
      checked = type_check_term(rhs, typ, cur_env, None, [])
      record_reads(checked, givens, cur_env)
      return cast(Term, checked.substitute(state))

    def record_reads(checked: object, givens: list[tuple[str, Formula]],
                     cur_env: Env) -> None:
      # Every executed mutable-array read `a[j]` in `checked` owes an in-bounds
      # obligation `j < length(a)` (#1118; the design's "all array accesses are
      # in bounds" goal). A read's handle is a parameter -- a proc that could
      # alias handles is deferred (`_array_write_aliasing_risk`) -- so the
      # subject is a `VarRef` naming a mutable-array binding.
      for read in _collect_array_gets(checked, []):
        subj = read.subject
        if not isinstance(subj, VarRef):
          continue
        binding = cur_env.dict.get(subj.get_name())
        if isinstance(binding, TermBinding) \
           and isinstance(binding.typ, MutableArrayType):
          idx = cast(Term, read.position.substitute(state))
          obligations.append(_array_bounds_obligation(
              read.location, subj.get_name(), binding, idx, givens, cur_env))

    for idx, s in enumerate(stmts):
      match s:
        case ImpVar(vloc, name, type_annot, rhs, _):
          if type_annot is not None:
            var_ty = check_type(type_annot, cur_env)
            state[name] = symbolic(cast(Term, rhs), var_ty)
          else:
            checked = type_synth_term(cast(Term, rhs), cur_env, None, [])
            var_ty = checked.typeof
            record_reads(checked, givens, cur_env)
            state[name] = cast(Term, checked.substitute(state))
          local_bindings[name] = (vloc, var_ty)
          cur_env = cur_env.declare_term_var(vloc, name, var_ty, local=True)
        case ImpAssign(aloc, lhs, rhs) if isinstance(lhs, LValueIndex):
          # Mutable-array element write `a[i] := v` (#1118): model it as a
          # functional `ArraySet` update of the array's symbolic state, so a
          # downstream read `a[j]` reduces by read-over-write. The write owes an
          # in-bounds obligation `i < length(a)`; `symbolic` also records the
          # bounds of any reads inside the index and value.
          arr_binding = cast(TermBinding, cur_env.dict[lhs.array])
          elt_type = cast(MutableArrayType, arr_binding.typ).elt_type
          new_index = type_synth_term(lhs.index, cur_env, None, [])
          _check_array_index_type(new_index)
          record_reads(new_index, givens, cur_env)
          sym_index = cast(Term, new_index.substitute(state))
          sym_value = symbolic(cast(Term, rhs), elt_type)
          obligations.append(_array_bounds_obligation(
              aloc, lhs.array, arr_binding, sym_index, givens, cur_env))
          current = state.get(lhs.array,
                              OverloadedVar(arr_binding.location,
                                            arr_binding.typ, [lhs.array]))
          state[lhs.array] = ArraySet(aloc, arr_binding.typ, current,
                                      sym_index, sym_value)
        case ImpAssign(_, lhs, rhs):
          target = cast(LValueVar, lhs)
          binding = cast(TermBinding, cur_env.dict[target.name])
          state[target.name] = symbolic(cast(Term, rhs), binding.typ)
        case ImpAssert(aloc, formula, proof):
          checked = type_check_formula(formula, cur_env)
          record_reads(checked, givens, cur_env)
          goal = cast(Formula, checked.substitute(state))
          obligations.append(
              ImperativeObligation(aloc, goal, ObligationKind.ASSERTION,
                                   givens=list(givens), proof=proof))
          # The asserted fact is available to everything downstream.
          givens = givens + [('assert' + str(len(givens)), goal)]
        case ImpAssume(_, formula):
          # `assume` has no runtime effect; it only adds a proof-only given for
          # the statements that follow it on this path. Its reads are trusted
          # (like a `requires`), so they raise no bounds obligation.
          fact = cast(Formula,
                      type_check_formula(formula, cur_env).substitute(state))
          givens = givens + [('assume' + str(len(givens)), fact)]
        case ImpIf(iloc, cond, then_body, else_body):
          checked_cond = type_check_formula(cond, cur_env)
          record_reads(checked_cond, givens, cur_env)
          cond_frm = cast(Formula, checked_cond.substitute(state))
          neg = IfThen(iloc, None, cond_frm, Bool(iloc, None, False))
          rest = stmts[idx + 1:]
          # Both branches are checked against the same continuation; each gets
          # its own copy of `state` so a branch-local write does not leak out.
          walk(cast(list[ImpStmt], then_body) + rest, dict(state),
               givens + [('if' + str(len(givens)), cond_frm)], cur_env, on_end)
          else_stmts = cast(list[ImpStmt], else_body) if else_body is not None \
              else []
          walk(else_stmts + rest, dict(state),
               givens + [('if' + str(len(givens)), neg)], cur_env, on_end)
          return  # both branch paths already handled the continuation
        case ImpWhile():
          handle_while(s, stmts[idx + 1:], state, givens, cur_env, on_end)
          return  # the loop owns the continuation on every exit path
        case ImpReturn(_, value):
          result = symbolic(value, cast(Type, decl.return_type))
          emit_posts(result, state, givens)
          return  # a `return` is terminal; anything after it is unreachable
    on_end(state, givens, cur_env)

  def handle_while(s: ImpWhile, rest: list[ImpStmt], state: Substitution,
                   givens: list[tuple[str, Formula]], cur_env: Env,
                   on_end: PathEnd) -> None:
    # Phase 2l (#1121): a local-state `while` loop. Its invariants must hold on
    # ENTRY (in the current state), be PRESERVED by one arbitrary iteration, and
    # -- with the negated loop condition -- carry the EXIT continuation. The
    # `decreases` measure (termination, #1122) and `modifies` frames (#1119) are
    # out of scope here; loop bodies are straight-line local state
    # (`_loop_body_verifiable`), so preservation is a single path.
    inv_checked = [cast(Formula, type_check_formula(inv, cur_env))
                   for inv in s.invariants]
    cond_checked = cast(Formula, type_check_formula(s.cond, cur_env))

    def invariant_goals(sub: Substitution) -> list[tuple[Meta, Formula]]:
      return [(inv.location, cast(Formula, checked.substitute(sub)))
              for (inv, checked) in zip(s.invariants, inv_checked)]

    def emit_invariants(sub: Substitution,
                        path_givens: list[tuple[str, Formula]],
                        kind: 'ObligationKind',
                        proof: Optional[Proof]) -> None:
      goals = invariant_goals(sub)
      if not goals:
        return
      if proof is not None:
        # A user `established`/`preserved` proof covers the whole invariant
        # conjunction, so it drives one combined obligation at the loop header.
        conj = goals[0][1] if len(goals) == 1 \
            else cast(Formula, And(s.location, None, [g for (_l, g) in goals]))
        obligations.append(
            ImperativeObligation(goals[0][0], conj, kind,
                                 givens=list(path_givens), proof=proof))
      else:
        for (goal_loc, goal) in goals:
          obligations.append(
              ImperativeObligation(goal_loc, goal, kind,
                                   givens=list(path_givens)))

    # Entry: the invariants must hold in the current (pre-loop) state.
    emit_invariants(state, givens, ObligationKind.LOOP_ENTRY, s.established)

    # Havoc the locals the loop assigns. Dropping them from the state leaves
    # them symbolic (as themselves), constrained only by the invariants and the
    # loop condition. A carried given that mentions one describes its pre-loop
    # value and would be unsound to keep (e.g. an invariant an *earlier* loop
    # exported about a local this loop reassigns), so such givens are dropped
    # too; the invariants are the only facts about a modified local afterwards.
    modified = {t.lhs.name for t in s.body
                if isinstance(t, ImpAssign) and isinstance(t.lhs, LValueVar)}
    havoc_state = {k: v for (k, v) in state.items() if k not in modified}
    havoc_givens = [(lbl, frm) for (lbl, frm) in givens
                    if not (_referenced_names(frm) & modified)]

    def loop_givens(negate_cond: bool) -> list[tuple[str, Formula]]:
      g = list(havoc_givens)
      for (_l, inv) in invariant_goals(havoc_state):
        g.append(('invariant' + str(len(g)), inv))
      guard = cast(Formula, cond_checked.substitute(havoc_state))
      if negate_cond:
        guard = IfThen(s.cond.location, None, guard,
                       Bool(s.cond.location, None, False))
      g.append(('condition' + str(len(g)), guard))
      return g

    # Preservation: assume the invariants and the loop condition, run one
    # iteration of the body, then re-check the invariants in the resulting
    # state (the body's fall-through continuation).
    def preserved_end(body_state: Substitution,
                      body_givens: list[tuple[str, Formula]],
                      _body_env: Env) -> None:
      emit_invariants(body_state, body_givens,
                      ObligationKind.LOOP_PRESERVATION, s.preserved)
    walk(list(s.body), dict(havoc_state), loop_givens(negate_cond=False),
         cur_env, preserved_end)

    # Exit: continue past the loop with the invariants and the negated loop
    # condition as givens, over the havoced state.
    walk(rest, dict(havoc_state), loop_givens(negate_cond=True), cur_env,
         on_end)

  def top_end(state: Substitution, path_givens: list[tuple[str, Formula]],
              _env: Env) -> None:
    # A path that falls off the end of the procedure without returning: its
    # postconditions hold with `result` unbound (so they may not mention
    # `result`). The fall-through state still rewrites any mutated binding.
    emit_posts(None, state, path_givens)

  walk(decl.body, {}, _proc_givens(decl), base_env, top_end)
  discharge_env = base_env
  for (name, (vloc, var_ty)) in local_bindings.items():
    discharge_env = discharge_env.declare_term_var(vloc, name, var_ty,
                                                    local=True)
  return discharge_env, obligations

def verify_proc(decl: ProcDecl, env: Env) -> None:
  # Phase 2f (issue #1115): verify a straight-line procedure by discharging
  # every obligation `proc_obligations` generates. A body this slice does not
  # model keeps the Phase 1m "not verified" warning instead (issue #1108).
  if not _proc_verifiable(decl):
    warn_unverified_imperative(decl)
    return
  cur_env, obligations = proc_obligations(decl, env)
  for obligation in obligations:
    obligation.discharge(cur_env)

def process_declaration_visibility(decl: Declaration, env: Env,
                                   module_chain: list[str],
                                   downstream_needs_checking: list[bool]
                                   ) -> tuple[Statement, Env]:
  match decl:
    case ProcDecl():
      return check_proc_signature(decl, env)

    case ObserverDecl() | ResourceDecl():
      return decl, env

    case Define(loc, name, ty, body):
      if ty == None:
        new_body = type_synth_term(body, env, None, [])
        new_ty = new_body.typeof
        # An unresolved overload is only meaningful as a define value when
        # every candidate is a function: such a name can still be narrowed at
        # each call site. A non-function overload (e.g. an overloaded nullary
        # constructor) has no use-site type to disambiguate it, so require an
        # annotation rather than storing an ambiguous value.
        if isinstance(new_ty, OverloadType) \
           and not all(isinstance(t, FunctionType) for (_, t) in new_ty.types):
          user_error(loc, "the value of '" + base_name(name)
                     + "' is ambiguous because it could have any of these types:\n\t"
                     + '\n\t'.join(str(t) for (_, t) in new_ty.types)
                     + "\nAdd a type annotation to disambiguate, e.g. "
                     + "define " + base_name(name) + " : <type> = ..."
                     + "\nOverloading is only allowed for function types.")
      else:
        new_ty = check_type(ty, env)
        new_body = body

      # Only allow overloading of functions
      unique_name = {base_name(n): n for n in env.dict.keys()}
      orig_name = base_name(name)
      if orig_name in unique_name.keys():
          match new_ty:
            case FunctionType(_, _, params, _):
              pass
            case _:
              binding = env.dict[unique_name[orig_name]]
              user_error(loc, 'the name ' + orig_name + ' is already defined:\n' \
                    + error_header(binding.location) \
                    + ' ' + orig_name + ' : ' + str(binding) + '\n' \
                    + 'Only functions may have multiple definitions with the same name.')
      decl.typ = new_ty
      return Define(loc, name, new_ty, new_body,
                    visibility=decl.visibility), \
              env.declare_term_var(loc, name, new_ty,
                                   visibility=decl.visibility)
  
    case RecFun(loc, name, typarams, params, returns, _):
      body_env = env.declare_type_vars(loc, typarams)
      checked_returns = check_type(returns, body_env)
      if len(params) == 0:
          user_error(loc, 'recursive functions need at least one parameter.')
      view_info = _instantiate_view_type(loc, params[0], body_env)
      if view_info is None:
        checked_params = [check_type(t, body_env) for t in params]
      else:
        _, source_ty, _ = view_info
        checked_params = [source_ty] + [check_type(t, body_env)
                                       for t in params[1:]]
      fun_type = FunctionType(loc, typarams, checked_params, checked_returns)
      # print('process declaration:')
      # print(decl.pretty_print(4))
      return decl, env.declare_term_var(loc, name, fun_type,
                                        visibility=decl.visibility)

    case GenRecFun(loc, name, typarams, param_pairs, returns, _, measure_ty,
                   body, _):
      body_env = env.declare_type_vars(loc, typarams)
      checked_returns = check_type(returns, body_env)
      checked_param_pairs = [(p, check_type(t, body_env) if t else None)
                             for (p, t) in param_pairs]
      [p for (p,t) in checked_param_pairs]
      param_types = [t for (p,t) in checked_param_pairs]
      if any([t == None for t in param_types]):
          user_error(loc, 'Add type annotations to the parameters.')
      checked_param_types: List[Type] = [cast(Type, t) for t in param_types]

      fun_type = FunctionType(loc, typarams, checked_param_types, checked_returns)
      # print('process declaration:')
      # print(decl.pretty_print(4))
      check_type(measure_ty, env)
      # return? GenRecFun(loc, name, typarams, params, returns, measure, measure_ty, body, terminates)
      # changed to decl
      return (decl, env.declare_term_var(loc, name, fun_type,
                                         visibility=decl.visibility))

    case ViewRecFun(loc, name, typarams, param_pairs, returns, _, _, _):
      body_env = env.declare_type_vars(loc, typarams)
      check_type(returns, body_env)
      for (p,t) in param_pairs:
          if t:
              check_type(t, body_env)
      param_types = [t for (p,t) in param_pairs]
      if any([t == None for t in param_types]):
          user_error(loc, 'Add type annotations to the parameters.')
      checked_param_types = [cast(Type, t) for t in param_types]
      if len(param_pairs) == 0:
          user_error(loc, 'viewrec needs at least one parameter to recurse on.')

      fun_type = FunctionType(loc, typarams, checked_param_types, returns)
      return (decl, env.declare_term_var(loc, name, fun_type,
                                         visibility=decl.visibility))

    case ViewDecl(loc, name, typarams, source, target, into, out, roundtrip,
                  inverse):
      body_env = env.declare_type_vars(loc, typarams)
      checked_source = check_type(source, body_env)
      checked_target = check_type(target, body_env)
      checked_decl = ViewDecl(loc, name, typarams, checked_source,
                              checked_target, into, out, roundtrip,
                              inverse,
                              visibility=decl.visibility)
      _check_view_function_type(loc, into,
                                FunctionType(loc, typarams,
                                             [checked_source], checked_target),
                                env, "into")
      _check_view_function_type(loc, out,
                                FunctionType(loc, typarams,
                                             [checked_target], checked_source),
                                env, "out")
      return checked_decl, env.declare_view(loc, checked_decl,
                                            decl.visibility)

    case TypeAlias(loc, name, typarams, body):
      body_env = env.declare_type_vars(loc, typarams)
      checked_body = check_type(body, body_env)
      checked_alias = TypeAlias(loc, name, typarams, checked_body,
                                visibility=decl.visibility)
      return checked_alias, env.define_type(loc, name, checked_alias,
                                            decl.visibility)

    case ObjectDecl(loc, name, typarams, fields):
      env = env.define_type(loc, name, decl, decl.visibility)
      body_env = env.declare_type_vars(loc, typarams)
      checked_fields = None
      if fields is not None:
        seen_fields: set[str] = set()
        checked_fields = []
        for field in fields:
          if field.name in seen_fields:
            user_error(field.location,
                       "duplicate object field name: " + base_name(field.name))
          seen_fields.add(field.name)
          checked_fields.append(ObjectField(field.location, field.name,
                                            check_type(field.typ, body_env),
                                            field.ghost))
      checked_object = ObjectDecl(loc, name, typarams, checked_fields,
                                  visibility=decl.visibility)
      return checked_object, env.define_type(loc, name, checked_object,
                                             decl.visibility)
  
    case Union(loc, name, typarams, alts):
      env = env.define_type(loc, name, decl, decl.visibility)
      # ResolvedVar is a VarRef in the class hierarchy but acts as a
      # Type wherever a Deduce type is named by an identifier (e.g.
      # `T<X>` parses to `TypeInst(typ=ResolvedVar("T"), ...)`).
      # Cast at the construction sites rather than widening every
      # `typ: Type` annotation across abstract_syntax.
      union_type = cast(Type, ResolvedVar(loc, None, name))
      body_env = env.declare_type_vars(loc, typarams)
      body_union_type = union_type
      infer_param_polarities(decl, body_env)
      new_alts = []
      for constr in alts:
        constr_type: Type
        if len(constr.parameters) > 0:
          if len(typarams) > 0:
            tyvars = [cast(Type, ResolvedVar(loc, None, p)) for p in typarams]
            return_type: Type = TypeInst(loc, body_union_type, tyvars)
          else:
            return_type = body_union_type
          # Narrow each constructor parameter's type. The check_type
          # return goes back into the new Constructor so the union's
          # AST has ResolvedVars in place of single-candidate
          # OverloadedVars.
          new_params = []
          for ty in constr.parameters:
            new_ty = check_type(ty, body_env)
            check_strict_positivity(new_ty, name, body_env)
            new_params.append(new_ty)
          constr_type = FunctionType(constr.location, typarams,
                                     new_params, return_type)
          new_constr = Constructor(constr.location, constr.name, new_params)
        elif len(typarams) > 0:
          constr_type = GenericUnknownInst(loc, union_type)
          new_constr = constr
        else:
          constr_type = union_type
          new_constr = constr

        env = env.declare_term_var(loc, constr.name, constr_type,
                                   visibility=decl.visibility)
        new_alts.append(new_constr)
      checked_union = Union(loc, name, typarams, new_alts,
                            visibility=decl.visibility)
      if decl.param_polarities is not None:
        checked_union.param_polarities = decl.param_polarities
      env = env.define_type(loc, name, checked_union, decl.visibility)
      return checked_union, env

    case Import(loc, name, ast, visibility=vis):
      old_verbose = get_verbose()
      if get_verbose() == VerboseLevel.CURR_ONLY:
        set_verbose(VerboseLevel.NONE)

      if name in module_chain:
          user_error(loc, 'error, recusive import:\n\t' + name\
                + '\nwhile processing files:\n\t' \
                + ', '.join(module_chain))
      elif name in imported_modules:
          set_verbose(old_verbose)
          if name in dirty_files:
              downstream_needs_checking[0] = True
          return Import(loc, name, ast, visibility=vis), env
      else:
          current_module = env.get_current_module()
          imported_modules.add(name)
          module_chain = [name] + module_chain

          filename = find_file(loc, name)
          needs_checking = [get_check_imports() and is_modified(filename)]

          ast2 = []
          assert ast is not None
          check_exported_contract_visibility(ast)
          for s in ast:
            new_s, env = process_declaration(s, env, module_chain, needs_checking)
            ast2.append(new_s)

          ast3 = []
          already_done_imports : dict[str, bool] = {}
          for s in ast2:
            new_s = type_check_stmt(s, env, already_done_imports)
            if new_s != None:
              ast3.append(new_s)

          if needs_checking[0]:
              dirty_files.add(name)
              downstream_needs_checking[0] = True
            
          if needs_checking[0] and name not in checked_modules:
              if get_quiet_mode() == False:
                  print('> checking ' + name)
              
          for s in ast3:
            env = collect_env(s, env)

            # TODO: only check if the pf file is newer than the thm file
            if name not in checked_modules and needs_checking[0]:
              check_proofs(s, env)
            
          if name not in checked_modules:
            checked_modules.add(name)  

          set_verbose(old_verbose)

          if needs_checking[0]:
            print_theorems(filename, ast3)
          
          return Import(loc, name, ast3, visibility=decl.visibility), \
              env.declare_module(current_module)

    case Predicate(loc, name, typarams, sig, rules, keyword):
      if typarams:
        # Generic predicates / relations are syntactically accepted but
        # the translation isn't yet finished: the auto-generated intro
        # theorems (and the rule_induction / rule_inversion theorems)
        # would each need an outer `all <T>:type. ...` quantifier, the
        # synthesised proofs would need to thread `arbitrary <T>:type`
        # through, and every internal reference to the predicate /
        # validator / constructors would need explicit type
        # instantiation. None of that is hard, just additive — flagged
        # for a follow-up commit.
        user_error(loc,
              "generic " + keyword + "s (with '<...>' type parameters) "
              "are not yet supported. Drop the type parameter list and "
              "specialise to a concrete type for now; full generics "
              "land in a follow-up commit.")

      body_env = env.declare_type_vars(loc, typarams)

      arity, param_types, checked_sig = _validate_predicate_signature(
          sig, name, keyword, body_env)

      _predicate_style_hint(loc, name, keyword, arity)

      # Register the predicate as a term-var so calls to it in rule bodies
      # type-check correctly. The predicate's full type combines the outer
      # type parameters from `predicate FOO<...>` with anything declared
      # inside the signature itself.
      pred_type: Type
      if isinstance(checked_sig, FunctionType):
        pred_type = FunctionType(checked_sig.location,
                                 list(typarams) + list(checked_sig.type_params),
                                 checked_sig.param_types,
                                 checked_sig.return_type)
      else:
        pred_type = checked_sig
      rule_env = body_env.declare_term_var(loc, name, pred_type,
                                           visibility=decl.visibility)

      checked_rules = []
      for rule in rules:
        _validate_predicate_rule_shape(rule, name, keyword, arity, rule_env)
        # Type-check the rule's body. This catches argument-type mismatches
        # in both the conclusion and the premises (which the shape pass does
        # not look at), and is what makes `even(true)` an error here rather
        # than later in the pipeline.
        checked_formula = check_formula(rule.formula, rule_env)
        checked_rules.append(Rule(rule.location, rule.name, checked_formula))

      for rule in checked_rules:
        _check_predicate_strict_positivity(rule, name, keyword, body_env)

      # Translation: lower this predicate to a Define (impredicative
      # encoding) plus one Postulate per rule. The generated decls are
      # threaded through the rest of the pipeline inline (mirroring how
      # Import processes its sub-AST), then stashed on the Predicate AST
      # node so the outer passes can recognise it as already handled.
      decl.signature = checked_sig
      decl.rules = checked_rules
      translated = _build_predicate_translation(decl, param_types)

      processed = []
      for s in translated:
        new_s, env = process_declaration(s, env, module_chain,
                                         downstream_needs_checking)
        processed.append(new_s)

      typed = []
      inline_imports : dict[str, bool] = {}
      for s in processed:
        new_s = type_check_stmt(s, env, inline_imports)
        if new_s is not None:
          typed.append(new_s)

      for s in typed:
        env = collect_env(s, env)

      decl.translated_ast = typed
      return decl, env

    case _:
      internal_error(decl.location, "unrecognized declaration:\n" + str(decl))


def process_declaration(stmt: Statement, env: Env,
                        module_chain: list[str],
                        downstream_needs_checking: list[bool]
                        ) -> tuple[Statement, Env]:
  if get_verbose():
    print('process_declaration(' + str(stmt) + ')')
    
  match stmt:
    case Theorem(loc, name, _, _):
      return stmt, env
  
    case Postulate(loc, name, _):
      return stmt, env

    case Declaration():
      return process_declaration_visibility(stmt, env, module_chain, downstream_needs_checking)
  
    case Assert(loc, _):
      return stmt, env
  
    case Print(loc, _):
      return stmt, env

    case Auto(loc, name):
      return stmt, env
  
    case Associative(loc, typarams, _, typeof):
      body_env = env.declare_type_vars(loc, typarams)
      checked_type = check_type(typeof, body_env)
      return Associative(loc, typarams, stmt.op, checked_type), env
  
    case Export(loc, name):
      return stmt, env
        
    case Module(loc, name):
      return stmt, env.declare_module(name)
    
    case Trace(loc, name):
      return stmt, env
    
    case Inductive(loc, typ, name):
      # `inductive Foo by ...` names a union by its bare name; suppress
      # the generic-arity check so `inductive Foo by ...` works when Foo
      # is a generic union. The `case Inductive(...)` in check_proofs
      # enforces that ``typ`` is a ``VarRef``.
      checked_typ = check_type(typ, env, arity_required=False)
      return Inductive(loc, checked_typ, name), env
  
    case _:
      internal_error(stmt.location, "in process_declaration, unrecognized statement:\n" + str(stmt))

def type_check_fun_case(fun_case: FunCase, name: str, params: list[Type],
                        returns: Type, body_env: Env,
                        cases_present: PatternCoverage) -> FunCase:
    body_env = check_pattern(fun_case.pattern, params[0], body_env, cases_present)
    fun_case.rator = type_synth_term(fun_case.rator, body_env, None, [])
    if len(fun_case.parameters) != len(params[1:]):
      user_error(fun_case.location, 'incorrect number of parameters, '\
            + 'expected ' + str(len(params)))
    body_env = body_env.declare_term_vars(fun_case.location,
                                          zip(fun_case.parameters, params[1:]))
    match fun_case.pattern:
      case PatternCons(_, _, parameters):
        pat_params = parameters
      case PatternBool(_, _):
        pat_params = []
    new_body = type_check_term(fun_case.body, returns, body_env, name, pat_params)
    check_no_recfun_escape(new_body, name)
    return FunCase(fun_case.location, fun_case.rator,
                   fun_case.pattern, fun_case.parameters, new_body)

def type_check_view_recursive_fun(stmt: RecFun, env: Env,
                                  view_info: ViewInfo) -> GenRecFun:
  loc = stmt.location
  name = stmt.name
  typarams = stmt.type_params
  params = stmt.params
  returns = stmt.returns
  cases = stmt.cases
  view_decl, source_ty, view_ty = view_info

  body_env = env.declare_type_vars(loc, typarams)
  checked_params = [source_ty] + [check_type(p, body_env)
                                 for p in params[1:]]
  checked_returns = check_type(returns, body_env)
  param_names = [generate_proof_name("view_arg")] \
    + [generate_proof_name("arg") for _ in checked_params[1:]]
  param_pairs = _as_param_pairs(param_names, checked_params)

  fun_type = _alpha_renamed_function_type(loc, typarams, checked_params,
                                          checked_returns)
  fun_value = _viewrec_placeholder(loc, name, typarams, param_pairs,
                                   checked_returns, stmt.visibility)
  env = env.define_term_var(loc, name, fun_type, fun_value, stmt.visibility)
  case_env = env.declare_type_vars(loc, typarams)
  case_env = case_env.declare_term_vars(loc, param_pairs)

  checked_subject = ResolvedVar(loc, checked_params[0], param_names[0])
  checked_view = type_check_term(view_call(loc, view_decl.into,
                                           checked_subject),
                                 view_ty, case_env, None, [])
  cases_present: PatternCoverage = {}
  new_cases: list[SwitchCase] = []
  reset_recursive_call_count()
  rec_ty = checked_params[0]

  for c in cases:
    new_env = check_pattern(c.pattern, view_ty, case_env, cases_present)
    if len(c.parameters) != len(checked_params[1:]):
      user_error(c.location, 'incorrect number of parameters, expected '
                 + str(len(checked_params) - 1))
    new_env = new_env.declare_term_vars(c.location,
                                        zip(c.parameters, checked_params[1:]))
    subterms = _viewrec_recursive_binders(c.pattern, rec_ty, new_env)
    new_body = type_check_term(c.body, checked_returns, new_env, name,
                               subterms)
    check_no_recfun_escape(new_body, name)
    for i, p in reversed(list(enumerate(c.parameters, start=1))):
      rhs = ResolvedVar(c.location, checked_params[i], param_names[i])
      new_body = TLet(c.location, checked_returns, p, rhs, new_body)
    new_cases.append(SwitchCase(c.location, c.pattern, new_body))

  uniondef = lookup_union(loc, view_ty, env)
  for alt in uniondef.alternatives:
    if alt.name not in cases_present.keys():
      user_error(loc, 'recursive function using view '
                 + base_name(view_decl.name)
                 + ' is missing a view case for ' + base_name(alt.name))

  if get_recursive_call_count() == 0:
      user_error(loc, name + ' is declared recursive, but does not make any recursive calls.\n' \
            + 'Use a "fun" statement instead.')

  body = Switch(loc, checked_returns, checked_view, new_cases)
  measure = ResolvedVar(loc, rec_ty, param_names[0])
  return GenRecFun(loc, name, typarams, param_pairs, checked_returns,
                   measure, rec_ty, body, PSorry(loc), True,
                   visibility=stmt.visibility)

def _alpha_renamed_function_type(loc: Meta, typarams: list[str],
                                 param_types: list[Type],
                                 returns: Type) -> FunctionType:
  new_typarams = [generate_proof_name(t) for t in typarams]
  sub: Substitution = {
      x: ResolvedVar(loc, None, y) for (x, y) in zip(typarams, new_typarams)
  }
  return FunctionType(loc, new_typarams,
                      [t.substitute(sub) for t in param_types],
                      returns.substitute(sub))

def _view_type_head_and_args(typ: Type | VarRef) -> tuple[VarRef | None, list[Type]]:
  if isinstance(typ, VarRef):
    return typ, []
  match typ:
    case TypeInst(_, head, args) if isinstance(head, VarRef):
      return head, args
    case _:
      return None, []

def _instantiate_view_type(loc: Meta, typ: Type | VarRef,
                           env: Env) -> ViewInfo | None:
  head, args = _view_type_head_and_args(typ)
  if head is None:
    return None
  view = env.get_view(head)
  if view is None:
    return None
  if len(args) != len(view.type_params):
    user_error(loc, "view " + base_name(view.name) + " expects "
               + str(len(view.type_params)) + " type argument"
               + ("" if len(view.type_params) == 1 else "s")
               + ", not " + str(len(args)))
  checked_args = [cast(Type, check_type(arg, env)) for arg in args]
  sub: Substitution = {x: t for (x, t) in zip(view.type_params, checked_args)}
  source = view.source.substitute(sub)
  target = view.target.substitute(sub)
  return view, source, target

def _as_param_pairs(names: list[str], types: list[Type]) -> list[tuple[str, Type]]:
  return [(x, t) for (x, t) in zip(names, types)]

def _viewrec_placeholder(loc: Meta, name: str, typarams: list[str],
                         params: ParamTypes, returns: Type,
                         visibility: str) -> GenRecFun:
  return GenRecFun(loc, name, typarams, params, returns,
                   ResolvedVar(loc, None, params[0][0]), params[0][1],
                   Hole(loc, None), PSorry(loc), True,
                   visibility=visibility)

def _viewrec_recursive_binders(pattern: PatternBool | PatternCons,
                               rec_ty: Type, env: Env) -> list[str]:
  binders = []
  match pattern:
    case PatternCons(_, _, params):
      for name in params:
        ty = env.get_type_of_term_var(ResolvedVar(pattern.location, None, name))
        if ty == rec_ty:
          binders.append(name)
  return binders

def _check_view_function_type(loc: Meta, name: str, expected: Type,
                              env: Env, label: str) -> None:
  actual = env.get_type_of_term_var(ResolvedVar(loc, None, name))
  if actual is None:
    user_error(loc, "undefined " + label + " function for view: "
               + base_name(name))
  if not alpha_equiv(actual, expected):
    user_error(loc, "view " + label + " function " + base_name(name)
               + " has type\n\t" + str(actual)
               + "\nbut expected\n\t" + str(expected))

def _view_composition_formula(loc: Meta, view: ViewDecl, val_type: Type,
                              inner: str, outer: str) -> Formula:
  """Build `all <type_params>. all v:val_type. outer(inner(v)) = v`."""
  value_name = generate_proof_name("v")
  value = ResolvedVar(loc, val_type, value_name)
  formula = mkEqual(loc,
                    view_call(loc, outer, view_call(loc, inner, value)),
                    value)
  formula = All(loc, None, (value_name, val_type), (0, 1), formula)
  for i, tp in enumerate(reversed(view.type_params)):
    formula = All(loc, None, (tp, TypeType(loc)),
                  (i, len(view.type_params)), formula)
  return formula

def _check_view_composition(loc: Meta, env: Env, label: str, proof_name: str,
                            formula: Formula) -> None:
  expected = type_check_formula(formula, env)
  actual = env.get_formula_of_proof_var(PVar(loc, proof_name))
  if actual is None:
    user_error(loc, "undefined " + label + " proof for view: "
               + base_name(proof_name))
  if not alpha_equiv(actual, expected):
    user_error(loc, "view " + label + " proof " + base_name(proof_name)
               + " proves\n\t" + str(actual)
               + "\nbut expected\n\t" + str(expected))

def _check_view_proofs(loc: Meta, view: ViewDecl, env: Env) -> None:
  _check_view_composition(
      loc, env, "roundtrip", view.roundtrip,
      _view_composition_formula(loc, view, view.target, view.out, view.into))
  if view.inverse is not None:
    _check_view_composition(
        loc, env, "inverse", view.inverse,
        _view_composition_formula(loc, view, view.source, view.into, view.out))

def _instantiate_view_for_subject(loc: Meta, view: ViewDecl,
                                  subject_ty: Type
                                  ) -> tuple[Type, Type, TypeMatching]:
  matching: TypeMatching = {}
  type_match(loc, type_names(loc, view.type_params),
             view.source, subject_ty, matching)
  sub = cast(Substitution, matching)
  return (view.source.substitute(sub),
          view.target.substitute(sub),
          matching)

def type_check_viewrec(stmt: ViewRecFun, env: Env) -> GenRecFun:
  loc = stmt.location
  name = stmt.name
  typarams = stmt.type_params
  param_pairs = stmt.vars
  returns = stmt.returns
  view_name = stmt.view_name
  view_subject = stmt.view_subject
  cases = stmt.cases

  body_env = env.declare_type_vars(loc, typarams)
  checked_params = [(x, check_type(t, body_env)) for (x, t) in param_pairs]
  checked_returns = check_type(returns, body_env)
  fun_type = _alpha_renamed_function_type(
      loc, typarams, [t for (_, t) in checked_params], checked_returns)
  fun_value = _viewrec_placeholder(loc, name, typarams, checked_params,
                                   checked_returns, stmt.visibility)
  env = env.define_term_var(loc, name, fun_type, fun_value, stmt.visibility)
  case_env = env.declare_type_vars(loc, typarams)
  case_env = case_env.declare_term_vars(loc, checked_params)

  view_decl = env.get_view(view_name)
  if view_decl is None:
    user_error(loc, "undefined view " + base_name(view_name))
  checked_subject = type_synth_term(view_subject, case_env, None, [])
  source_ty, view_ty, _ = _instantiate_view_for_subject(
      loc, view_decl, checked_subject.typeof)
  if source_ty != checked_params[0][1]:
    user_error(loc, "viewrec recurses on " + str(checked_params[0][1])
               + " but view " + base_name(view_name)
               + " views " + str(source_ty))
  checked_subject = type_check_term(view_subject, source_ty, case_env, None, [])
  checked_view = type_check_term(view_call(loc, view_decl.into,
                                           checked_subject),
                                 view_ty, case_env, None, [])
  cases_present: PatternCoverage = {}
  new_cases: list[SwitchCase] = []
  reset_recursive_call_count()
  rec_ty = checked_params[0][1]

  for c in cases:
    new_env = check_pattern(c.pattern, view_ty, case_env, cases_present)
    subterms = _viewrec_recursive_binders(c.pattern, rec_ty, new_env)
    new_body = type_check_term(c.body, checked_returns, new_env, name, subterms)
    check_no_recfun_escape(new_body, name)
    new_cases.append(SwitchCase(c.location, c.pattern, new_body))

  uniondef = lookup_union(loc, view_ty, env)
  for alt in uniondef.alternatives:
    if alt.name not in cases_present.keys():
      user_error(loc, 'viewrec is missing a view case for ' + base_name(alt.name))

  if get_recursive_call_count() == 0:
      user_error(loc, name + ' is declared viewrec, but does not make any recursive calls.\n' \
            + 'Use a "fun" statement instead.')

  body = Switch(loc, checked_returns, checked_view, new_cases)
  measure = ResolvedVar(loc, rec_ty, checked_params[0][0])
  return GenRecFun(loc, name, typarams, checked_params, checked_returns,
                   measure, rec_ty, body, PSorry(loc), True,
                   visibility=stmt.visibility)

def type_check_stmt(stmt: Statement, env: Env,
                    error_on_next_import: dict[str, bool]
                    ) -> Optional[Statement]:
  if get_verbose():
    print('type_check_stmt(' + str(stmt) + ')')
  match stmt:
    case Define(loc, name, ty, body):
      if ty == None:
        new_body = body # already type checked in process_declaration
        new_ty = body.typeof
      else:
        new_ty = check_type(ty, env)
        if isinstance(new_ty, OverloadType):
          # An unresolved overloaded value (all-function, per
          # process_declaration): there is no single type to check the body
          # against here -- it is resolved at each use site instead.
          new_body = body
        else:
          new_body = type_check_term(body, new_ty, env, None, [])
      return Define(loc, name, new_ty, new_body, visibility=stmt.visibility)
        
    case Theorem(loc, name, frm, pf, isLemma):
      new_frm = check_formula(frm, env)
      return Theorem(loc, name, new_frm, pf, isLemma,
                     visibility=stmt.visibility)

    case Postulate(loc, name, frm):
      new_frm = check_formula(frm, env)
      return Postulate(loc, name, new_frm, visibility=stmt.visibility)

    case Predicate():
      # The translation is processed inline during process_declaration
      # (`stmt.translated_ast` is the result). The wrapper itself has
      # nothing more to type-check.
      return stmt

    case RecFun(loc, name, typarams, params, returns, cases):
      if len(params) == 0:
        user_error(loc, 'recursive functions need at least one parameter.')
      view_info = _instantiate_view_type(loc, params[0],
                                         env.declare_type_vars(loc, typarams))
      if view_info is not None:
        return type_check_view_recursive_fun(stmt, env, view_info)

      body_env = env.declare_type_vars(loc, typarams)
      checked_params = [check_type(p, body_env) for p in params]
      checked_returns = check_type(returns, body_env)

      fun_type = _alpha_renamed_function_type(
          loc, typarams, checked_params, checked_returns)

      env = env.define_term_var(loc, name, fun_type, stmt.reduce(env),
                                stmt.visibility)
      cases_present: PatternCoverage = {}
      reset_recursive_call_count()
      new_cases = [type_check_fun_case(c, name, checked_params, checked_returns,
                                       body_env, cases_present) \
                   for c in cases]
      if get_recursive_call_count() == 0:
          user_error(loc, name + ' is declared recursive, but does not make any recursive calls.\n' \
                + 'Use a "fun" statement instead.')

      # check for completeness of cases
      uniondef = lookup_union(checked_params[0].location, checked_params[0], env)
      for c in uniondef.alternatives:
        if not c.name in cases_present.keys():
          user_error(loc, 'missing function case for ' + base_name(c.name))

      return RecFun(loc, name, typarams, checked_params, checked_returns,
                    new_cases, visibility=stmt.visibility)

    case GenRecFun(loc, name, typarams, param_pairs, returns, measure, measure_ty,
                   body, terminates):
      body_env = env.declare_type_vars(loc, typarams)
      checked_param_pairs = [(x, check_type(p, body_env))
                             for (x, p) in param_pairs]
      checked_returns = check_type(returns, body_env)
      checked_measure_ty = check_type(measure_ty, body_env)

      fun_type = _alpha_renamed_function_type(
          loc, typarams, [t for (_, t) in checked_param_pairs],
          checked_returns)

      env = env.define_term_var(loc, name, fun_type, stmt.reduce(env),
                                stmt.visibility)

      body_env = env.declare_type_vars(loc, typarams)
      body_env = body_env.declare_term_vars(loc, checked_param_pairs)
      new_measure = type_check_term(measure, checked_measure_ty, body_env, None, [])

      new_body = type_check_term(body, checked_returns, body_env, None, [])

      new_recfun = GenRecFun(loc, name, typarams, checked_param_pairs,
                             checked_returns, new_measure, checked_measure_ty,
                             new_body, terminates,
                             stmt.trusted_terminates,
                             visibility=stmt.visibility)
      # print('type check stmt:')
      # print(new_recfun.pretty_print(4))
      return new_recfun

    case ViewRecFun(loc, name, typarams, param_pairs, returns, _, _, cases):
      if len(param_pairs) == 0:
        user_error(loc, 'viewrec needs at least one parameter to recurse on.')
      return type_check_viewrec(stmt, env)

    case ViewDecl():
      return stmt

    case ProcDecl():
      # Phase 2d (issue #1113): type-check the procedure's straight-line body.
      # Specs are checked in `check_proc_signature` (Phase 2b); proving them is
      # a later slice, so the Phase 1m "not verified" warning still fires.
      # Phase 2e (issue #1114): the syntactic ghost-noninterference check runs
      # regardless of whether the body is type-modeled (see its note).
      check_ghost_noninterference(stmt)
      type_check_proc_body(stmt, env)
      return stmt

    case ObjectDecl() | ObserverDecl() | ResourceDecl():
      # Phase 1 imperative declarations (issue #854): recognized for module
      # boundaries and tooling, but their bodies and specs are not verified
      # here -- pass them through unchanged.
      return stmt

    case Trace(loc, var):
      var_ty = env.get_type_of_term_var(var)
      match var_ty:
        case FunctionType(_, _, _, _):
          pass
        case _:
          user_error(var.location, 'trace expects an identifer of type function, but instead got type ' + str(var_ty))
      return stmt
  
    case Union(loc, name, typarams, _):
      return stmt

    case TypeAlias():
      return stmt

    case Export(loc, name):
        return stmt
    
    case Import(loc, name, _):
      if name in error_on_next_import:
        if error_on_next_import[name]:
          # The first import was from the prelude
          # So instead of erroring we'll error next time
          # and return None to signal that this stmt should be removed
          error_on_next_import[name] = True
          return None # Return none to signify that this stmt should be removed
        else:
          # The user manually imported the module twice, so throw an error
          user_error(loc, "error, module:\n\t" + name + "\nwas imported twice")

      # If loc is empty then this import comes from the prelude
      error_on_next_import[name] = loc.empty
      return stmt
  
    case Assert(loc, frm):
      new_frm = check_formula(frm, env)
      return Assert(loc, new_frm)
  
    case Print(loc, trm):
      new_trm = type_synth_term(trm, env, None, [])
      return Print(loc, new_trm)

    case Auto(loc, name):
      return Auto(loc, name)
  
    case Associative(loc, typarams, op, typ):
      new_op = type_synth_term(op, env, None, [])
      body_env = env.declare_type_vars(loc, typarams)
      checked_type = check_type(typ, body_env)
      return Associative(loc, typarams, new_op, checked_type)
  
    case Module(loc, name):
      return stmt

    case Inductive(loc, ty, name):
      return Inductive(loc, ty, name)
  
    case _:
      internal_error(stmt.location,
                     "type checking, unrecognized statement:\n" + str(stmt))


def collect_env(stmt: Statement, env: Env) -> Env:
  if get_verbose():
    print('collect_env(' + str(stmt) + ')')
  match stmt:
    case Define(loc, name, ty, body):
      return env.define_term_var(loc, name, ty, body, stmt.visibility)
      
    case RecFun(loc, name, typarams, params, returns, _):
      fun_type = FunctionType(loc, typarams, params, returns)
      return env.define_term_var(loc, name, fun_type, stmt,
                                 stmt.visibility)

    case GenRecFun(loc, name, typarams, params, returns, _, _,
                  body, _):
      fun_type = FunctionType(loc, typarams, [t for (x,t) in params], returns)
      return env.define_term_var(loc, name, fun_type, stmt,
                                 stmt.visibility)

    case ViewRecFun(loc, name, typarams, params, returns, _, _, _):
      fun_type = FunctionType(loc, typarams, [t for (x,t) in params], returns)
      return env.define_term_var(loc, name, fun_type, stmt,
                                 stmt.visibility)

    case ViewDecl(loc, name, _, _, _, _, _, _, _):
      _check_view_proofs(loc, stmt, env)
      return env.declare_view(loc, stmt, stmt.visibility)
      
    case Union(loc, name, typarams, _):
      return env

    case TypeAlias():
      return env

    case ObjectDecl() | ProcDecl() | ObserverDecl() | ResourceDecl():
      return env

    case Theorem(loc, name, frm, _, _):
      return env.declare_proof_var(loc, name, frm)

    case Postulate(loc, name, frm):
      return env.declare_proof_var(loc, name, frm)

    case Predicate():
      # Already collected inline during process_declaration.
      return env

    case Export(loc, name, _):
      return env

    case Import(loc, name, _):
      return env
  
    case Assert(loc, frm):
      return env
  
    case Print(loc, _):
      return env

    case Module(loc, name):
      return env.declare_module(name)
  
    case Auto(loc, name):
      frm = env.get_formula_of_proof_var(name)
      return env.declare_auto_rewrite(loc, frm)
    
    case Inductive(loc, typ, name):
      frm = env.get_formula_of_proof_var(name)
      if not isinstance(cast(object, typ), VarRef):
        user_error(loc, "Only able to declare uninstantiated union types inductive")
      return env.declare_inductive(loc, match_induction(frm, typ), name)

      # Types, Predicate.
      # IfThen, Ands, all

      # Check that frm is a valid induction theorem, 
      # then declare it with the things it needs in the environment

        
    case Associative(loc, typarams, op, typ):
      # Example proof of associativity:
      # all U :type. all xs :List<U>, ys :List<U>, zs:List<U>. (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
      m_name = generate_proof_name("m")
      m_var = ResolvedVar(loc, typ, m_name)
      n_name = generate_proof_name("n")
      n_var = ResolvedVar(loc, typ, n_name)
      o_name = generate_proof_name("o")
      o_var = ResolvedVar(loc, typ, o_name)
      def makeOp(left: Term, right: Term) -> Call:
          return Call(loc, typ, op, [left,right])
      assoc_formula = mkEqual(loc, makeOp(makeOp(m_var, n_var), o_var),
                              makeOp(m_var, makeOp(n_var, o_var)))
      vars = [(m_name, typ), (n_name, typ), (o_name, typ)]
      for i, var in enumerate(reversed(vars)):
        assoc_formula = All(loc, None, var, (i,len(vars)), assoc_formula)
      
      for i, tp_name in enumerate(reversed(typarams)):
        assoc_formula = All(loc, None, (tp_name, TypeType(loc)), (i, len(typarams)), assoc_formula)

      assoc_formula = type_check_formula(assoc_formula, env)

      # determine which overload is for the given typ
      resolved_op = None
      op_ty = env.get_type_of_term_var(op)
      match op_ty:
          case OverloadType(_, overloads):
              for (x, funty) in overloads:
                  match funty:
                      case FunctionType(_, typarams2, param_types, _):
                          try:
                              matching: TypeMatching = {}
                              type_match(loc, typarams2, param_types[0], typ, matching)
                              resolved_op = x
                              break
                          except MatchFailed:
                              continue
          case FunctionType(_, typarams2, param_types, _):
              assert isinstance(op, VarRef)
              resolved_op = op.get_name()
      if assoc_formula in env.proofs():
          if resolved_op is None:
              user_error(loc, 'Could not find an overload of ' + str(op)
                         + ' with type ' + str(typ))
          return env.declare_assoc(loc, resolved_op, typarams, typ)
      else:
          user_error(loc, 'Could not find a proof of\n\t' + str(assoc_formula))
  
    case Trace(loc, function_name):
      return env.declare_tracing(function_name.get_name())

    case _:
      internal_error(stmt.location, "collect_env, unrecognized statement:\n" + str(stmt))


@dataclass
class RecCall:
  vars: List[Tuple[str,Type]]  # variables introduced by switch cases
  conditions: List[Term]
  args: List[Term]    

def add_condition(cond: Term, call: "RecCall") -> "RecCall":
    return RecCall(call.vars, [cond] + call.conditions, call.args)

def add_vars(vars: list[tuple[str, Type]], call: "RecCall") -> "RecCall":
    return RecCall(vars + call.vars, call.conditions, call.args)

def find_rec_calls(name: str, term: Term | RecFun | GenRecFun,
                   env: Env) -> list["RecCall"]:
  match term:
    case TermInst(loc2, _, subject, _, _):
      return find_rec_calls(name, subject, env)
    case Var() | OverloadedVar() | ResolvedVar():
      return []
    case Bool(loc2, _, _):
      return []
    case And(loc2, _, args):
      return sum([find_rec_calls(name, arg, env) for arg in args], [])
    case Or(loc2, _, args):
      return sum([find_rec_calls(name, arg, env) for arg in args], [])
    case IfThen(loc2, _, prem, conc):
      return find_rec_calls(name, prem, env) + find_rec_calls(name, conc, env)
    case All(loc2, _, _, _, frm2):
      return find_rec_calls(name, frm2, env)
    case Some(loc2, _, _, frm2):
      return find_rec_calls(name, frm2, env)
    case Call(loc2, _, rator, args):
      calls = find_rec_calls(name, rator, env) + \
          sum([find_rec_calls(name, arg, env) for arg in args], [])
      if callable_name(rator) == name:
          return [RecCall([], [], args)] + calls
      else:
          return calls
    case Switch(loc2, _, subject, cases):
      calls = []
      for c in cases:
        c_body_calls = find_rec_calls(name, c.body, env)
        match c.pattern:
          case PatternBool(loc3, value):
            cond = mkEqual(loc3, subject, value)
            new_c_body_calls = [add_condition(cond, call) for call in c_body_calls]
          case PatternCons(loc3, cons, params):
            cond = mkEqual(loc3, subject, pattern_to_term(c.pattern))
            new_c_body_calls = [add_condition(cond, call) for call in c_body_calls]
            cases_present: PatternCoverage = {}
            new_cons, params_types = check_constructor_pattern(
                loc3, cons, params, subject.typeof, env, cases_present)
            c.pattern.constructor = new_cons
            new_c_body_calls = [add_vars(params_types, call) for call in new_c_body_calls]
        calls += new_c_body_calls
      return calls
  
    case RecFun(_, name, _, params, _, cases):
      return []
    case GenRecFun(_, name, _, params, _, _, _,
                   body, _):
      return []
    case Conditional(loc2, _, cond, thn, els):
      thn_calls = find_rec_calls(name, thn, env)
      els_calls = find_rec_calls(name, els, env)
      new_thn_calls = [add_condition(cond, call) for call in thn_calls]
      not_cond = IfThen(loc2, None, cond, Bool(loc2, None, False))
      new_els_calls = [add_condition(not_cond, call) for call in els_calls]
      return find_rec_calls(name, cond, env) + new_thn_calls + new_els_calls
    case Lambda(loc2, _, _, body):
      return find_rec_calls(name, body, env)
    case Generic(loc2, _, _, body):
      return find_rec_calls(name, body, env)
    case TAnnote(loc2, _, subject, _):
      return find_rec_calls(name, subject, env)
    case ArrayGet(loc2, _, arr, ind):
      return find_rec_calls(name, arr, env) \
          + find_rec_calls(name, ind, env)
    case Array(loc2, _, elements):
      return sum([find_rec_calls(name, elt, env) for elt in elements], [])
    case MakeArray(loc2, _, subject):
      return find_rec_calls(name, subject, env)
    case TLet(loc2, _, _, rhs, body):
      return find_rec_calls(name, rhs, env) \
          + find_rec_calls(name, body, env)
    case Hole(loc2, _):
      return []
    case Omitted(loc2, _):
      return []
    case _:
      internal_error(cast(Meta, getattr(term, 'location', None)),
                     'in find_rec_calls, unhandled ' + str(term))
    

# Phase 1m transition guard (issue #1108): the experimental imperative
# layer (issue #854) parses `proc`, `observer`, and `resource`
# declarations and threads them through uniquify, module boundaries, and
# tooling. Observer and resource bodies/specs are still not verified, so this
# warning keeps a deliberately false one from being presented as fully valid.
#
# Phase 2 slices retire this per construct. Phase 2f (issue #1115) retired it
# for the *straight-line* procedures its verifier fully models: `verify_proc`
# in the `ProcDecl` case of `check_proofs` (below) verifies those and only
# falls back to this warning for a procedure whose body it does not model yet
# (branches, loops, calls, allocations, mutable arrays). The observer and
# resource cases warn until their own verifier arrives.
_IMPERATIVE_DECL_KIND = {ProcDecl: 'proc', ObserverDecl: 'observer',
                         ResourceDecl: 'resource'}

def warn_unverified_imperative(decl: Declaration) -> None:
  kind = _IMPERATIVE_DECL_KIND[type(decl)]
  warning(decl.location,
          f"warning: {kind} '{base_name(decl.name)}' is accepted but not "
          "verified -- parsing and declaration plumbing succeeded, but no "
          "verifier has run on its body or specs yet (experimental "
          "imperative layer, issue #854)")


def check_proofs(stmt: Statement, env: Env) -> None:
  if get_verbose():
    print('\n\ncheck_proofs(' + str(stmt) + ')')
  # Phase 5 / Step 21 hook: trap before evaluating each top-level
  # statement.  ``get_debugger()`` returns ``None`` in the common case
  # (no debug session attached), so non-debug runs pay one attribute
  # load and a None-check per statement -- well below the noise floor
  # of the surrounding match dispatch.  Step 22: ``env`` is passed in
  # so ``print <expr>`` and breakpoint conditions can be evaluated in
  # the current scope.
  _dbg = get_debugger()
  if _dbg is not None:
    _dbg.on_statement(stmt, env)
  match stmt:
    case Define(loc, name, _, body):
      pass
    case Theorem(loc, name, frm, pf, _):
      if get_verbose():
        print('checking proof of theorem ' + base_name(name))
      _try_check_proof_of(pf, frm, env)
      
    case Postulate(loc, name, frm):
      pass

    case Predicate():
      pass

    case RecFun(loc, name, typarams, params, _, _):
      pass

    case GenRecFun(loc, name, typarams, params, _, measure, _,
                   body, terminates):
      if stmt.trusted_terminates:
        return
      body_env = env.declare_type_vars(loc, typarams)
      
      # find recursive calls in the body
      calls = find_rec_calls(name, body, body_env)
      formulas: list[Formula] = []

      # create a formula Fi for each
      for call in calls:
        lhs = cast(Term, measure.substitute({x: arg for ((x,t),arg) in zip(params,call.args)}))
        rhs = measure.copy()
        #less = env.base_to_unique('<') # This doesn't work!
        less_ovlds = env.base_to_overloads('<')
        less = OverloadedVar(loc, None, less_ovlds)
        # `Call` is a Term in the class hierarchy but acts as a Formula
        # when its return type is Bool (here: `<` overloads).
        less_frm = cast(Formula, Call(loc, None, less, [lhs,rhs]))
        condition = And(loc, None, call.conditions) \
            if len(call.conditions) > 0 else None
        # `frm` is a name reused by the outer `match stmt:` Theorem
        # arm at line 5129 (also a Formula); the annotation lives there.
        frm = IfThen(loc, None, condition, less_frm) if condition is not None else less_frm
        i = 0
        for var in reversed(call.vars):
            frm = All(loc, None, var, (i,len(call.vars)),frm)
            i += 1
        formulas.append(frm)

      # combine into formula: all params. F1 and ... and Fn
      formula: Formula
      if len(formulas) > 1:
          formula = And(loc, None, formulas)
      elif len(formulas) == 1:
          formula = formulas[0]
      else:
          user_error(loc, 'There were no recursive calls in the body of this recfun')
      for (x,t) in reversed(params):
          formula = All(loc, None, (x,t), (0,1), formula)
      formula = check_formula(formula, body_env)

      # check that the terminates proof proves the above formula
      _try_check_proof_of(terminates, formula, body_env)
  
    case Union(loc, name, typarams, _):
      pass

    case TypeAlias():
      pass

    case ObjectDecl():
      # Object declarations are type-checked in earlier phases; nothing to
      # verify here and no unchecked-semantics warning (issue #1108).
      pass

    case ProcDecl():
      # Phase 2f (issue #1115): verify straight-line procedures; bodies this
      # slice does not model keep warning (issue #1108).
      verify_proc(stmt, env)

    case ObserverDecl() | ResourceDecl():
      warn_unverified_imperative(stmt)

    case ViewDecl():
      pass

    case Export(loc, name):
      pass
  
    case Import(loc, name, _):
      pass
  
    case Print(loc, trm):
      result = full_reduce(trm, env)
      print(str(result))
      
    case Assert(loc, frm):
      match frm:
        case Call(_, _, rator, [lhs, rhs]) if isinstance(rator, VarRef) and rator.get_name() == '=':
          L = full_reduce(lhs, env)
          R = full_reduce(rhs, env)
          if L == R:
            pass
          else:
              user_error(loc, 'assertion failed:\n' +
                    '\t' + str(L) + ' ≠ ' + str(R) + '\n')
        case IfThen(_, _,
                    Call(_, _, rator, [lhs, rhs]),
                    Bool(_, _, False)) if isinstance(rator, VarRef) and rator.get_name() == '=':
          L = full_reduce(lhs, env)
          R = full_reduce(rhs, env)
          if L != R:
            pass
          else:
              user_error(loc, 'assertion failed:\n' +
                    '\t' + str(L) + ' = ' + str(R) + '\n')
        case _:
          result = full_reduce(frm, env)
          match result:
            case Bool(_, _, True):
              pass
            case Bool(_, _, False):
              user_error(loc, 'assertion failed: ' + str(frm))
            case result:
              user_error(loc, 'assertion expected Boolean result, not ' \
                    + str(result))

    case Auto(loc, _):
      pass
  
    case Associative(loc, typarams, _, _):
      pass
  
    case Inductive():
      pass
  
    case Module(loc, name):
      pass

    case Trace(loc, _):
      pass

    case _:
      internal_error(stmt.location, "check_proofs: unrecognized statement:\n" + str(stmt))

  if _dbg is not None:
    _dbg.after_statement(stmt, env)

def _referenced_names(node: object) -> set[str]:
  # Collect every resolved name referenced anywhere inside `node` by walking
  # its dataclass fields (the same generic traversal as
  # checker_logic._ast_mentions_any, but gathering names instead of testing
  # membership). Used by the exported-contract visibility check.
  names: set[str] = set()
  seen: set[int] = set()
  stack: list[object] = [node]
  while stack:
    n = stack.pop()
    if isinstance(n, (list, tuple)):
      stack.extend(n)
      continue
    if isinstance(n, dict):
      stack.extend(n.values())
      continue
    nid = id(n)
    if nid in seen:
      continue
    seen.add(nid)
    if isinstance(n, OverloadedVar):
      names.update(n.resolved_names)
    elif isinstance(n, VarRef):
      names.add(n.get_name())
    if hasattr(n, '__dict__'):
      for v in vars(n).values():
        if v is not None and not isinstance(v, (str, int, float, bool)):
          stack.append(v)
  return names

def check_exported_contract_visibility(ast: List[Statement]) -> None:
  # Phase 1 module-boundary check (issue #854/#968). An exported imperative
  # contract may only mention names that are themselves visible to importing
  # modules. A `private` declaration in the same module resolves fine
  # internally but is dropped from the module's exports, so exposing it in a
  # public `proc`/`observer` contract would leave importers unable to state or
  # use that contract. We reject it here rather than letting importers hit a
  # confusing "undefined name" later. The declaration body stays hidden, so a
  # private name used only in a body (not the contract) is fine.
  private: dict[str, str] = {}
  for s in ast:
    if isinstance(s, Declaration) and s.visibility == 'private':
      private[s.name] = base_name(s.name)
  if not private:
    return
  for s in ast:
    match s:
      case ProcDecl() if s.visibility != 'private':
        contract: list[object] = [*s.params, *s.specs]
        if s.return_type is not None:
          contract.append(s.return_type)
        kind = 'proc'
      case ObserverDecl() if s.visibility != 'private':
        contract = [*s.params, s.return_type, *s.reads]
        kind = 'observer'
      case _:
        continue
    for ref in sorted(_referenced_names(contract) & private.keys()):
      user_error(s.location,
                 'exported ' + kind + " '" + base_name(s.name)
                 + "' mentions the private name '" + private[ref]
                 + "' in its contract; a public contract may only mention "
                 + 'names visible to importing modules.')

def check_deduce(ast: List[Statement], module_name: str, modified: bool,
                 tracing_functions: List[str],
                 error_sink: Optional[ErrorSink] = None) -> List[Statement]:
  """Run the four-phase pipeline (process_declarations, type_check_stmt,
  collect_env, check_proofs) over ``ast``.

  ``error_sink``: when ``None`` (default), exceptions raised by any
  phase propagate immediately — the historical CLI / goal_at / MCP
  behaviour. When given an :class:`ErrorSink`, each top-level
  statement runs inside a per-phase try/except: a raised exception is
  appended to the sink, the failing statement is dropped from the
  remaining phases, and processing continues to the next statement.
  ``lsp.query.check`` opts in to this so every user error and every ``?``
  hole in the file becomes a separate diagnostic instead of just the
  first one.

  The recovery boundary is the top-level statement; deep
  ``user_error()`` / ``incomplete_error()`` calls keep raising as before
  (refactoring 200+ raise sites to plumb a sink through every helper
  would require each site to invent a "what to return" continuation,
  with no benefit over a top-loop catch).
  """
  env = Env()
  env = env.declare_module(module_name)
  imported_modules.clear()
  needs_checking = [modified]

  prev_sink = get_active_sink()
  set_active_sink(error_sink)
  try:
    return _check_deduce_body(
      ast, module_name, modified, tracing_functions, error_sink, env, needs_checking
    )
  finally:
    set_active_sink(prev_sink)


def _check_deduce_body(ast: list[Statement], module_name: str, modified: bool,
                       tracing_functions: list[str],
                       error_sink: Optional[ErrorSink], env: Env,
                       needs_checking: list[bool]) -> list[Statement]:
  """Body of ``check_deduce``, split out so the ``_active_sink``
  push/pop in the caller stays a tidy try/finally."""

  def _collect_diagnostic(exc: Diagnostic) -> None:
    """Append ``exc`` to the sink, or re-raise when no sink is set."""
    if error_sink is None:
      raise exc
    error_sink.add(exc)

  if get_verbose():
      print('--------- Processing Declarations ------------------------')
  # Hash each statement structurally as we go.  Used by the
  # check_proofs cache below; computed here so we visit each AST
  # only once.  ``_hash_ast`` skips the ``location`` field, so two
  # parses of the same source produce matching hashes.
  # ``ast2_pairs`` collects (post-decl AST, hash) pairs only for
  # statements whose declaration phase succeeded; failed statements
  # are dropped here so they don't show up in later phases.
  try:
    check_exported_contract_visibility(ast)
  except Diagnostic as e:
    _collect_diagnostic(e)

  ast2_pairs = []
  for s in ast:
    sh = _hash_ast(s)
    try:
      new_s, env = process_declaration(s, env, [module_name], needs_checking)
    except Diagnostic as e:
      _collect_diagnostic(e)
      continue
    ast2_pairs.append((new_s, sh))
  if get_verbose():
    for s, _ in ast2_pairs:
      print(s)

  for func_name in tracing_functions:
    # TODO: base_to_unique is a hack so use another function instead
    new_name = env.base_to_unique(func_name)
    if new_name is None:
      print("Couldn't find function to trace:", func_name)
    else:
      env = env.declare_tracing(new_name)

  if get_verbose():
    print('--------- Type Checking ------------------------')
  ast3 = []
  ast3_hashes = []

  error_on_next_import : dict[str, bool] = {}
  for s, sh in ast2_pairs:
    try:
      new_s = type_check_stmt(s, env, error_on_next_import)
    except Diagnostic as e:
      _collect_diagnostic(e)
      continue
    # If None gets returned we want to remove the current statement
    # Which is represented by not appending it to the new ast
    if new_s != None:
      ast3.append(new_s)
      ast3_hashes.append(sh)
  if get_verbose():
    for s in ast3:
      print(s)

  if get_verbose():
    print('--------- Proof Checking ------------------------')
  if module_name not in checked_modules:
    if get_verbose() and needs_checking[0]:
        print('checking ' + module_name)
    # Per-statement cache for ``check_proofs`` (Steps 13 + 14).
    # Earlier loops (``process_declaration``, ``type_check_stmt``)
    # emit AST nodes whose ``Meta`` locations participate in
    # side-effecting behaviour (e.g. the ``target_hole_location``
    # flag used by ``goal_at`` to single out which `?` raises), so
    # caching their outputs across calls would let stale locations
    # leak into a new run.  ``check_proofs`` itself is the bulk of
    # the time and its only persistent effect is "verified" -- safe
    # to cache.
    #
    # Step 14: the cache key is ``(stmt_hash, deps_fingerprint,
    # target, module_name)`` where ``deps_fingerprint`` folds in
    # only the prior statements *this* statement actually references
    # (plus any global-barrier statements -- ``Import`` / ``Auto``
    # -- whose effects are observable everywhere downstream).
    # Editing an unrelated theorem leaves ``deps_fingerprint``
    # unchanged, so the entry hits.
    #
    # ``target`` is in the key so a different ``goal_at`` target
    # doesn't reuse a verdict made under the previous target (a `?`
    # that was previously treated as ``sorry`` should now raise, or
    # vice versa).
    target = get_target_hole_location()
    defined_to_idx: dict[str, int] = {}
    barrier_idxs: set[int] = set()
    auto_idxs: list[int] = []
    stmt_hashes_so_far: list[int] = []
    for i, (s, sh) in enumerate(zip(ast3, ast3_hashes)):
      try:
        env = collect_env(s, env)
      except Diagnostic as e:
        # collect_env failed -- skip check_proofs for this stmt and
        # the bookkeeping below. Append to ``stmt_hashes_so_far`` so
        # subsequent indices keep lining up with ``ast3`` for the
        # dependency lookup.
        _collect_diagnostic(e)
        stmt_hashes_so_far.append(sh)
        continue
      referenced = _collect_referenced_names(s)
      # ``auto`` declarations register theorems as implicit rewrite
      # rules consulted by every later proof.  A proof can rely on
      # an auto'd theorem without textually referencing it, so each
      # prior ``Auto``'s referenced names also contribute to this
      # statement's dependency set -- editing the auto'd theorem
      # then invalidates downstream proofs that relied on it
      # implicitly.
      for j in auto_idxs:
        referenced |= _collect_referenced_names(ast3[j])
      dep_idxs = set(barrier_idxs)
      for n in referenced:
        idx = defined_to_idx.get(n)
        if idx is not None:
          dep_idxs.add(idx)
      deps_fingerprint = hash(
        tuple(stmt_hashes_so_far[j] for j in sorted(dep_idxs))
      )
      key = ("check_proofs", sh, deps_fingerprint, target, module_name)
      if needs_checking[0]:
        # ``Print`` and ``Assert`` have observable side effects in
        # ``check_proofs`` (printing a value, raising on a failed
        # assertion).  Their cache key is fully determined by the
        # statement's text and its dependency set, so two identical
        # ``print zero`` lines hash to the same key -- caching the
        # verdict would skip the side effect on every duplicate.
        # ``ProcDecl``/``ObserverDecl``/``ResourceDecl`` are the same:
        # their only effect in ``check_proofs`` is the Phase 1m
        # "accepted but not verified" warning (issue #1108).  When no
        # warning sink is installed (``check_file(collect_errors=False)``,
        # e.g. the CLI) ``warnings_emitted`` below stays ``False``, so
        # the miss branch would cache them and a later re-check in a
        # long-lived process would silently drop the warning.  Bypass
        # the cache for all of these; ``check_proofs`` on them is cheap.
        try:
          _sink = get_active_sink()
          pre_n = len(_sink) if _sink is not None else 0
          # Warning sink is separate from the error sink; track its
          # size the same way so we can skip caching when a warning
          # fired (see below). Issue #991.
          _wsink = get_active_warning_sink()
          pre_wn = len(_wsink) if _wsink is not None else 0
          # Phase 5 / Step 21: when a debugger is attached, every
          # ``check_proofs`` call must run its hooks -- a cache hit
          # would silently skip the trap.  Re-check unconditionally;
          # this also avoids polluting the cache with cache-key
          # collisions caused by debugger-driven reduction order.
          if get_debugger() is not None:
            check_proofs(s, env)
            _record_miss("check_proofs")
          elif isinstance(s, (Print, Assert, ProcDecl, ObserverDecl,
                              ResourceDecl)):
            check_proofs(s, env)
            _record_miss("check_proofs")
          elif key in _stmt_cache:
            _record_hit("check_proofs")
          else:
            check_proofs(s, env)
            # Don't cache if check_proofs absorbed errors into the
            # sink -- next run must re-check so the diagnostic is
            # re-emitted. Same rule applies when a warning fired:
            # ``lsp.query.check`` surfaces warnings as diagnostics
            # (issue #991), so a cache hit that silently skipped the
            # warning-emitting statement would drop the diagnostic on
            # every subsequent run.
            _sink2 = get_active_sink()
            _wsink2 = get_active_warning_sink()
            errors_absorbed = _sink2 is not None and len(_sink2) != pre_n
            warnings_emitted = _wsink2 is not None and len(_wsink2) != pre_wn
            if not errors_absorbed and not warnings_emitted:
              _stmt_cache[key] = True
            _record_miss("check_proofs")
        except Diagnostic as e:
          # Don't update the cache on failure -- next run will
          # re-check this stmt, which is what we want once the user
          # fixes it.
          _collect_diagnostic(e)
      # Bookkeeping for the next iteration -- happens regardless of
      # ``needs_checking`` so the dependency map stays consistent.
      # ``defined_to_idx`` is updated *after* the dep lookup so a
      # statement's self-references (e.g. recursive functions) do
      # not get treated as a self-dependency.
      if _is_global_barrier(s):
        barrier_idxs.add(i)
      if isinstance(s, Auto):
        auto_idxs.append(i)
      for n in _collect_defined_names(s):
        defined_to_idx[n] = i
      stmt_hashes_so_far.append(sh)
    checked_modules.add(module_name)
  # Sanity-check the post-typecheck AST: every variable reference
  # should be ``ResolvedVar`` (or, if a real overload couldn't be
  # resolved, a multi-candidate ``OverloadedVar``). Any pre-uniquify
  # ``Var`` or single-candidate ``OverloadedVar`` is a refactor leak.
  check_post_typecheck_invariants(ast3)
  # Return the post-typecheck AST so callers (lsp.library.check_file,
  # the Deduce-to-C compiler) can read the overload-resolved form.
  # See issue #305.
  return ast3
