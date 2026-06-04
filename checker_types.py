"""Type checking for Deduce types, terms, calls, patterns, and unions.

File charter:
- Put code here when it checks or synthesizes term types, validates type
  expressions, resolves overloaded calls, checks patterns and constructors,
  enforces recursive-call escape/count rules, or validates union strict
  positivity and parameter polarity.
- Keep proof rules in ``checker_proofs.py`` and statement phase ordering in
  ``checker_pipeline.py``. This module should answer "what type does this
  expression have?" and "is this type-shaped thing valid?".
- Helpers for view-recursive declarations may live here only when they are
  needed by type checking itself; orchestration of view declarations belongs in
  ``checker_pipeline.py``.
"""

from pathlib import Path
from collections.abc import Sequence
from typing import TypeAlias as TypingTypeAlias, cast

from lark.tree import Meta

from abstract_syntax import (
    All,
    And,
    Array,
    ArrayGet,
    ArrayType,
    Bool,
    BoolType,
    Call,
    Conditional,
    Env,
    Formula,
    FunctionType,
    GenRecFun,
    Generic,
    GenericUnknownInst,
    Hole,
    IfThen,
    Int,
    IntType,
    Lambda,
    MakeArray,
    Mark,
    Omitted,
    Or,
    OverloadType,
    OverloadedVar,
    Pattern,
    PatternBool,
    PatternCons,
    RecFun,
    ResolvedVar,
    Some,
    Switch,
    SwitchCase,
    TAnnote,
    TLet,
    Term,
    TermInst,
    Type,
    TypeAlias,
    TypeInst,
    TypeType,
    Constructor,
    Union,
    Var,
    VarRef,
    ViewBinding,
    ViewDecl,
    base_name,
    callable_name,
    is_associative,
    type_match,
    type_names,
)
from checker_common import *
from error import MatchFailed, UserError, internal_error, user_error, wrap_user_error, error_header
from flags import get_verbose

TypeExpr: TypingTypeAlias = Type | VarRef
TypeMatching: TypingTypeAlias = dict[str, TypeExpr | None]
ViewInstantiation: TypingTypeAlias = tuple[object, TypeExpr, TypeExpr]
ViewMatch: TypingTypeAlias = tuple[ViewDecl, TypeExpr, TypeExpr]
PatternCoverage: TypingTypeAlias = dict[str, bool]
RecursiveName: TypingTypeAlias = str | None
SubtermNames: TypingTypeAlias = Sequence[str]
ParamBindings: TypingTypeAlias = list[tuple[str, Type]]
Substitution: TypingTypeAlias = dict[str, Term | Type | RecFun | GenRecFun]

# Lazy adapter for checker_pipeline._instantiate_view_type: a module-level
# import would close the cycle
# checker_types -> checker_pipeline -> checker_induction -> checker_proofs
# -> checker_types and crash at import time.
def _instantiate_view_type(
    loc: Meta, typ: TypeExpr, env: Env
) -> ViewInstantiation | None:
  import checker_pipeline
  return cast(ViewInstantiation | None,
              checker_pipeline._instantiate_view_type(loc, typ, env))

def _view_call(loc: Meta, fun_name: str, arg: Term) -> Call:
  return Call(loc, None, ResolvedVar(loc, None, fun_name), [arg])

def _term_bijective_view_for_source_type(
    loc: Meta, typ: TypeExpr, env: Env
) -> ViewMatch | None:
  for binding in env.dict.values():
    if not isinstance(binding, ViewBinding):
      continue
    view = binding.view
    if view.inverse is None:
      continue
    matching: TypeMatching = {}
    try:
      type_match(loc, type_names(loc, view.type_params),
                 view.source, typ, matching)
    except MatchFailed:
      continue
    sub = cast(Substitution, {
        name: value for name, value in matching.items()
        if value is not None
    })
    source_ty = cast(TypeExpr, view.source.substitute(sub))
    target_ty = cast(TypeExpr, view.target.substitute(sub))
    return view, source_ty, target_ty
  return None

def _switch_pattern_could_match_alts(
    pat: Pattern, alts: list[Constructor]
) -> bool:
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

def _switch_subject_via_bijective_view(
    loc: Meta,
    new_subject: Term,
    source_ty: TypeExpr,
    cases: list[SwitchCase],
    env: Env,
    recfun: RecursiveName,
    subterms: SubtermNames,
) -> tuple[Term, TypeExpr] | None:
  view_match = _term_bijective_view_for_source_type(loc, source_ty, env)
  if view_match is None:
    return None
  view, _, target_ty = view_match
  target_union = lookup_union(loc, target_ty, env)
  if not any(_switch_pattern_could_match_alts(c.pattern,
                                              target_union.alternatives)
             for c in cases):
    return None
  checked_view = type_check_term(
      _view_call(loc, view.into, new_subject), target_ty, env, recfun,
      subterms)
  return checked_view, target_ty

def _is_generic_unknown_argument(arg: Term, env: Env) -> bool:
  match arg:
    case Mark(_, _, subject):
      return _is_generic_unknown_argument(subject, env)
    case OverloadedVar(_, _, _) | ResolvedVar(_, _, _):
      return isinstance(env.get_type_of_term_var(arg), GenericUnknownInst)
    case _:
      return False

def type_check_call_funty(
    loc: Meta,
    new_rator: Term,
    args: list[Term],
    env: Env,
    recfun: RecursiveName,
    subterms: SubtermNames,
    ret_ty: TypeExpr | None,
    call: Call,
    typarams: list[str],
    param_types: list[Type],
    return_type: Type,
) -> Call:
  assoc_name = callable_name(new_rator)
  is_assoc = assoc_name is not None and is_associative(loc, assoc_name,
                                                       return_type, env)
  if get_verbose():
      print('is_assoc? ' + (assoc_name or '<anonymous>') + ' : '
            + str(return_type) + ' = ' + str(is_assoc))
  if (is_assoc and len(args) < len(param_types)) \
      or ((not is_assoc) and len(args) != len(param_types)):
    user_error(loc, 'incorrect number of arguments in call:\n\t' + str(call) \
          + '\n\texpected ' + str(len(param_types)) \
          + ' arguments, not ' + str(len(args)))
  # We force associative operators to have the same param type
  if is_assoc:
    param_types = [param_types[0]] * len(args)

  if len(typarams) == 0:
    if ret_ty != None and ret_ty != return_type:
      user_error(loc, 'expected ' + str(ret_ty) \
            + ' but the call returns ' + str(return_type))
    new_args: list[Term] = []
    for (param_type, arg) in zip(param_types, args):
      new_args.append(type_check_term(arg, param_type, env, recfun, subterms))
    return Call(loc, return_type, new_rator, new_args)
  else:
    #print('type check call to generic: ' + str(call))
    matching: TypeMatching = {}
    # If there is an expected return type, match that first.
    type_params = type_names(loc, typarams)
    if ret_ty:
      try:
          type_match(loc, type_params, return_type, ret_ty, matching)
      except MatchFailed:
        new_msg = 'expected type ' + str(ret_ty) + '\n' \
            + '\tbut the call ' + str(call) + '\n' \
            + '\thas return type ' + str(return_type) + '\n\n' \
            + '\tinferred type arguments: ' \
            + ', '.join([base_name(x) + ' := ' + str(ty) \
                         for (x,ty) in matching.items()])
        user_error(call.location, new_msg)
          
    # If we have already deduced the type parameters in the parameter type,
    # then we can check the term. Otherwise, we synthesize the term's type
    # and match it against the parameter type.
    try:
      checked_args: list[Term | None] = [None] * len(args)
      delayed_args: list[tuple[int, Term, Type]] = []
      for index, (arg, param_ty) in enumerate(zip(args, param_types)):
          param_type = param_ty.substitute(matching)
          fvs = param_type.free_vars()\
                          .intersection(set([ty.name for ty in type_params]))
          if get_verbose():
            print('arg = ' + str(arg))
            print('param_type = ' + str(param_type))
            print('fvs = ' + ', '.join([base_name(x) for x in fvs]) + '\n')
          if len(fvs) == 0:
            new_arg = type_check_term(arg, param_type, env, recfun, subterms)
          elif _is_generic_unknown_argument(arg, env):
            delayed_args.append((index, arg, param_ty))
            continue
          else:
            new_arg = type_synth_term(arg, env, recfun, subterms)
            type_match(loc, type_params, param_type, new_arg.typeof, matching)
          checked_args[index] = new_arg

      for (index, arg, param_ty) in delayed_args:
          param_type = param_ty.substitute(matching)
          fvs = param_type.free_vars()\
                          .intersection(set([ty.name for ty in type_params]))
          if len(fvs) == 0:
            new_arg = type_check_term(arg, param_type, env, recfun, subterms)
          else:
            new_arg = type_synth_term(arg, env, recfun, subterms)
            type_match(loc, type_params, param_type, new_arg.typeof, matching)
          checked_args[index] = new_arg
    except (UserError, MatchFailed) as e:
        context = '\n\n\t' + 'in context of call ' + str(call) + '\n' \
            + '\tfunction type: ' + str(FunctionType(loc, typarams, param_types,
                                                     return_type)) + '\n' \
            + '\tinferred type arguments: ' \
            + ', '.join([base_name(x) + ' := ' + str(ty) for (x,ty) in matching.items()])
        raise wrap_user_error(e, context) from e
    
    # Were all the type parameters deduced?
    for x in typarams:
        if x not in matching.keys():
            user_error(loc, 'in call ' + str(call) \
                  + '\n\tcould not deduce a type for ' \
                  + base_name(x) + ' to instantiate ' + str(call.rator) \
                  + '\n\twhose type is: ' + str(new_rator.typeof))

    missing_args = [
        str(index) for index, arg in enumerate(checked_args) if arg is None
    ]
    if missing_args:
      internal_error(loc, 'internal error in generic call: unchecked arguments for '
                     + ', '.join(missing_args))
    new_checked_args = [arg for arg in checked_args if arg is not None]
    type_args = [cast(Type, matching[x]) for x in typarams]
    inst_params = [p.substitute(matching) for p in param_types]
    inst_return_type = return_type.substitute(matching)
    inst_funty = FunctionType(loc, [], inst_params, inst_return_type)
    inst_rator = TermInst(loc, inst_funty, new_rator, type_args, True)
    ret = Call(loc, inst_return_type, inst_rator, new_checked_args)
    # print('{{{ type deduction for call: ' + str(ret))
    # print('arg_types: ' + ', '.join([str(arg.typeof) for arg in new_args]))
    # print(', '.join([x + ' = ' + str(t) for (x,t) in matching.items()]))
    # print('inst return type = ' + str(inst_return_type))
    # print('env:\n' + env.term_vars_str())
    # print('}}}')
    return ret

def overload_mismatch_annotation(
    loc: Meta,
    overload_funty: Type,
    arg_types: list[TypeExpr | None],
    ret_ty: TypeExpr | None,
) -> str | None:
  """Return a short annotation explaining why this overload doesn't fit, or
  ``None`` if neither side matches (in which case the bare overload type is
  already informative on its own). The annotation distinguishes the two
  common confusing cases: arguments line up but the return type is wrong,
  or vice versa."""
  match overload_funty:
    case FunctionType(_, typarams, param_types, return_type):
      type_params = type_names(loc, typarams)
      args_match = (len(param_types) == len(arg_types))
      if args_match:
        m: TypeMatching = {}
        try:
          for (pt, at) in zip(param_types, arg_types):
            type_match(loc, type_params, pt, at, m)
        except MatchFailed:
          args_match = False
      ret_matches = True
      if ret_ty is not None:
        m = {}
        try:
          type_match(loc, type_params, return_type, ret_ty, m)
        except MatchFailed:
          ret_matches = False
      if args_match and ret_ty is not None and not ret_matches:
        return 'argument types match, but result type ' + str(return_type) \
               + " doesn't match expected " + str(ret_ty)
      if ret_ty is not None and ret_matches and not args_match:
        return "result type matches, but argument types don't"
      return None
    case _:
      return None

def _function_type_covers(loc: Meta, general: Type, specific: Type) -> bool:
  """Return true when every call accepted by ``specific`` also fits
  ``general`` by instantiating ``general``'s type parameters."""
  match (general, specific):
    case (FunctionType(_, general_typarams, general_params, general_return),
          FunctionType(_, _, specific_params, specific_return)) \
        if len(general_params) == len(specific_params):
      type_params = type_names(loc, general_typarams)
      matching: TypeMatching = {}
      try:
        for (general_param, specific_param) in zip(general_params, specific_params):
          type_match(loc, type_params, general_param, specific_param, matching)
        type_match(loc, type_params, general_return, specific_return, matching)
        return True
      except MatchFailed:
        return False
    case _:
      return False

def _is_strictly_more_specific(loc: Meta, lhs: Type, rhs: Type) -> bool:
  return _function_type_covers(loc, rhs, lhs) \
      and not _function_type_covers(loc, lhs, rhs)

def type_check_call_helper(
    loc: Meta,
    new_rator: Term,
    args: list[Term],
    env: Env,
    recfun: RecursiveName,
    subterms: SubtermNames,
    ret_ty: TypeExpr | None,
    call: Call,
) -> Call:
  if get_verbose():
      print('tc_call_helper(' + str(call) + ') rator type: ' + str(new_rator.typeof))
  funty = new_rator.typeof
  match funty:
    case OverloadType(_, overloads):
      matches = []
      for (x, funty) in overloads:
          match funty:
            case FunctionType(_, typarams, param_types, return_type):
              # Preserve the rator's use-site location (e.g. the `+'
              # token in `x + y') on the resolved variable.  Using
              # `loc2' (the FunctionType's declaration site) here
              # would leak the operator's declaration location into
              # every Call.rator, breaking F12 / hover for overloaded
              # operators -- the location info is the only thing the
              # LSP can use to spot the use site.  Non-overloaded
              # names go through the `FunctionType' arm below where
              # ``new_rator'' is passed through unchanged.
              try:
                new_call = type_check_call_funty(loc, ResolvedVar(new_rator.location, funty, x), args, env, recfun,
                                                 subterms, ret_ty, call,
                                                 typarams, param_types, return_type)
                matches.append((x, funty, new_call))
              except (UserError, MatchFailed):
                pass
      if len(matches) > 1:
          matches = [
              candidate for candidate in matches
              if not any(
                  _is_strictly_more_specific(loc, other[1], candidate[1])
                  for other in matches
              )
          ]
      if len(matches) == 0:
          arg_types = [type_synth_term(arg, env, None, []).typeof for arg in args]
          msg = 'could not find a match for function call:\n\t' \
                + str(call) + '\n' \
                + 'argument types: ' + ', '.join([str(t) for t in arg_types]) + '\n'
          if ret_ty is not None:
              msg += 'expected return type: ' + str(ret_ty) + '\n'
          msg += 'overloads:'
          for (x, ty) in overloads:
              annotation = overload_mismatch_annotation(loc, ty, arg_types, ret_ty)
              msg += '\n\t' + str(ty)
              if annotation is not None:
                  msg += '   <-- ' + annotation
          user_error(loc, msg)
      elif len(matches) > 1:
          user_error(loc, 'in call to ' + str(new_rator) + '\n'\
                + 'ambiguous overloads:\n' \
                + '\n'.join([error_header(ty.location) + str(ty) for (x,ty,_) in matches]))
      else:
          return matches[0][2]
    case FunctionType(_, typarams, param_types, return_type):
      return type_check_call_funty(loc, new_rator, args, env, recfun, subterms, ret_ty, call,
                                   typarams, param_types, return_type)
    case _:
      user_error(loc, 'expected operator to have function type, not ' + str(funty))
      
def type_check_call(
    loc: Meta,
    rator: Term,
    args: list[Term],
    env: Env,
    recfun: RecursiveName,
    subterms: SubtermNames,
    ret_ty: TypeExpr | None,
    call: Call,
) -> Call:
  if get_verbose():
      print('tc_check_call(' + str(call) + ')')
      print('rator: ' + str(rator))
  new_rator = type_synth_term(rator, env, recfun, subterms)
  return type_check_call_helper(loc, new_rator, args, env, recfun, subterms, ret_ty, call)

recursive_call_count = 0

def get_recursive_call_count() -> int:
    global recursive_call_count
    return recursive_call_count

def increment_recursive_call_count() -> None:
    global recursive_call_count
    recursive_call_count += 1

def reset_recursive_call_count() -> None:
    global recursive_call_count
    recursive_call_count = 0

def check_recursive_call(
    call: Call, recfun: RecursiveName, subterms: SubtermNames
) -> None:
  # print('check_recursive_call(' + repr(call) + ') in ' + str(recfun))
  # print('callable_name = ' + str(callable_name(call.rator)))
  if recfun is None or callable_name(call.rator) != recfun:
      return
  increment_recursive_call_count()

  if isinstance(call.args[0], VarRef):
    if not (call.args[0].get_name() in subterms):
      user_error(call.location, "ill-formed recursive call\n" \
            + "expected first argument to be " \
            + " or ".join([base_name(x) for x in subterms]) \
            + ", not " + str(call.args[0]))
  else:
    user_error(call.location, "ill-formed recursive call\n" \
          + "expected first argument to be " \
          + " or ".join([base_name(x) for x in subterms]) \
          + ", not " + str(call.args[0]))

def _is_recfun_ref(node: Term, recfun: str) -> bool:
  if isinstance(node, ResolvedVar):
    return bool(node.name == recfun)
  if isinstance(node, OverloadedVar):
    return bool(recfun in node.resolved_names)
  if isinstance(node, Var):
    return bool(node.name == recfun)
  return False

def _escape_error(loc: Meta, recfun: str) -> None:
  user_error(loc,
        "the name '" + base_name(recfun) + "'"
        + " of a recursive function may only appear as the operator"
        + " of a function call within its own body")

def check_no_recfun_escape(term: Term | None, recfun: str) -> None:
  # Walk ``term`` and raise an error if ``recfun`` (the uniquified
  # name of the enclosing recursive function) appears anywhere other
  # than as the (optionally type-instantiated) operator of a Call.
  # This is the escape analysis from issue #215: it stops a body from
  # smuggling the recursive function out via a let-binding, an
  # argument position, or a return value, which would otherwise let
  # callers loop without the first-argument decreases check.
  if term is None:
    return
  if isinstance(term, VarRef):
    if _is_recfun_ref(term, recfun):
      _escape_error(term.location, recfun)
    return
  match term:
    case Call(_, _, rator, args):
      _check_rator_no_escape(rator, recfun)
      for a in args:
        check_no_recfun_escape(a, recfun)
    case TermInst(_, _, subject, _, _):
      check_no_recfun_escape(subject, recfun)
    case Generic(_, _, _, body):
      check_no_recfun_escape(body, recfun)
    case Conditional(_, _, cond, thn, els):
      check_no_recfun_escape(cond, recfun)
      check_no_recfun_escape(thn, recfun)
      check_no_recfun_escape(els, recfun)
    case TAnnote(_, _, subject, _):
      check_no_recfun_escape(subject, recfun)
    case Lambda(_, _, _, body):
      check_no_recfun_escape(body, recfun)
    case Switch(_, _, subject, cases):
      check_no_recfun_escape(subject, recfun)
      for c in cases:
        check_no_recfun_escape(c.body, recfun)
    case Array(_, _, elements):
      for e in elements:
        check_no_recfun_escape(e, recfun)
    case MakeArray(_, _, subject):
      check_no_recfun_escape(subject, recfun)
    case ArrayGet(_, _, subject, position):
      check_no_recfun_escape(subject, recfun)
      check_no_recfun_escape(position, recfun)
    case TLet(_, _, _, rhs, body):
      check_no_recfun_escape(rhs, recfun)
      check_no_recfun_escape(body, recfun)
    case Mark(_, _, subject):
      check_no_recfun_escape(subject, recfun)
    case And(_, _, args):
      for a in args:
        check_no_recfun_escape(a, recfun)
    case Or(_, _, args):
      for a in args:
        check_no_recfun_escape(a, recfun)
    case IfThen(_, _, premise, conclusion):
      check_no_recfun_escape(premise, recfun)
      check_no_recfun_escape(conclusion, recfun)
    case All(_, _, _, _, body):
      check_no_recfun_escape(body, recfun)
    case Some(_, _, _, body):
      check_no_recfun_escape(body, recfun)
    case Int() | Bool() | Hole() | Omitted():
      pass
    case _:
      # Other AST nodes (e.g. RecFun, GenRecFun appearing as values)
      # are conservatively rejected if they reference the recfun
      # name, allowed otherwise.
      if _is_recfun_ref(term, recfun):
        _escape_error(term.location, recfun)

def _check_rator_no_escape(rator: Term, recfun: str) -> None:
  # At a Call rator position, a direct VarRef to ``recfun`` is the
  # only place the name is legal; TermInst wrapping such a VarRef
  # (the ``@foo<T>(...)`` syntax) is the same shape. Anything else
  # is recursively walked as a non-rator subterm.
  if isinstance(rator, VarRef):
    return
  match rator:
    case TermInst(_, _, subject, _, _):
      _check_rator_no_escape(subject, recfun)
    case _:
      check_no_recfun_escape(rator, recfun)

# Helper for check_type: a bare reference to a generic union (one with N>0
# type parameters) is ill-formed. The arity check used to live in a separate
# `validate_union_type` pass that was only run on union-constructor parameters
# (issue #257); folding it into `check_type` makes every site that accepts a
# user-written type — postulate/define/recursive/theorem signatures, etc. —
# reject `Foo` when it should be `Foo<...>`.
def _check_union_arity(head: VarRef, given: int, env: Env) -> None:
  if not env.type_var_is_defined(head):
    return
  type_def = env.get_def_of_type_var(head)
  if isinstance(type_def, Union) and len(type_def.type_params) != given:
    user_error(head.location,
          f"Expected union type '{head}' to have "
          f"{len(type_def.type_params)} type arguments, not {given}")

def _lookup_type_alias(loc: Meta, typ: TypeExpr, env: Env) -> TypeAlias | None:
  match typ:
    case OverloadedVar(_, _, resolved_names):
      if not env.type_var_is_defined(typ):
        user_error(loc, 'undefined type variable ' + str(typ))
      if len(resolved_names) > 1:
        user_error(loc, 'type names may not be overloaded ' + str(typ))
      defn = env.get_def_of_type_var(typ)
    case ResolvedVar():
      if not env.type_var_is_defined(typ):
        user_error(loc, 'undefined type variable ' + str(typ))
      defn = env.get_def_of_type_var(typ)
    case _:
      return None
  return defn if isinstance(defn, TypeAlias) else None

def _type_alias_arity_error(loc: Meta, name: str, expected: int, got: int) -> None:
  user_error(loc,
        f"Expected type alias '{base_name(name)}' to have "
        f"{expected} type arguments, not {got}")

# Validate that ``typ`` is well-formed in ``env`` and return the type
# with every single-candidate ``OverloadedVar`` narrowed to
# ``ResolvedVar``. The returned type may share structure with ``typ``
# when nothing changed; otherwise it's a freshly constructed copy.
# Callers MUST use the returned value, not the original ``typ`` —
# the strict post-typecheck invariant rejects single-candidate
# OverloadedVars, so dropping the return on the floor leaks them.
#
# ``arity_required`` is internal: callers that wrap a bare generic union
# head (TypeInst, GenericUnknownInst) and certain declaration sites (e.g.
# ``inductive Foo by ...``, which legitimately names a union by its bare
# name) pass False to suppress the zero-arity error.
def check_type(typ: TypeExpr, env: Env, arity_required: bool = True) -> TypeExpr:
  match typ:
    case OverloadedVar(loc, tyof, rs):
      if not env.type_var_is_defined(typ):
        user_error(loc, 'undefined type variable ' + str(typ))
      if len(rs) > 1:
        user_error(loc, 'type names may not be overloaded ' + str(typ))
      view_info = _instantiate_view_type(loc, typ, env)
      if view_info is not None:
        _, source_ty, _ = view_info
        return source_ty
      alias = _lookup_type_alias(loc, typ, env)
      if alias is not None:
        if len(alias.type_params) != 0:
          if arity_required:
            _type_alias_arity_error(loc, alias.name, len(alias.type_params), 0)
          return ResolvedVar(loc, tyof, rs[0])
        return alias.body
      if arity_required:
        _check_union_arity(typ, 0, env)
      # len(rs) == 1: this is a non-overloaded type reference. Promote.
      return ResolvedVar(loc, tyof, rs[0])
    case ResolvedVar(loc, tyof, _):
      if not env.type_var_is_defined(typ):
        user_error(loc, 'undefined type variable ' + str(typ))
      view_info = _instantiate_view_type(loc, typ, env)
      if view_info is not None:
        _, source_ty, _ = view_info
        return source_ty
      alias = _lookup_type_alias(loc, typ, env)
      if alias is not None:
        if len(alias.type_params) != 0:
          if arity_required:
            _type_alias_arity_error(loc, alias.name, len(alias.type_params), 0)
          return typ
        return alias.body
      if arity_required:
        _check_union_arity(typ, 0, env)
      return typ
    case IntType(loc) | BoolType(loc) | TypeType(loc):
      return typ
    case FunctionType(loc, typarams, param_types, return_type):
      body_env = env.declare_type_vars(loc, typarams)
      new_param_types = [check_type(ty, body_env) for ty in param_types]
      new_return_type = check_type(return_type, body_env)
      return FunctionType(loc, typarams, new_param_types, new_return_type)
    case TypeInst(loc, inner_typ, arg_types):
      view_info = _instantiate_view_type(loc, typ, env)
      if view_info is not None:
        _, source_ty, _ = view_info
        return source_ty
      alias = _lookup_type_alias(loc, inner_typ, env)
      if alias is not None:
        new_args = [check_type(ty, env) for ty in arg_types]
        if len(alias.type_params) != len(new_args):
          _type_alias_arity_error(loc, alias.name,
                                  len(alias.type_params), len(new_args))
        subst = dict(zip(alias.type_params, new_args))
        expanded = alias.body.substitute(subst)
        return check_type(expanded, env)
      # The head is a generic-union reference applied to ``arg_types``;
      # suppress the bare-head arity check and validate against the
      # actual arg count instead.
      new_inner = check_type(inner_typ, env, arity_required=False)
      if isinstance(new_inner, VarRef):
        _check_union_arity(new_inner, len(arg_types), env)
      new_args = [check_type(ty, env) for ty in arg_types]
      return TypeInst(loc, new_inner, new_args)
    case GenericUnknownInst(loc, inner_typ):
      # Internal node deliberately wrapping an unapplied generic union.
      return GenericUnknownInst(loc, check_type(inner_typ, env, arity_required=False))
    case ArrayType(loc, elt_type):
      return ArrayType(loc, check_type(elt_type, env))
    case _:
      internal_error(typ.location, 'error in check_type: unhandled type ' + repr(typ) + ' ' + str(type(typ)))

def type_first_letter(typ: TypeExpr) -> str:
  if isinstance(typ, VarRef):
    return str(typ.get_name()[0])
  match typ:
    case IntType(_):
      return 'i'
    case BoolType(_):
      return 'b'
    case TypeType(_):
      return 't'
    case FunctionType(_, _, _, _):
      return 'f'
    case TypeInst(_, typ, _):
      return type_first_letter(typ)
    case GenericUnknownInst(_, typ):
      return type_first_letter(typ)
    case _:
      print('error in type_first_letter: unhandled type ' + repr(typ))
      exit(-1)

def type_check_term_inst(
    loc: Meta,
    subject: Term,
    tyargs: list[Type],
    inferred: bool,
    recfun: RecursiveName,
    subterms: SubtermNames,
    env: Env,
) -> TermInst:
  tyargs = [check_type(ty, env) for ty in tyargs]
  new_subject = type_synth_term(subject, env, recfun, subterms)
  ty = new_subject.typeof
  if isinstance(ty, VarRef):
    retty = TypeInst(loc, ty, tyargs)
  else:
    match ty:
      case FunctionType(loc2, typarams, param_types, return_type):
        sub = {x: t for (x,t) in zip(typarams, tyargs)}
        inst_param_types = [t.substitute(sub) for t in param_types]
        inst_return_type = return_type.substitute(sub)
        retty = FunctionType(loc2, [], inst_param_types, inst_return_type)
      case GenericUnknownInst(loc2, union_type):
        retty = TypeInst(loc2, union_type, tyargs)
      case _:
        user_error(loc, 'expected a type name, not ' + str(ty))
  return TermInst(loc, retty, new_subject, tyargs, inferred)

def type_check_term_inst_var(
    loc: Meta, subject_var: VarRef, tyargs: list[Type], inferred: bool, env: Env
) -> TermInst:
  if isinstance(subject_var, VarRef):
      tyargs = [check_type(ty, env) for ty in tyargs]
      ty = env.get_type_of_term_var(subject_var)
      if isinstance(ty, VarRef):
        retty = TypeInst(loc, ty, tyargs)
      else:
        match ty:
          case FunctionType(loc3, typarams, param_types, return_type):
            sub = {x: t for (x,t) in zip(typarams, tyargs)}
            inst_param_types = [t.substitute(sub) for t in param_types]
            inst_return_type = return_type.substitute(sub)
            retty = FunctionType(loc3, [], inst_param_types, inst_return_type)
          case GenericUnknownInst(loc3, union_type):
            retty = TypeInst(loc3, union_type, tyargs)
          case _:
            user_error(loc, 'cannot instantiate a term of type ' + str(ty))
      # Subject is now resolved (we've narrowed to its single typed name).
      return TermInst(loc, retty,
                      ResolvedVar(subject_var.location, subject_var.typeof,
                                  subject_var.get_name()),
                      tyargs, inferred)
  internal_error(loc, 'internal error, expected variable, not ' + str(subject_var))

def type_synth_term(
    term: Term, env: Env, recfun: RecursiveName, subterms: SubtermNames
) -> Term:
  if get_verbose():
    print('type_synth_term: ' + str(term) + '\n' \
          + '\tin ' + str(recfun))
  match term:
    case Mark(loc, _, subject):
      new_subject = type_synth_term(subject, env, recfun, subterms)
      ret = Mark(loc, new_subject.typeof, new_subject)
  
    case OverloadedVar(loc, _, rs):
      try:
        ty = env.get_type_of_term_var(term)
        if ty == None:
          raise Exception('while type checking, undefined variable ' + str(term) \
                + '\nin scope:\n' + 'str(env)')
      except Exception as e:
        user_error(loc, str(e))
      match ty:
        case GenericUnknownInst(loc2, _):
          user_error(loc, 'Cannot infer type arguments for\n' \
                + '\t' + base_name(rs[0]) + '\nPlease make them explicit.')

      if len(rs) == 1:
          # No real overload — promote to ResolvedVar so downstream
          # code can rely on the type-system narrowing.
          ret = ResolvedVar(loc, ty, rs[0])
      else:
          if get_verbose():
              print('type_synth_term(' + str(term) + ') waiting to resolve name')
          ret = OverloadedVar(loc, ty, rs)

    case ResolvedVar(loc, _, name):
      ty = env.get_type_of_term_var(term)
      if ty is None:
        user_error(loc, 'while type checking, undefined variable ' + str(term))
      match ty:
        case GenericUnknownInst(loc2, _):
          user_error(loc, 'Cannot infer type arguments for\n' \
                + '\t' + base_name(name) + '\nPlease make them explicit.')
      ret = ResolvedVar(loc, ty, name)
      
    case Generic(loc, _, type_params, body):
      body_env = env.declare_type_vars(loc, type_params)
      new_body = type_synth_term(body, body_env, recfun, subterms)
      match new_body.typeof:
        case FunctionType(loc2, [], param_types, return_type):
          ty = FunctionType(loc, type_params, param_types, return_type)
          ret = Generic(loc, ty, type_params, new_body)
        case _:
          user_error(loc, 'body of generic must be a function, not ' \
                + str(new_body.typeof))

    case Lambda(loc, _, params, body):
      checked_params = [(p, check_type(t, env) if t else None)
                        for (p, t) in params]
      vars = [p for (p,t) in params]
      param_types = [t for (p,t) in checked_params]
      if any([t == None for t in param_types]):
          user_error(loc, 'Cannot synthesize a type for ' + str(term) + '.\n'\
                + 'Add type annotations to the parameters.')
      body_env = env.declare_term_vars(loc, checked_params)
      new_body = type_synth_term(body, body_env, recfun, subterms)
      typ = FunctionType(loc, [], param_types, new_body.typeof)
      return Lambda(loc, typ, checked_params, new_body)
      
    case TLet(loc, _, var, rhs, body):
      new_rhs = type_synth_term(rhs, env, recfun, subterms)
      body_env = env.declare_term_var(loc, var, new_rhs.typeof)
      new_body = type_synth_term(body, body_env, recfun, subterms)
      ret = TLet(loc, new_body.typeof, var, new_rhs, new_body)
  
    case Conditional(loc, _, cond, thn, els):
      new_cond = type_check_term(cond, BoolType(loc), env, recfun, subterms)
      new_thn = type_synth_term(thn, env, recfun, subterms)
      new_els = type_synth_term(els, env, recfun, subterms)
      if isinstance(new_thn.typeof, OverloadType) \
          and not isinstance(new_els.typeof, OverloadType):
        new_thn = type_check_term(thn, new_els.typeof, env, recfun, subterms)
      elif isinstance(new_els.typeof, OverloadType) \
          and not isinstance(new_thn.typeof, OverloadType):
        new_els = type_check_term(els, new_thn.typeof, env, recfun, subterms)
      if new_thn.typeof != new_els.typeof:
        user_error(loc, 'conditional expects same type for the two branches'\
              + ' but ' + str(new_thn.typeof) + ' ≠ ' + str(new_els.typeof))
      ret = Conditional(loc, new_thn.typeof, new_cond, new_thn, new_els)
      
    case Int(loc, _, value):
      ty = IntType(loc)
      ret = Int(loc, ty, value)
      
    case Bool(loc, _, value):
      ty = BoolType(loc)
      ret = Bool(loc, ty, value)
      
    case And(loc, _, args):
      new_args = [check_formula(arg, env, recfun, subterms) for arg in args]
      ty = BoolType(loc)
      ret = And(loc, ty, new_args)
      
    case Or(loc, _, args):
      new_args = [check_formula(arg, env, recfun, subterms) for arg in args]
      ty = BoolType(loc)
      ret = Or(loc, ty, new_args)
      
    case IfThen(loc, _, prem, conc):
      new_prem = check_formula(prem, env, recfun, subterms)
      new_conc = check_formula(conc, env, recfun, subterms)
      ty = BoolType(loc)
      ret = IfThen(loc, ty, new_prem, new_conc)
      
    case All(loc, _, var, pos, body):
      x, ty = var
      new_ty = check_type(ty, env)
      new_var = (x, new_ty)
      body_env = env.declare_term_vars(loc, [new_var])
      new_body = check_formula(body, body_env, recfun, subterms)
      ret = All(loc, BoolType(loc), new_var, pos, new_body)

    case Some(loc, _, vars, body):
      new_vars = [(x, check_type(ty, env)) for (x, ty) in vars]
      body_env = env.declare_term_vars(loc, new_vars)
      new_body = check_formula(body, body_env, recfun, subterms)
      ret = Some(loc, BoolType(loc), new_vars, new_body)
      
    case MakeArray(loc, _, arg):
      lst = type_synth_term(arg, env, recfun, subterms)
      match lst.typeof:
        case TypeInst(loc2, lst_ty, [elt_type]):
          union_def = lookup_union(loc, lst_ty, env)
          if base_name(union_def.name) == 'List':
            ret = MakeArray(loc, ArrayType(loc, elt_type), lst)
          else:
            user_error(loc, 'expected List, not union ' + union_def.name)
        case _:
          user_error(loc, 'expected List, not ' + str(lst.typeof))

    case ArrayGet(loc, _, array, index):
      new_array = type_synth_term(array, env, recfun, subterms)
      new_index = type_synth_term(index, env, recfun, subterms)
      match new_array.typeof:
        case ArrayType(loc2, elt_type):
          ret = ArrayGet(loc, elt_type, new_array, new_index)
        case _:
          user_error(loc, 'expected an array, not ' + str(new_array.typeof))
          
    case Call(loc, _, (OverloadedVar(loc2, ty2, [op_name, *_])
                       | ResolvedVar(loc2, ty2, op_name)), args) \
        if op_name == '=' or op_name == '≠':
      assert len(args) == 2
      lhs = type_synth_term(args[0], env, recfun, subterms)
      rhs = type_check_term(args[1], lhs.typeof, env, recfun, subterms)
      ty = BoolType(loc)
      if lhs.typeof != rhs.typeof:
          user_error(loc, 'expected arguments of equality to have the same type, but\n' \
                + '\t' + str(lhs.typeof) + ' ≠ ' + str(rhs.typeof))
      ret = Call(loc, ty, ResolvedVar(loc2, ty2, op_name), [lhs, rhs])
        
    case Call(loc, _, rator, args):
      ret = type_check_call(loc, rator, args, env, recfun, subterms, None, term)
      check_recursive_call(ret, recfun, subterms)
      
    case Switch(loc, _, subject, cases):
      new_subject = type_synth_term(subject, env, recfun, subterms)
      ty = new_subject.typeof
      view_subject = _switch_subject_via_bijective_view(
          loc, new_subject, ty, cases, env, recfun, subterms)
      if view_subject is not None:
        new_subject, ty = view_subject

      cases_present: PatternCoverage = {}
      result_type: list[TypeExpr | None] = [None] # boxed to allow mutable update in process_case

      def process_case(
          c: SwitchCase,
          result_type: list[TypeExpr | None],
          cases_present: PatternCoverage,
      ) -> SwitchCase:
        new_env = check_pattern(c.pattern, ty, env, cases_present)
        new_body = type_synth_term(c.body, new_env, recfun, subterms)
        case_type = new_body.typeof
        if result_type[0] == None:
          result_type[0] = case_type
        elif case_type != result_type[0]:
          user_error(c.location, 'bodies of cases must have same type, but ' \
                + str(case_type) + ' ≠ ' + str(result_type[0]))
        return SwitchCase(c.location, c.pattern, new_body)

      new_cases = [process_case(c, result_type, cases_present) \
                   for c in cases]
      ret = Switch(loc, result_type[0], new_subject, new_cases)
      
      # check exhaustiveness
      match ty:
        case BoolType(loc2):
          has_true_case = False
          has_false_case = False
          for scase in cases:
            match scase.pattern:
              case PatternBool(_, True):
                has_true_case = True
              case PatternBool(_, False):
                has_false_case = True
              case _:
                user_error(scase.location, 'not an appropriate case for bool\n\t' \
                           + str(scase))
          if not has_true_case:
            user_error(loc, 'missing case for true')
          if not has_false_case:
            user_error(loc, 'missing case for false')
        case _:
          dfn = lookup_union(loc, ty, env)
          match dfn:
            case Union(loc2, name, typarams, alts):
              for alt in alts:
                  if alt.name not in cases_present.keys():
                      user_error(loc, 'this switch is missing a case for: ' \
                            + str(alt))
            case _:
              user_error(loc, 'expected a union type, not ' + str(ty))

    case TermInst(loc, _, subject, tyargs, inferred) if isinstance(subject, VarRef):
      ret = type_check_term_inst_var(loc, subject, tyargs, inferred, env)

    case TermInst(loc, _, subject, tyargs, inferred):
      ret = type_check_term_inst(loc, subject, tyargs, inferred, recfun, subterms, env)

    case TAnnote(loc, _, subject, typ):
      checked_typ = check_type(typ, env)
      ret = type_check_term(subject, checked_typ, env, recfun, subterms)

    case RecFun(loc, name, typarams, params, returns, cases):
      fun_type = FunctionType(loc, typarams, params, returns)
      ret = term
      term.typeof = fun_type
      
    case GenRecFun(loc, name, typarams, params, returns, _, _,
                   body, _):
      param_types = [t for (p,t) in params]
      fun_type = FunctionType(loc, typarams, param_types, returns)
      ret = term
      term.typeof = fun_type
      
    case _:
      if isinstance(term, Type):
        internal_error(term.location, 'type_synth_term called on type ' + str(term))
      else:
        user_error(term.location, 'cannot synthesize a type for ' + str(term))
  if get_verbose():
    print('\ttype synth: ' + str(term) + '\n\t=> ' + str(ret) + ' : ' + str(ret.typeof))
  return ret

def type_check_formula(term: Term, env: Env) -> Term:
  return type_check_term(term, BoolType(term.location), env, None, [])

def type_check_term(
    term: Term, typ: TypeExpr, env: Env, recfun: RecursiveName, subterms: SubtermNames
) -> Term:
  if get_verbose():
    print('\ntype_check_term: ' + str(term) + ' : ' + str(typ) + '?\n')
  match term:
    case Mark(loc, _, subject):
      new_subject = type_check_term(subject, typ, env, recfun, subterms)
      return Mark(loc, new_subject.typeof, new_subject)
    case Hole(loc, _):
      return Hole(loc, typ)
    case Omitted(loc, _):
      return Omitted(loc, typ)
    case Generic(loc, _, type_params, body):
      match typ:
        case FunctionType(loc2, type_params2, param_types2, return_type2):
          sub = {U: ResolvedVar(loc, None, T) \
                 for (T,U) in zip(type_params, type_params2) }
          new_param_types = [ty.substitute(sub) for ty in param_types2]
          new_return_type = return_type2.substitute(sub)
          body_env = env.declare_type_vars(loc, type_params)
          funty = FunctionType(loc2, [], new_param_types, new_return_type)
          new_body = type_check_term(body, funty, body_env, recfun, subterms)
          return Generic(loc, typ, type_params, new_body)
        case _:
          user_error(loc, 'unexpected generic term, expected ' + str(typ))
        
    case ResolvedVar(loc, _, name):
      var_typ = env.get_type_of_term_var(term)
      if var_typ is None:
        user_error(loc, 'variable ' + str(term) + ' is not defined')
      match (var_typ, typ):
        case (GenericUnknownInst(loc2, union1), TypeInst(_, union2, tyargs)):
          if union1 == union2:
            return TermInst(loc, typ, ResolvedVar(loc, typ, name),
                            tyargs, True)
        case (FunctionType(_, typarams, param_types1, ret_type1),
              FunctionType(loc2, [], param_types2, ret_type2)):
          if len(typarams) > 0:
            resolved_matching: TypeMatching = {}
            type_params = type_names(loc, typarams)
            try:
              type_match(loc, type_params, ret_type1, ret_type2, resolved_matching)
              for (p1, p2) in zip(param_types1, param_types2):
                  type_match(loc, type_params, p1, p2, resolved_matching)
              type_args = [cast(Type, resolved_matching[x]) for x in typarams]
              return TermInst(loc, typ, ResolvedVar(loc, var_typ, name),
                              type_args, True)
            except UserError:
              pass
      if var_typ != typ:
        user_error(loc, 'expected a term of type ' + str(typ) \
                   + '\nbut got term ' + str(term) \
                   + ' of type ' + str(var_typ))
      return ResolvedVar(loc, typ, name)

    case OverloadedVar(loc, _, rs):
      var_typ = env.get_type_of_term_var(term)
      if get_verbose():
          print('var_typ = ' + str(var_typ))
      if var_typ == None:
        user_error(loc, 'variable ' + str(term) + ' is not defined' \
              + '\nin scope:\n' + 'str(env)')
      match (var_typ, typ):
        case (OverloadType(loc2, overloads), _):
          for (x, ty) in overloads:
              if ty == typ:
                  if get_verbose():
                      print('found overload ' + x + ' of type ' + str(typ))
                  return ResolvedVar(loc, typ, x)
          user_error(loc, 'could not find an overload of ' + base_name(rs[0]) \
                + ' of type ' + str(typ) + '\nin: ' + str(var_typ))
        case (GenericUnknownInst(loc2, union1), TypeInst(_, union2, tyargs)):
          if union1 == union2:
              return TermInst(loc, typ, ResolvedVar(loc, typ, rs[0]),
                              tyargs, True)
        case (FunctionType(_, typarams, param_types1, ret_type1),
              FunctionType(loc2, [], param_types2, ret_type2)):
          if len(typarams) > 0:
            overloaded_matching: TypeMatching = {}
            type_params = type_names(loc, typarams)
            try:
              type_match(loc, type_params, ret_type1, ret_type2, overloaded_matching)
              for (p1, p2) in zip(param_types1, param_types2):
                  type_match(loc, type_params, p1, p2, overloaded_matching)
              type_args = [cast(Type, overloaded_matching[x]) for x in typarams]
              return TermInst(loc, typ, ResolvedVar(loc, var_typ, rs[0]),
                              type_args, True)
            except UserError:
              pass
      if var_typ != typ:
        user_error(loc, 'expected a term of type ' + str(typ) \
                   + '\nbut got term ' + str(term) \
                   + ' of type ' + str(var_typ))
      return ResolvedVar(loc, typ, rs[0])
  
    case Lambda(loc, _, params, body):
      match typ:
        case FunctionType(loc2, [], param_types, return_type):
          vars = [n for (n,t) in params]
          body_env = env.declare_term_vars(loc, zip(vars, param_types))
          new_body = type_check_term(body, return_type, body_env,
                                     recfun, subterms)
          return Lambda(loc, typ, params, new_body)
        case FunctionType(loc2, ty_params, _, _):
          pretty_params = ", ".join([base_name(x) for x in ty_params])
          plural = 's' if len(ty_params) > 1 else ''
          user_error(loc, f'Expected type parameter{plural} {pretty_params}, ' \
                     + 'but got a lambda.\n\t' + \
                     f'Add generic {pretty_params} {"{ ... }"} around ' + \
                     'the function body.')
        case _:
          user_error(loc, 'expected a term of type ' + str(typ) + '\n'\
                + 'but instead got a lambda')
          
    case TLet(loc, _, var, rhs, body):
      new_rhs = type_synth_term(rhs, env, recfun, subterms)
      body_env = env.declare_term_var(loc, var, new_rhs.typeof)
      new_body = type_check_term(body, typ, body_env, recfun, subterms)
      return TLet(loc, typ, var, new_rhs, new_body)
      
    case Call(loc, _, (OverloadedVar(loc2, _, [op_name, *_])
                       | ResolvedVar(loc2, _, op_name)), args) \
        if op_name == '=' or op_name == '≠':
      new_term = type_synth_term(term, env, recfun, subterms)
      ty = new_term.typeof
      if ty != typ:
        user_error(term.location, 'expected term of type ' + str(typ) \
              + ' but got ' + str(ty))
      return new_term
      
    case Call(loc, _, rator, args):
      ret = type_check_call(loc, rator, args, env, recfun, subterms, typ, term)
      check_recursive_call(ret, recfun, subterms)
      return ret

    case Switch(loc, _, subject, cases):
      new_subject = type_synth_term(subject, env, recfun, subterms)
      ty = new_subject.typeof
      view_subject = _switch_subject_via_bijective_view(
          loc, new_subject, ty, cases, env, recfun, subterms)
      if view_subject is not None:
        new_subject, ty = view_subject

      cases_present: PatternCoverage = {}
      result_type: list[TypeExpr | None] = [None] # boxed to allow mutable update in process_case

      def process_case(
          c: SwitchCase,
          result_type: list[TypeExpr | None],
          cases_present: PatternCoverage,
      ) -> SwitchCase:
        new_env = check_pattern(c.pattern, ty, env, cases_present)
        #print('\n$\n' + str(c) + '\nnew env:\n' + str(new_env))
        new_body = type_check_term(c.body, typ, new_env, recfun, subterms)
        case_type = new_body.typeof
        if result_type[0] == None:
          result_type[0] = case_type
        elif case_type != result_type[0]:
          user_error(c.location, 'bodies of cases must have same type, but ' \
                + str(case_type) + ' ≠ ' + str(result_type[0]))
        return SwitchCase(c.location, c.pattern, new_body)

      new_cases = [process_case(c, result_type, cases_present) for c in cases]

      # Check case coverage
      match ty:
        case BoolType(loc2):
          if 'True' not in cases_present.keys():
            user_error(loc, 'missing case for true')
          if 'False' not in cases_present.keys():
            user_error(loc, 'missing case for false')
        case _:
          dfn = lookup_union(loc, ty, env)
          match dfn:
            case Union(loc2, name, typarams, alts):
              for alt in alts:
                  if alt.name not in cases_present.keys():
                      user_error(loc, 'missing a case for:\n\t' \
                            + str(alt))
            case _:
              user_error(loc, 'expected a union type, not ' + str(ty))
      
      return Switch(loc, result_type[0], new_subject, new_cases)
      
    case Conditional(loc, _, cond, thn, els):
      new_cond = type_check_term(cond, BoolType(loc), env, recfun, subterms)
      new_thn = type_check_term(thn, typ, env, recfun, subterms)
      new_els = type_check_term(els, typ, env, recfun, subterms)
      return Conditional(loc, typ, new_cond, new_thn, new_els)
  
    case TermInst(loc, _, subject, tyargs, inferred) if isinstance(subject, VarRef):
      return type_check_term_inst_var(loc, subject, tyargs, inferred, env)

    case TermInst(loc, _, subject, tyargs, inferred):
      return type_check_term_inst(loc, subject, tyargs, inferred, recfun, subterms, env)

    case _:
      if get_verbose():
          print('type_check_term delegating to type_synth_term')
      new_term = type_synth_term(term, env, recfun, subterms)
      ty = new_term.typeof
      if ty != typ:
        user_error(term.location, 'expected term of type ' + str(typ) \
              + ' but got ' + str(ty))
      return new_term
  
def lookup_union(loc: Meta, typ: TypeExpr, env: Env) -> Union:
  if isinstance(typ, VarRef):
    defn = env.get_def_of_type_var(typ)
  else:
    match typ:
      case TypeInst(_, inst_typ, _) if isinstance(inst_typ, VarRef):
        defn = env.get_def_of_type_var(inst_typ)
      case _:
        user_error(loc, 'expected a union type but instead got ' + str(typ))
  if isinstance(defn, Union):
    return defn
  user_error(loc, 'expected a union type but instead got ' + str(typ))

def check_constructor_pattern(
    loc: Meta,
    pat_constr: VarRef,
    params: list[str],
    typ: TypeExpr,
    env: Env,
    cases_present: PatternCoverage,
) -> tuple[ResolvedVar, ParamBindings]:
  if get_verbose():
    print('check_constructor_pattern: ' + str(pat_constr))
  defn = lookup_union(loc, typ, env)
  if get_verbose():
    print('for union: ' + str(defn))
  match defn:
    case Union(_, _, typarams, alts):
      # example:
      # typ is List<E>
      # union List<T> { empty; node(T, List<T>); }
      # pat_constr == node
      #found_pat_constr = False
      # Candidates the parser/uniquify pass observed for this pattern's
      # constructor. For an OverloadedVar this is the full list; for an
      # already-narrowed ResolvedVar we just have the chosen name.
      if isinstance(pat_constr, OverloadedVar):
        candidates = pat_constr.resolved_names
      else:
        candidates = [pat_constr.get_name()]
      for constr in alts:
        # constr = node(T, List<T>)
        if constr.name in candidates:
          # Narrowing happens via class transition: the surrounding
          # PatternCons gets a new ResolvedVar in place of its old
          # (overloaded) constructor. We return that new node alongside
          # the parameter types so the caller can swap it in. (We don't
          # have the PatternCons here, so the caller does the mutation.)
          if len(typarams) > 0:
            if not isinstance(typ, TypeInst):
                internal_error(loc, 'problem in check_constr_pattern with: ' + str(typ))
            sub = { T: ty for (T,ty) in zip(typarams, typ.arg_types)}
            parameter_types = [p.substitute(sub) for p in constr.parameters]
          else:
            parameter_types = constr.parameters
          cases_present[constr.name] = True
          new_constr = ResolvedVar(pat_constr.location,
                                   pat_constr.typeof, constr.name)
          return new_constr, list(zip(params, parameter_types))
      user_error(loc, base_name(pat_constr.get_name()) \
            + ' is not a constructor of union ' + str(defn))
      #return env
    case _:
      user_error(loc, str(typ) + ' is not a union type')
        
def check_pattern(
    pattern: Pattern, typ: TypeExpr, env: Env, cases_present: PatternCoverage
) -> Env:
  if get_verbose():
    print('check pattern: ' + str(pattern))
    print('against type: ' + str(typ))
    #print('in env: ' + str(env))
#  pattern.typeof = typ
  match pattern:
    case PatternBool(loc, value):
      match typ:
        case BoolType(_):
          cases_present[str(value)] = True
          return env
        case _:
          user_error(pattern.location, 'expected a pattern of type\n\t' \
                + str(typ) + '\nbut got\n\t' + str(pattern))
    case PatternCons(loc, constr, params):
      if not isinstance(constr, VarRef):
        user_error(loc, 'expected a constructor name in pattern, not\n\t'
                   + str(constr))
      new_constr, param_types = check_constructor_pattern(
          loc, constr, params, typ, env, cases_present)
      pattern.constructor = new_constr
      return env.declare_term_vars(loc, param_types)
    case _:
      user_error(pattern.location, 'expected a pattern, not\n\t' \
            + str(pattern))

def check_formula(
    frm: Term,
    env: Env,
    recfun: RecursiveName = None,
    subterms: SubtermNames = (),
) -> Term:
  return type_check_term(frm, BoolType(frm.location), env, recfun, subterms)

modules: set[str] = set()

dirty_files: set[str] = set()

def is_modified(filename: str) -> bool:
    path = Path(filename)
    last_mod = path.stat().st_mtime
    thm_path = path.with_suffix('.thm')
    if thm_path.exists():
        thm_last_mod = thm_path.stat().st_mtime
        return thm_last_mod < last_mod
    else:
        return True
          
# Strict-positivity check for inductive (union) types.
#
# A constructor parameter type is strictly positive in the union being defined
# (`union_name`) if `union_name` does not appear in any "negative position",
# i.e. to the left of an arrow in a `FunctionType`. Without this restriction
# the type theory is inconsistent: `union Bad { Wrap(fn Bad -> bool) }` admits
# Russell's paradox via `R = Wrap(fun x { not unwrap(x)(x) })`.
#
# When walking through a `TypeInst(D, args)` of some other generic union `D`,
# the polarity for each arg is adjusted by the polarity that `D` uses for that
# parameter. Per-parameter polarities for each generic union are inferred by
# `infer_param_polarities` and stored on the `Union` AST node before this
# check runs. This catches "nested" non-positivity such as
# `union B { Mk(Set<B>) }`, where `Set<X>` is `char_fun(fn X -> bool)` — `Set`'s
# parameter `X` is negative, so `B` ends up in a negative position.
#
# Deduce does not allow forward references between unions, so polarities can be
# computed in source order.
def _flip_polarity(pol: str) -> str:
  return '-' if pol == '+' else '+'

def _lookup_param_polarities(head: TypeExpr, env: Env) -> list[str] | None:
  """If `head` resolves to a Union, return its inferred per-parameter polarities
  (or None if not yet inferred)."""
  if not isinstance(head, VarRef):
    return None
  try:
    head_def = env.get_def_of_type_var(head)
  except Exception:
    return None
  if isinstance(head_def, Union):
    return getattr(head_def, 'param_polarities', None)
  return None

def check_strict_positivity(
    ty: TypeExpr, union_name: str, env: Env, forbidden: bool = False
) -> None:
  if isinstance(ty, VarRef):
    ref_name = ty.get_name()
    if forbidden and ref_name == union_name:
      user_error(ty.location,
            f"the union '{base_name(union_name)}' must not occur in a "
            f"negative position (to the left of '->') of its own "
            f"constructor parameters; this would make the logic "
            f"inconsistent (Russell's paradox)")
    return
  match ty:
    case TypeInst(_, head, type_args):
      check_strict_positivity(head, union_name, env, forbidden)
      head_pols = _lookup_param_polarities(head, env)
      for i, t in enumerate(type_args):
        if head_pols is not None and i < len(head_pols) and head_pols[i] == '-':
          # Sticky: passing through a negative parameter forbids occurrences
          # in this arg, even under further negations.
          eff_forbidden = True
        else:
          eff_forbidden = forbidden
        check_strict_positivity(t, union_name, env, eff_forbidden)
    case FunctionType(_, _, param_types, return_type):
      for t in param_types:
        check_strict_positivity(t, union_name, env, forbidden=True)
      check_strict_positivity(return_type, union_name, env, forbidden)
    case ArrayType(_, elt_ty):
      check_strict_positivity(elt_ty, union_name, env, forbidden)
    case _:
      pass

# Infer per-parameter polarities for `union_decl` and stash them on the AST
# node as `param_polarities`. The list is mutable and used in-place during a
# fixpoint iteration so self-references read the in-progress polarities. This
# converges in at most |type_params| iterations because polarity is monotone
# (only goes '+' -> '-').
def infer_param_polarities(union_decl: Union, env: Env) -> None:
  if not union_decl.type_params:
    union_decl.param_polarities = []
    return

  polarities = ['+'] * len(union_decl.type_params)
  union_decl.param_polarities = polarities  # exposed in-place for self-refs

  type_param_names = set(union_decl.type_params)

  def walk(ty: TypeExpr, current: str) -> None:
    if isinstance(ty, VarRef):
      ref_name = ty.get_name()
      if ref_name in type_param_names:
        idx = union_decl.type_params.index(ref_name)
        if current == '-':
          polarities[idx] = '-'
      return
    match ty:
      case TypeInst(_, head, type_args):
        walk(head, current)
        head_pols = _lookup_param_polarities(head, env)
        for i, arg in enumerate(type_args):
          if head_pols is not None and i < len(head_pols) and head_pols[i] == '-':
            # Sticky: descending through a negative parameter records this arg
            # as negative regardless of how deeply further function arrows
            # nest. This matches Coq's strict positivity (no parity flipping).
            eff = '-'
          else:
            eff = current
          walk(arg, eff)
      case FunctionType(_, _, param_types, return_type):
        for t in param_types:
          walk(t, '-')
        walk(return_type, current)
      case ArrayType(_, elt_ty):
        walk(elt_ty, current)
      case _:
        pass

  while True:
    before = list(polarities)
    for con in union_decl.alternatives:
      for ty in con.parameters:
        walk(ty, '+')
    if before == polarities:
      break
