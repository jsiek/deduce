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
from typing import List, Optional, Tuple, cast

from lark.tree import Meta

from abstract_syntax import (
    All, And, Array, ArrayGet, Assert, Associative, Auto, Bool,
    Call, Conditional, Constructor, Declaration, Define, Env, Export,
    Formula, FunCase, FunctionType, GenRecFun, Generic, GenericUnknownInst,
    Hole, IfThen, Import, Inductive, Lambda, MakeArray, Module, ObjectDecl,
    ObjectField, ObserverDecl, Omitted, Or, OverloadType, OverloadedVar, PSorry, PVar,
    PatternBool, PatternCons, Postulate, Predicate, Print, ProcDecl, RecFun,
    ResolvedVar, Rule, Some,
    Statement, Switch, SwitchCase, TAnnote, TLet, Term, TermInst, Theorem,
    Trace, Type, TypeAlias, TypeInst, TypeType, Union, Var, VarRef, VerboseLevel,
    ViewDecl, ViewRecFun, alpha_equiv, base_name, callable_name,
    check_post_typecheck_invariants, find_file, mkEqual, print_theorems,
    set_eval_all, set_reduce_all, type_match, type_names,
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
    check_constructor_pattern, check_formula, check_no_recfun_escape,
    check_pattern, check_strict_positivity, check_type, dirty_files,
    get_recursive_call_count, infer_param_polarities, is_modified,
    lookup_union, reset_recursive_call_count, type_check_formula,
    type_check_term, type_synth_term,
)
from error import (
    Diagnostic, ErrorSink, MatchFailed, error_header, get_active_sink,
    internal_error, set_active_sink, user_error,
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

def process_declaration_visibility(decl: Declaration, env: Env,
                                   module_chain: list[str],
                                   downstream_needs_checking: list[bool]
                                   ) -> tuple[Statement, Env]:
  match decl:
    case ProcDecl(loc, name, _, _, _, _):
      user_error(loc, 'imperative proc declarations are not supported yet: '
                 + base_name(name))

    case ObserverDecl(loc, name, _, _, _, _, _):
      user_error(loc, 'imperative observer declarations are not supported yet: '
                 + base_name(name))

    case Define(loc, name, ty, body):
      if ty == None:
        new_body = type_synth_term(body, env, None, [])
        new_ty = new_body.typeof
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
  checked_view = type_check_term(_view_call(loc, view_decl.into,
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

def _view_call(loc: Meta, fun_name: str, arg: Term) -> Call:
  return Call(loc, None, ResolvedVar(loc, None, fun_name), [arg])

def _view_roundtrip_formula(loc: Meta, view: ViewDecl) -> Formula:
  value_name = generate_proof_name("v")
  value = ResolvedVar(loc, view.target, value_name)
  formula = mkEqual(loc,
                    _view_call(loc, view.into,
                               _view_call(loc, view.out, value)),
                    value)
  formula = All(loc, None, (value_name, view.target), (0, 1), formula)
  for i, tp in enumerate(reversed(view.type_params)):
    formula = All(loc, None, (tp, TypeType(loc)),
                  (i, len(view.type_params)), formula)
  return formula

def _view_inverse_formula(loc: Meta, view: ViewDecl) -> Formula:
  value_name = generate_proof_name("v")
  value = ResolvedVar(loc, view.source, value_name)
  formula = mkEqual(loc,
                    _view_call(loc, view.out,
                               _view_call(loc, view.into, value)),
                    value)
  formula = All(loc, None, (value_name, view.source), (0, 1), formula)
  for i, tp in enumerate(reversed(view.type_params)):
    formula = All(loc, None, (tp, TypeType(loc)),
                  (i, len(view.type_params)), formula)
  return formula

def _check_view_roundtrip(loc: Meta, view: ViewDecl, env: Env) -> None:
  expected = type_check_formula(_view_roundtrip_formula(loc, view), env)
  actual = env.get_formula_of_proof_var(PVar(loc, view.roundtrip))
  if actual is None:
    user_error(loc, "undefined roundtrip proof for view: "
               + base_name(view.roundtrip))
  if not alpha_equiv(actual, expected):
    user_error(loc, "view roundtrip proof " + base_name(view.roundtrip)
               + " proves\n\t" + str(actual)
               + "\nbut expected\n\t" + str(expected))

def _check_view_inverse(loc: Meta, view: ViewDecl, env: Env) -> None:
  if view.inverse is None:
    return
  expected = type_check_formula(_view_inverse_formula(loc, view), env)
  actual = env.get_formula_of_proof_var(PVar(loc, view.inverse))
  if actual is None:
    user_error(loc, "undefined inverse proof for view: "
               + base_name(view.inverse))
  if not alpha_equiv(actual, expected):
    user_error(loc, "view inverse proof " + base_name(view.inverse)
               + " proves\n\t" + str(actual)
               + "\nbut expected\n\t" + str(expected))

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
  checked_view = type_check_term(_view_call(loc, view_decl.into,
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

    case ObjectDecl():
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

    case ObjectDecl():
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
      _check_view_roundtrip(loc, stmt, env)
      _check_view_inverse(loc, stmt, env)
      return env.declare_view(loc, stmt, stmt.visibility)
      
    case Union(loc, name, typarams, _):
      return env

    case TypeAlias():
      return env

    case ObjectDecl():
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
      pass

    case ViewDecl():
      pass
  
    case Export(loc, name):
      pass
  
    case Import(loc, name, _):
      pass
  
    case Print(loc, trm):
      set_reduce_all(True)
      set_eval_all(True)
      result = trm.reduce(env)
      set_eval_all(False)
      set_reduce_all(False)
      print(str(result))
      
    case Assert(loc, frm):
      match frm:
        case Call(_, _, rator, [lhs, rhs]) if isinstance(rator, VarRef) and rator.get_name() == '=':
          set_reduce_all(True)
          set_eval_all(True)
          L = lhs.reduce(env)
          R = rhs.reduce(env)
          set_eval_all(False)
          set_reduce_all(False)
          if L == R:
            pass
          else:
              user_error(loc, 'assertion failed:\n' +
                    '\t' + str(L) + ' ≠ ' + str(R) + '\n')
        case IfThen(_, _,
                    Call(_, _, rator, [lhs, rhs]),
                    Bool(_, _, False)) if isinstance(rator, VarRef) and rator.get_name() == '=':
          set_reduce_all(True)
          set_eval_all(True)
          L = lhs.reduce(env)
          R = rhs.reduce(env)
          set_eval_all(False)
          set_reduce_all(False)
          if L != R:
            pass
          else:
              user_error(loc, 'assertion failed:\n' +
                    '\t' + str(L) + ' = ' + str(R) + '\n')
        case _:
          set_reduce_all(True)
          set_eval_all(True)
          result = frm.reduce(env)
          set_eval_all(False)
          set_reduce_all(False)
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
        # Bypass the cache for them; ``check_proofs`` on these is
        # cheap anyway.
        try:
          _sink = get_active_sink()
          pre_n = len(_sink) if _sink is not None else 0
          # Phase 5 / Step 21: when a debugger is attached, every
          # ``check_proofs`` call must run its hooks -- a cache hit
          # would silently skip the trap.  Re-check unconditionally;
          # this also avoids polluting the cache with cache-key
          # collisions caused by debugger-driven reduction order.
          if get_debugger() is not None:
            check_proofs(s, env)
            _record_miss("check_proofs")
          elif isinstance(s, (Print, Assert)):
            check_proofs(s, env)
            _record_miss("check_proofs")
          elif key in _stmt_cache:
            _record_hit("check_proofs")
          else:
            check_proofs(s, env)
            # Don't cache if check_proofs absorbed errors into the
            # sink -- next run must re-check so the diagnostic is
            # re-emitted.
            _sink2 = get_active_sink()
            if _sink2 is None or len(_sink2) == pre_n:
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
