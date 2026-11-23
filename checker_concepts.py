"""Checking concepts, models, and where clauses (#1264).

A where formula means its F^G translation (see
``abstract_syntax/concepts.py``):

    all T:type where { C<T> }. P   ==   all T:type. all ops. if axioms then P

``check_where_all`` builds that expansion when the formula is type
checked, so every other part of the checker sees an ordinary formula.
The rest of this module gives the where clause its meaning at the two
places it matters:

* ``arbitrary T:type where { C<T> }`` introduces the operations and
  assumes the axioms under the names the proof binds (F^G's TAbs).
* ``thm<τ>`` looks up the models of the clause's concepts at ``τ``,
  passes their operations, discharges the axioms with the models' own
  (already checked) theorems, and unfolds the operations that the client
  can see (F^G's TApp, with dictionary projections reduced).

A model's operations are hidden definitions named by the model, so a
client depends only on what the model's module exports: an opaque model
leaves them folded. A parameterized model (#1321) is found by matching
its head, and its where clause's models are found where it is used.
"""

from __future__ import annotations

import itertools
from typing import Callable, cast

from abstract_syntax import (
    All, AllElimTypes, And, ArrayType, AssocType, BoolType, Call, ConceptBinding, ConceptDecl,
    ConceptMember, ConceptMemberProof, ConceptRef, Env,
    Formula, IfThen, ModelBinding, MutableArrayType, ModelDecl, ModelInstance, Proof,
    ResolvedVar, Term, TermBinding, TermInst, Type, TypeAlias, TypeBinding, FunctionType, TypeInst, TypeType, VarRef, WhereClause, WhereMember, base_name, concept_closure,
    where_body,
)
from checker_types import check_formula, check_type, type_check_term
from error import UserError, user_error, wrap_user_error
from lark.tree import Meta

# What stands for a member of a concept instance: a where clause's
# binder, or a model's operation or associated type.
MemberLookup = Callable[[ConceptRef, str], Term | Type]
# The model chosen for each concept instance.
Models = list[tuple[ConceptRef, ModelInstance]]

# The environment key of the models that the where clauses and local
# models (`model` inside a proof) in scope provide, innermost first.
SCOPED_MODELS_KEY = ' where models'

# How deeply the where clauses of parameterized models may ask for
# further models before model lookup gives up.
MAX_MODEL_DEPTH = 16


def _model_for(models: Models, inst: ConceptRef) -> ModelInstance:
  return next(m for (i, m) in models if i == inst)


def concept_of(env: Env, name: str, loc: Meta) -> ConceptDecl:
  binding = env.dict.get(name)
  if not isinstance(binding, ConceptBinding):
    user_error(loc, 'expected a concept, not ' + base_name(name))
  return binding.decl


def _param_sub(decl: ConceptDecl, inst: ConceptRef) -> dict[str, Type]:
  return dict(zip(decl.type_params, inst.type_args))


def member_type(env: Env, inst: ConceptRef, member: str, loc: Meta,
                types: dict[str, Type] | None = None) -> Type:
  """The type of the operation ``member`` of ``inst``, whose associated
  types are ``types`` (#1321)."""
  decl = concept_of(env, inst.concept, loc)
  return dict(decl.funs)[member].substitute(_param_sub(decl, inst)
                                            | (types or {}))


def _model_types(m: ModelInstance) -> dict[str, Type]:
  """The associated types of the model instance ``m``."""
  model = m.binding.model
  sub: dict[str, Term | Type] = dict(zip(model.type_params, m.type_args))
  return {t: ty.substitute(sub) for (t, ty) in model.types}


def _instance_sub(env: Env, inst: ConceptRef, lookup: MemberLookup,
                  loc: Meta) -> dict[str, Term | Type]:
  """Takes the vocabulary of ``inst``'s concept (its type parameters, its
  associated types, its operations, and the binders of the members it
  refines) to ``inst``'s type arguments and to ``lookup``'s types and
  terms."""
  decl = concept_of(env, inst.concept, loc)
  psub = _param_sub(decl, inst)
  sub: dict[str, Term | Type] = dict(psub)
  for m in decl.types + [f for (f, _) in decl.funs]:
    sub[m] = lookup(inst, m)
  for wm in decl.refines.operations():
    sub[wm.binder] = lookup(wm.instance.substitute(psub), wm.member)
  return sub


def axiom(env: Env, inst: ConceptRef, theorem: str, lookup: MemberLookup,
          loc: Meta) -> Formula:
  decl = concept_of(env, inst.concept, loc)
  return dict(decl.theorems)[theorem].substitute(
      _instance_sub(env, inst, lookup, loc))


def _premise(env: Env, where: WhereClause, lookup: MemberLookup,
             loc: Meta) -> Formula | None:
  axioms = [axiom(env, wm.instance, wm.member, lookup, loc)
            for wm in where.theorems()]
  if not axioms:
    return None
  return axioms[0] if len(axioms) == 1 else And(loc, BoolType(loc), axioms)


def _binder_lookup(env: Env, where: WhereClause, loc: Meta) -> MemberLookup:
  def lookup(inst: ConceptRef, member: str) -> Term | Type:
    types = where.assoc_types(inst)
    if member in types:
      return types[member]
    for wm in where.operations():
      if wm.instance == inst and wm.member == member:
        return ResolvedVar(loc, member_type(env, inst, member, loc, types),
                           wm.binder)
    user_error(loc, 'no binder for ' + base_name(member) + ' of ' + str(inst))
  return lookup


def check_where(where: WhereClause, env: Env,
                own: list[str] | None = None) -> WhereClause:
  """Type check the concept applications of a where clause (including
  its refinement closure) in ``env``, and solve its same-type
  constraints, which may determine the type variables ``own`` that the
  clause introduces."""
  def check_ref(ref: ConceptRef) -> ConceptRef:
    concept_of(env, ref.concept, ref.location)
    return ConceptRef(ref.location, ref.concept,
                      [check_type(t, env) for t in ref.type_args])
  checked = WhereClause(where.location,
                        [check_ref(c) for c in where.constraints],
                        [WhereMember(check_ref(wm.instance), wm.member,
                                     wm.binder, wm.is_theorem)
                         for wm in where.members],
                        where.expanded, equations=where.equations,
                        assoc=[(check_ref(i), t, p) for (i, t, p) in where.assoc])
  if where.equations:
    _solve(checked, env, own or [])
  return checked


def _solve(where: WhereClause, env: Env, own: list[str]) -> None:
  """Solve the same-type constraints of ``where`` (#1321), following the
  congruence closure of G (Siek's thesis, §4.5 and §5.2): type the
  constraints, unify their sides, and merge the instances that become
  equal, which merges their associated types (if `S = T` then
  `@C<S>.Elem = @C<T>.Elem`). Only the clause's own type variables
  ``own`` and its proxies can be determined, each by a type or by a
  variable bound before it; the types of outer scopes are fixed. Sets
  the checked constraints, the solution, and the instances in terms of
  the solution."""
  loc = where.location
  proxies = where.proxies()
  variables = own + proxies
  scope = add_where_models(loc, where, env.declare_type_vars(loc, proxies))
  written = [(str(s) + ' = ' + str(t), s.location) for (s, t) in where.equations]
  where.equations = [(check_type(s, scope), check_type(t, scope))
                     for (s, t) in where.equations]
  sol: dict[str, Type] = {}

  def describe(x: str) -> str:
    return next(('@' + str(i) + '.' + str(base_name(t))
                 for (i, t, p) in where.assoc if p == x),
                None) or _outer_projection(x, env)

  def unify(s: Type, t: Type, why: str, loc: Meta) -> None:
    s, t = s.substitute(sol), t.substitute(sol)
    if s == t:
      return
    free = [x for u in (s, t) if (x := _var_name(u)) and x in variables]
    if free:
      x = max(free, key=variables.index)
      other = t if _var_name(s) == x else s
      if x in other.free_vars():
        user_error(loc, why + ' makes ' + describe(x) + ' part of itself')
      for q in sol:
        sol[q] = sol[q].substitute({x: other})
      sol[x] = other
      return
    pairs = _decompose(s, t)
    if pairs is not None:
      for (a, b) in pairs:
        unify(a, b, why, loc)
      return
    fixed = [x for u in (s, t) if (x := _var_name(u)) and _is_type_var(x, env)]
    if fixed:
      user_error(loc, why + ' constrains ' + describe(fixed[0])
                 + ', which is fixed outside this where clause')
    user_error(loc, why + ' is inconsistent: ' + str(s) + ' ≠ ' + str(t))

  pending = [(s, t, 'the same-type constraint ' + w, eq_loc)
             for ((s, t), (w, eq_loc)) in zip(where.equations, written)]
  while pending:
    for (s, t, why, eq_loc) in pending:
      unify(s, t, why, eq_loc)
    # Congruence: instances that have become equal are one instance, so
    # their associated types are equal.
    pending = []
    seen: list[tuple[ConceptRef, str, Type, ConceptRef]] = []
    for (i, t, p) in where.assoc:
      inst = i.substitute(sol)
      proxy = cast(Type, ResolvedVar(loc, None, p)).substitute(sol)
      same = next(((q, k) for (j, u, q, k) in seen if j == inst and u == t),
                  None)
      if same is None:
        seen.append((inst, t, proxy, i))
      elif same[0] != proxy:
        pending.append((same[0], proxy, 'merging ' + str(same[1]) + ' and '
                        + str(i), written[-1][1]))
  where.solution = sol
  # Instances that have become equal are one instance: keep the first's
  # members (G, Siek's thesis §5.2.3).
  members: list[WhereMember] = []
  for wm in where.members:
    m = WhereMember(wm.instance.substitute(sol), wm.member, wm.binder,
                    wm.is_theorem)
    if not any(o.instance == m.instance and o.member == m.member
               for o in members):
      members.append(m)
  where.members = members
  where.assoc = [(i.substitute(sol), t, p) for (i, t, p) in where.assoc]


def _is_type_var(x: str, env: Env) -> bool:
  b = env.dict.get(x)
  return (isinstance(b, TermBinding) and isinstance(b.typ, TypeType)) \
    or (isinstance(b, TypeBinding) and b.defn is None)


def _group_vars(env: Env, n: int) -> list[str]:
  """The ``n`` type variables declared last in ``env``: those bound by
  the same `all` as a where clause's own variable, before it."""
  names: list[str] = []
  for (name, b) in reversed(list(env.dict.items())):
    if len(names) == n or not (isinstance(b, TermBinding)
                               and isinstance(b.typ, TypeType)):
      break
    names.insert(0, name)
  return names


def _outer_projection(x: str, env: Env) -> str:
  """The type variable ``x``, as the projection on an outer where clause's
  instance that it stands for, if it is one of that clause's proxies."""
  for name in cast(list[str], env.dict.get(SCOPED_MODELS_KEY, [])):
    b = env.dict[name]
    if isinstance(b, ModelBinding):
      for (t, ty) in b.model.types:
        if _var_name(ty) == x:
          return '@' + str(b.model.concept) + '.' + str(base_name(t))
  return str(base_name(x))


def _var_name(t: Type) -> str | None:
  return t.get_name() if isinstance(t, VarRef) else None


def _decompose(s: Type, t: Type) -> list[tuple[Type, Type]] | None:
  """The pairs of parts that must be equal for ``s`` and ``t``, built
  with the same type constructor, to be equal (``None`` if they are not
  built with the same one). Associated types are not constructors:
  `@C<S>.Elem = @C<T>.Elem` doesn't make `S` and `T` equal."""
  if isinstance(s, TypeInst) and isinstance(t, TypeInst) \
     and s.typ == t.typ and len(s.arg_types) == len(t.arg_types):
    return list(zip(s.arg_types, t.arg_types))
  if isinstance(s, FunctionType) and isinstance(t, FunctionType) \
     and not s.type_params and not t.type_params \
     and len(s.param_types) == len(t.param_types):
    return list(zip(s.param_types, t.param_types)) \
      + [(s.return_type, t.return_type)]
  if isinstance(s, (ArrayType, MutableArrayType)) and type(t) is type(s):
    return [(s.elt_type, cast(ArrayType, t).elt_type)]
  return None


def _unsatisfied(where: WhereClause, lookup: MemberLookup) -> str | None:
  """Why ``lookup``'s associated types don't satisfy the same-type
  constraints of ``where`` (instantiated at the caller's types), if they
  don't (#1321)."""
  sub: dict[str, Term | Type] = {p: lookup(i, t) for (i, t, p) in where.assoc}
  for (s, t) in where.equations:
    a, b = s.substitute(sub), t.substitute(sub)
    if a != b:
      eq: str = where.equation_str(s, t)
      return 'the same-type constraint ' + eq + ' does not hold' \
        + ('' if eq == str(a) + ' = ' + str(b) else ': ' + str(a) + ' ≠ ' + str(b))
  return None


def _binder_type(env: Env, where: WhereClause, wm: WhereMember,
                 loc: Meta) -> Type:
  return member_type(env, wm.instance, wm.member, loc,
                     where.assoc_types(wm.instance))


def declare_where_operations(where: WhereClause, env: Env, loc: Meta) -> Env:
  """The proxies of the where clause's associated types, as type
  variables, the type variables that its same-type constraints determine,
  as aliases, and the binders of its operations."""
  env = env.declare_type_vars(loc, where.proxies())
  proxies = [p for (_, _, p) in where.assoc]
  for (x, ty) in where.solution.items():
    if x not in proxies:
      env = env.define_type(loc, x, TypeAlias(loc, x, [], ty))
  return env.declare_term_vars(
      loc, [(wm.binder, _binder_type(env, where, wm, loc))
            for wm in where.operations()])


def check_where_all(frm: All, env: Env,
                    check_body: Callable[[Formula, Env], Formula]) -> All:
  """Type check ``all x:type where {...}. P``, expanding its body to
  ``all ops. if axioms then P``."""
  loc = frm.location
  x, ty = frm.var
  new_ty = check_type(ty, env)
  if not isinstance(new_ty, TypeType):
    user_error(loc, 'a where clause must follow a type variable, not '
               + base_name(x) + ':' + str(new_ty))
  body_env = env.declare_term_vars(loc, [(x, new_ty)])
  assert frm.where is not None
  where = check_where(frm.where, body_env,
                      _group_vars(env, frm.pos[1] - 1) + [x])
  body_env = declare_where_operations(where, body_env, loc)
  body = check_body(where_body(frm), add_where_models(loc, where, body_env))
  lookup = _binder_lookup(body_env, where, loc)
  premise = _premise(body_env, where, lookup, loc)
  if premise is not None:
    body = IfThen(loc, BoolType(loc), premise, body)
  for wm in reversed(where.operations()):
    body = All(loc, BoolType(loc), (wm.binder, _binder_type(body_env, where, wm, loc)),
               (0, 1), body)
  for p in reversed(where.proxies()):
    body = All(loc, BoolType(loc), (p, TypeType(loc)), (0, 1), body)
  where.expanded = True
  return All(loc, BoolType(loc), (x, new_ty), frm.pos, body, where=where)


def _strip_operations(loc: Meta, frm: Formula, where: WhereClause,
                      lookup: MemberLookup) -> Formula:
  """Instantiate the ``all`` binders of an expanded where formula's body,
  for its associated types and operations, with ``lookup``'s types and
  terms."""
  sub = {}
  for (inst, member, binder) in [(i, t, p) for (i, t, p) in where.assoc
                                 if p not in where.solution] \
      + [(wm.instance, wm.member, wm.binder) for wm in where.operations()]:
    if not isinstance(frm, All) or frm.var[0] != binder:
      user_error(loc, 'expected the operations of the where clause, not\n\t'
                 + str(frm))
    sub[binder] = lookup(inst, member)
    frm = frm.body
  return frm.substitute(sub)


def _discharge(loc: Meta, frm: Formula, premise: Formula | None) -> Formula:
  """The conclusion of ``frm``, whose premise must be exactly ``premise``,
  the axioms of the where clause. A formula whose premise was changed
  (say, by a proof step that strengthened it) is not a where formula any
  more, so it can't be instantiated by passing models."""
  if premise is None:
    return frm
  if not isinstance(frm, IfThen) or frm.premise != premise:
    user_error(loc, 'the axioms of the where clause have been changed:\n\t'
                    + str(frm))
  return frm.conclusion


def intro_where(loc: Meta, goal: All, x: str, where: WhereClause,
                env: Env) -> tuple[Formula, Env]:
  """``arbitrary x:type where {...}`` against the where formula ``goal``:
  the body to prove and the environment that has the proof's operations
  and axioms."""
  assert goal.where is not None
  goal_where = goal.where.substitute({goal.var[0]: ResolvedVar(loc, None, x)})
  body_env = env.declare_term_vars(loc, [(x, TypeType(loc))])
  # The proof repeats the goal's where clause, so its constraints
  # determine the type variables that the goal's determine.
  goal_proxies = [p for (_, _, p) in goal_where.assoc]
  where = check_where(where, body_env, [v for v in goal_where.solution
                                        if v not in goal_proxies])
  mismatch = 'arbitrary expects the where clause\n\t' + str(goal_where) \
      + '\nbut got\n\t' + str(where)
  rename: dict[str, Term | Type] = \
      {gp: ResolvedVar(loc, None, p)
       for ((_, _, gp), (_, _, p)) in zip(goal_where.assoc, where.assoc)}
  if goal_where.constraints != where.constraints \
     or [(s.substitute(rename), t.substitute(rename))
         for (s, t) in goal_where.equations] != where.equations:
    user_error(loc, mismatch)
  body_env = declare_where_operations(where, body_env, loc)
  lookup = _binder_lookup(body_env, where, loc)
  frm = goal.body.substitute({goal.var[0]: ResolvedVar(loc, None, x)})
  frm = _strip_operations(loc, frm, goal_where, lookup)
  frm = _discharge(loc, frm, _premise(body_env, where, lookup, loc))
  return frm, _assume_where(loc, where, body_env, lookup)


def where_scope(loc: Meta, where: WhereClause, env: Env) -> Env:
  """The scope of the (checked) where clause ``where``, as after
  `arbitrary T:type where {...}`: its operations, its theorems as
  givens, and its models."""
  env = declare_where_operations(where, env, loc)
  return _assume_where(loc, where, env, _binder_lookup(env, where, loc))


def _assume_where(loc: Meta, where: WhereClause, env: Env,
                  lookup: MemberLookup) -> Env:
  for wm in where.theorems():
    env = env.declare_local_proof_var(
        loc, wm.binder, axiom(env, wm.instance, wm.member, lookup, loc))
  return add_where_models(loc, where, env)


def add_where_models(loc: Meta, where: WhereClause, env: Env) -> Env:
  """Add a model for each concept instance of ``where`` (its refinement
  closure), whose operations are the where clause's binders: in its
  scope, a where clause models its concepts (F^G's where clauses add
  models to the context), so a where theorem can be instantiated at the
  clause's types."""
  # From the constraints, not the members: a concept may have none.
  insts = check_where(WhereClause(loc, concept_closure(where.constraints)),
                      env).constraints
  bindings: dict[str, ModelBinding] = {}
  for inst in insts:
    funs = [(wm.member, wm.binder,
             ResolvedVar(loc, _binder_type(env, where, wm, loc), wm.binder))
            for wm in where.operations() if wm.instance == inst]
    model = ModelDecl(loc, _where_prefix(loc) + str(inst), inst,
                      cast(list[tuple[str, str, Term]], funs), [],
                      types=list(where.assoc_types(inst).items()))
    bindings[str(inst)] = ModelBinding(loc, model, [],
                                       module=env.get_current_module())
  for inst in insts:
    b = bindings[str(inst)]
    decl = concept_of(env, inst.concept, loc)
    psub = _param_sub(decl, inst)
    b.refined = [ModelInstance(bindings[str(r.substitute(psub))])
                 for r in decl.refines.constraints]
    env = env._with_binding(b.model.name, b)
  return scope_models([b.model.name for b in bindings.values()], env)


def _where_prefix(loc: Meta) -> str:
  """The start of the names of the models of the where clause at
  ``loc``."""
  return '<where ' + str(loc.line) + '.' + str(loc.column) + '> '


def scope_models(names: list[str], env: Env) -> Env:
  """Put the models ``names`` in scope ahead of the outer ones: those of
  a where clause, or a `model` inside a proof (#1321)."""
  return env._with_binding(
      SCOPED_MODELS_KEY,
      names + cast(list[str], env.dict.get(SCOPED_MODELS_KEY, [])))


def find_model(env: Env, inst: ConceptRef, models: list[str],
               loc: Meta, depth: int = 0) -> ModelInstance:
  """The model of ``inst`` that the innermost where clause or local
  model in scope provides, or else the one among ``models``, the models
  in lexical scope (recorded by uniquify). A parameterized model fits
  when its head matches ``inst``; the models its where clause needs are
  then found the same way."""
  if depth > MAX_MODEL_DEPTH:
    user_error(loc, 'gave up looking for models: the where clauses of'
               + ' parameterized models keep needing more models')
  for name in cast(list[str], env.dict.get(SCOPED_MODELS_KEY, [])):
    b = env.dict[name]
    if isinstance(b, ModelBinding) and (sub := _head_match(b, inst)) is not None:
      return _instance(env, b, sub, models, loc, depth)
  found = [(b, sub) for name in models
           if isinstance(b := env.dict.get(name), ModelBinding)
           and (sub := _head_match(b, inst)) is not None]
  if not found:
    user_error(loc, 'no model of ' + str(inst) + ' in scope')
  if len(found) > 1:
    user_error(loc, 'more than one model of ' + str(inst) + ' in scope')
  (b, sub) = found[0]
  return _instance(env, b, sub, models, loc, depth)


def _head_match(b: ModelBinding, inst: ConceptRef) -> dict[str, Type] | None:
  """The type arguments for which the model ``b`` models ``inst``, if
  any."""
  head = b.model.concept
  sub: dict[str, Type] = {}
  if head.concept == inst.concept \
     and all(_match_type(p, t, b.model.type_params, sub)
             for (p, t) in zip(head.type_args, inst.type_args)):
    return sub
  return None


def _instance(env: Env, b: ModelBinding, sub: dict[str, Type],
              models: list[str], loc: Meta, depth: int) -> ModelInstance:
  """The model ``b`` at the type arguments ``sub``, with the models of its
  where clause at them, found among ``models`` (F^G: models are found
  where they are used)."""
  model = b.model
  type_args = [sub[p] for p in model.type_params]
  if model.where is None:
    return ModelInstance(b, type_args)
  try:
    args = _models_in_scope(loc, model.where.substitute(sub).constraints,
                            models, env, depth + 1)
  except UserError as e:
    if depth > 0:
      raise
    raise wrap_user_error(e, '\n(needed by ' + model.head() + ' for '
                          + str(model.concept.substitute(sub)) + ')')
  return ModelInstance(b, type_args, args)


def where_arguments(loc: Meta, where: WhereClause, in_scope: list[str],
                    env: Env) -> list[Term]:
  """The operations to pass to a function with the where clause
  ``where`` (instantiated at the call's types): those of the models in
  scope, unfolded where they are visible (F^G's dictionary passing)."""
  models = _models_in_scope(loc, where.constraints, in_scope, env)
  lookup = _model_lookup(env, models, loc)
  return [lookup(wm.instance, wm.member) for wm in where.operations()]


def _match_type(pattern: Type, ty: Type, tyvars: list[str],
                sub: dict[str, Type]) -> bool:
  """Match ``pattern`` against ``ty``, binding the type variables
  ``tyvars`` wherever they occur in ``pattern`` (say, ``T`` in
  ``List<T>`` against ``List<bool>``)."""
  if isinstance(pattern, VarRef) and pattern.get_name() in tyvars:
    x = pattern.get_name()
    if x in sub:
      return bool(sub[x] == ty)
    sub[x] = ty
    return True
  if isinstance(pattern, TypeInst) and isinstance(ty, TypeInst):
    return len(pattern.arg_types) == len(ty.arg_types) \
      and _match_type(pattern.typ, ty.typ, tyvars, sub) \
      and all(_match_type(p, t, tyvars, sub)
              for (p, t) in zip(pattern.arg_types, ty.arg_types))
  if isinstance(pattern, FunctionType) and isinstance(ty, FunctionType):
    return not pattern.type_params and not ty.type_params \
      and len(pattern.param_types) == len(ty.param_types) \
      and all(_match_type(p, t, tyvars, sub)
              for (p, t) in zip(pattern.param_types, ty.param_types)) \
      and _match_type(pattern.return_type, ty.return_type, tyvars, sub)
  if isinstance(pattern, (ArrayType, MutableArrayType)) \
     and type(ty) is type(pattern):
    return _match_type(pattern.elt_type, cast(ArrayType, ty).elt_type,
                       tyvars, sub)
  return bool(pattern == ty)


def where_instances(loc: Meta, frm: Formula, base: Proof, models: list[str],
                    env: Env) -> list[Proof] | None:
  """For a where formula used without its types, ``base`` instantiated at
  each combination of types that the models in scope ``models`` allow
  (``None`` if ``frm`` is not a where formula). The type variables are
  those bound before the where clause; each ranges over the type
  arguments of the models of the constraints it appears in."""
  tyvars: list[str] = []
  while isinstance(frm, All) and isinstance(frm.var[1], TypeType):
    tyvars.append(frm.var[0])
    if frm.where is not None:
      break
    frm = frm.body
  if not isinstance(frm, All) or frm.where is None:
    return None
  options: list[list[Type]] = [[] for _ in tyvars]
  for name in cast(list[str], env.dict.get(SCOPED_MODELS_KEY, [])) + models:
    b = env.dict.get(name)
    # A parameterized model's head has type variables of its own: give
    # the types explicitly to use it.
    if not isinstance(b, ModelBinding) or b.model.type_params:
      continue
    for c in frm.where.constraints:
      if c.concept != b.model.concept.concept:
        continue
      sub: dict[str, Type] = {}
      if not all(_match_type(arg, ty, tyvars, sub)
                 for (arg, ty) in zip(c.type_args, b.model.concept.type_args)):
        continue
      for (x, types) in zip(tyvars, options):
        if x in sub and sub[x] not in types:
          types.append(sub[x])
  instances: list[Proof] = []
  for choice in itertools.product(*options):
    proof = base
    for i, ty in enumerate(choice):
      proof = AllElimTypes(loc, proof, ty, (i, len(choice)), models=models)
    instances.append(proof)
  return instances


def _model_lookup(env: Env, models: Models, loc: Meta) -> MemberLookup:
  def lookup(inst: ConceptRef, member: str) -> Term | Type:
    m = _model_for(models, inst)
    types = _model_types(m)
    return types[member] if member in types else _member(env, m, member, loc)
  return lookup


def _member(env: Env, m: ModelInstance, member: str, loc: Meta) -> Term:
  """The operation ``member`` of the model instance ``m``: its body where
  this module can see the model, and otherwise its hidden definition,
  folded (F^G's dictionary projection, reduced). Only these names
  change: the result is not otherwise reduced, so auto rules don't
  collapse it. A parameterized model's operation is its body at the
  instance's types and at the operations of its where clause's models."""
  model = m.binding.model
  sub: dict[str, Term | Type] = dict(zip(model.type_params, m.type_args))
  inst = model.concept.substitute(sub)
  found = [(define, body) for (mem, define, body) in model.funs if mem == member]
  if not found:
    user_error(loc, 'model ' + str(inst) + ' has no ' + base_name(member))
  (define, body) = found[0]
  where_ops = model.where.operations() if model.where else []
  ops = [_member(env, _model_for(m.args, wm.instance.substitute(sub)),
                 wm.member, loc) for wm in where_ops]
  if m.binding.visibility != 'opaque' \
     or m.binding.module == env.get_current_module():
    sub.update({wm.binder: op for (wm, op) in zip(where_ops, ops)})
    return body.substitute(sub)
  ty = member_type(env, inst, member, loc, _model_types(m))
  if not model.type_params:
    return ResolvedVar(loc, ty, define)
  generic_ty = member_type(env, model.concept, member, loc, dict(model.types))
  fun = TermInst(loc, FunctionType(loc, [], [op.typeof for op in ops], ty),
                 ResolvedVar(loc, model.definition_type(generic_ty), define),
                 m.type_args, False)
  return Call(loc, ty, fun, ops)


def instantiate_where(loc: Meta, allfrm: All, type_arg: Type,
                      env: Env, in_scope: list[str]) -> Formula:
  """``thm<τ>`` for a where formula: pass the models of the clause's
  concepts at ``τ`` (F^G's TApp)."""
  assert allfrm.where is not None
  sub = {allfrm.var[0]: type_arg}
  where = allfrm.where.substitute(sub)
  models = _models_in_scope(loc, where.constraints, in_scope, env)
  lookup = _model_lookup(env, models, loc)
  if (why := _unsatisfied(where, lookup)) is not None:
    user_error(loc, why)
  frm = _strip_operations(loc, allfrm.body.substitute(sub), where, lookup)
  return _discharge(loc, frm, _premise(env, where, lookup, loc))


def _models_in_scope(loc: Meta, refs: list[ConceptRef], in_scope: list[str],
                     env: Env, depth: int = 0) -> Models:
  """The models in scope of the concept instances ``refs`` require
  (their refinement closure), checked for coherence: every refinement
  path to an instance reaches one model."""
  models = [(inst, find_model(env, inst, in_scope, loc, depth))
            for inst in concept_closure(refs)]
  for (head, m) in models:
    concept = concept_of(env, head.concept, loc)
    psub = _param_sub(concept, head)
    for ref, refined in zip(concept.refines.constraints, m.binding.refined):
      inst = ref.substitute(psub)
      if _model_for(models, inst).key() != _rebase(refined, m).key():
        user_error(loc, 'the model of ' + str(head)
                   + ' uses a different model of ' + str(inst)
                   + ' than the one in scope here')
  return models


def _rebase(r: ModelInstance, m: ModelInstance) -> ModelInstance:
  """The model ``r``, found where the parameterized model of ``m`` is
  declared (in terms of its type parameters and where clause), at the
  types and models of ``m``."""
  model = m.binding.model
  if not model.type_params:
    return r
  sub: dict[str, Term | Type] = dict(zip(model.type_params, m.type_args))
  if model.where is not None \
     and r.binding.model.name.startswith(_where_prefix(model.where.location)):
    return _model_for(m.args, r.binding.model.concept.substitute(sub))
  return ModelInstance(r.binding, [t.substitute(sub) for t in r.type_args],
                       [(c.substitute(sub), _rebase(a, m)) for (c, a) in r.args])


def _qualified(loc: Meta, ref: ConceptRef, in_scope: list[str],
               env: Env) -> tuple[ConceptRef, Models]:
  ref = check_where(WhereClause(loc, [ref]), env).constraints[0]
  return ref, _models_in_scope(loc, [ref], in_scope, env)


def check_concept_member(term: ConceptMember, env: Env) -> Term:
  """`@C<τ>.m` outside a where clause binding ``C<τ>``: the operation of
  the model in scope, unfolded where the model is visible."""
  loc = term.location
  ref, models = _qualified(loc, term.ref, term.models, env)
  model = _model_for(models, ref)
  found = [m for (m, _, _) in model.binding.model.funs
           if base_name(m) == term.member]
  if len(found) > 1:
    user_error(loc, '@' + str(ref) + '.' + term.member + ' could be any of '
               + str(len(found)) + ' operations of the model; use the'
               + ' operation unqualified, where its type tells which')
  return _member(env, model, found[0], loc)


def check_assoc_type(typ: AssocType, env: Env) -> Type:
  """`@C<τ>.Elem` is the type that the model of ``C<τ>`` in scope gives
  ``Elem``. Checked types are kept in this normal form (#1321), so they
  never contain a projection and `==` on them needs no type equations."""
  ref, models = _qualified(typ.location, typ.ref, typ.models, env)
  return _model_types(_model_for(models, ref))[typ.name]


def well_founded_less(less: ConceptMember, env: Env) -> Term:
  """The `<` that a recfun's measure decreases along (#1308): the
  operation of the model of ``WellFounded<τ>`` in scope. The concept must
  be the concept of well-founded orders: one operation `<` and the
  theorem that `<` admits strong induction, which every model proves."""
  loc = less.location
  decl = concept_of(env, less.ref.concept, loc)
  if not _is_well_founded(decl):
    user_error(loc, 'the concept ' + base_name(decl.name) + ' in scope is not'
               + ' the concept of well-founded orders (lib/WellFounded.pf):'
               + ' it needs one operation `<` and the theorem\n\t'
               + 'all P: fn T -> bool, n:T. if (all j:T. if (all i:T.'
               + ' if i < j then P(i)) then P(j)) then P(n)')
  try:
    return check_concept_member(less, env)
  except UserError as e:
    raise wrap_user_error(e, '\nA recfun\'s measure decreases along the `<`'
                          + ' of a model of WellFounded at its type, which'
                          + ' proves that `<` is well-founded.')


def _is_well_founded(decl: ConceptDecl) -> bool:
  if len(decl.type_params) != 1 or len(decl.funs) != 1:
    return False
  (lt, lt_ty) = decl.funs[0]
  if base_name(lt) != '<' or not isinstance(lt_ty, FunctionType) \
     or lt_ty.type_params or len(lt_ty.param_types) != 2 \
     or not isinstance(lt_ty.return_type, BoolType):
    return False
  t = lt_ty.param_types[0]
  if not (isinstance(t, VarRef) and t.get_name() == decl.type_params[0]
          and lt_ty.param_types[1] == t):
    return False
  loc = decl.location
  bool_ty = BoolType(loc)
  pred_ty = FunctionType(loc, [], [t], bool_ty)
  def var(x: str, ty: Type) -> Term:
    return ResolvedVar(loc, ty, x)
  def call(f: Term, args: list[Term]) -> Formula:
    return Call(loc, bool_ty, f, args)
  p, n, j, i = var('P', pred_ty), var('n', t), var('j', t), var('i', t)
  smaller = All(loc, bool_ty, ('i', t), (0, 1),
                IfThen(loc, bool_ty, call(var(lt, lt_ty), [i, j]), call(p, [i])))
  step = All(loc, bool_ty, ('j', t), (0, 1),
             IfThen(loc, bool_ty, smaller, call(p, [j])))
  strong = All(loc, bool_ty, ('P', pred_ty), (1, 2),
               All(loc, bool_ty, ('n', t), (0, 2),
                   IfThen(loc, bool_ty, step, call(p, [n]))))
  return any(frm == strong for (_, frm) in decl.theorems)


def concept_member_formula(proof: ConceptMemberProof, env: Env) -> Formula:
  """`@C<τ>.thm` outside a where clause binding ``C<τ>``: the concept's
  theorem at the operations of the model in scope (which proved it)."""
  loc = proof.location
  ref, models = _qualified(loc, proof.ref, proof.models, env)
  decl = concept_of(env, ref.concept, loc)
  theorem = next(m for (m, _) in decl.theorems if base_name(m) == proof.member)
  return axiom(env, ref, theorem, _model_lookup(env, models, loc), loc)


################ Declarations ################

def process_concept(decl: ConceptDecl, env: Env) -> tuple[ConceptDecl, Env]:
  loc = decl.location
  for ref in decl.refines.constraints:
    if set(decl.types) & set().union(*[t.free_vars() for t in ref.type_args]):
      user_error(ref.location, 'requirements on associated types, such as '
                 + str(ref) + ', are not supported yet (#1321)')
  # Inside the concept, its associated types are like type parameters.
  body_env = env.declare_type_vars(loc, decl.type_params + decl.types)
  refines = check_where(decl.refines, body_env)
  body_env = declare_where_operations(refines, body_env, loc)
  funs = [(f, check_type(t, body_env)) for (f, t) in decl.funs]
  body_env = body_env.declare_term_vars(loc, funs)
  theorems = [(n, check_formula(frm, body_env)) for (n, frm) in decl.theorems]
  new_decl = ConceptDecl(loc, decl.name, decl.type_params, refines, funs,
                         theorems, visibility=decl.visibility,
                         types=decl.types, requires=decl.requires)
  return new_decl, env._with_binding(
      decl.name, ConceptBinding(loc, new_decl, module=env.get_current_module(),
                                visibility=decl.visibility))


def _model_scope(model: ModelDecl, env: Env) -> Env:
  """The scope of a (checked) model's members: for a parameterized model,
  its type parameters and its where clause, whose theorems are givens."""
  env = env.declare_type_vars(model.location, model.type_params)
  if model.where is not None:
    env = where_scope(model.where.location, model.where, env)
  return env


def process_model(model: ModelDecl, env: Env) -> tuple[ModelDecl, Env]:
  loc = model.location
  where = None
  if model.where is not None:
    where = check_where(model.where,
                        env.declare_type_vars(loc, model.type_params))
  model = ModelDecl(loc, model.name, model.concept, model.funs, model.theorems,
                    visibility=model.visibility, models=model.models,
                    type_params=model.type_params, where=where,
                    types=model.types)
  body_env = _model_scope(model, env)
  concept_ref = check_where(WhereClause(loc, [model.concept]),
                            body_env).constraints[0]
  occurs: dict[str, Type] = {}
  for t in concept_ref.type_args:
    _match_type(t, t, model.type_params, occurs)
  for p in model.type_params:
    if p not in occurs:
      user_error(loc, 'the type parameter ' + base_name(p) + ' of the model'
                 + ' must occur in ' + str(concept_ref))
  decl = concept_of(env, concept_ref.concept, loc)
  types = [(t, check_type(ty, body_env)) for (t, ty) in model.types]
  psub = _param_sub(decl, concept_ref)
  refined = [find_model(body_env, ref.substitute(psub), model.models, loc)
             for ref in decl.refines.constraints]
  funs = []
  for (m, define, body) in model.funs:
    ty = member_type(body_env, concept_ref, m, loc, dict(types))
    funs.append((m, define, type_check_term(body, check_type(ty, body_env),
                                            body_env, None, [])))
  new_model = ModelDecl(loc, model.name, concept_ref, funs, model.theorems,
                        visibility=model.visibility, models=model.models,
                        type_params=model.type_params, where=where,
                        types=types)
  for (m, define, _) in funs:
    ty = member_type(body_env, concept_ref, m, loc, dict(types))
    env = env.declare_term_var(loc, define, new_model.definition_type(ty),
                               visibility=model.visibility)
  return new_model, env._with_binding(
      model.name, ModelBinding(loc, new_model, refined,
                               module=env.get_current_module(),
                               visibility=model.visibility))


def collect_model(model: ModelDecl, env: Env) -> Env:
  for (m, define, body) in model.funs:
    ty = member_type(env, model.concept, m, model.location, dict(model.types))
    env = env.define_term_var(model.location, define,
                              model.definition_type(ty),
                              model.definition(body), model.visibility)
  return env


def model_obligations(model: ModelDecl,
                      env: Env) -> list[tuple[Proof, Formula, Env]]:
  """Each theorem of the model with the axiom it must prove (the
  concept's, at the model's operations and those of the models it uses
  for the refined concepts) and the scope to prove it in."""
  loc = model.location
  binding = cast(ModelBinding, env.dict[model.name])
  env = _model_scope(model, env)
  models = [(inst, find_model(env, inst, model.models, loc))
            for inst in concept_closure([model.concept])[:-1]]
  sub = _head_match(binding, model.concept)
  assert sub is not None
  models.append((model.concept,
                 _instance(env, binding, sub, model.models, loc, 0)))
  lookup = _model_lookup(env, models, loc)
  return [(pf, axiom(env, model.concept, m, lookup, loc), env)
          for (m, pf) in model.theorems]
