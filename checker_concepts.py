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
leaves them folded.
"""

from __future__ import annotations

import itertools
from typing import Callable, cast

from abstract_syntax import (
    All, AllElimTypes, And, BoolType, ConceptBinding, ConceptDecl,
    ConceptMember, ConceptMemberProof, ConceptRef, Env,
    Formula, IfThen, ModelBinding, ModelDecl, Proof, ResolvedVar, Term, Type,
    FunctionType, TypeInst, TypeType, VarRef, WhereClause, WhereMember, base_name, concept_closure,
)
from checker_types import check_formula, check_type, type_check_term
from error import user_error
from lark.tree import Meta

# The term that stands for a member of a concept instance: a where
# clause's binder, or a model's operation.
MemberLookup = Callable[[ConceptRef, str], Term]
# The model chosen for each concept instance.
Models = list[tuple[ConceptRef, ModelBinding]]

# The environment key of the models that the where clauses in scope
# provide, innermost first.
WHERE_MODELS_KEY = ' where models'


def _model_for(models: Models, inst: ConceptRef) -> ModelBinding:
  return next(m for (i, m) in models if i == inst)


def concept_of(env: Env, name: str, loc: Meta) -> ConceptDecl:
  binding = env.dict.get(name)
  if not isinstance(binding, ConceptBinding):
    user_error(loc, 'expected a concept, not ' + base_name(name))
  return binding.decl


def _param_sub(decl: ConceptDecl, inst: ConceptRef) -> dict[str, Type]:
  return dict(zip(decl.type_params, inst.type_args))


def member_type(env: Env, inst: ConceptRef, member: str, loc: Meta) -> Type:
  decl = concept_of(env, inst.concept, loc)
  return dict(decl.funs)[member].substitute(_param_sub(decl, inst))


def _instance_sub(env: Env, inst: ConceptRef, lookup: MemberLookup,
                  loc: Meta) -> dict[str, Term | Type]:
  """Takes the vocabulary of ``inst``'s concept (its type parameters, its
  operations, and the binders of the members it refines) to ``inst``'s
  type arguments and to ``lookup``'s terms."""
  decl = concept_of(env, inst.concept, loc)
  psub = _param_sub(decl, inst)
  sub: dict[str, Term | Type] = dict(psub)
  for (m, _) in decl.funs:
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
  def lookup(inst: ConceptRef, member: str) -> Term:
    for wm in where.operations():
      if wm.instance == inst and wm.member == member:
        return ResolvedVar(loc, member_type(env, inst, member, loc), wm.binder)
    user_error(loc, 'no binder for ' + base_name(member) + ' of ' + str(inst))
  return lookup


def check_where(where: WhereClause, env: Env) -> WhereClause:
  """Type check the concept applications of a where clause (including
  its refinement closure) in ``env``."""
  def check_ref(ref: ConceptRef) -> ConceptRef:
    concept_of(env, ref.concept, ref.location)
    return ConceptRef(ref.location, ref.concept,
                      [check_type(t, env) for t in ref.type_args])
  return WhereClause(where.location,
                     [check_ref(c) for c in where.constraints],
                     [WhereMember(check_ref(wm.instance), wm.member,
                                  wm.binder, wm.is_theorem)
                      for wm in where.members],
                     where.expanded)


def declare_where_operations(where: WhereClause, env: Env, loc: Meta) -> Env:
  return env.declare_term_vars(
      loc, [(wm.binder, member_type(env, wm.instance, wm.member, loc))
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
  where = check_where(frm.where, body_env)
  body_env = declare_where_operations(where, body_env, loc)
  body = check_body(frm.body, body_env)
  lookup = _binder_lookup(body_env, where, loc)
  premise = _premise(body_env, where, lookup, loc)
  if premise is not None:
    body = IfThen(loc, BoolType(loc), premise, body)
  for wm in reversed(where.operations()):
    body = All(loc, BoolType(loc),
               (wm.binder, member_type(body_env, wm.instance, wm.member, loc)),
               (0, 1), body)
  where.expanded = True
  return All(loc, BoolType(loc), (x, new_ty), frm.pos, body, where=where)


def _strip_operations(loc: Meta, frm: Formula, where: WhereClause,
                      lookup: MemberLookup) -> Formula:
  """Instantiate the ``all ops`` of an expanded where formula's body with
  ``lookup``'s terms."""
  sub = {}
  for wm in where.operations():
    if not isinstance(frm, All) or frm.var[0] != wm.binder:
      user_error(loc, 'expected the operations of the where clause, not\n\t'
                 + str(frm))
    sub[wm.binder] = lookup(wm.instance, wm.member)
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
  where = check_where(where, body_env)
  if goal_where.constraints != where.constraints:
    user_error(loc, 'arbitrary expects the where clause\n\t' + str(goal_where)
               + '\nbut got\n\t' + str(where))
  body_env = declare_where_operations(where, body_env, loc)
  lookup = _binder_lookup(body_env, where, loc)
  frm = goal.body.substitute({goal.var[0]: ResolvedVar(loc, None, x)})
  frm = _strip_operations(loc, frm, goal_where, lookup)
  frm = _discharge(loc, frm, _premise(body_env, where, lookup, loc))
  for wm in where.theorems():
    body_env = body_env.declare_local_proof_var(
        loc, wm.binder, axiom(body_env, wm.instance, wm.member, lookup, loc))
  return frm, _where_models(loc, where, body_env)


def _where_models(loc: Meta, where: WhereClause, env: Env) -> Env:
  """Add a model for each concept instance of ``where`` (its refinement
  closure), whose operations are the where clause's binders: in its
  scope, a where clause models its concepts (F^G's where clauses add
  models to the context), so a where theorem can be instantiated at the
  clause's types."""
  insts: list[ConceptRef] = []
  for wm in where.members:
    if wm.instance not in insts:
      insts.append(wm.instance)
  if not insts:
    return env
  clause = where.members[0].binder
  names = {str(inst): '<where ' + clause + '> ' + str(inst) for inst in insts}
  for inst in insts:
    decl = concept_of(env, inst.concept, loc)
    psub = _param_sub(decl, inst)
    funs = [(wm.member, wm.binder,
             ResolvedVar(loc, member_type(env, inst, wm.member, loc), wm.binder))
            for wm in where.operations() if wm.instance == inst]
    model = ModelDecl(loc, names[str(inst)], inst, cast(list[tuple[str, str, Term]], funs), [])
    refined = [names[str(r.substitute(psub))] for r in decl.refines.constraints]
    env = env._with_binding(model.name, ModelBinding(
        loc, model, refined, module=env.get_current_module()))
  return env._with_binding(
      WHERE_MODELS_KEY,
      list(names.values()) + cast(list[str], env.dict.get(WHERE_MODELS_KEY, [])))


def find_model(env: Env, inst: ConceptRef, models: list[str],
               loc: Meta) -> ModelBinding:
  """The model of ``inst`` that the innermost where clause in scope
  provides, or else the one among ``models``, the models in lexical
  scope (recorded by uniquify)."""
  for name in cast(list[str], env.dict.get(WHERE_MODELS_KEY, [])):
    b = env.dict[name]
    if isinstance(b, ModelBinding) and b.model.concept == inst:
      return b
  found = [b for name in models
           if isinstance(b := env.dict.get(name), ModelBinding)
           and b.model.concept == inst]
  if not found:
    user_error(loc, 'no model of ' + str(inst) + ' in scope')
  if len(found) > 1:
    user_error(loc, 'more than one model of ' + str(inst) + ' in scope')
  return found[0]


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
  for name in cast(list[str], env.dict.get(WHERE_MODELS_KEY, [])) + models:
    b = env.dict.get(name)
    if not isinstance(b, ModelBinding):
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


def _model_lookup(env: Env, models: Models,
                  use_bodies: bool, loc: Meta) -> MemberLookup:
  """The model's operations: its hidden definitions, or (inside the
  model's own module, to check its theorems) their bodies."""
  def lookup(inst: ConceptRef, member: str) -> Term:
    model = _model_for(models, inst).model
    for (m, define, body) in model.funs:
      if m == member:
        if use_bodies:
          return body
        return ResolvedVar(loc, member_type(env, inst, member, loc), define)
    user_error(loc, 'model ' + str(inst) + ' has no ' + base_name(member))
  return lookup


def instantiate_where(loc: Meta, allfrm: All, type_arg: Type,
                      env: Env, in_scope: list[str]) -> Formula:
  """``thm<τ>`` for a where formula: pass the models of the clause's
  concepts at ``τ`` (F^G's TApp)."""
  assert allfrm.where is not None
  sub = {allfrm.var[0]: type_arg}
  where = allfrm.where.substitute(sub)
  models = _models_in_scope(loc, where.constraints, in_scope, env)
  lookup = _model_lookup(env, models, False, loc)
  frm = _strip_operations(loc, allfrm.body.substitute(sub), where, lookup)
  frm = _discharge(loc, frm, _premise(env, where, lookup, loc))
  return _unfold(frm, [m for (_, m) in models], env)


def _models_in_scope(loc: Meta, refs: list[ConceptRef], in_scope: list[str],
                     env: Env) -> Models:
  """The models in scope of the concept instances ``refs`` require
  (their refinement closure), checked for coherence: every refinement
  path to an instance reaches one model."""
  models = [(inst, find_model(env, inst, in_scope, loc))
            for inst in concept_closure(refs)]
  for (_, model) in models:
    concept = concept_of(env, model.model.concept.concept, loc)
    psub = _param_sub(concept, model.model.concept)
    for ref, name in zip(concept.refines.constraints, model.refined):
      inst = ref.substitute(psub)
      if _model_for(models, inst).model.name != name:
        user_error(loc, 'the model of ' + str(model.model.concept)
                   + ' uses a different model of ' + str(inst)
                   + ' than the one in scope here')
  return models


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
  found = [(m, define) for (m, define, _) in model.model.funs
           if base_name(m) == term.member]
  if len(found) > 1:
    user_error(loc, '@' + str(ref) + '.' + term.member + ' could be any of '
               + str(len(found)) + ' operations of the model; use the'
               + ' operation unqualified, where its type tells which')
  (m, define) = found[0]
  var = ResolvedVar(loc, member_type(env, ref, m, loc), define)
  return _unfold(var, [model], env)


def concept_member_formula(proof: ConceptMemberProof, env: Env) -> Formula:
  """`@C<τ>.thm` outside a where clause binding ``C<τ>``: the concept's
  theorem at the operations of the model in scope (which proved it)."""
  loc = proof.location
  ref, models = _qualified(loc, proof.ref, proof.models, env)
  decl = concept_of(env, ref.concept, loc)
  theorem = next(m for (m, _) in decl.theorems if base_name(m) == proof.member)
  frm = axiom(env, ref, theorem, _model_lookup(env, models, False, loc), loc)
  return _unfold(frm, [m for (_, m) in models], env)


def _unfold(frm: Formula, models: list[ModelBinding], env: Env) -> Formula:
  """Replace the operations of ``models`` that this module can see by
  their definitions; an opaque model's stay folded (F^G's dictionary
  projection, reduced). Only these names change: the formula is not
  otherwise reduced, so auto rules don't collapse it."""
  current = env.get_current_module()
  sub: dict[str, Term] = {}
  for m in models:
    if m.visibility == 'opaque' and m.module != current:
      continue
    for (_, define, body) in m.model.funs:
      sub[define] = body
  return frm.substitute(sub)


################ Declarations ################

def process_concept(decl: ConceptDecl, env: Env) -> tuple[ConceptDecl, Env]:
  loc = decl.location
  body_env = env.declare_type_vars(loc, decl.type_params)
  refines = check_where(decl.refines, body_env)
  body_env = declare_where_operations(refines, body_env, loc)
  funs = [(f, check_type(t, body_env)) for (f, t) in decl.funs]
  body_env = body_env.declare_term_vars(loc, funs)
  theorems = [(n, check_formula(frm, body_env)) for (n, frm) in decl.theorems]
  new_decl = ConceptDecl(loc, decl.name, decl.type_params, refines, funs,
                         theorems, visibility=decl.visibility)
  return new_decl, env._with_binding(
      decl.name, ConceptBinding(loc, new_decl, module=env.get_current_module(),
                                visibility=decl.visibility))


def process_model(model: ModelDecl, env: Env) -> tuple[ModelDecl, Env]:
  loc = model.location
  concept_ref = check_where(WhereClause(loc, [model.concept]), env).constraints[0]
  decl = concept_of(env, concept_ref.concept, loc)
  psub = _param_sub(decl, concept_ref)
  refined = [find_model(env, ref.substitute(psub), model.models, loc).model.name
             for ref in decl.refines.constraints]
  funs = []
  for (m, define, body) in model.funs:
    ty = check_type(dict(decl.funs)[m].substitute(psub), env)
    funs.append((m, define, type_check_term(body, ty, env, None, [])))
    env = env.declare_term_var(loc, define, ty, visibility=model.visibility)
  new_model = ModelDecl(loc, model.name, concept_ref, funs, model.theorems,
                        visibility=model.visibility, models=model.models)
  return new_model, env._with_binding(
      model.name, ModelBinding(loc, new_model, refined,
                               module=env.get_current_module(),
                               visibility=model.visibility))


def collect_model(model: ModelDecl, env: Env) -> Env:
  for (m, define, body) in model.funs:
    env = env.define_term_var(model.location, define,
                              member_type(env, model.concept, m, model.location),
                              body, model.visibility)
  return env


def model_obligations(model: ModelDecl, env: Env) -> list[tuple[Proof, Formula]]:
  """Each theorem of the model with the axiom it must prove: the
  concept's, at the model's operations (and those of the models it uses
  for the refined concepts)."""
  loc = model.location
  binding = cast(ModelBinding, env.dict[model.name])
  models = [(inst, find_model(env, inst, model.models, loc))
            for inst in concept_closure([model.concept])[:-1]]
  models.append((model.concept, binding))
  lookup = _model_lookup(env, models, True, loc)
  return [(pf, axiom(env, model.concept, m, lookup, loc))
          for (m, pf) in model.theorems]
