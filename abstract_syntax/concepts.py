"""Concepts, models, and where clauses (#1264).

Scope: the AST for ``concept`` and ``model`` declarations and for the
``where { C<T>, ... }`` clause of ``all`` formulas and ``arbitrary``
proofs, plus the uniquify-time registry of concepts that where clauses
and models consult to learn a concept's members.

The meaning follows System F^G (Siek & Lumsdaine, PLDI 2005) by
translation into formulas Deduce already checks:

    all T:type where { C<T> }. P
      ==  all T:type. all ops. if axioms(ops) then P

where ``ops`` are the operations of ``C`` and of every concept it
refines, each bound by a fresh *binder* name, and ``axioms`` are their
theorems. ``WhereClause.members`` records that refinement closure, one
``WhereMember`` per member. A model's operations become hidden
definitions, which the checker passes for the binders when a where
formula is instantiated.

Goes here:
  * AST nodes for concepts, models, and where clauses
  * the concept registry and the refinement-closure helper

Does NOT go here:
  * checking concepts and models, or instantiating where formulas; those
    live in the checker (``checker_concepts.py``)
"""

from __future__ import annotations

import textwrap
from dataclasses import dataclass, field

from .core import *
from .terms import *
from .proofs import *
from .declarations import *
from .env import *

# Every concept declaration seen by uniquify, by unique name. Where
# clauses and models look up a concept's members here; a concept's
# unique name never changes once generated, so stale entries are
# harmless.
concept_decls: dict[str, "ConceptDecl"] = {}


@dataclass
class ConceptRef(AST):
  """A concept applied to types, ``C<T1, ..., Tn>``, as written in a
  where clause, a ``refines`` member, or a model head."""
  concept: str
  type_args: List[Type]

  def __str__(self) -> str:
    return name2str(self.concept) + '<' \
      + ', '.join(str(t) for t in self.type_args) + '>'

  def __eq__(self, other: object) -> bool:
    return isinstance(other, ConceptRef) \
      and self.concept == other.concept \
      and len(self.type_args) == len(other.type_args) \
      and all(a == b for a, b in zip(self.type_args, other.type_args))

  def uniquify(self, env: UniquifyEnv, ctx: UniquifyContext) -> ConceptRef:
    names = env.get(self.concept)
    if not names or names[0] not in concept_decls:
      static_error(self.location, 'undefined concept: ' + self.concept)
    decl = concept_decls[names[0]]
    if len(decl.type_params) != len(self.type_args):
      static_error(self.location, 'concept ' + self.concept + ' expects '
                   + str(len(decl.type_params)) + ' type argument(s), not '
                   + str(len(self.type_args)))
    return ConceptRef(self.location, names[0],
                      [t.uniquify(env, ctx) for t in self.type_args])

  def substitute(self, sub: Mapping[str, Term | Type | RecFun | GenRecFun]) -> ConceptRef:
    return ConceptRef(self.location, self.concept,
                      [t.substitute(sub) for t in self.type_args])


@dataclass
class AssocType(Type):
  """`@C<τ>.Elem`: the associated type ``Elem`` of the instance ``C<τ>``
  (#1321)."""
  ref: ConceptRef
  name: str

  def __str__(self) -> str:
    return '@' + str(self.ref) + '.' + name2str(self.name)

  def __eq__(self, other: object) -> bool:
    return isinstance(other, AssocType) and self.ref == other.ref \
      and self.name == other.name

  def free_vars(self) -> Set[str]:
    return set().union(*[t.free_vars() for t in self.ref.type_args])

  def uniquify(self, env: UniquifyEnv, ctx: UniquifyContext) -> AssocType:
    ref = self.ref.uniquify(env, ctx)
    names = [t for t in concept_decls[ref.concept].types
             if base_name(t) == self.name]
    if not names:
      static_error(self.location, base_name(ref.concept)
                   + ' has no associated type ' + self.name)
    return AssocType(self.location, ref, names[0])


@dataclass
class WhereMember:
  """One member of one concept instance in a where clause's refinement
  closure: the concept member ``member`` of ``instance`` is bound by
  ``binder``. Theorem members are bound as proof labels (only used in
  ``arbitrary``); operations as term variables."""
  instance: ConceptRef
  member: str
  binder: str
  is_theorem: bool


@dataclass
class WhereClause(AST):
  constraints: List[ConceptRef]
  # The refinement closure, filled in by ``bind``.
  members: List[WhereMember] = field(default_factory=list)
  # Set by the checker once the body of the ``all`` has been expanded to
  # ``all ops. if axioms then P``.
  expanded: bool = False
  # The same-type constraints `σ = τ` (#1321).
  equations: List[Tuple[Type, Type]] = field(default_factory=list, kw_only=True)

  def __str__(self) -> str:
    return 'where { ' + ', '.join([str(c) for c in self.constraints]
                                  + [str(s) + ' = ' + str(t)
                                     for (s, t) in self.equations]) + ' }'

  def __eq__(self, other: object) -> bool:
    return isinstance(other, WhereClause) \
      and len(self.constraints) == len(other.constraints) \
      and all(a == b for a, b in zip(self.constraints, other.constraints)) \
      and self.equations == other.equations

  def bind(self, env: UniquifyEnv, ctx: UniquifyContext) -> WhereClause:
    """Uniquify the constraints and bind a fresh name for every member
    of their refinement closure in ``env`` (which the caller has already
    copied for the scope of the where clause). Operations overload their
    base names, so ``x + y`` with ``x : T`` resolves to the binder by type;
    theorems shadow theirs."""
    constraints = [c.uniquify(env, ctx) for c in self.constraints]
    members = []
    labels: dict[str, list[str]] = {}
    for inst in concept_closure(constraints):
      decl = concept_decls[inst.concept]
      for (m, _) in decl.funs:
        binder = generate_name(m, ctx)
        extend(env, base_name(m), binder, self.location)
        members.append(WhereMember(inst, m, binder, False))
      for (m, _) in decl.theorems:
        binder = generate_name(m, ctx)
        labels.setdefault(base_name(m), []).append(binder)
        members.append(WhereMember(inst, m, binder, True))
    # A theorem name adds to the overloads of the name: other instances'
    # theorems (say, `where { Monoid<T>, Monoid<U> }`) and any outer
    # theorem with that name. The where clause's come first.
    overloaded = set()
    for (name, binders) in labels.items():
      env[name] = binders + [n for n in env.get(name, []) if n not in binders]
      if len(env[name]) > 1:
        overloaded.add(name)
    # Innermost first, so an inner clause binding the same instance as an
    # outer one takes precedence; the clause is identified by its first
    # binder.
    clause = members[0].binder if members else ''
    env[WHERE_MEMBERS_KEY] = \
        [(wm.instance, base_name(wm.member), wm.binder, wm.is_theorem, clause)
         for wm in members] + env.get(WHERE_MEMBERS_KEY, [])
    if overloaded:
      env[OVERLOADED_PROOFS_KEY] = env.get(OVERLOADED_PROOFS_KEY, set()) | overloaded
    equations = [(s.uniquify(env, ctx), t.uniquify(env, ctx))
                 for (s, t) in self.equations]
    return WhereClause(self.location, constraints, members,
                       equations=equations)

  def substitute(self, sub: Mapping[str, Term | Type | RecFun | GenRecFun]) -> WhereClause:
    return WhereClause(self.location,
                       [c.substitute(sub) for c in self.constraints],
                       [WhereMember(m.instance.substitute(sub), m.member,
                                    m.binder, m.is_theorem)
                        for m in self.members],
                       self.expanded,
                       equations=[(s.substitute(sub), t.substitute(sub))
                                  for (s, t) in self.equations])

  def operations(self) -> List[WhereMember]:
    return [m for m in self.members if not m.is_theorem]

  def theorems(self) -> List[WhereMember]:
    return [m for m in self.members if m.is_theorem]


def where_body(frm: All) -> Formula:
  """The body of ``frm`` as the user wrote it: for an expanded where
  clause, without the ``all ops. if axioms then`` that the checker
  added."""
  body = frm.body
  if frm.where is None or not frm.where.expanded:
    return body
  for _ in frm.where.operations():
    if not isinstance(body, All):
      return body
    body = body.body
  if frm.where.theorems() and isinstance(body, IfThen):
    return body.conclusion
  return body


def _where_binders(ref: ConceptRef, member: str, is_theorem: bool,
                   env: UniquifyEnv) -> List[str]:
  """The binders of ``member`` of the instance ``ref`` in the innermost
  where clause in scope that binds that instance."""
  found = [(binder, clause)
           for (inst, m, binder, thm, clause) in env.get(WHERE_MEMBERS_KEY, [])
           if inst == ref and m == member and thm == is_theorem]
  return [binder for (binder, clause) in found if clause == found[0][1]]


def _check_member(ref: ConceptRef, member: str, is_theorem: bool,
                  loc: Meta) -> None:
  decl = concept_decls[ref.concept]
  names = [m for (m, _) in (decl.theorems if is_theorem else decl.funs)]
  if member not in map(base_name, names):
    static_error(loc, base_name(ref.concept) + ' has no '
                 + ('theorem ' if is_theorem else 'operation ') + member)


@dataclass
class ConceptMember(Term):
  """`@C<τ>.m`: the operation ``m`` of the instance ``C<τ>``. Uniquify
  turns it into the where clause's binder when a where clause in scope
  binds the instance; otherwise the checker takes it from the model in
  scope (recorded in ``models``)."""
  ref: ConceptRef
  member: str
  models: List[str] = field(default_factory=list, kw_only=True)

  def __str__(self) -> str:
    return '@' + str(self.ref) + '.' + member_str(self.member)

  def uniquify(self, env: UniquifyEnv, ctx: UniquifyContext) -> Term:  # type: ignore[override]
    ref = self.ref.uniquify(env, ctx)
    _check_member(ref, self.member, False, self.location)
    binders = _where_binders(ref, self.member, False, env)
    if binders:
      return OverloadedVar(self.location, None, binders)
    return ConceptMember(self.location, None, ref, self.member,
                         models=env.get(MODELS_KEY, []))


@dataclass
class ConceptMemberProof(Proof):
  """`@C<τ>.thm`: the theorem ``thm`` of the instance ``C<τ>``: the
  where clause's assumption, or the model's theorem."""
  ref: ConceptRef
  member: str
  models: List[str] = field(default_factory=list, kw_only=True)

  def __str__(self) -> str:
    return '@' + str(self.ref) + '.' + self.member

  def pretty_print(self, indent: int, afterNewline: bool = False) -> str:
    return str(self)

  def uniquify(self, env: UniquifyEnv, ctx: UniquifyContext) -> Proof:  # type: ignore[override]
    ref = self.ref.uniquify(env, ctx)
    _check_member(ref, self.member, True, self.location)
    binders = _where_binders(ref, self.member, True, env)
    if binders:
      return PVar(self.location, binders[0])
    return ConceptMemberProof(self.location, ref, self.member,
                              models=env.get(MODELS_KEY, []))


def where_params(where: WhereClause) -> List[Tuple[str, Type]]:
  """The extra parameters of a function with the where clause ``where``
  (#1282): the binders of its operations, with their types. They are the
  dictionary of F^G's translation of ``Λt̄ where c̄. e``; a type
  application passes the models' operations for them."""
  params = []
  for wm in where.operations():
    decl = concept_decls[wm.instance.concept]
    sub = {p: t for (p, t) in zip(decl.type_params, wm.instance.type_args)}
    params.append((wm.binder, dict(decl.funs)[wm.member].substitute(sub)))
  return params


def member_str(name: str) -> str:
  return ('operator ' if is_operator_name(name) else '') + name2str(name)


def concept_closure(refs: List[ConceptRef]) -> List[ConceptRef]:
  """The concept instances that ``refs`` require, refined concepts first,
  each instance once (F^G de-duplicates only associated types; Deduce
  also de-duplicates members, since duplicates would show up in
  formulas)."""
  result: List[ConceptRef] = []
  def visit(ref: ConceptRef) -> None:
    if ref in result:
      return
    decl = concept_decls[ref.concept]
    sub = {p: t for (p, t) in zip(decl.type_params, ref.type_args)}
    for r in decl.refines.constraints:
      visit(r.substitute(sub))
    result.append(ref)
  for ref in refs:
    visit(ref)
  return result


@dataclass
class ConceptDecl(Declaration):
  type_params: List[str]
  # The refined concepts, as a where clause whose binders name the refined
  # members in this concept's theorems.
  refines: WhereClause
  funs: List[Tuple[str, Type]]
  theorems: List[Tuple[str, Formula]]
  # The associated types (#1321), bound in the members like type
  # parameters.
  types: List[str] = field(default_factory=list, kw_only=True)
  # The constraints of `refines` written as `require` (G's nested
  # requirements, usually on associated types). They mean the same as
  # `refines`; this list only keeps the keyword for printing.
  requires: List[ConceptRef] = field(default_factory=list, kw_only=True)

  def __str__(self) -> str:
    lines = [self.visibility_prefix() + 'concept ' + name2str(self.name)
             + '<' + ', '.join(name2str(p) for p in self.type_params) + '> {']
    lines += ['  type ' + name2str(t) for t in self.types]
    lines += [('  require ' if r in self.requires else '  refines ') + str(r)
              for r in self.refines.constraints]
    lines += ['  fun ' + member_str(f) + ' : ' + str(t) for (f, t) in self.funs]
    lines += ['  theorem ' + name2str(n) + ': ' + str(frm)
              for (n, frm) in self.theorems]
    return '\n'.join(lines) + '\n}\n'

  def uniquify(self, env: object, ctx: object) -> ConceptDecl:
    env = cast(UniquifyEnv, env)
    ctx = cast(UniquifyContext, ctx)
    body_env, type_params = uniquify_type_params(
        env, self.type_params, ctx, self.location, overwrite)
    body_env, types = uniquify_type_params(
        body_env, self.types, ctx, self.location, overwrite)
    requires = [r.uniquify(body_env, ctx) for r in self.requires]
    refines = self.refines.bind(body_env, ctx)
    funs = []
    for (f, t) in self.funs:
      new_f = generate_name(f, ctx)
      extend(body_env, f, new_f, self.location)
      funs.append((new_f, t.uniquify(body_env, ctx)))
    theorems = [(generate_name(n, ctx), frm.uniquify(body_env, ctx))
                for (n, frm) in self.theorems]
    new_name = generate_name(self.name, ctx)
    overwrite(env, self.name, new_name, self.location)
    env['no overload'][self.name] = 'concept'
    decl = ConceptDecl(self.location, new_name, type_params, refines, funs,
                       theorems, visibility=self.visibility, types=types,
                       requires=requires)
    concept_decls[new_name] = decl
    return decl


@dataclass
class ModelDecl(Declaration):
  concept: ConceptRef
  # (concept member, hidden definition name, body). Before uniquify the
  # member is its base name and the definition name is empty; uniquify
  # fills in a body for every operation the model leaves out, by name
  # from the enclosing scope (as in G).
  funs: List[Tuple[str, str, Term]]
  theorems: List[Tuple[str, Proof]]
  # The models in scope where this model is declared, recorded by
  # uniquify: the models of the refined concepts come from here (F^G's
  # MDL rule).
  models: List[str] = field(default_factory=list, kw_only=True)
  # A parameterized model (#1321), `model <T> where { C<T> } D<F<T>>`,
  # models a family of instances. Its operations' bodies are in the scope
  # of its type parameters and of its where clause's binders.
  type_params: List[str] = field(default_factory=list, kw_only=True)
  where: Optional[WhereClause] = field(default=None, kw_only=True)
  # (associated type of the concept, its definition), `type Elem = σ`
  # (#1321).
  types: List[Tuple[str, Type]] = field(default_factory=list, kw_only=True)

  def type_members(self) -> List[str]:
    return ['  type ' + name2str(t) + ' = ' + str(ty) for (t, ty) in self.types]

  def head(self) -> str:
    params = ('<' + ', '.join(name2str(p) for p in self.type_params) + '> '
              if self.type_params else '')
    where = str(self.where) + ' ' if self.where else ''
    return 'model ' + params + where + str(self.concept)

  def definition(self, body: Term) -> Term:
    """The hidden definition of an operation whose body is ``body``. For
    a parameterized model it is generic over the type parameters and
    takes the operations of the where clause (F^G's function from
    dictionaries to a dictionary)."""
    if not self.type_params:
      return body
    loc = self.location
    ty = cast(Type, body.typeof)
    params = where_params(self.where) if self.where else []
    fun = Lambda(loc, FunctionType(loc, [], [t for (_, t) in params], ty),
                 cast(Any, params), body)
    return Generic(loc, self.definition_type(ty), self.type_params, fun)

  def definition_type(self, ty: Type) -> Type:
    """The type of the hidden definition of an operation of type ``ty``."""
    if not self.type_params:
      return ty
    params = where_params(self.where) if self.where else []
    return FunctionType(self.location, self.type_params,
                        [t for (_, t) in params], ty)

  def __str__(self) -> str:
    lines = [self.visibility_prefix() + self.head() + ' {']
    lines += self.type_members()
    lines += ['  fun ' + member_str(m) + ' = ' + str(body)
              for (m, _, body) in self.funs]
    lines += ['  theorem ' + name2str(m) + ' = ' + str(pf)
              for (m, pf) in self.theorems]
    return '\n'.join(lines) + '\n}\n'

  def opaque_signature(self) -> str | None:
    # An opaque model still exports its associated types (#1321).
    if not self.types:
      return 'opaque ' + self.head() + '\n'
    return 'opaque ' + self.head() + ' {\n' \
      + ''.join(line + '\n' for line in self.type_members()) + '}\n'

  def print_theorems_statement(self, f: TextIO) -> None:
    # A model's interface is its types and operations; its proofs are not.
    if self.visibility == 'private':
      return
    if self.visibility == 'opaque':
      print(self.opaque_signature(), file=f)
      return
    print(self.head() + ' {\n'
          + ''.join(line + '\n' for line in self.type_members())
          + ''.join('  fun ' + member_str(m) + ' = ' + str(body) + '\n'
                    for (m, _, body) in self.funs)
          + '}\n', file=f)

  def uniquify(self, env: object, ctx: object) -> ModelDecl:
    env = cast(UniquifyEnv, env)
    ctx = cast(UniquifyContext, ctx)
    # A parameterized model's members are in the scope of its type
    # parameters and its where clause (#1321).
    body_env, type_params = uniquify_type_params(
        env, self.type_params, ctx, self.location, overwrite)
    where = self.where.bind(body_env, ctx) if self.where else None
    concept = self.concept.uniquify(body_env, ctx)
    decl = concept_decls[concept.concept]
    given_funs = {f: body for (f, _, body) in self.funs}
    given_thms = {n: pf for (n, pf) in self.theorems}
    given_types = {t: ty for (t, ty) in self.types}
    members = {base_name(m) for (m, _) in decl.funs + decl.theorems}
    for name in list(given_funs) + list(given_thms):
      if name not in members:
        static_error(self.location, name + ' is not a member of concept '
                     + base_name(decl.name))
    for name in given_types:
      if name not in map(base_name, decl.types):
        static_error(self.location, name + ' is not an associated type of '
                     + 'concept ' + base_name(decl.name))
    types = []
    for t in decl.types:
      ty = given_types.get(base_name(t))
      if ty is None:
        static_error(self.location, 'model ' + str(self.concept)
                     + ' is missing type ' + base_name(t))
      types.append((t, ty.uniquify(body_env, ctx)))
    funs = []
    for (m, _) in decl.funs:
      body = given_funs.get(base_name(m)) \
          or Var(self.location, None, base_name(m))
      funs.append((m, generate_name(base_name(m), ctx),
                   body.uniquify(body_env, ctx)))
    theorems = []
    for (m, _) in decl.theorems:
      pf = given_thms.get(base_name(m))
      if pf is None:
        static_error(self.location, 'model ' + str(self.concept)
                     + ' is missing theorem ' + base_name(m))
      theorems.append((m, pf.uniquify(body_env, ctx)))
    models = list(env.get(MODELS_KEY, []))
    new_name = generate_name('model', ctx)
    # A new list, not an append: environments are copied shallowly.
    env[MODELS_KEY] = models + [new_name]
    return ModelDecl(self.location, new_name, concept, funs, theorems,
                     visibility=self.visibility, models=models,
                     type_params=type_params, where=where, types=types)

  def collect_exports(self, export_env: UniquifyEnv, importing_module: str) -> None:
    # A model has no name; it is exported into the scope of models,
    # where the checker finds it by its concept and type arguments.
    in_scope = export_env.get(MODELS_KEY, [])
    if not self._skip_export(importing_module) and self.name not in in_scope:
      export_env[MODELS_KEY] = in_scope + [self.name]


@dataclass
class PModel(Proof):
  """A `model` statement inside a proof (#1321): the model is in scope
  for the rest of the proof, where it wins over outer models of the same
  concept instance."""
  model: ModelDecl
  body: Proof

  def pretty_print(self, indent: int) -> str:
    return textwrap.indent(str(self.model), indent*' ') \
        + self.body.pretty_print(indent)

  def __str__(self) -> str:
    return str(self.model) + str(self.body)

  def uniquify(self, env: UniquifyEnv, ctx: UniquifyContext) -> PModel:
    body_env = dict(env)
    model = self.model.uniquify(body_env, ctx)
    return PModel(self.location, model, self.body.uniquify(body_env, ctx))


@dataclass
class ConceptBinding(Binding):
  # The type-checked concept.
  decl: ConceptDecl

  def __str__(self) -> str:
    return str(self.decl)


@dataclass
class ModelBinding(Binding):
  # The type-checked model, and the models it uses for the concepts its
  # concept refines (fixed where the model is declared, as in F^G's
  # (MDL) rule).
  model: ModelDecl
  refined: List["ModelInstance"]

  def __str__(self) -> str:
    return self.model.head()


@dataclass
class ModelInstance:
  """A model used at a concept instance: the model and, for a
  parameterized model (#1321), its type arguments and the models of its
  where clause's instances, found where it is used."""
  binding: ModelBinding
  type_args: List[Type] = field(default_factory=list)
  args: List[Tuple[ConceptRef, "ModelInstance"]] = field(default_factory=list)

  def key(self) -> str:
    """The instance's identity: two refinement paths to a concept
    instance must reach the same one."""
    key = self.binding.model.name
    if self.type_args:
      key += '<' + ', '.join(str(t) for t in self.type_args) + '>'
    if self.args:
      key += '{' + ', '.join(m.key() for (_, m) in self.args) + '}'
    return key
