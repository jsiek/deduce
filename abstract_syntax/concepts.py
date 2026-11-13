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

  def __str__(self) -> str:
    return 'where { ' + ', '.join(str(c) for c in self.constraints) + ' }'

  def __eq__(self, other: object) -> bool:
    return isinstance(other, WhereClause) \
      and len(self.constraints) == len(other.constraints) \
      and all(a == b for a, b in zip(self.constraints, other.constraints))

  def bind(self, env: UniquifyEnv, ctx: UniquifyContext) -> WhereClause:
    """Uniquify the constraints and bind a fresh name for every member
    of their refinement closure in ``env`` (which the caller has already
    copied for the scope of the where clause). Operations overload their
    base names, so ``x + y`` with ``x : T`` resolves to the binder by type;
    theorems shadow theirs."""
    constraints = [c.uniquify(env, ctx) for c in self.constraints]
    members = []
    for inst in concept_closure(constraints):
      decl = concept_decls[inst.concept]
      for (m, _) in decl.funs:
        binder = generate_name(m, ctx)
        extend(env, base_name(m), binder, self.location)
        members.append(WhereMember(inst, m, binder, False))
      for (m, _) in decl.theorems:
        binder = generate_name(m, ctx)
        overwrite(env, base_name(m), binder, self.location, warn=False)
        members.append(WhereMember(inst, m, binder, True))
    return WhereClause(self.location, constraints, members)

  def substitute(self, sub: Mapping[str, Term | Type | RecFun | GenRecFun]) -> WhereClause:
    return WhereClause(self.location,
                       [c.substitute(sub) for c in self.constraints],
                       [WhereMember(m.instance.substitute(sub), m.member,
                                    m.binder, m.is_theorem)
                        for m in self.members],
                       self.expanded)

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

  def __str__(self) -> str:
    lines = [self.visibility_prefix() + 'concept ' + name2str(self.name)
             + '<' + ', '.join(name2str(p) for p in self.type_params) + '> {']
    lines += ['  refines ' + str(r) for r in self.refines.constraints]
    lines += ['  fun ' + member_str(f) + ' : ' + str(t) for (f, t) in self.funs]
    lines += ['  theorem ' + name2str(n) + ': ' + str(frm)
              for (n, frm) in self.theorems]
    return '\n'.join(lines) + '\n}\n'

  def uniquify(self, env: object, ctx: object) -> ConceptDecl:
    env = cast(UniquifyEnv, env)
    ctx = cast(UniquifyContext, ctx)
    body_env, type_params = uniquify_type_params(
        env, self.type_params, ctx, self.location, overwrite)
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
                       theorems, visibility=self.visibility)
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

  def __str__(self) -> str:
    lines = [self.visibility_prefix() + 'model ' + str(self.concept) + ' {']
    lines += ['  fun ' + member_str(m) + ' = ' + str(body)
              for (m, _, body) in self.funs]
    lines += ['  theorem ' + name2str(m) + ' = ' + str(pf)
              for (m, pf) in self.theorems]
    return '\n'.join(lines) + '\n}\n'

  def opaque_signature(self) -> str | None:
    return 'opaque model ' + str(self.concept) + '\n'

  def print_theorems_statement(self, f: TextIO) -> None:
    # A model's interface is its operations; its proofs are not.
    if self.visibility == 'private':
      return
    if self.visibility == 'opaque':
      print(self.opaque_signature(), file=f)
      return
    print('model ' + str(self.concept) + ' {\n'
          + ''.join('  fun ' + member_str(m) + ' = ' + str(body) + '\n'
                    for (m, _, body) in self.funs)
          + '}\n', file=f)

  def uniquify(self, env: object, ctx: object) -> ModelDecl:
    env = cast(UniquifyEnv, env)
    ctx = cast(UniquifyContext, ctx)
    concept = self.concept.uniquify(env, ctx)
    decl = concept_decls[concept.concept]
    given_funs = {f: body for (f, _, body) in self.funs}
    given_thms = {n: pf for (n, pf) in self.theorems}
    members = {base_name(m) for (m, _) in decl.funs + decl.theorems}
    for name in list(given_funs) + list(given_thms):
      if name not in members:
        static_error(self.location, name + ' is not a member of concept '
                     + base_name(decl.name))
    funs = []
    for (m, _) in decl.funs:
      body = given_funs.get(base_name(m)) \
          or Var(self.location, None, base_name(m))
      funs.append((m, generate_name(base_name(m), ctx),
                   body.uniquify(env, ctx)))
    theorems = []
    for (m, _) in decl.theorems:
      pf = given_thms.get(base_name(m))
      if pf is None:
        static_error(self.location, 'model ' + str(self.concept)
                     + ' is missing theorem ' + base_name(m))
      theorems.append((m, pf.uniquify(env, ctx)))
    return ModelDecl(self.location, generate_name('model', ctx), concept,
                     funs, theorems, visibility=self.visibility)

  def collect_exports(self, export_env: UniquifyEnv, importing_module: str) -> None:
    # A model has no name to export; the checker finds it by its concept
    # and type arguments.
    pass


@dataclass
class ConceptBinding(Binding):
  # The type-checked concept.
  decl: ConceptDecl

  def __str__(self) -> str:
    return str(self.decl)


@dataclass
class ModelBinding(Binding):
  # The type-checked model, and the unique names of the models it uses
  # for the concepts its concept refines (fixed where the model is
  # declared, as in F^G's (MDL) rule).
  model: ModelDecl
  refined: List[str]

  def __str__(self) -> str:
    return 'model ' + str(self.model.concept)
