"""Concrete top-level ``Statement`` nodes — the declarations of a module.

Scope: every dataclass node that can appear at the top level of a ``.pf``
file, together with the bookkeeping that supports them across imports.
This covers the ``Declaration`` family (``Theorem``, ``Postulate``,
``Predicate``, ``Union``, ``TypeAlias``, ``ObjectDecl``, ``ObserverDecl``,
``ResourceDecl``,
``RecFun``, ``GenRecFun``, ``ViewRecFun``, ``ViewDecl``, ``Define``,
``Import``) and the non-``Declaration``
statements (``Auto``, ``Inductive``, ``Module``, ``Export``,
``Associative``, ``Trace``, ``Assert``, ``Print``). Their AST helpers
(``Constructor``, ``Rule``, ``FunCase``) also live here because they only
make sense as parts of these declarations.

Module-level state for cross-module bookkeeping lives here too:
``uniquified_modules`` (the registry of already-checked modules consulted
by ``Import``), ``find_private_lemma_definers``, ``find_file`` (the
import-path resolver), ``get_predicate_decl``, and helpers like
``extend``/``overwrite`` for inserting into name environments.

Goes here:
  * a new top-level statement form
  * helpers/registries scoped to one declaration kind, or to whole-module
    import bookkeeping

Does NOT go here:
  * the immutable proof-checker ``Env`` and ``Binding`` types (``env``)
  * proof-checking logic — that lives in ``proof_checker`` / ``checker_*``
"""

from __future__ import annotations

from typing import TYPE_CHECKING, ClassVar

from .core import *
from .terms import *
from .proofs import *

if TYPE_CHECKING:
    from .env import Env
    from .ops import uniquify_deduce

@dataclass
class Declaration(Statement):
  name: str
  visibility: str = field(default='public', kw_only=True)

  def key(self) -> str:
      if is_operator_name(self.name):
          return 'operator ' + name2str(self.name)
      else:
          return name2str(self.name)

  def print_theorems_statement(self, f: TextIO) -> None:
      if not self.visibility == 'private':
        print(self.pretty_print(0), file=f)

  def visibility_prefix(self) -> str:
      # Source-level visibility keywords that prefix a declaration head.
      # `default` is the historical "no keyword written" sentinel and
      # `public` is its concrete spelling once normalised — neither emits
      # a prefix. Lemma/private theorems handle their own surface form.
      if self.visibility in ('private', 'opaque'):
        return self.visibility + ' '
      return ''

  def _skip_export(self, importing_module: str) -> bool:
    # A private declaration is visible only within its own module.
    return self.visibility == 'private' \
        and importing_module != get_current_module()

  # Function-like declarations (`Define`, `RecFun`, ...) permit several
  # definitions sharing a base name, so they accumulate overloads via
  # `extend`; other declarations just overwrite their single name.
  _exports_overload: ClassVar[bool] = False

  def collect_exports(self, export_env: UniquifyEnv, importing_module: str) -> None:
    # Default: export this declaration's single name. Subclasses that
    # export additional names (constructors, rules) or use a different
    # visibility rule override this.
    if self._skip_export(importing_module):
      return
    if self._exports_overload:
      extend(export_env, base_name(self.name), self.name, self.location)
    else:
      export_env[base_name(self.name)] = [self.name]

################ Statements ######################################

## Updates the environment with a name, creating overloads
def extend(env: UniquifyEnv, name: str, new_name: str, loc: Meta) -> None:
  if name in env['no overload']:
    ty = env['no overload'][name]
    user_error(loc, f"Cannot overload {ty} names. {name} is already defined as a {ty}")

  if name in env.keys():
      if not new_name in env[name]:
          env[name].append(new_name)
  else:
    env[name] = [new_name]

## Overwrites a value in the environment, with a warning
def overwrite(env: UniquifyEnv, name: str, new_name: str, loc: Meta) -> None:
  if name in env['no overload']:
    ty = env['no overload'][name]
    user_error(loc, f"Cannot overload {ty} names. {name} is already defined as a {ty}")

  if base_name(name) != "_" and name in env.keys():
    warning(loc, f"WARNING: {name} is already defined")
  env[name] = [new_name]

@dataclass
class FrameExpr(AST):
  def pretty_print(self, indent: int) -> str:
      return indent*' ' + str(self)

@dataclass
class FrameTerm(FrameExpr):
  subject: Term

  def __str__(self) -> str:
    return str(self.subject)

@dataclass
class FrameFootprint(FrameExpr):
  subject: Term

  def __str__(self) -> str:
    return 'footprint(' + str(self.subject) + ')'

@dataclass
class FrameEmpty(FrameExpr):

  def __str__(self) -> str:
    return '{}'

################ Imperative procedure bodies ####################
#
# Parser/AST only (experimental imperative layer, issue #854 Phase 1d).
# These nodes represent the statements inside a `proc` body. They are
# rejected before proof checking -- there is no assignment semantics,
# frame checking, or loop verification here. All expression subparts are
# ordinary `Term`/`Formula` ASTs.

def _pretty_block(stmts: List['ImpStmt'], indent: int) -> str:
  # Render a `{ ... }` imperative block. Whitespace is cosmetic -- the
  # lexer ignores it -- so the point is only to reparse identically.
  if not stmts:
    return '{\n' + indent * ' ' + '}'
  lines = '\n'.join(s.pretty_print(indent + 2) for s in stmts)
  return '{\n' + lines + '\n' + indent * ' ' + '}'

@dataclass
class PostconditionRef(Proof):
  # A qualified call-postcondition reference such as `h.valid_post`, used
  # inside a proof clause (`by h.valid_post`). `subject` is a prior call
  # label (`call f(..) as h`) and `field` names one of the callee's
  # labelled postconditions. Parser/AST only: the names are not resolved
  # here -- tying `subject` to its call label and `field` to a labelled
  # postcondition is a later verifier phase. The default `_map_children`
  # uniquify leaves both (plain string) fields untouched.
  subject: str
  field: str

  def pretty_print(self, indent: int) -> str:
    return base_name(self.subject) + '.' + base_name(self.field)

  def __str__(self) -> str:
    return base_name(self.subject) + '.' + base_name(self.field)

@dataclass
class ImpStmt(AST):
  def pretty_print(self, indent: int) -> str:
    return indent * ' ' + str(self)

@dataclass
class LValueVar(AST):
  name: str

  def __str__(self) -> str:
    return base_name(self.name)

@dataclass
class LValueIndex(AST):
  array: str
  index: Term

  def __str__(self) -> str:
    return base_name(self.array) + '[' + str(self.index) + ']'

@dataclass
class LValueField(AST):
  subject: str
  field: str

  def __str__(self) -> str:
    return base_name(self.subject) + '.' + base_name(self.field)

@dataclass
class ImpCallExpr(AST):
  # A `call f(args)` used as the right-hand side of a `var`/assignment,
  # optionally introducing a call label with `as h`. Distinct from the
  # `ImpCall` statement form: this one produces a value.
  call: Term
  label: Optional[str] = None

  def __str__(self) -> str:
    result = 'call ' + str(self.call)
    if self.label is not None:
      result += ' as ' + base_name(self.label)
    return result

@dataclass
class ImpVar(ImpStmt):
  name: str
  type_annot: Optional[Type]
  rhs: Term | ImpCallExpr
  ghost: bool = False

  def __str__(self) -> str:
    prefix = 'ghost var ' if self.ghost else 'var '
    annot = ': ' + str(self.type_annot) if self.type_annot is not None else ''
    return prefix + base_name(self.name) + annot + ' := ' + str(self.rhs)

@dataclass
class ImpAssign(ImpStmt):
  lhs: LValueVar | LValueIndex | LValueField
  rhs: Term | ImpCallExpr

  def __str__(self) -> str:
    return str(self.lhs) + ' := ' + str(self.rhs)

@dataclass
class ImpIf(ImpStmt):
  cond: Term
  then_body: List['ImpStmt']
  else_body: Optional[List['ImpStmt']] = None

  def pretty_print(self, indent: int) -> str:
    pad = indent * ' '
    result = pad + 'if ' + str(self.cond) + ' ' \
        + _pretty_block(self.then_body, indent)
    if self.else_body is not None:
      result += ' else ' + _pretty_block(self.else_body, indent)
    return result

  def __str__(self) -> str:
    return self.pretty_print(0)

@dataclass
class ImpWhile(ImpStmt):
  cond: Term
  invariants: List[Term]
  modifies: List[FrameExpr]
  decreases: Optional[Term]
  body: List['ImpStmt']
  established: Optional[Proof] = None
  preserved: Optional[Proof] = None
  decreases_proof: Optional[Proof] = None

  def pretty_print(self, indent: int) -> str:
    pad = indent * ' '
    spec_pad = (indent + 2) * ' '
    lines = [pad + 'while ' + str(self.cond)]
    for inv in self.invariants:
      lines.append(spec_pad + 'invariant ' + str(inv))
    if self.modifies:
      lines.append(spec_pad + 'modifies '
                   + ', '.join(str(f) for f in self.modifies))
    if self.established is not None:
      lines.append(spec_pad + 'established by ' + str(self.established))
    if self.preserved is not None:
      lines.append(spec_pad + 'preserved by ' + str(self.preserved))
    if self.decreases is not None:
      decreases_line = spec_pad + 'decreases ' + str(self.decreases)
      if self.decreases_proof is not None:
        decreases_line += ' by ' + str(self.decreases_proof)
      lines.append(decreases_line)
    header = '\n'.join(lines)
    return header + '\n' + pad + _pretty_block(self.body, indent)

  def __str__(self) -> str:
    return self.pretty_print(0)

@dataclass
class ImpAssert(ImpStmt):
  formula: Term
  proof: Optional[Proof] = None

  def __str__(self) -> str:
    result = 'assert ' + str(self.formula)
    if self.proof is not None:
      result += ' by ' + str(self.proof)
    return result

@dataclass
class ImpAssume(ImpStmt):
  formula: Term

  def __str__(self) -> str:
    return 'assume ' + str(self.formula)

@dataclass
class ImpCall(ImpStmt):
  call: Term
  label: Optional[str] = None
  proof: Optional[Proof] = None

  def __str__(self) -> str:
    result = 'call ' + str(self.call)
    if self.label is not None:
      result += ' as ' + base_name(self.label)
    if self.proof is not None:
      result += ' by ' + str(self.proof)
    return result

@dataclass
class ImpReturn(ImpStmt):
  value: Term

  def __str__(self) -> str:
    return 'return ' + str(self.value)

def _resolve_local(name: str, env: UniquifyEnv) -> str:
  # Resolve an assignment-target name to its unique binding when one is in
  # scope. Assignment targets are plain strings (not `Var` nodes), so this
  # is best-effort: field names and not-yet-supported globals stay as-is.
  names = env.get(name)
  return names[0] if names else name

def _uniquify_lvalue(lv: LValueVar | LValueIndex | LValueField,
                     env: UniquifyEnv,
                     ctx: UniquifyContext) -> LValueVar | LValueIndex | LValueField:
  if isinstance(lv, LValueIndex):
    return LValueIndex(lv.location, _resolve_local(lv.array, env),
                       lv.index.uniquify(env, ctx))
  if isinstance(lv, LValueField):
    return LValueField(lv.location, _resolve_local(lv.subject, env), lv.field)
  return LValueVar(lv.location, _resolve_local(lv.name, env))

def _uniquify_imp_rhs(rhs: Term | ImpCallExpr, env: UniquifyEnv,
                      ctx: UniquifyContext) -> Term | ImpCallExpr:
  # A `var`/assignment right-hand side is either an ordinary term or a
  # `call f(..) as h` expression. For the call form, resolve the call
  # term's subparts but leave the label as-is (see the proof-clause note
  # in `ProcDecl.uniquify`).
  if isinstance(rhs, ImpCallExpr):
    return ImpCallExpr(rhs.location, rhs.call.uniquify(env, ctx), rhs.label)
  return rhs.uniquify(env, ctx)

def _uniquify_imp_proof(proof: Optional[Proof], env: UniquifyEnv,
                        ctx: UniquifyContext) -> Optional[Proof]:
  # A `by` proof clause. Uniquify it so its embedded term/type subparts are
  # resolved (no pre-uniquify `Var` may survive). Bare proof-slot labels
  # resolve because `ProcDecl.uniquify` pre-binds the out-of-line proof-block
  # labels; `PostconditionRef` (`h.valid_post`) carries plain-string names
  # that the default walker leaves alone -- tying them to a call label is a
  # later verifier phase.
  return proof.uniquify(env, ctx) if proof is not None else None

def _uniquify_imp_stmt(s: ImpStmt, env: UniquifyEnv,
                       ctx: UniquifyContext) -> ImpStmt:
  # `env` is the enclosing block's environment; a `var` declaration mutates
  # it so later statements in the same block see the binding. Nested blocks
  # receive a copy so their locals do not leak outward.
  if isinstance(s, ImpVar):
    new_rhs = _uniquify_imp_rhs(s.rhs, env, ctx)
    new_type = (s.type_annot.uniquify(env, ctx)
                if s.type_annot is not None else None)
    new_name = generate_name(s.name, ctx)
    overwrite(env, s.name, new_name, s.location)
    return ImpVar(s.location, new_name, new_type, new_rhs, s.ghost)
  if isinstance(s, ImpAssign):
    return ImpAssign(s.location, _uniquify_lvalue(s.lhs, env, ctx),
                     _uniquify_imp_rhs(s.rhs, env, ctx))
  if isinstance(s, ImpIf):
    new_cond = s.cond.uniquify(env, ctx)
    then_body = _uniquify_imp_block(s.then_body, copy_dict(env), ctx)
    else_body = (_uniquify_imp_block(s.else_body, copy_dict(env), ctx)
                 if s.else_body is not None else None)
    return ImpIf(s.location, new_cond, then_body, else_body)
  if isinstance(s, ImpWhile):
    new_cond = s.cond.uniquify(env, ctx)
    new_invariants = [inv.uniquify(env, ctx) for inv in s.invariants]
    new_modifies = [f.uniquify(env, ctx) for f in s.modifies]
    new_decreases = (s.decreases.uniquify(env, ctx)
                     if s.decreases is not None else None)
    body = _uniquify_imp_block(s.body, copy_dict(env), ctx)
    return ImpWhile(s.location, new_cond, new_invariants, new_modifies,
                    new_decreases, body,
                    _uniquify_imp_proof(s.established, env, ctx),
                    _uniquify_imp_proof(s.preserved, env, ctx),
                    _uniquify_imp_proof(s.decreases_proof, env, ctx))
  if isinstance(s, ImpAssert):
    return ImpAssert(s.location, s.formula.uniquify(env, ctx),
                     _uniquify_imp_proof(s.proof, env, ctx))
  if isinstance(s, ImpAssume):
    return ImpAssume(s.location, s.formula.uniquify(env, ctx))
  if isinstance(s, ImpCall):
    return ImpCall(s.location, s.call.uniquify(env, ctx), s.label,
                   _uniquify_imp_proof(s.proof, env, ctx))
  if isinstance(s, ImpReturn):
    return ImpReturn(s.location, s.value.uniquify(env, ctx))
  return s

def _uniquify_imp_block(stmts: List[ImpStmt], env: UniquifyEnv,
                        ctx: UniquifyContext) -> List[ImpStmt]:
  return [_uniquify_imp_stmt(s, env, ctx) for s in stmts]

@dataclass
class ProcParam(AST):
  name: str
  typ: Type
  ghost: bool = False

  def __str__(self) -> str:
    prefix = 'ghost ' if self.ghost else ''
    return prefix + base_name(self.name) + ': ' + str(self.typ)

@dataclass
class ProcSpec(AST):
  keyword: str
  value: Term | List[FrameExpr]
  label: Optional[str] = None

  def __str__(self) -> str:
    if isinstance(self.value, list):
      value = ', '.join(str(t) for t in self.value)
    else:
      value = str(self.value)
    label = ''
    if self.label is not None:
      label = base_name(self.label) + ': '
    return self.keyword + ' ' + label + value

  def pretty_print(self, indent: int) -> str:
    return indent * ' ' + str(self)

@dataclass
class ProcProofEntry(AST):
  # One `label { proof }` entry of a procedure's out-of-line `proof ... end`
  # block. The label is the proof-slot name cited by a `by label` clause
  # somewhere in the procedure; the proof is an ordinary Deduce proof.
  label: str
  proof: Proof

  def pretty_print(self, indent: int) -> str:
    pad = indent * ' '
    return pad + base_name(self.label) + ' {\n' \
      + self.proof.pretty_print(indent + 2) + '\n' + pad + '}'

  def __str__(self) -> str:
    return self.pretty_print(0)

@dataclass
class ProcDecl(Declaration):
  type_params: List[str]
  params: List[ProcParam]
  return_type: Optional[Type]
  specs: List[ProcSpec]
  body: List[ImpStmt] = field(default_factory=list)
  proof_block: List[ProcProofEntry] = field(default_factory=list)

  def __str__(self) -> str:
    return self.pretty_print(0)

  def pretty_print(self, indent: int) -> str:
    if get_verbose():
      shown_name = self.name
      typarams = self.type_params
    else:
      shown_name = base_name(self.name)
      typarams = [base_name(t) for t in self.type_params]
    pad = indent * ' '
    header = pad + self.visibility_prefix() + 'proc ' + shown_name
    if typarams:
      header += '<' + ','.join(typarams) + '>'
    header += '(' + ', '.join(str(p) for p in self.params) + ')'
    if self.return_type is not None:
      header += ' -> ' + str(self.return_type)
    if self.specs:
      header += '\n' + '\n'.join(spec.pretty_print(indent + 2)
                                 for spec in self.specs)
    result = header + '\n' + pad + _pretty_block(self.body, indent)
    if self.proof_block:
      entries = '\n'.join(entry.pretty_print(indent + 2)
                          for entry in self.proof_block)
      result += '\n' + pad + 'proof\n' + entries + '\n' + pad + 'end'
    return result

  def uniquify(self, env: object, ctx: object) -> ProcDecl:
    env_map = cast(UniquifyEnv, env)
    uniq_ctx = cast(UniquifyContext, ctx)
    if self.name in env_map.keys():
      user_error(self.location,
                 "proc names may not be overloaded: " + base_name(self.name))
    new_name = generate_name(self.name, uniq_ctx)
    overwrite(env_map, self.name, new_name, self.location)
    env_map['no overload'][self.name] = 'proc'

    proc_env = copy_dict(env_map)
    new_type_params = [generate_name(t, uniq_ctx) for t in self.type_params]
    for (old, new) in zip(self.type_params, new_type_params):
      overwrite(proc_env, old, new, self.location)

    new_params = []
    for param in self.params:
      new_typ = param.typ.uniquify(proc_env, uniq_ctx)
      new_param_name = generate_name(param.name, uniq_ctx)
      overwrite(proc_env, param.name, new_param_name, param.location)
      new_params.append(ProcParam(param.location, new_param_name,
                                  new_typ, param.ghost))

    new_return_type = (
        self.return_type.uniquify(proc_env, uniq_ctx)
        if self.return_type is not None
        else None
    )
    if new_return_type is not None:
      overwrite(proc_env, 'result', generate_name('result', uniq_ctx),
                self.location)
    new_specs = [spec.uniquify(proc_env, uniq_ctx) for spec in self.specs]
    # Parser/AST only: uniquify resolves the body's term subparts (so no
    # pre-uniquify `Var` nodes leak past this pass) and alpha-renames local
    # `var` bindings, but there is no assignment semantics, frame checking, or
    # loop verification here. The out-of-line `proof ... end` block's slot
    # labels are pre-bound so bare `by label` references in the body resolve;
    # this is alpha-renaming only. Deciding whether a bare `by name` is a slot
    # label or a theorem, generating proof-slot goals, and tying
    # `h.valid_post` to a call label are all later verifier phases (#854).
    body_env = copy_dict(proc_env)
    new_labels = [generate_name(entry.label, uniq_ctx)
                  for entry in self.proof_block]
    for entry, new_label in zip(self.proof_block, new_labels):
      overwrite(body_env, entry.label, new_label, entry.location)
    new_body = _uniquify_imp_block(self.body, copy_dict(body_env), uniq_ctx)
    new_proof_block = [
        ProcProofEntry(entry.location, new_label,
                       entry.proof.uniquify(copy_dict(body_env), uniq_ctx))
        for entry, new_label in zip(self.proof_block, new_labels)
    ]
    return ProcDecl(self.location, new_name, new_type_params, new_params,
                    new_return_type, new_specs, new_body, new_proof_block,
                    visibility=self.visibility)

@dataclass
class Postulate(Declaration):
  what: Formula

  def key(self) -> str:
      return self.name

  def print_theorems_statement(self, f: TextIO) -> None:
      print(base_name(self.name) + ': ' + str(self.what) + '\n', file=f)
  
  def __str__(self) -> str:
    return self.visibility_prefix() + 'postulate ' + self.name \
      + ': ' + str(self.what) + '\n\n'

  def uniquify(self, env: object, ctx: object) -> Postulate:
    env_map = cast(UniquifyEnv, env)
    uniq_ctx = cast(UniquifyContext, ctx)
    if self.name in env_map.keys():
      user_error(self.location, "theorem names may not be overloaded")
    new_what = self.what.uniquify(env_map, uniq_ctx)
    new_name = generate_name(self.name, uniq_ctx)
    overwrite(env_map, self.name, new_name, self.location)
    env_map['no overload'][self.name] = 'theorem'
    return Postulate(self.location, new_name, new_what,
                     visibility=self.visibility)

  def collect_exports(self, export_env: UniquifyEnv, importing_module: str) -> None:
    if self.visibility != 'private' or importing_module == get_current_module():
      export_env[base_name(self.name)] = [self.name]

@dataclass
class Theorem(Declaration):
  what: Formula
  proof: Proof
  isLemma: bool = False   # TODO: remove this, use visibility

  def key(self) -> str:
      return self.name

  def print_theorems_statement(self, f: TextIO) -> None:
      print(base_name(self.name) + ': ' + str(self.what) + '\n', file=f)
  
  def __str__(self) -> str:
    return self.visibility_prefix() \
      + ('lemma ' if self.isLemma else 'theorem ') \
      + self.name + ': ' + str(self.what) \
      + '\nproof\n' + self.proof.pretty_print(2) + '\nend\n'

  def uniquify(self, env: object, ctx: object) -> Theorem:
    env_map = cast(UniquifyEnv, env)
    uniq_ctx = cast(UniquifyContext, ctx)
    if self.name in env_map.keys():
      user_error(self.location, "theorem names may not be overloaded: " + base_name(self.name))
    new_what = self.what.uniquify(env_map, uniq_ctx)
    new_proof = self.proof.uniquify(env_map, uniq_ctx)
    new_name = generate_name(self.name, uniq_ctx)
    overwrite(env_map, self.name, new_name, self.location)
    env_map['no overload'][self.name] = 'theorem'
    return Theorem(self.location, new_name, new_what, new_proof, self.isLemma,
                   visibility=self.visibility)

  def collect_exports(self, export_env: UniquifyEnv, importing_module: str) -> None:
    if importing_module == get_current_module() or not self.isLemma:
      export_env[base_name(self.name)] = [self.name]
    
@dataclass
class Constructor(AST):
  name: str
  parameters: List[Type]

  def pretty_print(self, indent: int) -> str:
      return indent*' ' + str(self)
  
  def uniquify(  # type: ignore[override]
      self,
      env: object,
      body_env: object,
      ctx: object,
  ) -> Constructor:
    env_map = cast(UniquifyEnv, env)
    body_env_map = cast(UniquifyEnv, body_env)
    uniq_ctx = cast(UniquifyContext, ctx)
    new_params = [ty.uniquify(body_env_map, uniq_ctx) for ty in self.parameters]
    new_name = generate_name(self.name, uniq_ctx)
    extend(env_map, self.name, new_name, self.location)
    return Constructor(self.location, new_name, new_params)

  def instantiate_parameters(
      self, typarams: List[str], type_args: List[Type]
  ) -> List[Type]:
    """Apply the union's `typarams → type_args` substitution to this
    constructor's field types. If `typarams` is empty, returns the parameters
    unchanged."""
    if not typarams:
      return list(self.parameters)
    sub: dict[str, Type] = {T: ty for (T, ty) in zip(typarams, type_args)}
    return [p.substitute(sub) for p in self.parameters]

  def __str__(self) -> str:
    if get_verbose():
      name = self.name
    else:
      name = base_name(self.name)
    if len(self.parameters) > 0:
      return name + '(' + ', '.join([str(ty) for ty in self.parameters]) + ')'
    else:
      return name
  
      
@dataclass
class Rule(AST):
  # An introduction rule of a `predicate` / `relation` declaration.
  # The formula is whatever the user wrote on the right of `name :`.
  # Validation (must be a quantified implication or a bare conclusion of
  # the form `pred(args)`) happens later, with diagnostics that quote
  # `original_keyword` and the rule's name.
  name: str
  formula: Formula

  def uniquify(  # type: ignore[override]
      self,
      env: object,
      body_env: object,
      ctx: object,
  ) -> Rule:
    env_map = cast(UniquifyEnv, env)
    body_env_map = cast(UniquifyEnv, body_env)
    uniq_ctx = cast(UniquifyContext, ctx)
    new_formula = self.formula.uniquify(body_env_map, uniq_ctx)
    if self.name in env_map.keys():
      user_error(self.location,
                 "rule names may not be overloaded: " + base_name(self.name))
    new_name = generate_name(self.name, uniq_ctx)
    overwrite(env_map, self.name, new_name, self.location)
    env_map['no overload'][self.name] = 'rule'
    return Rule(self.location, new_name, new_formula)

  def __str__(self) -> str:
    return base_name(self.name) + ' : ' + str(self.formula)

  def pretty_print(self, indent: int) -> str:
    return indent*' ' + base_name(self.name) + ' : ' + str(self.formula)


@dataclass
class Predicate(Declaration):
  # An inductively defined predicate or relation. `original_keyword` is
  # 'predicate' or 'relation' — kept on the AST so error messages echo the
  # form the user actually wrote.
  type_params: List[str]
  signature: Type
  rules: List[Rule]
  original_keyword: str = 'predicate'
  # Names of the auto-generated `<pred>_rule_induction` and
  # `<pred>_rule_inversion` theorems. Populated by `Predicate.uniquify`
  # so the proof checker can find them when desugaring `rule induction`
  # / `rule inversion` proofs. `None` on a pre-uniquify Predicate.
  rule_induction_name: Optional[str] = None
  rule_inversion_name: Optional[str] = None
  # The Predicate's impredicative-encoding translation (Define + one
  # Postulate per rule), populated by `process_declaration`'s Predicate
  # arm after it threads the synthesised decls through the pipeline.
  # `None` on a Predicate that hasn't been processed yet.
  translated_ast: Optional[List["Statement"]] = None

  def reduce(self, env: object) -> Self:
    return self

  def substitute(self, sub: object) -> Self:
    return self

  def uniquify(self, env: object, ctx: object) -> Predicate:
    env_map = cast(UniquifyEnv, env)
    uniq_ctx = cast(UniquifyContext, ctx)
    if self.name in env_map.keys():
      user_error(self.location,
                 self.original_keyword + " names may not be overloaded: " \
                 + base_name(self.name))
    new_name = generate_name(self.name, uniq_ctx)
    env_map[self.name] = [new_name]
    env_map['no overload'][self.name] = self.original_keyword
    base_pred = base_name(self.name)

    # Pre-register the synthesised `<pred>_rule_induction` theorem name so
    # user code referencing it gets resolved correctly during uniquify.
    # The translation pass in proof_checker.py reads `rule_induction_name`
    # off the AST and emits a Theorem with that exact uniquified name.
    rule_ind_base = base_pred + '_rule_induction'
    if rule_ind_base in env_map.keys():
      user_error(self.location,
                 "name '" + rule_ind_base + "' is already defined; the "
                 + self.original_keyword + " '" + base_pred
                 + "' would auto-generate a theorem with that name")
    rule_ind_unique = generate_name(rule_ind_base, uniq_ctx)
    env_map[rule_ind_base] = [rule_ind_unique]
    env_map['no overload'][rule_ind_base] = 'theorem'
    # Same treatment for the inversion principle.
    rule_inv_base = base_pred + '_rule_inversion'
    if rule_inv_base in env_map.keys():
        user_error(self.location,
                   "name '" + rule_inv_base + "' is already defined; the "
                   + self.original_keyword + " '" + base_pred
                   + "' would auto-generate a theorem with that name")
    rule_inv_unique = generate_name(rule_inv_base, uniq_ctx)
    env_map[rule_inv_base] = [rule_inv_unique]
    env_map['no overload'][rule_inv_base] = 'theorem'

    body_env = copy_dict(env_map)
    new_type_params = [generate_name(t, uniq_ctx) for t in self.type_params]
    for (old, new) in zip(self.type_params, new_type_params):
      extend(body_env, old, new, self.location)

    new_signature = self.signature.uniquify(body_env, uniq_ctx)
    new_rules = [rule.uniquify(env_map, body_env, uniq_ctx) for rule in self.rules]

    new_pred = Predicate(self.location, new_name, new_type_params,
                         new_signature, new_rules,
                         self.original_keyword,
                         rule_induction_name=rule_ind_unique,
                         rule_inversion_name=rule_inv_unique,
                         visibility=self.visibility)
    # Register a back-pointer keyed by the predicate's uniquified name so
    # the proof checker can recover this AST node (specifically
    # `rule_induction_name` / `rule_inversion_name` and the rule list)
    # when desugaring a `rule induction` / `rule inversion` proof.
    _predicate_decls_by_unique_name[new_name] = new_pred
    return new_pred

  def collect_exports(self, export_env: UniquifyEnv, importing_module: str) -> None:
    super().collect_exports(export_env, importing_module)
    if self._skip_export(importing_module):
      return
    for rule in self.rules:
      extend(export_env, base_name(rule.name), rule.name, self.location)
    if self.rule_induction_name is not None:
      extend(export_env, base_name(self.rule_induction_name),
             self.rule_induction_name, self.location)

  def __str__(self) -> str:
    if get_verbose():
      shown_name = self.name
    else:
      shown_name = complete_name(self.name)
    header = self.visibility_prefix() + self.original_keyword + ' ' + shown_name
    if self.type_params:
      header += '<' + ','.join([base_name(t) for t in self.type_params]) + '>'
    body = '\n'.join('  ' + str(r) for r in self.rules)
    return header + ' : ' + str(self.signature) + ' {\n' + body + '\n}'

  def pretty_print(self, indent: int) -> str:
    return indent*' ' + str(self)


@dataclass
class Union(Declaration):
  type_params: List[str]
  alternatives: List[Constructor]
  param_polarities: Optional[List[str]] = None

  def reduce(self, env: object) -> Self:
    return self
  
  def uniquify(self, env: object, ctx: object) -> Union:
    env_map = cast(UniquifyEnv, env)
    uniq_ctx = cast(UniquifyContext, ctx)
    if self.name in env_map.keys():
      user_error(self.location, "union names may not be overloaded")
    new_name = generate_name(self.name, uniq_ctx)
    env_map[self.name] = [new_name]
    env_map['no overload'][self.name] = 'union'

    body_env = copy_dict(env_map)
    new_type_params = [generate_name(t, uniq_ctx) for t in self.type_params]
    for (old, new) in zip(self.type_params, new_type_params):
      extend(body_env, old, new, self.location)

    new_alts = [con.uniquify(env_map, body_env, uniq_ctx)
                for con in self.alternatives]
    return Union(self.location, new_name, new_type_params, new_alts,
                 visibility=self.visibility)

  def collect_exports(self, export_env: UniquifyEnv, importing_module: str) -> None:
    super().collect_exports(export_env, importing_module)
    if self._skip_export(importing_module):
      return
    if not self.visibility == 'opaque' or (importing_module == get_current_module()):
      for con in self.alternatives:
        extend(export_env, base_name(con.name), con.name, self.location)
    
  def substitute(self, sub: object) -> Self:
    return self
      
  def pretty_print(self, indent: int, afterNewline: bool = False) -> str:
      header = self.visibility_prefix() + 'union ' + base_name(self.name) \
          + ('<' + ','.join([base_name(t) for t in self.type_params]) + '>' if len(self.type_params) > 0 \
             else '')
      ret = header + ' {\n' \
                   + '\n'.join([c.pretty_print(indent+2) for c in self.alternatives]) + '\n'\
                   + indent*' ' + '}\n'

      return indent*' ' + ret
  
  def __str__(self) -> str:
    if get_verbose():
      return 'union ' + self.name + '<' + ','.join(self.type_params) + '> {' \
        + ' '.join([str(c) for c in self.alternatives]) + '}'
    else:
      return base_name(self.name)


@dataclass
class TypeAlias(Declaration):
  type_params: List[str]
  body: Type

  def reduce(self, env: object) -> Self:
    return self

  def uniquify(self, env: object, ctx: object) -> TypeAlias:
    env_map = cast(UniquifyEnv, env)
    uniq_ctx = cast(UniquifyContext, ctx)
    if self.name in env_map.keys():
      user_error(self.location, "type names may not be overloaded")
    new_name = generate_name(self.name, uniq_ctx)
    env_map[self.name] = [new_name]
    env_map['no overload'][self.name] = 'type alias'

    body_env = copy_dict(env_map)
    new_type_params = [generate_name(t, uniq_ctx) for t in self.type_params]
    for old, new in zip(self.type_params, new_type_params):
      extend(body_env, old, new, self.location)

    return TypeAlias(self.location, new_name, new_type_params,
                     self.body.uniquify(body_env, uniq_ctx),
                     visibility=self.visibility)

  def substitute(self, sub: object) -> Self:
    return self

  def pretty_print(self, indent: int, afterNewline: bool = False) -> str:
    header = self.visibility_prefix() + 'type ' + base_name(self.name) \
        + ('<' + ','.join([base_name(t) for t in self.type_params]) + '>' if self.type_params else '')
    return indent*' ' + header + ' = ' + str(self.body) + '\n'

  def __str__(self) -> str:
    if get_verbose():
      shown_name = self.name
      params = '<' + ','.join(self.type_params) + '>' if self.type_params else ''
      return 'type ' + shown_name + params + ' = ' + str(self.body)
    return base_name(self.name)


@dataclass
class ObjectField(AST):
  name: str
  typ: Type
  ghost: bool = False

  def uniquify(
      self,
      env: object,
      ctx: object,
  ) -> ObjectField:
    env_map = cast(UniquifyEnv, env)
    uniq_ctx = cast(UniquifyContext, ctx)
    return ObjectField(self.location, self.name,
                       self.typ.uniquify(env_map, uniq_ctx), self.ghost)

  def pretty_print(self, indent: int) -> str:
    return indent * ' ' + ('ghost ' if self.ghost else '') \
      + 'var ' + base_name(self.name) + ' : ' + str(self.typ)

  def __str__(self) -> str:
    return self.pretty_print(0)


@dataclass
class ObjectDecl(Declaration):
  type_params: List[str]
  fields: Optional[List[ObjectField]] = None

  def reduce(self, env: object) -> Self:
    return self

  def uniquify(self, env: object, ctx: object) -> ObjectDecl:
    env_map = cast(UniquifyEnv, env)
    uniq_ctx = cast(UniquifyContext, ctx)
    if self.name in env_map.keys():
      user_error(self.location, "object names may not be overloaded")
    new_name = generate_name(self.name, uniq_ctx)
    env_map[self.name] = [new_name]
    env_map['no overload'][self.name] = 'object'

    body_env = copy_dict(env_map)
    new_type_params = [generate_name(t, uniq_ctx) for t in self.type_params]
    for old, new in zip(self.type_params, new_type_params):
      extend(body_env, old, new, self.location)
    new_fields = None if self.fields is None \
      else [field.uniquify(body_env, uniq_ctx) for field in self.fields]
    return ObjectDecl(self.location, new_name, new_type_params, new_fields,
                      visibility=self.visibility)

  def substitute(self, sub: object) -> Self:
    return self

  def pretty_print(self, indent: int, afterNewline: bool = False) -> str:
    header = self.visibility_prefix() + 'object ' + base_name(self.name) \
        + ('<' + ','.join([base_name(t) for t in self.type_params]) + '>' if self.type_params else '')
    if self.fields is None:
      return indent * ' ' + header + '\n'
    if len(self.fields) == 0:
      return indent * ' ' + header + ' {}\n'
    body = '\n'.join([field.pretty_print(indent + 2)
                      for field in self.fields])
    return indent * ' ' + header + ' {\n' + body + '\n' \
      + indent * ' ' + '}\n'

  def __str__(self) -> str:
    if get_verbose():
      params = '<' + ','.join(self.type_params) + '>' if self.type_params else ''
      return 'object ' + self.name + params
    return base_name(self.name)


@dataclass
class ObserverDecl(Declaration):
  type_params: List[str]
  params: List[ProcParam]
  return_type: Type
  reads: List[List[FrameExpr]]
  body: Optional[Term] = None

  def reduce(self, env: object) -> Self:
    return self

  def substitute(self, sub: object) -> Self:
    return self

  def uniquify(self, env: object, ctx: object) -> ObserverDecl:
    env_map = cast(UniquifyEnv, env)
    uniq_ctx = cast(UniquifyContext, ctx)
    if self.name in env_map.keys():
      user_error(self.location,
                 "observer names may not be overloaded: "
                 + base_name(self.name))
    new_name = generate_name(self.name, uniq_ctx)
    overwrite(env_map, self.name, new_name, self.location)
    env_map['no overload'][self.name] = 'observer'

    body_env = copy_dict(env_map)
    new_type_params = [generate_name(t, uniq_ctx) for t in self.type_params]
    for (old, new) in zip(self.type_params, new_type_params):
      overwrite(body_env, old, new, self.location)

    new_params = []
    for param in self.params:
      new_typ = param.typ.uniquify(body_env, uniq_ctx)
      new_param_name = generate_name(param.name, uniq_ctx)
      overwrite(body_env, param.name, new_param_name, param.location)
      new_params.append(ProcParam(param.location, new_param_name,
                                  new_typ, param.ghost))

    new_return_type = self.return_type.uniquify(body_env, uniq_ctx)
    new_reads = [
      [frame.uniquify(body_env, uniq_ctx) for frame in clause]
      for clause in self.reads
    ]
    new_body = (self.body.uniquify(body_env, uniq_ctx)
                if self.body is not None else None)
    return ObserverDecl(self.location, new_name, new_type_params,
                        new_params, new_return_type, new_reads,
                        new_body, visibility=self.visibility)

  def __str__(self) -> str:
    if get_verbose():
      shown_name = self.name
      typarams = self.type_params
    else:
      shown_name = base_name(self.name)
      typarams = [base_name(t) for t in self.type_params]
    header = self.visibility_prefix() + 'observer ' + shown_name
    if typarams:
      header += '<' + ','.join(typarams) + '>'
    header += '(' + ', '.join(str(p) for p in self.params) + ')'
    header += ' -> ' + str(self.return_type)
    lines = [header]
    for clause in self.reads:
      lines.append('  reads ' + ', '.join(str(f) for f in clause))
    s = '\n'.join(lines)
    if self.body is not None:
      s += '\n{\n  ' + str(self.body) + '\n}'
    return s

  def pretty_print(self, indent: int, afterNewline: bool = False) -> str:
    return indent * ' ' \
      + str(self).replace('\n', '\n' + indent * ' ').rstrip() + '\n'


@dataclass
class ResourceDecl(Declaration):
  # Separation-logic resource declaration (experimental imperative layer,
  # issue #854 Phase 1h). Parser/AST only: it is rejected before proof
  # checking, so there is no ownership accounting or resource-aware proof
  # rule here. The optional body is an ordinary `Term` that may use the
  # resource formula connectives `emp`, `**`, and `|->`.
  type_params: List[str]
  params: List[ProcParam]
  body: Optional[Term] = None

  def reduce(self, env: object) -> Self:
    return self

  def substitute(self, sub: object) -> Self:
    return self

  def uniquify(self, env: object, ctx: object) -> ResourceDecl:
    env_map = cast(UniquifyEnv, env)
    uniq_ctx = cast(UniquifyContext, ctx)
    if self.name in env_map.keys():
      user_error(self.location,
                 "resource names may not be overloaded: "
                 + base_name(self.name))
    new_name = generate_name(self.name, uniq_ctx)
    overwrite(env_map, self.name, new_name, self.location)
    env_map['no overload'][self.name] = 'resource'

    body_env = copy_dict(env_map)
    new_type_params = [generate_name(t, uniq_ctx) for t in self.type_params]
    for (old, new) in zip(self.type_params, new_type_params):
      overwrite(body_env, old, new, self.location)

    new_params = []
    for param in self.params:
      new_typ = param.typ.uniquify(body_env, uniq_ctx)
      new_param_name = generate_name(param.name, uniq_ctx)
      overwrite(body_env, param.name, new_param_name, param.location)
      new_params.append(ProcParam(param.location, new_param_name,
                                  new_typ, param.ghost))

    new_body = (self.body.uniquify(body_env, uniq_ctx)
                if self.body is not None else None)
    return ResourceDecl(self.location, new_name, new_type_params,
                        new_params, new_body, visibility=self.visibility)

  def __str__(self) -> str:
    if get_verbose():
      shown_name = self.name
      typarams = self.type_params
    else:
      shown_name = base_name(self.name)
      typarams = [base_name(t) for t in self.type_params]
    header = self.visibility_prefix() + 'resource ' + shown_name
    if typarams:
      header += '<' + ','.join(typarams) + '>'
    header += '(' + ', '.join(str(p) for p in self.params) + ')'
    if self.body is not None:
      header += ' {\n  ' + str(self.body) + '\n}'
    return header

  def pretty_print(self, indent: int, afterNewline: bool = False) -> str:
    return indent * ' ' \
      + str(self).replace('\n', '\n' + indent * ' ').rstrip() + '\n'


@dataclass
class FunCase(AST):
  rator: Term
  pattern: Pattern
  parameters: List[str]
  body: Term

  def pretty_print(self, indent: int) -> str:
      return indent*' ' + str(self.rator) + '(' + str(self.pattern) \
          + (', ' + ', '.join([base_name(p) for p in self.parameters]) if len(self.parameters) > 0 else '') \
          + ') = ' + self.body.pretty_print(indent+2)
  
  def __str__(self) -> str:
      return str(self.rator) + '(' + str(self.pattern) + ',' + ",".join(self.parameters) \
          + ') = ' + str(self.body)

  def uniquify(  # type: ignore[override]
      self,
      env: object,
      fun_name: str,
      ctx: object,
  ) -> FunCase:
    env_map = cast(UniquifyEnv, env)
    uniq_ctx = cast(UniquifyContext, ctx)
    rator = cast(Var, self.rator)
    if rator.name != fun_name:
        user_error(self.rator.location, 'expected function name "' + fun_name + \
                   '", not "' + str(rator.name) + '"')
    new_rator = self.rator.uniquify(env_map, uniq_ctx)
    new_pat = self.pattern.uniquify(env_map, uniq_ctx)
    body_env = copy_dict(env_map)

    match new_pat:
      case PatternCons(_, _, parameters):
        new_pat_params = [generate_name(x, uniq_ctx) for x in parameters]
        for (old, new) in zip(parameters, new_pat_params):
          overwrite(body_env, old, new, self.location)
        new_pat = new_pat.with_bindings(new_pat_params)
      case PatternBool(_, _):
        pass

    new_params = [generate_name(x, uniq_ctx) for x in self.parameters]
    for (old, new) in zip(self.parameters, new_params):
      overwrite(body_env, old, new, self.location)

    new_body = self.body.uniquify(body_env, uniq_ctx)
    return FunCase(self.location, new_rator, new_pat, new_params, new_body)


def funcdecl_ref_eq(decl: RecFun | GenRecFun, other: object) -> bool | None:
  """Name-based equality of a function declaration against the reference
  forms that can point at it. Shared by ``RecFun`` and ``GenRecFun``.
  Returns ``None`` when ``other`` is not one of those forms, leaving the
  same-kind comparison to the caller (which keeps ``RecFun`` and
  ``GenRecFun`` from comparing equal to each other)."""
  if isinstance(other, ResolvedVar):
    return decl.name == other.name
  elif isinstance(other, OverloadedVar):
    return decl.name == other.resolved_names[0]
  elif isinstance(other, Var):
    return decl.name == other.name
  elif isinstance(other, TermInst):
    return decl == other.subject
  return None


@dataclass
class RecFun(Declaration):
  type_params: List[str]
  params: List[Type]
  returns: Type
  cases: List[FunCase]

  def uniquify(self, env: object, ctx: object) -> RecFun:
    env_map = cast(UniquifyEnv, env)
    uniq_ctx = cast(UniquifyContext, ctx)
    old_name = self.name
    new_name = generate_name(self.name, uniq_ctx)
    extend(env_map, self.name, new_name, self.location)

    body_env = copy_dict(env_map)
    new_type_params = [generate_name(t, uniq_ctx) for t in self.type_params]
    for (old, new) in zip(self.type_params, new_type_params):
      extend(body_env, old, new, self.location)

    new_params = [ty.uniquify(body_env, uniq_ctx) for ty in self.params]
    new_returns = self.returns.uniquify(body_env, uniq_ctx)
    new_cases = [c.uniquify(body_env, old_name, uniq_ctx) for c in self.cases]

    return RecFun(self.location, new_name, new_type_params,
                  new_params, new_returns, new_cases,
                  visibility=self.visibility)
      
  _exports_overload = True

  def __str__(self) -> str:
    if get_verbose():
      return '`' + name2str(self.name)
    else:
      return name2str(self.name)
    
  def to_string(self) -> str:
    return 'recursive ' + self.name + '<' + ','.join([name2str(t) for t in self.type_params]) + '>' \
      + '(' + ','.join([str(ty) for ty in self.params]) + ')' \
      + ' -> ' + str(self.returns) + '{\n' \
      + '\n'.join([str(c) for c in self.cases]) \
      + '\n}'

  def pretty_print(self, indent: int, afterNewline: bool = False) -> str:
    header = complete_name(self.name) \
        + ('<' + ','.join([name2str(t) for t in self.type_params]) + '>' \
           if len(self.type_params) > 0 else '') \
      + '(' + ','.join([str(ty) for ty in self.params]) + ')' \
      + ' -> ' + str(self.returns)
    ret = self.visibility_prefix() + 'recursive ' + header + '{\n' \
      + '\n'.join([c.pretty_print(indent+2) for c in self.cases]) + '\n' \
      + '}\n'

    return indent*' ' + ret

  def __eq__(self, other: object) -> bool:
    res = funcdecl_ref_eq(self, other)
    if res is not None:
      return res
    return isinstance(other, RecFun) and self.name == other.name

  def reduce(self, env: object) -> Self:
    return self

  def substitute(self, sub: object) -> Self:
    return self

def pretty_print_function_header(
    name: str,
    type_params: Sequence[str],
    params: Sequence[tuple[str, Type | None]],
) -> str:
    return 'fun ' + complete_name(name) \
        + ('<' + ', '.join([base_name(t) for t in type_params]) + '>' \
           if len(type_params) > 0 else '') \
        + '(' + ', '.join([x + ':' + str(t) if t else x \
                           for (x,t) in params]) + ')\n'

def pretty_print_function(
    name: str,
    type_params: list[str],
    params: list[tuple[str, Type | None]],
    body: Term,
) -> str:
    return 'fun ' + complete_name(name) \
        + ('<' + ', '.join([base_name(t) for t in type_params]) + '>' \
           if len(type_params) > 0 else '') \
        + '(' + ', '.join([x + ':' + str(t) if t else x \
                           for (x,t) in params]) + ')' \
        + " {\n" + body.pretty_print(2, True) + "\n}\n"

@dataclass
class GenRecFun(Declaration):
  type_params: List[str]
  vars: List[Tuple[str,Type]]
  returns: Type
  measure: Term
  measure_ty: Type
  body: Term
  terminates: Proof
  trusted_terminates: bool = False

  def uniquify(self, env: object, ctx: object) -> GenRecFun:
    env_map = cast(UniquifyEnv, env)
    uniq_ctx = cast(UniquifyContext, ctx)
    new_name = generate_name(self.name, uniq_ctx)
    extend(env_map, self.name, new_name, self.location)

    body_env = copy_dict(env_map)
    terminates_env = copy_dict(env_map)
    new_type_params = [generate_name(t, uniq_ctx) for t in self.type_params]
    for (old, new) in zip(self.type_params, new_type_params):
      extend(body_env, old, new, self.location)
      extend(terminates_env, old, new, self.location)

    new_returns = self.returns.uniquify(body_env, uniq_ctx)

    new_var_types = cast(
      List[Type],
      [t.uniquify(body_env, uniq_ctx) if t else None
       for (_, t) in self.vars],
    )
    new_vars = [(generate_name(x, uniq_ctx), nt)
                for ((x, _), nt) in zip(self.vars, new_var_types)]
    for ((old, _), (new, _)) in zip(self.vars, new_vars):
      overwrite(body_env, old, new, self.location)

    new_measure = self.measure.uniquify(body_env, uniq_ctx)
    new_measure_ty = self.measure_ty.uniquify(env_map, uniq_ctx)
    new_terminates = self.terminates.uniquify(terminates_env, uniq_ctx)
    new_body = self.body.uniquify(body_env, uniq_ctx)

    return GenRecFun(self.location, new_name, new_type_params,
                     new_vars, new_returns, new_measure,
                     new_measure_ty, new_body, new_terminates,
                     self.trusted_terminates, visibility=self.visibility)
    
  _exports_overload = True

  def __str__(self) -> str:
    if get_verbose():
      return self.to_string()
    else:
      return self.name if get_unique_names() else base_name(self.name)
    
  def to_string(self) -> str:
    return 'recfun ' + self.name + '<' + ','.join(self.type_params) + '>' \
        + '(' + ', '.join([x + ':' + str(t) if t else x\
                           for (x,t) in self.vars]) + ')' \
        + ' -> ' + str(self.returns) + '\n' \
        + '\tmeasure ' + str(self.measure) \
        + ' {\n' + str(self.body) + '\n}\n' \
        + 'terminates {\n' + str(self.terminates) + '\n}\n'

  def pretty_print(self, indent: int, afterNewline: bool = False) -> str:
    pad = indent * ' '
    header = complete_name(self.name) \
        + ('<' + ','.join([name2str(t) for t in self.type_params]) + '>' \
           if len(self.type_params) > 0 else '') \
      + '(' + ', '.join([base_name(x) + ':' + str(t) if t else x for (x,t) in self.vars])\
      + ') -> ' + str(self.returns) \
      + '\n' + pad + '  measure ' + str(self.measure) \
      + ' of ' + str(self.measure_ty)

    terminates_str = self.terminates.pretty_print(indent + 2)
    if not terminates_str.startswith('\n'):
      terminates_str = '\n' + terminates_str
    if not terminates_str.endswith('\n'):
      terminates_str = terminates_str + '\n'

    ret = self.visibility_prefix() + 'recfun ' + header + '\n' \
      + pad + '{' + self.body.pretty_print(indent + 2) + '\n' + pad + '}\n' \
      + pad + 'terminates {' + terminates_str + pad + '}\n'

    return pad + ret


  def __eq__(self, other: object) -> bool:
    res = funcdecl_ref_eq(self, other)
    if res is not None:
      return res
    return isinstance(other, GenRecFun) and self.name == other.name

  def reduce(self, env: object) -> Self:
    return self

  def substitute(self, sub: object) -> Self:
    return self

@dataclass
class ViewRecFun(Declaration):
  type_params: List[str]
  vars: List[Tuple[str,Type]]
  returns: Type
  view_name: str
  view_subject: Term
  cases: List[SwitchCase]

  def uniquify(self, env: object, ctx: object) -> ViewRecFun:
    env = cast(UniquifyEnv, env)
    ctx = cast(UniquifyContext, ctx)
    new_name = generate_name(self.name, ctx)
    extend(env, self.name, new_name, self.location)

    body_env = copy_dict(env)
    new_type_params = [generate_name(t, ctx) for t in self.type_params]
    for (old, new) in zip(self.type_params, new_type_params):
      extend(body_env, old, new, self.location)

    new_returns = self.returns.uniquify(body_env, ctx)
    new_var_types = [t.uniquify(body_env, ctx) if t else None
                     for (_, t) in self.vars]
    new_vars = cast(List[Tuple[str, Type]],
                    [(generate_name(x, ctx), nt)
                     for ((x, _), nt) in zip(self.vars, new_var_types)])
    for ((old, _), (new, _)) in zip(self.vars, new_vars):
      overwrite(body_env, old, new, self.location)

    def uniquify_case(c: SwitchCase) -> SwitchCase:
      case_env = copy_dict(body_env)
      pattern = c.pattern
      params = pattern.bindings()
      new_params = [generate_name(x, ctx) for x in params]
      for (old, new) in zip(params, new_params):
        case_env[old] = [new]
      new_pat = pattern.with_bindings(new_params).uniquify(case_env, ctx)
      new_body = c.body.uniquify(case_env, ctx)
      return SwitchCase(c.location, new_pat, new_body)

    if self.view_name not in env.keys():
      user_error(self.location, "undefined view " + self.view_name)
    if len(env[self.view_name]) != 1:
      user_error(self.location, "view names may not be overloaded: "
                 + self.view_name)
    new_view_name = env[self.view_name][0]
    new_view_subject = self.view_subject.uniquify(body_env, ctx)
    new_cases = [uniquify_case(c) for c in self.cases]
    return ViewRecFun(self.location, new_name, new_type_params,
                      new_vars, new_returns, new_view_name,
                      new_view_subject, new_cases,
                      visibility=self.visibility)

  _exports_overload = True

  def __str__(self) -> str:
    return self.name if get_unique_names() else base_name(self.name)

  def pretty_print(self, indent: int) -> str:
    header = complete_name(self.name) \
        + ('<' + ','.join([name2str(t) for t in self.type_params]) + '>' \
           if len(self.type_params) > 0 else '') \
      + '(' + ', '.join([base_name(x) + ':' + str(t) if t else x for (x,t) in self.vars])\
      + ') -> ' + str(self.returns)
    ret = self.visibility_prefix() + 'viewrec ' + header \
      + '\nview ' + base_name(self.view_name) \
      + '(' + str(self.view_subject) + ')\n' \
      + '\n'.join([c.pretty_print(indent+2)
                   for c in self.cases]) + '\n'
    return indent*' ' + ret

@dataclass
class ViewDecl(Declaration):
  type_params: List[str]
  source: Type
  target: Type
  into: str
  out: str
  roundtrip: str
  inverse: str | None = None

  def uniquify(self, env: object, ctx: object) -> ViewDecl:
    env = cast(UniquifyEnv, env)
    ctx = cast(UniquifyContext, ctx)
    if self.name in env.keys():
      user_error(self.location, "view names may not be overloaded")
    new_name = generate_name(self.name, ctx)
    env[self.name] = [new_name]
    env['no overload'][self.name] = 'view'

    body_env = copy_dict(env)
    new_type_params = [generate_name(t, ctx) for t in self.type_params]
    for (old, new) in zip(self.type_params, new_type_params):
      extend(body_env, old, new, self.location)

    def resolve_name(name: str, kind: str) -> str:
      if name not in env.keys():
        user_error(self.location, "undefined " + kind + " " + name)
      if len(env[name]) != 1:
        user_error(self.location, kind + " names may not be overloaded: "
                   + name)
      return cast(str, env[name][0])

    new_source = self.source.uniquify(body_env, ctx)
    new_target = self.target.uniquify(body_env, ctx)
    new_into = resolve_name(self.into, "view function")
    new_out = resolve_name(self.out, "view function")
    new_roundtrip = resolve_name(self.roundtrip, "proof")
    new_inverse = None if self.inverse is None \
      else resolve_name(self.inverse, "proof")
    return ViewDecl(self.location, new_name, new_type_params,
                    new_source, new_target, new_into, new_out,
                    new_roundtrip, new_inverse, visibility=self.visibility)

  _exports_overload = True

  def __str__(self) -> str:
    return self.name if get_unique_names() else base_name(self.name)

  def pretty_print(self, indent: int) -> str:
    header = complete_name(self.name) \
      + ('<' + ','.join([name2str(t) for t in self.type_params]) + '>' \
         if len(self.type_params) > 0 else '')
    # The view's own declaration names its underlying source type
    # (e.g. `source Binary`); suppress the source→view-name alias so
    # that line doesn't self-referentially print as `source UInt`.
    push_suppress_view_alias()
    try:
      source_str = str(self.source)
      target_str = str(self.target)
    finally:
      pop_suppress_view_alias()
    ret = self.visibility_prefix() + 'view ' + header + ' {\n' \
      + '  source ' + source_str + '\n' \
      + '  target ' + target_str + '\n' \
      + '  into ' + base_name(self.into) + '\n' \
      + '  out ' + base_name(self.out) + '\n' \
      + '  roundtrip ' + base_name(self.roundtrip) + '\n' \
      + ('' if self.inverse is None
         else '  inverse ' + base_name(self.inverse) + '\n') \
      + '}\n'
    return indent*' ' + ret

@dataclass
class Define(Declaration):
  typ: Optional[Type]
  body: Term

  def _can_use_fun_form(self) -> bool:
    # The `fun name(params) { body }` shape drops `self.typ`, so it
    # only round-trips when the user wrote no type annotation. Same
    # logic for the `fun name<T>(...)` (Generic) variant.
    if self.typ is not None:
      return False
    if isinstance(self.body, Lambda):
      return True
    if isinstance(self.body, Generic) and isinstance(self.body.body, Lambda):
      return True
    return False

  def __str__(self) -> str:
    prefix = self.visibility_prefix()
    if self._can_use_fun_form() and isinstance(self.body, Lambda):
        params = [(base_name(x), t) for (x,t) in self.body.vars]
        return prefix + pretty_print_function(self.name,[],params, self.body.body)
    elif self._can_use_fun_form() and isinstance(self.body, Generic):
        assert isinstance(self.body.body, Lambda)
        typarams = self.body.type_params
        params = [(base_name(x), t) for (x,t) in self.body.body.vars]
        return prefix + pretty_print_function(self.name, typarams, params,
                                              self.body.body.body)
    else:
        return prefix + 'define ' + complete_name(self.name) \
            + (' : ' + str(self.typ) if self.typ else '') \
            + ' = ' + self.body.pretty_print(4, False) + '\n'

  def uniquify(self, env: object, ctx: object) -> Define:
    env = cast(UniquifyEnv, env)
    ctx = cast(UniquifyContext, ctx)
    new_typ = self.typ.uniquify(env, ctx) if self.typ else None
    new_body = self.body.uniquify(env, ctx)

    new_name = generate_name(self.name, ctx)
    extend(env, self.name, new_name, self.location)
    return Define(self.location, new_name, new_typ, new_body,
                  visibility=self.visibility)

  _exports_overload = True

uniquified_modules: "dict[str, List[Statement]]" = {}

def get_uniquified_modules() -> "dict[str, List[Statement]]":
  global uniquified_modules
  return uniquified_modules

def add_uniquified_module(module_name: str, ast: "List[Statement]") -> None:
  global uniquified_modules
  uniquified_modules[module_name] = ast

def find_private_lemma_definers(name: str) -> list[tuple[str, str | None, int | None]]:
  """Return a list of (module, filename, line) tuples for every private
  `lemma` whose base name matches `name`. Used by `PVar.uniquify` to give
  a more specific error than "undefined proof variable" when a lookup
  fails because the matching definition was filtered out by
  `Theorem.collect_exports` (lemmas are module-private).

  The `module` field is the module declared by the file (one module can
  span several files — e.g., `lib/Nat.pf` and `lib/NatMult.pf` both
  declare `module Nat`); falls back to the import key for files with no
  `module` declaration. `filename` and `line` come from the `lemma`'s
  source location and may be `None` if the location is empty."""
  global uniquified_modules
  hits: list[tuple[str, str | None, int | None]] = []
  modules = cast(dict[str, List[Statement] | None], uniquified_modules)
  for import_key, ast in modules.items():
    if ast is None:
      continue
    declared_module = None
    matching_loc = None
    for stmt in ast:
      if isinstance(stmt, Module) and declared_module is None:
        declared_module = stmt.name
      if isinstance(stmt, Theorem) and stmt.isLemma \
         and base_name(stmt.name) == name and matching_loc is None:
        matching_loc = stmt.location
    if matching_loc is not None:
      reported = declared_module if declared_module is not None else import_key
      filename = cast(str | None, getattr(matching_loc, "filename", None)) \
        if not matching_loc.empty else None
      line = cast(int | None, getattr(matching_loc, "line", None)) \
        if not matching_loc.empty else None
      hits.append((reported, filename, line))
  return hits


@dataclass
class Assert(Statement):
  formula : Term

  def __str__(self) -> str:
    return 'assert ' + str(self.formula)

  def collect_exports(self, export_env: UniquifyEnv, importing_module: str) -> None:
    pass

@dataclass
class Print(Statement):
  term : Term

  def __str__(self) -> str:
    return 'print ' + str(self.term)

  def collect_exports(self, export_env: UniquifyEnv, importing_module: str) -> None:
    pass


def find_file(loc: Meta, name: str) -> str:
  for dir in get_import_directories():
    filename = os.path.join(dir, name + ".pf")
    if os.path.isfile(filename):
      return filename
  user_error(loc, 'could not find a file for import: ' + name)

def greatest_lower_bound(vis1: str, vis2: str) -> str:
    if vis1 == 'public':
        return vis2
    elif vis1 == 'private' or vis1 == 'default':
        return 'private'
    else:
        raise InternalError('in greatest_lower_bound: unknown visibility: ' + vis1)

def _stmt_primary_name(stmt: Statement) -> str | None:
  # The user-visible name to match against an import's using/hiding list,
  # or None for statements that don't export a name.
  name = getattr(stmt, 'name', None)
  if isinstance(name, str):
    return base_name(name)
  return None

@dataclass
class Import(Declaration):
  # `ast` is the parsed module body (a list of top-level Statements),
  # not a single AST node. The dataclass field is annotated as such so
  # downstream consumers (lower.py, the proof-checker's Import-arm
  # process_declaration loop) get the right narrowing.
  ast: Optional[List["Statement"]] = None
  using:  Optional[List[str]] = None    # whitelist; None means no whitelist
  hiding: Optional[List[str]] = None    # blacklist; None means no blacklist

  def _filter_clause_str(self) -> str:
    # Operator names are stored bare (`≲`), but the parser only accepts
    # them in a using/hiding list behind the `operator` keyword, so print
    # them with `complete_name` to keep the clause reparseable.
    if self.using is not None:
      return ' using ' + ' | '.join(complete_name(n) for n in self.using)
    if self.hiding is not None:
      return ' hiding ' + ' | '.join(complete_name(n) for n in self.hiding)
    return ''

  def __str__(self) -> str:
    prefix = 'public ' if self.visibility == 'public' else ''
    return prefix + 'import ' + self.name + self._filter_clause_str()

  def pretty_print(self, indent: int) -> str:
    return indent*' '  + str(self) + '\n'

  def _filter_admits(self, stmt: Statement) -> bool:
    using = self.using
    hiding = self.hiding
    if using is None and hiding is None:
      return True
    name = _stmt_primary_name(stmt)
    if name is None:
      return True
    if using is not None:
      return name in using
    return name not in cast(List[str], hiding)

  def _validate_filter(self, new_ast: List[Statement],
                       importing_module: str) -> None:
    if self.using is None and self.hiding is None:
      return
    # Build the set of names actually exported to the importing module by
    # replaying collect_exports over the module body. A statement's primary
    # name counts only when that statement contributes at least one visible
    # name to the importer, so private (non-exported) declarations are
    # rejected the same way an unknown name is. `module`/`import` statements
    # thread the current-module context exactly as the real export loop does,
    # so we restore it before returning.
    saved_module = get_current_module()
    exported: set[str] = set()
    for s in new_ast:
      name = _stmt_primary_name(s)
      probe: UniquifyEnv = {'no overload': {}}
      s.collect_exports(probe, importing_module)
      if name is not None and any(
          k != 'no overload' and not k.startswith('__module__') for k in probe):
        exported.add(name)
    set_current_module(saved_module)
    requested = self.using if self.using is not None else self.hiding
    assert requested is not None
    for name in requested:
      if name not in exported:
        clause = 'using' if self.using is not None else 'hiding'
        user_error(self.location,
                   "import " + clause + ": '" + name
                   + "' is not exported by module '" + self.name + "'")

  def uniquify(self, env: object, ctx: object) -> Import:
    env = cast(UniquifyEnv, env)
    ctx = cast(UniquifyContext, ctx)
    importing_module = get_current_module()
    set_current_module(self.name)
    if get_verbose():
      print('uniquify import ' + self.name + ' ==> ' + importing_module + '\n')
    old_verbose = get_verbose()
    if get_verbose() == VerboseLevel.CURR_ONLY:
      set_verbose(VerboseLevel.NONE)

    # Restore the module/verbose globals even if an error (e.g. a bad
    # using/hiding filter) aborts the import, so a later top-level check
    # sharing this process does not inherit a stale current module.
    try:
      global uniquified_modules
      if self.name in uniquified_modules.keys():
        new_ast = uniquified_modules[self.name]
      else:
        filename = find_file(self.location, self.name)
        file = open(filename, 'r', encoding="utf-8")
        src = file.read()
        file.close()
        if get_recursive_descent():
          from rec_desc_parser import get_filename, set_filename, parse
        else:
          from parser import get_filename, set_filename, parse
        old_filename = get_filename()
        set_filename(filename)
        parsed_ast = parse(src, trace=False)
        set_filename(old_filename)
        new_ast = uniquify_deduce(parsed_ast, ctx)
        uniquified_modules[self.name] = new_ast

      env['__module__' + self.name] = None
      if get_verbose():
          print('collecting exports from ' + self.name + ' for import to ' + importing_module + '\n')
      self._validate_filter(new_ast, importing_module)
      for stmt in new_ast:
        if self._filter_admits(stmt):
          stmt.collect_exports(env, importing_module)
      if get_verbose():
        print('\tuniquify finished import ' + self.name)
    finally:
      set_verbose(old_verbose)
      set_current_module(importing_module)
    return Import(self.location, self.name, new_ast,
                  visibility=self.visibility,
                  using=self.using, hiding=self.hiding)

  def collect_exports(self, export_env: UniquifyEnv, importing_module: str) -> None:
    module_name = '__module__' + self.name
    if self.visibility == 'public' and not (module_name in export_env.keys()):
      set_current_module(self.name)
      export_env[module_name] = None
      for stmt in cast(List[Statement], self.ast):
        if self._filter_admits(stmt):
          stmt.collect_exports(export_env, importing_module)
      set_current_module(importing_module)

@dataclass
class Auto(Statement):
  name: Term

  def key(self) -> str:
      return str(self.name)

  def print_theorems_statement(self, f: TextIO) -> None:
      print('auto ' + str(self.name) + '\n', file=f)

  def __str__(self) -> str:
    return 'auto ' + str(self.name)

  def collect_exports(self, export_env: UniquifyEnv, importing_module: str) -> None:
    pass

@dataclass
class Inductive(Statement):
  typ: Type
  thm_name: Term

  def __str__(self) -> str:
    return 'inductive ' + str(self.typ) + ' by ' + str(self.thm_name)

  def collect_exports(self, export_env: UniquifyEnv, importing_module: str) -> None:
    pass


@dataclass
class Module(Statement):
  name: str

  def pretty_print(self, indent: int) -> str:
      return indent*' ' + 'module ' + self.name + '\n'
  
  def uniquify(self, env: UniquifyEnv, ctx: UniquifyContext) -> Module:
      set_current_module(self.name)
      return Module(self.location, self.name)

  def collect_exports(self, export_env: UniquifyEnv, importing_module: str) -> None:
      set_current_module(self.name)

@dataclass
class Export(Statement):
  name: str
  resolved_names: list[str] = field(default_factory=list)

  def pretty_print(self, indent: int) -> str:
      return indent*' ' + 'export ' + self.name + '\n'
  
  def uniquify(self, env: UniquifyEnv, ctx: UniquifyContext) -> Export:
      return Export(self.location, self.name, env[self.name])

  def collect_exports(self, export_env: UniquifyEnv, importing_module: str) -> None:
      for x in self.resolved_names:
          extend(export_env, base_name(x), x, self.location)
      
@dataclass
class Associative(Statement):
  type_params: List[str]
  op: Term
  typeof: Type

  def __str__(self) -> str:
    op_name = complete_name(self.op.get_name()) if isinstance(self.op, VarRef) else str(self.op)
    type_params = ' <' + ','.join(self.type_params) + '>' if len(self.type_params) > 0 else ''
    return 'associative ' + op_name + type_params + ' in ' + str(self.typeof)

  def uniquify(self, env: UniquifyEnv, ctx: UniquifyContext) -> Associative:
    new_op = self.op.uniquify(env, ctx)
    body_env = {x:y for (x,y) in env.items()}
    new_type_params = [generate_name(x, ctx) for x in self.type_params]
    for (old, new) in zip(self.type_params, new_type_params):
      overwrite(body_env, old, new, self.location)
    new_typeof = self.typeof.uniquify(body_env, ctx)
    return Associative(self.location, new_type_params, new_op, new_typeof)

  def collect_exports(self, export_env: UniquifyEnv, importing_module: str) -> None:
    opname = cast(VarRef, self.op).get_name()
    full_name = '__associative_' + opname
    base = base_name(opname)
    full_base_name = '__associative_' + base
    export_env[full_base_name] = [full_name]

@dataclass
class Trace(Statement):
  rec_fun: Var

  def __str__(self) -> str:
    return 'trace ' + str(self.rec_fun)

  def reduce(self, env: Env) -> None:  # type: ignore[override]
    # Side-effecting: drives the runtime trace flag via `Var.reduce`'s
    # env-lookup path. Returns None on purpose; the default
    # `_map_children`-based `reduce` would build a fresh Trace node,
    # which is not what callers want here.
    reduce_rec_fun = cast(Callable[[Env], object], self.rec_fun.reduce)
    reduce_rec_fun(env)


################################################################################

# Back-pointers from a predicate's uniquified name to its Predicate AST
# node. Populated during Predicate.uniquify and read by the proof checker
# when desugaring `rule induction`. Persisted across check_deduce
# invocations because uniquify happens once per file.
_predicate_decls_by_unique_name: dict[str, Predicate] = {}

def get_predicate_decl(unique_name:str) -> Predicate | None:
  return _predicate_decls_by_unique_name.get(unique_name)
