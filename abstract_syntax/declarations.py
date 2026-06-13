"""Concrete top-level ``Statement`` nodes — the declarations of a module.

Scope: every dataclass node that can appear at the top level of a ``.pf``
file, together with the bookkeeping that supports them across imports.
This covers the ``Declaration`` family (``Theorem``, ``Postulate``,
``Predicate``, ``Union``, ``TypeAlias``, ``RecFun``, ``GenRecFun``, ``ViewRecFun``,
``ViewDecl``, ``Define``, ``Import``) and the non-``Declaration``
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

from typing import TYPE_CHECKING

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

  def collect_exports(
      self,
      export_env: UniquifyEnv,
      importing_module: str,
  ) -> None:
    if self.visibility == 'private' and importing_module != get_current_module():
      return
    export_env[base_name(self.name)] = [self.name]
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

  def collect_exports(
      self,
      export_env: UniquifyEnv,
      importing_module: str,
  ) -> None:
    if self.visibility == 'private' and importing_module != get_current_module():
      return
    export_env[base_name(self.name)] = [self.name]

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

  def collect_exports(
      self,
      export_env: UniquifyEnv,
      importing_module: str,
  ) -> None:
    if self.visibility == 'private' and importing_module != get_current_module():
      return
    export_env[base_name(self.name)] = [self.name]

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
      
  def collect_exports(
      self,
      export_env: UniquifyEnv,
      importing_module: str,
  ) -> None:
    if self.visibility == 'private' and importing_module != get_current_module():
      return
    extend(export_env, base_name(self.name), self.name, self.location)

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
    if isinstance(other, ResolvedVar):
      return self.name == other.name
    elif isinstance(other, OverloadedVar):
      return self.name == other.resolved_names[0]
    elif isinstance(other, Var):
      return self.name == other.name
    elif isinstance(other, TermInst):
      return self == other.subject
    elif isinstance(other, RecFun):
      return self.name == other.name
    else:
      return False

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
    
  def collect_exports(
      self,
      export_env: UniquifyEnv,
      importing_module: str,
  ) -> None:
    if self.visibility == 'private' and (importing_module != get_current_module()):
      return
    extend(export_env, base_name(self.name), self.name, self.location)

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
    if isinstance(other, ResolvedVar):
      return self.name == other.name
    elif isinstance(other, OverloadedVar):
      return self.name == other.resolved_names[0]
    elif isinstance(other, Var):
      return self.name == other.name
    elif isinstance(other, TermInst):
      return self == other.subject
    elif isinstance(other, GenRecFun):
      return self.name == other.name
    else:
      return False
  
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

  def collect_exports(self, export_env: UniquifyEnv, importing_module: str) -> None:
    if self.visibility == 'private' and (importing_module != get_current_module()):
      return
    extend(export_env, base_name(self.name), self.name, self.location)

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

  def collect_exports(self, export_env: UniquifyEnv, importing_module: str) -> None:
    if self.visibility == 'private' and (importing_module != get_current_module()):
      return
    extend(export_env, base_name(self.name), self.name, self.location)

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

  def collect_exports(self, export_env: UniquifyEnv, importing_module: str) -> None:
    if self.visibility == 'private' and (importing_module != get_current_module()):
      return
    extend(export_env, base_name(self.name), self.name, self.location)

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
    if self.using is not None:
      return ' using ' + ' | '.join(self.using)
    if self.hiding is not None:
      return ' hiding ' + ' | '.join(self.hiding)
    return ''

  def __str__(self) -> str:
    return 'import ' + self.name + self._filter_clause_str()

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

  def _validate_filter(self, new_ast: List[Statement]) -> None:
    if self.using is None and self.hiding is None:
      return
    exported = {n for n in (_stmt_primary_name(s) for s in new_ast) if n is not None}
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
    self._validate_filter(new_ast)
    for stmt in new_ast:
      if self._filter_admits(stmt):
        stmt.collect_exports(env, importing_module)
    set_verbose(old_verbose)
    if get_verbose():
      print('\tuniquify finished import ' + self.name)
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
