from __future__ import annotations

from dataclasses import dataclass, field, fields as dc_fields
from lark.tree import Meta
from typing import Any, Callable, Iterator, Tuple, List, Optional, Protocol, Set, Self, overload, TextIO, Sequence, cast, no_type_check
from error import (
    InternalError,
    MatchFailed,
    UserError,
    internal_error,
    match_failed,
    static_error,
    user_error,
    warning,
)
from flags import (
    VerboseLevel,
    add_import_directory as add_import_directory,
    get_debugger,
    get_import_directories,
    get_recursive_descent as get_recursive_descent,
    get_unique_names,
    get_verbose,
    init_import_directories as init_import_directories,
    set_check_imports as set_check_imports,
    set_recursive_descent as set_recursive_descent,
    set_verbose,
)
from pathlib import Path
from edit_distance import edit_distance
from math import ceil
import os

infix_precedence = {'+': 6, '-': 6, '∸': 6, '⊝': 6, '*': 7, '/': 7, '%': 7,
                    '=': 1, '<': 1, '≤': 1, '≥': 1, '>': 1, 'and': 2, 'or': 3,
                    '≲': 1, '≈': 1,
                    '++': 6, '⨄': 6, '∈':1, '∪':6, '∩':6, '⊆': 1, '⇔': 2,
                    '∘': 7, '^' : 8}
prefix_precedence = {'-': 9, 'not': 4}
recursion_depth = 0

def name2str(s: str) -> str:
    if get_unique_names():
        return s
    else:
        return base_name(s)

# current_module is used during uniquify and collect_exports
current_module = 'none'

def get_current_module() -> str:
    global current_module
    return current_module

def set_current_module(name: str) -> None:
    global current_module
    current_module = name

############ AST Base Classes ###########

@dataclass
class AST:
  location: Meta

  # Field names that the default `_map_children` walker leaves alone.
  # `location` is opaque source-position metadata. `Term` extends this
  # with `'typeof'` because the cached type annotation is rewritten only
  # by `substitute` (via the `on_typeof` hook), not by `copy` /
  # `uniquify` / `reduce`.
  _NON_STRUCTURAL_FIELDS = frozenset({'location'})

  def _map_children(
      self,
      f: Callable[[AST], AST],
      *,
      on_typeof: Callable[[Optional[Type]], Optional[Type]] | None = None,
  ) -> Self:
    # Return a fresh instance of the same class with `f` applied to
    # every AST-typed value in every structural field. Lists and tuples
    # are walked element-wise; non-AST scalars (strings, ints, bools)
    # pass through. The `on_typeof` hook lets `substitute` rewrite the
    # otherwise non-structural `typeof` field via `subst_typeof`.
    # The trailing loop preserves any non-dataclass attribute attached
    # to `self` after construction. New post-hoc attributes are
    # discouraged — declare an `Optional[...]` field on the dataclass
    # instead (see issue #480) — but the loop is kept as a safety net.
    cls = cast(Any, type(self))
    non_struct = cls._NON_STRUCTURAL_FIELDS
    new_args: dict[str, object] = {}
    field_names = set()
    for fld in dc_fields(self):
      field_names.add(fld.name)
      val = getattr(self, fld.name)
      if fld.name == 'typeof' and on_typeof is not None:
        new_args['typeof'] = on_typeof(val)
      elif fld.name in non_struct:
        new_args[fld.name] = val
      else:
        new_args[fld.name] = _ast_map(val, f)
    new_obj: Self = cls(**new_args)
    for k, v in self.__dict__.items():
      if k not in field_names:
        setattr(new_obj, k, v)
    return new_obj

  def copy(self) -> Self:
    return self._map_children(lambda x: x.copy())

  def uniquify(self, env: dict[str, Any], ctx: UniquifyContext) -> Self:
    return self._map_children(lambda x: x.uniquify(env, ctx))

  def substitute(self, sub: object) -> Self:
    return self._map_children(lambda x: x.substitute(sub))

  def reduce(self, env: object) -> Self:
    return self._map_children(lambda x: x.reduce(env))

def _ast_map(value: object, f: Callable[[AST], AST]) -> object:
  # Apply `f` to AST-typed values inside a field value, preserving
  # list / tuple structure. Non-AST scalars (str, int, bool, None) are
  # returned unchanged. Used by `AST._map_children` to walk dataclass
  # fields uniformly.
  if value is None:
    return None
  if isinstance(value, AST):
    return f(value)
  if isinstance(value, list):
    return [_ast_map(v, f) for v in value]
  if isinstance(value, tuple):
    return tuple(_ast_map(v, f) for v in value)
  return value


@dataclass
class Type(AST):

  def free_vars(self) -> Set[str]:
    internal_error(self.location, 'free_vars not implemented')


@dataclass
class Term(AST):
  typeof: Optional[Type]

  _NON_STRUCTURAL_FIELDS = frozenset({'location', 'typeof'})

  def subst_typeof(self, sub: object) -> Optional[Type]:
    # Apply `sub` to the cached `typeof` annotation. Kept as a named
    # helper because a handful of bespoke `substitute` methods (Var,
    # OverloadedVar, ResolvedVar) call it directly to short-circuit
    # when the annotation didn't actually change.
    return self.typeof.substitute(sub) if self.typeof is not None else None

  def substitute(self, sub: object) -> Self:
    return self._map_children(
      lambda x: x.substitute(sub),
      on_typeof=lambda t: t.substitute(sub) if t is not None else None,
    )

  def pretty_print(self, indent: int, afterNewline: bool = False) -> str:
      if afterNewline:
          return indent*' ' + str(self)
      else:
          return str(self)

@dataclass
class Formula(Term):
  pass

@dataclass
class Proof(AST):

  def pretty_print(self, indent: int) -> str:
      return str(self)

@dataclass
class Statement(AST):

  def pretty_print(self, indent: int) -> str:
      return str(self)

class TheoremFilePrinting(Protocol):
  def key(self) -> str: ...

  def print_theorems_statement(self, f: TextIO) -> None: ...

################ Miscellaneous Functions #####################

def copy_dict[T](d: dict[str, T]) -> dict[str, T]:
  return {k: v for k, v in d.items()}


def maybe_str(o: Optional[str], default: str = '') -> str:
  return str(o) if o is not None else default

def maybe_pretty_print(o: Optional["Proof"], indent: int, default: str = '') -> str:
  return o.pretty_print(indent) if o is not None else default

class UniquifyContext:
  """Mutable state threaded through an ``uniquify_deduce`` call.

  Holds two pieces of state for fresh-name allocation:

  * ``name_id`` -- a counter that increments on every ``generate_name``.
  * ``scope`` -- a string prepended to the counter when forming the
    name suffix.  ``uniquify_deduce`` resets ``name_id`` and pushes a
    per-statement segment onto ``scope`` at each top-level statement,
    so two top-level statements get *disjoint* suffix spaces and an
    edit confined to statement N can no longer shift statement N+1's
    bound-name suffixes.  Without this, Step 14's dependency-aware
    invalidation never gets to fire -- the structural hash of an
    unrelated downstream statement would change as a side-effect of
    counter drift.

  Two uniquify runs with the same input AST and a fresh
  ``UniquifyContext`` each produce byte-equal output -- that's the
  acceptance for Step 12 of ``docs/lsp-plan.md`` and the foundation
  Step 13's caching needs.
  """

  def __init__(self, name_id: int = 0, scope: str = ""):
    self.name_id = name_id
    self.scope = scope

  def snapshot(self) -> "UniquifyContext":
    """Return a fresh context with the same counter and scope.

    Used by the LSP pipeline to fork off a per-user-file context
    from the post-prelude baseline, so each user-file check starts
    from the same counter state and produces reproducible names.
    """
    return UniquifyContext(name_id=self.name_id, scope=self.scope)


def generate_name(name: str, ctx: UniquifyContext) -> str:
  base = name.split('.')[0]
  new_id = ctx.name_id
  ctx.name_id += 1
  return base + '.' + ctx.scope + str(new_id)


def base_name(name: str) -> str:
  ls = name.split('.')
  return ls[0]

def type_names(loc: Meta, names: List[str]) -> list[ResolvedVar]:
  index = 0
  result: List["ResolvedVar"] = []
  for n in reversed(names):
    result.insert(0, ResolvedVar(loc, None, n))
    index += 1
  return result


def type_match(
    loc: Meta,
    tyvars: Sequence[VarRef | str],
    param_ty: Type | VarRef | None,
    arg_ty: Type | VarRef | None,
    matching: dict[str, Type | VarRef | None],
) -> None:
  if get_verbose():
    print("type_match(" + str(param_ty) + "," + str(arg_ty) + ")")
    print("\tin  " + ', '.join([str(x) for x in tyvars]))
    print("\twith " + str(matching))
  # `param_ty` may be a tyvar reference encoded as either an
  # OverloadedVar (if it came straight from uniquify) or a ResolvedVar
  # (if a prior narrowing has already occurred). `get_name()` gives us
  # the canonical identifier in both cases.
  if isinstance(param_ty, VarRef) and param_ty in tyvars:
    tyvar_name = param_ty.get_name()
    if tyvar_name in matching.keys():
      if matching[tyvar_name] == arg_ty:
        return
      else:
        type_match(loc, tyvars, matching[tyvar_name], arg_ty, matching)
    else:
      if get_verbose():
        print('matching ' + tyvar_name + ' := ' + str(arg_ty))
      matching[tyvar_name] = arg_ty
    return
  if isinstance(param_ty, VarRef) and isinstance(arg_ty, VarRef) \
     and param_ty.get_name() == arg_ty.get_name():
    return
  match (param_ty, arg_ty):
    case (FunctionType(_, tv1, pts1, rt1), FunctionType(_, tv2, pts2, rt2)) \
      if len(tv1) == len(tv2) and len(pts1) == len(pts2):
      for (pt1, pt2) in zip(pts1, pts2):
        type_match(loc, tyvars, pt1, pt2, matching)
      type_match(loc, tyvars, rt1, rt2, matching)
    case (TypeInst(_, n1, args1), TypeInst(_, n2, args2)):
      if n1 != n2 or len(args1) != len(args2):
        match_failed(loc, str(arg_ty) + " does not match " + str(param_ty))
      for (arg1, arg2) in zip(args1, args2):
        type_match(loc, tyvars, arg1, arg2, matching)
    # How to handle GenericUnknownInst?
    case (TypeInst(_, n1, args1), GenericUnknownInst(_, n2)):
      if n1 != n2:
        match_failed(loc, str(arg_ty) + " does not match " + str(param_ty))
    case _:
      if param_ty != arg_ty:
        match_failed(loc, str(arg_ty) + " does not match " + str(param_ty))


def is_associative(loc: Meta, opname: str, typ: Type | None, env: Env) -> bool:
  for (typarams, ty) in env.get_assoc_types(opname):
    type_params = type_names(loc, typarams)
    matching: dict[str, Type | VarRef | None] = {}
    try:
      type_match(loc, type_params, ty, typ, matching)
      return True
    except MatchFailed:
      pass
  return False

def named_callable_name(t: VarRef | RecFun | GenRecFun) -> str:
  if isinstance(t, VarRef):
    return t.get_name()
  return t.name


def callable_name(t: Term | RecFun | GenRecFun) -> str | None:
  if isinstance(t, VarRef | RecFun | GenRecFun):
    return named_callable_name(t)
  match t:
    case TermInst(_, _, subject, _, _):
      return callable_name(subject)
    case _:
      return None


def flatten_assoc(op_name: str, trm: Term) -> list[Term]:
  match trm:
    case Call(_, _, rator, args) if callable_name(rator) == op_name:
      return sum([flatten_assoc(op_name, arg) for arg in args], [])
    case _:
      return [trm]


def flatten_assoc_list(op_name: str, args: Sequence[Term]) -> list[Term]:
  return sum([flatten_assoc(op_name, arg) for arg in args], [])


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

################ Types ######################################

@dataclass
class IntType(Type):

  def __str__(self):
    return 'int'

  def __eq__(self, other: object) -> bool:
    return isinstance(other, IntType)

  def free_vars(self) -> Set[str]:
    return set()

@dataclass
class BoolType(Type):

  def __str__(self):
    return 'bool'

  def __eq__(self, other: object) -> bool:
    return isinstance(other, BoolType)

  def free_vars(self):
    return set()

@dataclass
class TypeType(Type):

  def __str__(self):
    return 'type'

  def __eq__(self, other: object) -> bool:
    return isinstance(other, TypeType)

  def free_vars(self):
    return set()

@dataclass
class OverloadType(Type):
  types: List[Tuple[str,Type]]

  def __str__(self):
    return '(' + ' & '.join([base_name(x) + ': ' + str(ty) \
                             for (x,ty) in self.types]) + ')'

  def __eq__(self, other: object) -> bool:
    match other:
      case OverloadType(_, types2):
        ret = True
        for ((x,t1), (y,t2)) in zip(self.types, types2):
          ret = ret and t1 == t2
        return ret
      case _:
        return False

  def free_vars(self):
    fvs = [t.free_vars() for (x,t) in self.types]
    return set().union(*fvs)


@dataclass
class FunctionType(Type):
  type_params: List[str]
  param_types: List[Type]
  return_type: Type

  def __str__(self):
    if len(self.type_params) > 0:
      typarams = '<' + ','.join([(x if get_verbose() else base_name(x)) for x in self.type_params]) + '> '
    else:
      typarams = ''
    return '(' + 'fn ' + typarams + ', '.join([str(ty) for ty in self.param_types]) \
      + ' -> ' + str(self.return_type) + ')'

  def __eq__(self, other: object) -> bool:
    if not isinstance(other, FunctionType):
      return False
    return _alpha_equiv_function_type(self, other, {}, {})

  def free_vars(self):
    fvs = [pt.free_vars() for pt in self.param_types] \
      + [self.return_type.free_vars()]
    return set().union(*fvs) - set(self.type_params)

  def uniquify(self, env: dict[str, Any], ctx: UniquifyContext) -> FunctionType:
    body_env = {x:y for (x,y) in env.items()}
    new_type_params = [generate_name(t, ctx) for t in self.type_params]
    for (old,new) in zip(self.type_params, new_type_params):
      overwrite(body_env, old, new, self.location)
    new_param_types = [p.uniquify(body_env, ctx) for p in self.param_types]
    new_return_type = self.return_type.uniquify(body_env, ctx)
    return FunctionType(self.location, new_type_params,
                        new_param_types, new_return_type)

@dataclass
class ArrayType(Type):
  elt_type: Type

  def __str__(self):
    return '[' + str(self.elt_type) + ']'

  def __eq__(self, other: object) -> bool:
    match other:
      case ArrayType(_, elt_type):
        return self.elt_type == elt_type
      case _:
        return False

  def free_vars(self):
    return self.elt_type.free_vars()

@dataclass
class TypeInst(Type):
  typ: Type
  arg_types: List[Type]

  def __str__(self):
    return str(self.typ) + \
      '<' + ','.join([str(arg) for arg in self.arg_types]) + '>'

  def __eq__(self, other: object) -> bool:
    match other:
      case TypeInst(_, typ, arg_types):
        return self.typ == typ and \
          all([t1 == t2 for (t1, t2) in zip(self.arg_types, arg_types)])
      # case GenericUnknownInst(loc, typ):
      #   return self.typ == typ
      case _:
        return False

  def free_vars(self):
    return set().union(*[at.free_vars() for at in self.arg_types])

# This is the type of a constructor such as 'empty' of a generic union
# when we do not yet know the type arguments.
@dataclass
class GenericUnknownInst(Type):
  typ: Type

  def __str__(self):
    return str(self.typ) + '<?>'

  def __eq__(self, other: object) -> bool:
    match other:
      # case TypeInst(l, typ, arg_types):
      #   return self.typ == typ
      case GenericUnknownInst(_, typ):
        return self.typ == typ
      case _:
        return False

  def free_vars(self):
    return set()

  # The inner `typ` is the bare constructor name from a generic union
  # whose type arguments haven't been resolved yet -- substituting
  # through it would mistake the constructor for a substitutable
  # variable. Hand-roll a no-op `substitute` to override the default.
  def substitute(self, sub: object) -> Self:
    return self

def get_type_name(ty: Type) -> Type:
  if isinstance(ty, VarRef):
    return ty
  match ty:
    case TypeInst(_, ty, _):
      return get_type_name(ty)
    case _:
      raise InternalError('unhandled case in get_type_name: ' + repr(ty))
  
################ Patterns ######################################

@dataclass
class Pattern(AST):
  # Patterns are leaves from `substitute`/`reduce`'s point of view: the
  # constructor name they carry is a binding occurrence used for
  # matching, not a variable reference to be rewritten. Compound nodes
  # (`SwitchCase`, `IndCase`, `FunCase`) call `with_bindings` to
  # rename pattern parameters during uniquify.
  def substitute(self, sub: object) -> Self:
    return self

  def reduce(self, env: Env) -> Self:  # type: ignore[override]
    return self

@dataclass
class PatternBool(Pattern):
  value : bool

  def __str__(self):
      return "true" if self.value else "false"

  def bindings(self):
    return []

  def with_bindings(self, new_bindings: list[str]) -> PatternBool:
    return self

@dataclass
class PatternCons(Pattern):
  constructor : Term         # typically a Var
  parameters : List[str]

  def bindings(self):
    return self.parameters

  def with_bindings(self, params: list[str]) -> PatternCons:
    return PatternCons(self.location, self.constructor, params)

  def __str__(self):
      if len(self.parameters) > 0:
        return str(self.constructor) \
          + '(' + ', '.join([base_name(p) for p in self.parameters]) + ')'
      else:
        return str(self.constructor)

@dataclass
class PatternTerm(Pattern):
  term: Term
  parameters: list[str]

  def bindings(self):
    return self.parameters

  def with_bindings(self, params: list[str]) -> PatternTerm:
    return PatternTerm(self.location, self.term, params)

  def __str__(self):
    return str(self.term)
    
################ Terms ######################################

@dataclass
class Generic(Term):
  type_params: List[str]
  body: Term

  def __str__(self):
    return "generic " + ",".join([(t if get_verbose() else base_name(t)) for t in self.type_params]) \
      + " { " + str(self.body) + " }"

  def pretty_print(self, indent: int, afterNewline: bool = False) -> str:
    return (indent*' ' if afterNewline else '') \
        + 'generic ' + ', '.join([(t if get_verbose() else base_name(t)) for t in self.type_params]) \
      + ' {\n' + self.body.pretty_print(indent+2, True) + '\n' \
      + indent*' ' + '}'

  def __eq__(self, other: object) -> bool:
      if not isinstance(other, Generic):
          return False
      ren = {x: ResolvedVar(self.location, None, y) \
             for (x,y) in zip(self.type_params, other.type_params) }
      new_body = self.body.substitute(ren)
      return new_body == other.body

  def uniquify(self, env: dict[str, Any], ctx: UniquifyContext) -> Generic:
    body_env = {x:y for (x,y) in env.items()}
    new_type_params = [generate_name(x, ctx) for x in self.type_params]
    for (old,new) in zip(self.type_params, new_type_params):
      overwrite(body_env, old, new, self.location)
    return Generic(self.location, self.typeof, new_type_params,
                   self.body.uniquify(body_env, ctx))


@dataclass
class Conditional(Term):
  cond: Term
  thn: Term
  els: Term

  def __str__(self):
      return '(if ' + str(self.cond) \
        + ' then ' + str(self.thn) \
        + ' else ' + str(self.els) + ')'

  def pretty_print(self, indent: int, afterNewline: bool = False) -> str:
      return ('' if afterNewline else '\n') + indent*' ' + 'if ' + str(self.cond) + ' then\n' \
          + self.thn.pretty_print(indent+2, True) + '\n'\
          + indent*' ' + 'else\n' \
          + self.els.pretty_print(indent+2, True)

  def __eq__(self, other: object) -> bool:
    if not isinstance(other, Conditional):
      return False
    return self.cond == other.cond and self.thn == other.thn and self.els == other.els

  def reduce(self, env: Env) -> Term:  # type: ignore[override]
     cond = self.cond.reduce(env)
     if get_reduce_all():   # Does this work? Need to test!
         match cond:
           case Bool(_, _, True):
             return self.thn.reduce(env)
           case Bool(_, _, False):
             return self.els.reduce(env)
           case _:
             return Conditional(self.location, self.typeof, cond, self.thn, self.els)
     else:
         thn = self.thn.reduce(env)
         els = self.els.reduce(env)
         match cond:
           case Bool(_, _, True):
             return thn
           case Bool(_, _, False):
             return els
           case _:
             return Conditional(self.location, self.typeof, cond, thn, els)


@dataclass
class TAnnote(Term):
  subject: Term
  typ: Type

  def __str__(self):
      return str(self.subject) + ':' + str(self.typ)

  def reduce(self, env: Env) -> Term:  # type: ignore[override]
    return self.subject.reduce(env)

  def __eq__(self, other: object) -> bool:
    if isinstance(other, TAnnote):
      return self.subject == other.subject
    return self.subject == other


@dataclass
class VarRef(Term):
  # Abstract base for variable references. Concrete subclasses are
  # `Var` (post-parse, holds a source identifier) and `OverloadedVar`
  # (post-uniquify, holds uniquified candidate names). Code that wants
  # to operate on either variant should `isinstance(node, VarRef)` and
  # call `get_name()` rather than reach for a `name` field — the two
  # subclasses store names differently on purpose.
  def get_name(self) -> str:
    internal_error(self.location, 'get_name not implemented on VarRef base')

  def free_vars(self):
    return {self.get_name()}

  def operator_str(self):
    return name2str(self.get_name())


@dataclass
class Var(VarRef):
  # A source-level variable reference, before name resolution.
  # `name` is the identifier as written by the user. After uniquify
  # this node is replaced by `OverloadedVar`, which carries the
  # uniquified candidate names and is what the rest of the pipeline
  # operates on.
  name: str

  def get_name(self):
    return self.name

  def copy(self):
    return Var(self.location, self.typeof, self.name)

  def __eq__(self, other: object) -> bool:
      if isinstance(other, OverloadedVar):
        # Pre- and post-uniquify references are not interchangeable.
        return False
      elif isinstance(other, RecFun):
        result = self.name == other.name
      elif isinstance(other, GenRecFun):
        result = self.name == other.name
      elif isinstance(other, TermInst):
        result = self == other.subject
      elif isinstance(other, TAnnote):
        result = self == other.subject
      elif not isinstance(other, Var):
        result = False
      else:
        result = self.name == other.name
      return result

  def __str__(self):
      if base_name(self.name) == 'empty' and not get_unique_names() and not get_verbose():
          return '[]'
      elif get_unique_names():
        return name2str(self.name) + '{}'
      elif is_var_operator(self):
        return 'operator ' + name2str(self.name)
      else:
        return name2str(self.name)

  def reduce(self, env: Env) -> Self:  # type: ignore[override]
      # Pre-uniquify Vars don't appear in the runtime environment, so
      # they reduce to themselves. The post-uniquify form is
      # `OverloadedVar`, which has its own reduce.
      return self

  def substitute(self, sub: dict[str, Any]) -> Any:  # type: ignore[override]
      if self.name in sub:
          trm = sub[self.name]
          if not isinstance(trm, RecFun) and not isinstance(trm, GenRecFun):
            add_reduced_def(self.name)
          return trm
      else:
          new_typeof = self.subst_typeof(sub)
          if new_typeof is self.typeof:
            return self
          return Var(self.location, new_typeof, self.name)

  def uniquify(self, env: dict[str, Any], ctx: UniquifyContext) -> OverloadedVar:  # type: ignore[override]
    if self.name not in env.keys():
      if get_verbose():
        env_str = '\nenvironment: ' + ', '.join(env.keys())
      else:
        env_str = ''

      import_advice = ''

      if self.name == "suc" or self.name == "zero" or self.name == "lit":
        import_advice = "\n\tAdd `import Nat` to use natural numbers."
      elif self.name == "empty" or self.name == "node":
        import_advice = "\n\tAdd `import List` to use lists."
      elif self.name == "bzero" or self.name == "dub_inc" or self.name == "inc_dub" or self.name == "fromNat":
        import_advice = "\n\tAdd `import UInt` to use unsigned integers."
      if import_advice != '':
          static_error(self.location, import_advice)

      close_matches = []
      for var in env.keys():
        if edit_distance(self.name, var) <= ceil(len(self.name) / 5):
          close_matches.append(var)
      if len(close_matches) > 0:
        mispell_advice = '\n\tdid you intend: ' + ', '.join(close_matches) + '\n'
      else:
        mispell_advice = ''
      static_error(self.location, 'undefined variable: ' + self.name \
                   + mispell_advice + '' + env_str)

    return OverloadedVar(self.location, self.typeof, env[self.name])


@dataclass
class OverloadedVar(VarRef):
  # A variable reference after uniquify. `resolved_names` is the
  # non-empty list of uniquified candidate names this reference could
  # resolve to. The canonical chosen name is `resolved_names[0]`;
  # overload resolution during type checking narrows the list to
  # length 1. There is *no* source-name field on this class — recover
  # it via `base_name(self.get_name())` when you need to display it.
  resolved_names: list[str]

  def __post_init__(self):
    if len(self.resolved_names) == 0:
      internal_error(self.location,
            'OverloadedVar must have at least one resolved name')

  @property
  def name(self):
    # Derived, read-only. Always equal to the canonical chosen name.
    # Exposed so ``.name`` access works uniformly with `Var`, but
    # there is no `name` field that could drift out of sync with
    # `resolved_names`.
    return self.resolved_names[0]

  def get_name(self):
    return self.resolved_names[0]

  def copy(self):
    return OverloadedVar(self.location, self.typeof,
                       list(self.resolved_names))

  def __eq__(self, other: object) -> bool:
    if isinstance(other, OverloadedVar):
      return self.resolved_names[0] == other.resolved_names[0]
    elif isinstance(other, ResolvedVar):
      # Symmetric with ResolvedVar.__eq__ (see comment there).
      return self.resolved_names[0] == other.name
    elif isinstance(other, RecFun):
      return self.resolved_names[0] == other.name
    elif isinstance(other, GenRecFun):
      return self.resolved_names[0] == other.name
    elif isinstance(other, TermInst):
      return self == other.subject
    elif isinstance(other, TAnnote):
      return self == other.subject
    elif isinstance(other, Var):
      # Pre- and post-uniquify references are not interchangeable.
      return False
    else:
      return False

  def __str__(self):
    chosen = self.resolved_names[0]
    if base_name(chosen) == 'empty' and not get_unique_names() and not get_verbose():
      return '[]'
    elif get_unique_names():
      return name2str(chosen) + '{' + ','.join(self.resolved_names) + '}'
    elif is_var_operator(self):
      return 'operator ' + name2str(chosen)
    else:
      return name2str(chosen)

  @no_type_check
  def reduce(self, env: Env) -> Term:
    if get_reduce_all() or (self in get_reduce_only()):
      chosen = self.resolved_names[0]
      if get_dont_reduce_opaque() and chosen in env.dict.keys():
        binding = env.dict[chosen]
        if binding.visibility == 'opaque' \
           and binding.module != env.get_current_module():
            return self if get_eval_all() else auto_rewrites(self, env)

      res = env.get_value_of_term_var(self)
      if res:
        if get_verbose():
          print('\t var ' + chosen + ' ===> ' + str(res))
        if isinstance(res, Union):
          return self if get_eval_all() else auto_rewrites(self, env)
        return res.reduce(env)
      else:
        return self if get_eval_all() else auto_rewrites(self, env)
    else:
      return self if get_eval_all() else auto_rewrites(self, env)

  @no_type_check
  def substitute(self, sub: dict[str, Term | Type | RecFun | GenRecFun]) -> Term | RecFun | GenRecFun:
    chosen = self.resolved_names[0]
    if chosen in sub:
      trm = sub[chosen]
      if not isinstance(trm, RecFun) and not isinstance(trm, GenRecFun):
        add_reduced_def(chosen)
      return trm
    else:
      new_typeof = self.subst_typeof(sub)
      if new_typeof is self.typeof:
        return self
      return OverloadedVar(self.location, new_typeof, list(self.resolved_names))

  @no_type_check
  def uniquify(self, env: dict[str, Any], ctx: UniquifyContext) -> OverloadedVar:
    # Already uniquified — re-uniquify is a no-op (we'd hit this if
    # uniquify_deduce were ever called twice on the same AST).
    return self

  def resolve_to(self, chosen_name: str, ty: Type | None = None) -> ResolvedVar:
    """Transition this OverloadedVar into a ResolvedVar bound to a
    single chosen name. Used by type-check overload resolution and
    by `check_constr_pattern` once the constructor for a pattern
    has been determined. The returned `ResolvedVar` is a different
    class — pattern matches and isinstance checks distinguish it
    from the still-overloaded form, which is the whole point of
    the split."""
    return ResolvedVar(self.location, ty if ty is not None else self.typeof,
                       chosen_name)


@dataclass
class ResolvedVar(VarRef):
  # A variable reference after overload resolution. `name` is the
  # single uniquified name this reference is bound to. There is no
  # candidate list — that's the OverloadedVar state. Once a Var has
  # become a ResolvedVar, no further name-narrowing is possible: the
  # only transitions are substitution / reduction, which produce a
  # different node entirely.
  name: str

  def get_name(self):
    return self.name

  def copy(self):
    return ResolvedVar(self.location, self.typeof, self.name)

  def __eq__(self, other: object) -> bool:
    if isinstance(other, ResolvedVar):
      return self.name == other.name
    elif isinstance(other, OverloadedVar):
      # A resolved name matches an overloaded reference iff it's
      # the chosen candidate. Comparing across the boundary lets
      # post-typecheck code keep working with code that hasn't yet
      # narrowed (e.g. equality reduction in mixed sub-ASTs).
      return self.name == other.resolved_names[0]
    elif isinstance(other, RecFun):
      return self.name == other.name
    elif isinstance(other, GenRecFun):
      return self.name == other.name
    elif isinstance(other, TermInst):
      return self == other.subject
    elif isinstance(other, TAnnote):
      return self == other.subject
    elif isinstance(other, Var):
      # Pre- and post-uniquify references are not interchangeable.
      return False
    else:
      return False

  def __str__(self):
    if base_name(self.name) == 'empty' and not get_unique_names() and not get_verbose():
      return '[]'
    elif get_unique_names():
      return name2str(self.name) + '{' + self.name + '}'
    elif is_var_operator(self):
      return 'operator ' + name2str(self.name)
    else:
      return name2str(self.name)

  @no_type_check
  def reduce(self, env: Env) -> Term:
    if get_reduce_all() or (self in get_reduce_only()):
      if get_dont_reduce_opaque() and self.name in env.dict.keys():
        binding = env.dict[self.name]
        if binding.visibility == 'opaque' \
           and binding.module != env.get_current_module():
            return self if get_eval_all() else auto_rewrites(self, env)

      res = env.get_value_of_term_var(self)
      if res:
        if get_verbose():
          print('\t var ' + self.name + ' ===> ' + str(res))
        if isinstance(res, Union):
          return self if get_eval_all() else auto_rewrites(self, env)
        return res.reduce(env)
      else:
        return self if get_eval_all() else auto_rewrites(self, env)
    else:
      return self if get_eval_all() else auto_rewrites(self, env)

  @no_type_check
  def substitute(self, sub: dict[str, Term | Type | RecFun | GenRecFun]) -> Term | RecFun | GenRecFun:
    if self.name in sub:
      trm = sub[self.name]
      if not isinstance(trm, RecFun) and not isinstance(trm, GenRecFun):
        add_reduced_def(self.name)
      return trm
    else:
      new_typeof = self.subst_typeof(sub)
      if new_typeof is self.typeof:
        return self
      return ResolvedVar(self.location, new_typeof, self.name)

  @no_type_check
  def uniquify(self, env: dict[str, Any], ctx: UniquifyContext) -> ResolvedVar:
    # Already uniquified.
    return self


@dataclass
class Int(Term):
  value: int

  def __eq__(self, other: object) -> bool:
      if isinstance(other, TermInst):
        return self == other.subject
      elif not isinstance(other, Int):
          return False
      return self.value == other.value

  def __str__(self):
    return str(self.value)


@dataclass
class Lambda(Term):
  vars: List[Tuple[str,Type]]
  body: Term
  # Captured runtime environment, populated by `Lambda.reduce` under
  # `--eval-all` so the closure can be applied later. `None` for an
  # un-reduced lambda.
  env: Optional['Env'] = None

  def __str__(self):
    if get_unique_names():
      params = self.vars
    else:
      params = [(base_name(x), t) for (x,t) in self.vars]
    return "fun " + ",".join([x + ':' + str(t) if t else x\
                              for (x,t) in params]) \
           + " { " + str(self.body) + " }"

  def pretty_print(self, indent: int, afterNewline: bool = False) -> str:
    params = [(base_name(x), t)for (x,t) in self.vars]
    return (indent*' ' if afterNewline else '') \
        + "fun " + ', '.join([x + ':' + str(t) if t else x\
                            for (x,t) in params]) \
        + " {\n" + self.body.pretty_print(indent+2, True) + '\n'\
        + indent*' ' + '}'

  def __eq__(self, other: object) -> bool:
      if not isinstance(other, Lambda):
        return False
      return _alpha_equiv_lambda(self, other, {}, {})

  @no_type_check
  def reduce(self, env: Env) -> Lambda:
    if get_eval_all():
      return Lambda(self.location, self.typeof, self.vars, self.body,
                    env=self.env if self.env is not None else env)
    else:
      return Lambda(self.location, self.typeof, self.vars, self.body.reduce(env))

  @no_type_check
  def uniquify(self, env: dict[str, Any], ctx: UniquifyContext) -> Lambda:
    body_env = {x:y for (x,y) in env.items()}
    new_var_types = [t.uniquify(env, ctx) if t else None for (x,t) in self.vars]
    new_vars = [(generate_name(x, ctx), nt) \
                for ((x,_), nt) in zip(self.vars, new_var_types)]
    for ((old,_), (new,_)) in zip(self.vars, new_vars):
      overwrite(body_env, old, new, self.location)
    new_body = self.body.uniquify(body_env, ctx)
    return Lambda(self.location, self.typeof, new_vars, new_body)

def is_match(pattern: Pattern, arg: Term, subst: dict[str, Term]) -> bool:
    ret = False
    match pattern:
      case PatternBool(loc1, value):
        match arg:
          case Bool(_, _, arg_value):
            ret = arg_value == value
          case _ if isinstance(arg, VarRef):
            ret = False
          case _:
            user_error(loc1, 'Boolean pattern expected boolean argument, not\n\t' \
                       + str(arg))
      case PatternCons(loc1, constr, []):
        if isinstance(arg, VarRef):
          ret = constr == arg
        else:
          match arg:
            case TermInst(_, _, arg2, _):
              ret = is_match(pattern, arg2, subst)
            case _:
              ret = False

      case PatternCons(loc1, constr, params):
        match arg:
          case Call(_, _, rator, args):
            # `rator` may be a (possibly term-instantiated) VarRef.
            inner = rator
            if isinstance(inner, TermInst):
              inner = inner.subject
            if isinstance(inner, VarRef) \
               and constr == inner and len(params) == len(args):
              for (k, v) in zip(params, args):
                subst[k] = v
                if isinstance(v, TermInst):
                  v.inferred = False
              ret = True
            else:
              ret = False
          case _:
            ret = False
      case _:
        ret = False
    if get_verbose():
      print('is_match(' + str(pattern) + ', ' + str(arg) + ') = ' + str(ret))
    return ret

# The variables that should be reduced.
reduce_only: List[VarRef] = []

def set_reduce_only(defs: list[VarRef]) -> None:
  global reduce_only
  reduce_only = defs

def get_reduce_only() -> list[VarRef]:
  global reduce_only
  return reduce_only

reduce_all = False

def get_reduce_all() -> bool:
  global reduce_all
  return reduce_all

def set_reduce_all(b: bool) -> None:
  global reduce_all
  reduce_all = b

dont_reduce_opaque = False

def get_dont_reduce_opaque() -> bool:
  global dont_reduce_opaque
  return dont_reduce_opaque

def set_dont_reduce_opaque(b: bool) -> None:
  global dont_reduce_opaque
  dont_reduce_opaque = b

eval_all = False

def get_eval_all() -> bool:
  # return False
  global eval_all
  return eval_all

def set_eval_all(b: bool) -> None:
  global eval_all
  eval_all = b

# Definitions that were reduced.
reduced_defs: set[str] = set()

def reset_reduced_defs():
  global reduced_defs
  reduced_defs = set()

def get_reduced_defs():
  global reduced_defs
  return reduced_defs

def add_reduced_def(df: str) -> None:
  global reduced_defs
  reduced_defs.add(df)

def complete_name(name: str) -> str:
    if base_name(name) in infix_precedence.keys() \
       or base_name(name) in prefix_precedence.keys():
        return 'operator ' + base_name(name)
    else:
        return name2str(name)
    
def is_operator_name(name: str) -> bool:
    return base_name(name) in infix_precedence.keys() \
        or base_name(name) in prefix_precedence.keys()
    
    
def is_var_operator(trm: Term) -> bool:
  # `Var.__str__` / `OverloadedVar.__str__` use this without recursing
  # through `is_operator_callable`, which would loop on TermInst(Var(...)).
  return isinstance(trm, VarRef) and is_operator_name(trm.get_name())

def is_operator_callable(trm: Term | RecFun | GenRecFun) -> bool:
  name = callable_name(trm)
  return name is not None and is_operator_name(name)

def _callable_display_subject(trm: Term | RecFun | GenRecFun) -> Term | RecFun | GenRecFun:
  while isinstance(trm, TermInst):
    trm = trm.subject
  return trm

def operator_display_name(trm: Term | RecFun | GenRecFun) -> str:
  name = callable_name(trm)
  if name is None:
    raise InternalError('operator_display_name, unexpected term ' + str(trm))
  if isinstance(_callable_display_subject(trm), VarRef) and get_unique_names():
    return name
  return base_name(name)

def is_infix_operator(trm: Term | RecFun | GenRecFun) -> bool:
  name = callable_name(trm)
  return name is not None and base_name(name) in infix_precedence.keys()

def is_prefix_operator(trm: Term | RecFun | GenRecFun) -> bool:
  name = callable_name(trm)
  return name is not None and base_name(name) in prefix_precedence.keys()

def precedence(trm: Term) -> int | None:
  match trm:
    case Call(_, _, rator, args) if is_operator_callable(rator):
      op_name = base_name(operator_display_name(rator))
      if len(args) >= 2:
        return infix_precedence.get(op_name, None)
      elif len(args) == 1:
        return prefix_precedence.get(op_name, None)
      else:
        return None
    case _:
      return None

def left_child(parent: Term, child: Term) -> bool:
  match parent:
    case Call(_, _, _, [left, _]):
      return child is left
    case _:
      return False
    
def op_arg_str(trm: Term, arg: Term) -> str:
  trm_precedence = precedence(trm)
  arg_precedence = precedence(arg)
  if trm_precedence is not None and arg_precedence is not None:
    if arg_precedence < trm_precedence:
      return "(" + str(arg) + ")"
    elif arg_precedence == trm_precedence: # and left_child(trm, arg):
      return "(" + str(arg) + ")"
  return str(arg)



@no_type_check
def do_function_call(loc: Meta, name: str, type_params: list[str],
                     type_args: list[Type], params: list[str],
                     args: list[Term], body: Term,
                     subst: dict[str, Term | Type], env: Env,
                     return_type: Type | None,
                     display_args: list[Term] | None = None) -> Term:
  # Phase 5 / Step 21 hook: trap on every named user-function reduction.
  # This single site catches RecFun, GenRecFun, and the recursive
  # case-dispatch path -- all of which funnel through here.  Lambdas
  # are handled separately in ``Call.reduce``'s ``Lambda`` arm because
  # they have no name binding.  PR #269 hooked all three call sites
  # and double-fired; do not carry that pattern forward.
  _dbg = get_debugger()
  if _dbg is not None:
    # ``subst`` holds the *pattern-bound* names introduced by the
    # recursive case dispatch (e.g. ``n'`` -> the predecessor of
    # the matched ``suc(n')``).  Without it, ``locals`` would be
    # empty for every recursive call that consumes its argument
    # via pattern matching -- a very common Deduce idiom.
    #
    # ``display_args``: the *original* call's args, before pattern
    # match splits the first arg off.  Use this for the call header
    # in trap output so the user sees what they actually passed
    # (e.g. ``count_down(suc(suc(zero)))``) rather than what survived
    # the pattern match (``count_down(n'=suc(zero))``).  Defaults to
    # ``args`` for callers that haven't been updated.
    #
    # ``defn_loc``: ``loc`` is whatever the caller passed -- for the
    # generic ``TermInst(RecFun)`` arm of ``Call.reduce`` that's the
    # *call site* in the user file, which would let prelude
    # functions slip past a ``skip lib/`` rule the very first time
    # they're entered.  ``body.location`` always points to the
    # function's *defining* site, which is the right thing to key
    # skip decisions on.
    defn_loc = getattr(body, 'location', None)
    _dbg.on_function(name, loc, env, params=params, args=args, subst=subst,
                     defn_loc=defn_loc,
                     display_args=display_args if display_args is not None
                                                 else args)
  fast_call = False
  if get_eval_all() and len(args) == 2  and isNat(args[0]) and isNat(args[1]):
    op = base_name(name)
    x = natToInt(args[0])
    y = natToInt(args[1])
    # This is a really hack-y fix
    sname = getSuc(args[0])
    sname = sname if sname else getSuc(args[1])
    zname = getZero(args[0])
    ty = return_type
    ret = None
    if op == '+':
      ret = intToNat(loc, x + y, sname=sname, zname=zname, ty=ty)
    elif op == '-':
      ret = intToNat(loc, x - y, sname=sname, zname=zname, ty=ty)
    elif op == '/':
      ret = intToNat(loc, x // y, sname=sname, zname=zname, ty=ty)
    elif op == '*':
      ret = intToNat(loc, x * y, sname=sname, zname=zname, ty=ty)
    elif op == '^':
      ret = intToNat(loc, x ** y, sname=sname, zname=zname, ty=ty)
    if ret: 
      if get_verbose():
        print(f"Doing fast arithmetic on call {x} {op} {y}.")
      ret.typeof = return_type
      fast_call = True

  if not fast_call:    
    body_env = env
    if False and len(params) != len(args): # TODO: why if False?? -Jeremy
      user_error(loc, 'in function call ' + name2str(name) \
                 + '(' + ', '.join([str(a) for a in args]) + ')\n' \
                 + '\tnumber of parameters: ' + str(len(params)) + '\n' \
                 + '\tdoes not match number of arguments')
    for (x,ty) in zip(type_params, type_args):
      subst[x] = ty
    for (k,v) in zip(params, args):
      subst[k] = v

    for k, v in subst.items():
      if isinstance(v, TermInst):
        v.inferred = False

    if get_reduce_all() and get_eval_all():
      if get_verbose():
        print("Fast evaluate", body)
      for k, v in subst.items():
        if k in type_params:
          env = env.define_type(loc, k, v)
        else:
          env = env.define_term_var(loc, k, v.typeof, v)

      ret = body.reduce(env)
    else:
      new_fun_case_body = body.substitute(subst)
      old_defs = get_reduce_only()
      reduce_defs = [x for x in old_defs]
      if ResolvedVar(loc, None, name) in reduce_defs:
        reduce_defs.remove(ResolvedVar(loc, None, name))
      else:
        pass
      reduce_defs += [ResolvedVar(loc, None, x) for x in params]
      # Revisit the following -Jeremy  
      # reduce_defs += [ResolvedVar(loc, None, x) \
      #                 for x in fun_case.pattern.parameters \
      #                 + fun_case.parameters]
      set_reduce_only(reduce_defs)

      # Reduce the body of the function
      ret = new_fun_case_body.reduce(body_env)

      set_reduce_only(old_defs)

  add_reduced_def(name)
  if get_verbose():
    print('\tcall to ' + name + ' returns ' + str(ret))

  if env.get_tracing(name):
    global recursion_depth
    print('<' * recursion_depth, str(ret))
    recursion_depth -= 1

  if _dbg is not None:
    _dbg.after_function(name, env, return_value=ret)
  return explicit_term_inst(ret)


@dataclass
class Call(Term):
  rator: Term
  args: list[Term]

  def __str__(self):
    if is_infix_operator(self.rator) and len(self.args) >= 2:
      op_str = ' ' + operator_display_name(self.rator) + ' '
      return op_str.join([op_arg_str(self, arg) for arg in self.args])
    elif is_prefix_operator(self.rator) and len(self.args) == 1:
      return operator_display_name(self.rator) + " " + op_arg_str(self, self.args[0])
    elif isDeduceInt(self):
      return deduceIntToInt(self)
    elif isLitNat(self): # and not get_verbose():
      return 'ℕ' + str(natToInt(self))
    # elif isNat(self): # and not get_verbose():
    #   return '`' + str(natToInt(self))
    elif isLitUInt(self): # and not get_verbose():
      return str(uintToInt(self))
    elif isUInt(self) and not get_verbose():
      return str(uintToInt(self))
    elif isNodeList(self):
      return '[' + nodeListToString(self)[:-2] + ']'
    elif isEmptySet(self) and not get_verbose():
      return '∅'
    else:
      return str(self.rator) + "(" \
        + ", ".join([str(arg) for arg in self.args])\
        + ")"

  def __eq__(self, other: object) -> bool:
      if isinstance(other, TermInst):
        return self == other.subject
      if not isinstance(other, Call):
        return False
      if len(self.args) != len(other.args):
        return False
      eq_rators = self.rator == other.rator
      eq_rands = all([arg1 == arg2 for arg1,arg2 in zip(self.args, other.args)])
      result = eq_rators and eq_rands
      #print(str(self) + ' =? ' + str(other) + ' = ' + str(result))
      return result

  @no_type_check
  def reduce(self, env: Env) -> Term:
    fun = self.rator.reduce(env)
    if get_eval_all():
      is_assoc = False
      assoc_name = None
    else:
      assoc_name = callable_name(self.rator)
      is_assoc = assoc_name is not None and is_associative(self.location,
                                assoc_name, self.typeof, env)
    if is_assoc:
      assert assoc_name is not None
      flat_args = flatten_assoc_list(assoc_name, self.args)
    else:
      flat_args = self.args
    args = [arg.reduce(env) for arg in flat_args]
    ret = None
    match fun:
      case Var(loc, _, '=') | OverloadedVar(loc, _, ['=']) | ResolvedVar(loc, _, '='):
        if args[0] == args[1]:
          ret = Bool(loc, BoolType(loc), True)
        elif constructor_conflict(args[0], args[1], env):
          ret = Bool(loc, BoolType(loc), False)
        else:
          ret = Call(self.location, self.typeof, fun, args)
      case (OverloadedVar() | ResolvedVar()) if is_assoc:
        ret = Call(self.location, self.typeof, fun,
                   flatten_assoc_list(assoc_name, args))

      case Lambda(loc, _, vars, body):
        # Note (Phase 5 / Step 22): no debugger hook here.
        # ``do_call`` forwards to ``do_function_call`` which is
        # already hooked; trapping a second time here would
        # double-fire on every lambda application -- the exact bug
        # PR #269 had with named functions.  We do pass the source
        # rator's name down so the REPL displays the user-visible
        # name (e.g. a ``define f = λ ...``) rather than a generic
        # ``anonymous``; literal lambdas with no name fall back to
        # ``<lambda>``.
        call_env = fun.env if fun.env is not None else env
        display_name = callable_name(self.rator) or '<lambda>'
        ret = self.do_call(loc, vars, body, args, call_env, name=display_name)
    
      case GenRecFun(loc, name, [], params, returns, _, _,
                   body, _):
        if env.get_tracing(name):
          global recursion_depth
          recursion_depth += 1
          print('>' * recursion_depth, str(base_name(name)) + '(' + str(' '.join([str(x) for x in args]) + ')'))

        subst = {k: v for ((k,t),v) in zip(params, args)}
        ret = do_function_call(loc, name, [], [], [x for (x,t) in params], args,
                               body, subst, env, None,
                               display_args=args)

      case TermInst(loc, _,
                    GenRecFun(_, name, typarams, params, returns,
                              _, _, body, _),
                    type_args):
        subst = {k: v for ((k,t),v) in zip(params, args)}
        ret = do_function_call(loc, name, typarams, type_args, [x for (x,t) in params], args,
                               body, subst, env, None,
                               display_args=args)
    
      case RecFun(loc, name, [], params, returns, cases):
        ret = self.do_recursive_call(loc, name, fun, [], [], params, args,
                                     returns, cases, is_assoc, env)
      case TermInst(loc, _,
                    RecFun(_, name, typarams, params, returns, cases),
                    type_args):
        ret = self.do_recursive_call(loc, name, fun, typarams, type_args,
                                     params, args, returns, cases, is_assoc,
                                     env)
      case Generic(_, _, typarams, body):
        internal_error(self.location, 'in reduction, call to generic\n\t' + str(self))
      case _:
        ret = Call(self.location, self.typeof, fun, args)

    if not get_eval_all():
        ret = auto_rewrites(ret, env)
    
    return ret

  @no_type_check
  def do_call(self, loc: Meta, vars: list[tuple[str, Type | None]],
              body: Term, args: list[Term], env: Env,
              name: str = "anonymous") -> Term:
    # because of associativity, args can be longer than vars.
    # ``name`` is the source-visible name of the function being
    # called -- caller passes the result of ``callable_name(self.rator)``
    # so debugger traps and trace output see ``foo`` rather than
    # ``anonymous`` when the lambda came from a named binding.
    subst = {k: v for ((k,t),v) in zip(vars, args)}
    return do_function_call(loc, name, [], [], [], [], body, subst, env, None,
                            display_args=args)

  @no_type_check
  def do_recursive_call(self, loc: Meta, name: str, fun: Term | RecFun,
                        type_params: list[str], type_args: list[Type],
                        params: list[Type], args: list[Term],
                        returns: Type, cases: list[FunCase],
                        is_assoc: bool, env: Env) -> Term:
    if get_verbose():
      print('call to recursive function: ' + str(fun))
      print('\targs: ' + ', '.join([str(a) for a in args]))

    if env.get_tracing(name):
      global recursion_depth
      recursion_depth += 1
      print('>' * recursion_depth, str(base_name(name)) + '(' + str(' '.join([str(x) for x in args]) + ')'))

    if is_assoc and len(args) > len(params):
      return self.reduce_associative(loc, name, fun, type_params, type_args,
                                     params, args, cases, env, returns)

    if len(args) == len(params):
      first_arg = args[0]
      rest_args = args[1:]
      for fun_case in cases:
          subst = {}
          if is_match(fun_case.pattern, first_arg, subst):
              # Pass the matched case's own location to
              # ``do_function_call``, not the RecFun's overall
              # location.  This is what surfaces in the debugger's
              # ``-> call ... at L:C`` line and what ``list`` points
              # the ``->`` arrow at -- the user wants the *matched
              # case body* (line 13/14 for ``count_down``'s base /
              # inductive case), not the bare ``recursive`` header
              # on line 12.
              return do_function_call(fun_case.location, name,
                                      type_params, type_args,
                                      fun_case.parameters, rest_args,
                                      fun_case.body, subst, env, returns,
                                      display_args=args)
    if is_assoc:
      if get_verbose():
        print('not reducing recursive call to associative ' + str(fun))
      return Call(self.location, self.typeof, fun,
                 flatten_assoc_list(name, args))
    else:
      if get_verbose():
        print('not reducing recursive call to ' + str(fun))
      return Call(self.location, self.typeof, fun, args)
  
  @no_type_check
  def reduce_associative(self, loc: Meta, name: str, fun: Term | RecFun,
                         type_params: list[str], type_args: list[Type],
                         params: list[Type], args: list[Term],
                         cases: list[FunCase], env: Env,
                         returns: Type) -> Term:
    if get_verbose():
      print('<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<')
      print('begin associative operator ' + str(fun))
      print('\targs: ' + ', '.join([str(a) for a in args]))
      print('\tparams: ' + ', '.join([str(p) for p in params]))

    old_reduce_only = get_reduce_only()
    reduce_only = [x for x in old_reduce_only]
    new_args = []
    worklist = args
    while len(worklist) > 1:
      first_arg = worklist[0]; worklist = worklist[1:]
      did_call = False
      for fun_case in cases:
          subst = {}
          if is_match(fun_case.pattern, first_arg, subst):
              rest_args = worklist[:len(fun_case.parameters)]
              # Use the matched case's location so the debugger's
              # ``->`` arrow lands on the case body, not on the
              # surrounding ``recursive`` declaration header.  Same
              # rationale as the change in ``do_recursive_call``.
              # For associative reduction, the "call" conceptually
              # consumes ``first_arg`` plus enough of ``worklist`` to
              # match the remaining params -- that's the original
              # arg list to display.
              result = do_function_call(fun_case.location, name,
                                        type_params, type_args,
                                        fun_case.parameters, rest_args,
                                        fun_case.body, subst, env, returns,
                                        display_args=[first_arg] + rest_args)
              # if get_verbose():
              #   print('call result: ' + str(result))
              worklist = [result] + worklist[len(fun_case.parameters):]
              did_call = True
              rator_var = ResolvedVar(loc, None, name)
              if rator_var in reduce_only:
                reduce_only.remove(rator_var)
              set_reduce_only(reduce_only)
              break
      if not did_call:
        new_args.append(first_arg)
      if did_call and not get_reduce_all():
        break
    set_reduce_only(old_reduce_only)

    new_args += worklist
    flat_results = flatten_assoc_list(name, new_args)
    if len(flat_results) == 1:
      return explicit_term_inst(flat_results[0])
    else:
      return Call(self.location, self.typeof, fun, flat_results)


@dataclass
class SwitchCase(AST):
  pattern: Pattern
  body: Term

  def __str__(self):
      return 'case ' + str(self.pattern) + ' { ' + str(self.body) + ' }'

  def pretty_print(self, indent: int) -> str:
      return indent*' ' + 'case ' + str(self.pattern) + ' {\n' \
          + (indent+2)*' ' + str(self.body) + '\n'\
          + indent*' ' + '}'

  @no_type_check
  def uniquify(self, env: dict[str, Any], ctx: UniquifyContext) -> SwitchCase:
    new_pat = self.pattern.uniquify(env, ctx)
    body_env = {x:y for (x,y) in env.items()}
    match new_pat:
      case PatternBool(_, _):
        pass
      case PatternCons(_, _, params) | PatternTerm(_, _, params):
        new_params = [generate_name(x, ctx) for x in params]
        for (old,new) in zip(params, new_params):
          overwrite(body_env, old, new, self.location)
        new_pat = new_pat.with_bindings(new_params)
    new_body = self.body.uniquify(body_env, ctx)
    return SwitchCase(self.location, new_pat, new_body)

  def __eq__(self, other: object) -> bool:
    if not isinstance(other, SwitchCase):
      return False
    match self.pattern, other.pattern:
      case PatternBool(_, value1), PatternBool(_, value2):
        return value1 == value2 and self.body == other.body
      case PatternCons(_, constr1, params1), PatternCons(_, constr2, params2):
        # Use ResolvedVar in the rename so substituted-in references
        # compare equal to the (already uniquified) ResolvedVars in
        # `other.body`. Picking Var here would break post-uniquify
        # equality across the two bodies.
        alpha_rename = {x: ResolvedVar(self.location, None, y) \
                        for (x,y) in zip(params1, params2) }
        new_body = self.body.substitute(alpha_rename)
        return constr1 == constr2 \
          and new_body == other.body
      case _:
        return False

@dataclass
class Switch(Term):
  subject: Term
  cases: List[SwitchCase]

  def __str__(self):
      return 'switch ' + str(self.subject) + ' { ' \
          + ' '.join([str(c) for c in self.cases]) \
          + ' }'

  def pretty_print(self, indent: int, afterNewline: bool = False) -> str:
      return ('' if afterNewline else '\n') + indent*' '+ 'switch ' + str(self.subject) + ' {\n' \
          + '\n'.join([c.pretty_print(indent+2) for c in self.cases]) + '\n'\
          + indent*' ' + '}'

  @no_type_check
  def reduce(self, env: Env) -> Term:
      new_subject = self.subject.reduce(env)
      for c in self.cases:
          subst = {}
          if is_match(c.pattern, new_subject, subst):
            if get_verbose():
              print('switch, matched ' + str(c.pattern) + ' and ' \
                    + str(new_subject))
            if get_eval_all():
              for k, v in subst.items():
                env = env.define_term_var(self.location, k, v.typeof, v)
              ret = c.body.reduce(env)
            else:
              new_body = c.body.substitute(subst)
              new_env = env
              old_defs = get_reduce_only()
              set_reduce_only(old_defs + [ResolvedVar(self.location, None, x) \
                                          for x in subst.keys()])
              ret = new_body.reduce(new_env)
              set_reduce_only(old_defs)
            return ret
      ret = Switch(self.location, self.typeof, new_subject, self.cases)
      return ret

  def __eq__(self, other: object) -> bool:
    if not isinstance(other, Switch):
      return False
    eq_subject = self.subject == other.subject
    eq_cases = all([c1 == c2 for (c1,c2) in zip(self.cases, other.cases)])
    return eq_subject and eq_cases

@dataclass
class TermInst(Term):
  subject: Term
  type_args: List[Type]
  inferred : bool = True

  def __eq__(self, other: object) -> bool:
    if isinstance(other, RecFun):
      return self.subject == other
    elif isinstance(other, TermInst):
      return self.subject == other.subject \
        and all([t1 == t2 for (t1,t2) in zip(self.type_args, other.type_args)])
    else:
      return self.subject == other

  def __str__(self):
    if self.inferred and not get_verbose():
      return str(self.subject)
    else:
      return '@' + str(self.subject) + '<' + ','.join([str(ty) for ty in self.type_args]) + '>'

  def reduce(self, env: Env) -> Term:  # type: ignore[override]
    subject_red = self.subject.reduce(env)
    type_args_red = [t.reduce(env) for t in self.type_args]
    match subject_red:
      case Generic(_, _, typarams, body):
        # sub = {x:t for (x,t) in zip(typarams, self.type_args)}
        sub = {x:t for (x,t) in zip(typarams, type_args_red)}
        return body.substitute(sub)
      case _:
        # return TermInst(self.location, self.typeof, subject_red,
        #                self.type_args, self.inferred)
        return TermInst(self.location, self.typeof, subject_red,
                        type_args_red, self.inferred)

@dataclass
class Array(Term):
  elements: List[Term]

  def __eq__(self, other: object) -> bool:
    if isinstance(other, Array):
      return all([elt == other_elt for (elt, other_elt) in zip(self.elements,
                                                               other.elements)])
    else:
      return False

  def __str__(self):
    return 'array(' + ', '.join([str(elt) for elt in self.elements]) + ')'

@dataclass
class MakeArray(Term):
  subject: Term

  def __eq__(self, other: object) -> bool:
    if isinstance(other, MakeArray):
      return self.subject == other.subject
    else:
      return False

  def __str__(self):
    return 'array(' + str(self.subject) + ')'

  def reduce(self, env: Env) -> Term:  # type: ignore[override]
    subject_red = self.subject.reduce(env)
    if isNodeList(subject_red):
      elements = nodeListToList(subject_red)
      return Array(self.location, self.typeof, elements)
    else:
      return MakeArray(self.location, self.typeof, self.subject.reduce(env))

@dataclass
class ArrayGet(Term):
  subject: Term
  position: Term

  def __eq__(self, other: object) -> bool:
    if isinstance(other, ArrayGet):
      return self.subject == other.subject \
        and self.position == other.position
    else:
      return False

  def __str__(self):
    return str(self.subject) + '[' + str(self.position) + ']'

  def reduce(self, env: Env) -> Term:  # type: ignore[override]
    subject_red = self.subject.reduce(env)
    position_red = self.position.reduce(env)
    index = None
    if isNat(position_red):
      index = natToInt(position_red)
    elif isUInt(position_red):
      index = uintToInt(position_red)
    match subject_red:
      case Array(loc2, _, elements):
        # If the index is not a concrete number (e.g. a free variable in
        # a proof), leave the access unreduced rather than erroring.
        if index is not None and 0 <= index and index < len(elements):
          return elements[index].reduce(env)
        # Don't signal an error for out-of-bounds! -Jeremy
      case MakeArray(loc2, marr_ty, list_term):
        # Peel as many leading `node` constructors off the list as the
        # index calls for. This lets `array(node(x, xs))[0]` reduce to
        # `x` even when the tail `xs` is not concrete, which is what
        # makes arrays useful inside proofs.
        if index is not None and index >= 0:
          cur = list_term
          i = index
          while True:
            match cur:
              case Call(_, _, TermInst(_, _, ctor, _, _), [hd, tl]) \
                   if _is_named(ctor, 'node'):
                if i == 0:
                  return hd.reduce(env)
                cur = tl
                i -= 1
              case _:
                break
        else:
          # Index-shift rule (#469): when the position is symbolic but
          # has a "successor"-shaped constructor (UInt `dub_inc` /
          # `inc_dub`, or Nat `suc`), peel one leading node off the list
          # and rebuild the access with the decremented index. This
          # unblocks inductive proofs over a universally-quantified index.
          match list_term:
            case Call(_, _, TermInst(_, _, ctor, _, _), [_hd, tl]) \
                 if _is_named(ctor, 'node'):
              new_pos = _array_index_predecessor(position_red, env)  # type: ignore[no-untyped-call]
              if new_pos is not None:
                new_subject = MakeArray(loc2, marr_ty, tl)
                new_get = ArrayGet(self.location, self.typeof,
                                   new_subject, new_pos)
                return new_get.reduce(env)
    return ArrayGet(self.location, self.typeof, subject_red, position_red)

@dataclass
class TLet(Term):
  var: str
  rhs: Term
  body: Term

  def __str__(self):
    return 'define ' + base_name(self.var) + ' = ' + str(self.rhs) + ';' \
      + '\n\t' + str(self.body)

  def reduce(self, env: Env) -> Term:  # type: ignore[override]
    new_body = self.body.substitute({self.var: self.rhs})
    return new_body.reduce(env)

  def reduceLets(self, env: Env) -> Term:
    new_body = self.body.substitute({self.var: self.rhs})
    if isinstance(new_body, TLet):
      return new_body.reduceLets(env)
    else:
      return new_body

  def uniquify(self, env: dict[str, Any], ctx: UniquifyContext) -> TLet:
    new_rhs = self.rhs.uniquify(env, ctx)
    body_env = {x:y for (x,y) in env.items()}
    new_var = generate_name(self.var, ctx)
    overwrite(body_env, self.var, new_var, self.location)
    new_body = self.body.uniquify(body_env, ctx)
    return TLet(self.location, self.typeof, new_var, new_rhs, new_body)

  def __eq__(self, other: object) -> bool:
    if not isinstance(other, TLet):
      return False
    return _alpha_equiv_tlet(self, other, {}, {})

@dataclass
class Hole(Term):

  def __str__(self):
      return '?'

@dataclass
class Omitted(Term):

  def __str__(self):
      return '--'

@dataclass
class Mark(Term):
  subject: Term

  def __eq__(self, other: object) -> bool:
    if isinstance(other, Mark):
      return self.subject == other.subject
    else:
      return self.subject == other

  def __str__(self):
    return '#' + str(self.subject) + '#'

################ Formulas ######################################
  
@dataclass
class Bool(Formula):
  value: bool

  def __eq__(self, other: object) -> bool:
      if not isinstance(other, Bool):
          return False
      return self.value == other.value
  def __str__(self):
    return 'true' if self.value else 'false'

def list_of_and(arg: Formula) -> list[Formula]:
  match arg:
    case And(_, _, args):
      return args
    case _:
      return [arg]
    
def flatten_and(args: Sequence[Formula]) -> list[Formula]:
  lol = [list_of_and(arg) for arg in args]
  ret = sum(lol, [])
  return ret

def is_true(b: Formula) -> bool:
  match b:
    case Bool(_, _, val):
        return val
    case _:
        return False

@dataclass
class And(Formula):
  args: list[Formula]

  def __str__(self):
    ret_args = []
    skip = False
    for i in range(len(self.args) - 1):
      if skip: 
        skip = False
        continue
      match self.args[i]:
        case IfThen(loc, tyof, prem, conc):
          if (self.args[i + 1]) == IfThen(loc, tyof, conc, prem):
            iff = Call(self.location, None, ResolvedVar(self.location, None, '⇔'),
                       [prem,conc])
            iff_str = '(' + op_arg_str(iff, prem) + ' ⇔ ' + op_arg_str(iff, conc) +')'
            ret_args.append(iff_str)
            skip = True
            continue
      ret_args.append(self.args[i])
    
    if not skip:
      ret_args.append(self.args[-1])

    if len(ret_args) == 1:
      return str(ret_args[0])

    return '(' + ' and '.join([str(arg) for arg in ret_args]) + ')'

  def __eq__(self, other: object) -> bool:
    if not isinstance(other, And):
      return False
    if len(self.args) != len(other.args):
      return False
    return all([arg1 == arg2 for arg1,arg2 in zip(self.args, other.args)])
  
  def reduce(self, env: Env) -> Formula:  # type: ignore[override]
    #new_args = [arg.reduce(env) for arg in self.args]
    new_args = flatten_and([arg.reduce(env) for arg in self.args])
    newer_args = []
    for arg in new_args:
      match arg:
        case Bool(_, _, val):
          if val:  # true: throw this away
            pass
          else:    # false: the whole thing is false
            return arg
        case _:
          newer_args.append(arg)
    if len(newer_args) == 0:
      return Bool(self.location, BoolType(self.location), True)
    elif len(newer_args) == 1:
      return newer_args[0]
    else:
      return And(self.location, self.typeof, newer_args)

def list_of_or(arg: Formula) -> list[Formula]:
  match arg:
    case Or(_, _, args):
      return args
    case _:
      return [arg]

def flatten_or(args: Sequence[Formula]) -> list[Formula]:
  lol = [list_of_or(arg) for arg in args]
  ret = sum(lol, [])
  return ret
    
@dataclass
class Or(Formula):
  args: list[Formula]

  def __str__(self):
    return '(' + ' or '.join([str(arg) for arg in self.args]) + ')'
  
  def __eq__(self, other: object) -> bool:
    if not isinstance(other, Or):
      return False
    if len(self.args) != len(other.args):
      return False
    return all([arg1 == arg2 for arg1,arg2 in zip(self.args, other.args)])
  
  def reduce(self, env: Env) -> Formula:  # type: ignore[override]
    new_args = flatten_or([arg.reduce(env) for arg in self.args])
    newer_args = []
    for arg in new_args:
      match arg:
        case Bool(_, _, val):
          if val:  # true: the whole thing is true
            return arg 
          else:    # false: throw this away
            pass
        case _:
          newer_args.append(arg)
    if len(newer_args) == 0:
      return Bool(self.location, BoolType(self.location), False)
    elif len(newer_args) == 1:
      return newer_args[0]
    else:
      return Or(self.location, self.typeof, newer_args)

@dataclass
class IfThen(Formula):
  premise: Formula
  conclusion : Formula

  def __str__(self):
    match self.conclusion:
      case Bool(_, _, False):
        return str(Call(self.location, self.typeof,
                        Var(self.location, None, 'not'),
                        [self.premise]))
      case _:
        return '(if ' + str(self.premise) \
          + ' then ' + str(self.conclusion) + ')'

  def __eq__(self, other: object) -> bool:
    if not isinstance(other, IfThen):
      return False
    return self.premise == other.premise and self.conclusion == other.conclusion
  
  def reduce(self, env: Env) -> Formula:  # type: ignore[override]
    prem = self.premise.reduce(env)
    conc = self.conclusion.reduce(env)
    ret: Formula
    if prem == conc:
      if get_verbose():
         print('reduce if, prem == conc')
      ret = Bool(self.location, BoolType(self.location), True)
    else:
      match prem:
        case Bool(loc, tyof, True):
          if get_verbose():
            print('reduce if, prem == True')
          ret = self.conclusion
        case Bool(loc, tyof, False):
          if get_verbose():
            print('reduce if, prem == False')
          ret = Bool(loc, tyof, True)
        case _:
          match conc:
            case Bool(loc, tyof, True):
              if get_verbose():
                print('reduce if, conc == True')
              ret = Bool(self.location, tyof, True)
            case _:
              ret = IfThen(self.location, self.typeof, prem, conc)
    if get_verbose():
      print('reduce ' + str(self) + '\n\t==> ' + str(ret))
    return ret

@dataclass
class All(Formula):
  var: Tuple[str,Type]
  # Position (s, e), where
  #  s : The variable's index in the list, starting from the last var
  #  e : The number of vars in the block
  pos: Tuple[int, int]
  body: Formula

  def __str__(self):
    v, t = self.var
    v = name2str(v)

    (s, e) = self.pos

    result = ''
    if s + 1 == e:
      result += "(all "
    result += f"{v}:{str(t)}"
    if s == 0:
      result += ". "
    else:
      result += ", "

    result += f"{str(self.body)}"

    if s + 1 == e: 
      result += ")"

    return result

  def reduce(self, env: Env) -> Formula:  # type: ignore[override]
    new_body = self.body.reduce(env)
    match new_body:
      case Bool(_, _, _):
        if get_verbose():
          print('reduce ' + str(self) + '\n\t==> ' + str(new_body))
        return new_body
      case _:
        x, ty = self.var
        return All(self.location,
                   self.typeof,
                   (x, ty.reduce(env)),
                   self.pos,
                   new_body)

  def __eq__(self, other: object) -> bool:
    if not isinstance(other, All):
      return False
    return _alpha_equiv_all(self, other, {}, {})

  def uniquify(self, env: dict[str, Any], ctx: UniquifyContext) -> All:
    body_env = {x:y for (x,y) in env.items()}
    (x, ty) = self.var
    new_t = ty.uniquify(body_env, ctx)
    new_x = generate_name(x, ctx)
    overwrite(body_env, x, new_x, self.location)
    new_body = self.body.uniquify(body_env, ctx)
    return All(self.location, self.typeof, (new_x, new_t),
               self.pos, new_body)

@dataclass
class Some(Formula):
  vars: list[Tuple[str,Type]]
  body: Formula

  def __str__(self):
      return 'some ' + ",".join([(v if get_verbose() else base_name(v)) + ":" + str(t) \
                                 for (v,t) in self.vars]) \
        + '. ' + str(self.body)
  
  def reduce(self, env: Env) -> Formula:  # type: ignore[override]
    len(self.vars)
    new_body = self.body.reduce(env)
    match new_body:
      case Bool(_, _, True):
        return new_body
      case Bool(_, _, False):
        return new_body
      case _:
        return Some(self.location,
                    self.typeof,
                    [(x, ty.reduce(env)) for (x,ty) in self.vars],
                    new_body)

  def uniquify(self, env: dict[str, Any], ctx: UniquifyContext) -> Some:
    body_env = {x:y for (x,y) in env.items()}
    new_vars = []
    for (x, ty) in self.vars:
      new_t = ty.uniquify(body_env, ctx)
      new_x = generate_name(x, ctx)
      new_vars.append((new_x, new_t))
      overwrite(body_env, x, new_x, self.location)
    new_body = self.body.uniquify(body_env, ctx)
    return Some(self.location, self.typeof, new_vars, new_body)

  def __eq__(self, other: object) -> bool:
    if not isinstance(other, Some):
      return False
    return _alpha_equiv_some(self, other, {}, {})
  
################ Proofs ######################################
  
@dataclass
class PVar(Proof):
  name: str

  def __eq__(self, other: object) -> bool:
    if not isinstance(other, PVar):
      return False
    return self.name == other.name

  def pretty_print(self, indent: int) -> str:
      return str(self)
  
  def __str__(self):
      return base_name(self.name)

  def uniquify(self, env: dict[str, Any], ctx: UniquifyContext) -> PVar:
    if self.name not in env.keys():
      hits = find_private_lemma_definers(self.name)
      if hits:
        def fmt_hit(h: tuple[str, str | None, int | None]) -> str:
          module, filename, line = h
          if filename is not None and line is not None:
            return "module " + module + " (" + filename + ":" + str(line) + ")"
          return "module " + module
        where = ', '.join(fmt_hit(h) for h in hits)
        msg = ("'" + self.name + "' is declared as a `lemma` in "
               + where + "; lemmas are module-private and not accessible"
               + " from other modules. To make it accessible here, change"
               + " `lemma` to `theorem` there.")
        user_error(self.location, msg)
      env_str = ('\n' + ', '.join(env.keys())) if get_verbose() else ''
      user_error(self.location, "undefined proof variable " + self.name + env_str)
    if not isinstance(env[self.name], list):
      user_error(self.location, "proof variable not bound to list " + self.name)
    return PVar(self.location, env[self.name][0])
    
@dataclass
class PLet(Proof):
  label: str
  proved: Formula
  because: Proof
  body: Proof

  def pretty_print(self, indent: int) -> str:
      return indent*' ' + 'have ' + base_name(self.label) + ': ' + str(self.proved) + ' by {\n' \
          + self.because.pretty_print(indent+2) + '\n' \
          + indent*' ' + '}\n' \
          + maybe_pretty_print(self.body, indent)
  
  def __str__(self):
      return 'have ' + base_name(self.label) + ': ' + str(self.proved) \
        + ' by ' + str(self.because) + (' ' + str(self.body) if self.body else '')

  def uniquify(self, env: dict[str, Any], ctx: UniquifyContext) -> PLet:
    new_proved = self.proved.uniquify(env, ctx)
    new_because = self.because.uniquify(env, ctx)
    body_env = {x:y for (x,y) in env.items()}
    new_label = generate_name(self.label, ctx)
    overwrite(body_env, self.label, new_label, self.location)
    new_body = self.body.uniquify(body_env, ctx)
    return PLet(self.location, new_label, new_proved, new_because, new_body)

@dataclass
class PTLetNew(Proof):
  var: str
  rhs : Term
  body: Proof

  def pretty_print(self, indent: int) -> str:
      return indent*' ' + 'define ' + base_name(self.var) + ' = ' + str(self.rhs) + '\n' \
          + self.body.pretty_print(indent)
  
  def __str__(self):
      return 'define ' + base_name(self.var) + ' = ' + str(self.rhs) + '\n' \
         + str(self.body)

  def uniquify(self, env: dict[str, Any], ctx: UniquifyContext) -> PTLetNew:
    new_rhs = self.rhs.uniquify(env, ctx)
    body_env = {x:y for (x,y) in env.items()}
    new_var = generate_name(self.var, ctx)
    overwrite(body_env, self.var, new_var, self.location)
    new_body = self.body.uniquify(body_env, ctx)
    return PTLetNew(self.location, new_var, new_rhs, new_body)


@dataclass
class PRecall(Proof):
  facts: List[Formula]

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self):
      return 'recall ' + ', '.join([str(f) for f in self.facts])


@dataclass
class PAnnot(Proof):
  claim: Formula
  body: Proof

  def pretty_print(self, indent: int) -> str:
      return indent*' ' + 'conclude ' + str(self.claim) + ' by {\n' \
          + self.body.pretty_print(indent+2) + '\n' \
          + indent*' ' + '}\n'

  def __str__(self):
      return 'conclude ' + str(self.claim) + ' by ' + str(self.body)

@dataclass
class Suffices(Proof):
  claim: Formula
  reason: Proof
  body: Proof

  def pretty_print(self, indent: int) -> str:
      return indent*' ' + 'suffices ' + str(self.claim) + '  by {\n' \
          + self.reason.pretty_print(indent+2) + '\n' \
          + maybe_pretty_print(self.body, indent)

  def __str__(self):
    return 'suffices ' + str(self.claim) + '  by ' + str(self.reason) + '\n' + maybe_str(self.body)

@dataclass
class Cases(Proof):
  subject: Proof
  cases: List[Tuple[str,Optional[Formula],Proof]]

  def pretty_print(self, indent: int) -> str:
      cases_str = ''
      for (label, frm, body) in self.cases:
          cases_str += indent*' ' + 'case ' + base_name(label) + ' : ' + str(frm) + '{\n' \
              + body.pretty_print(indent+2) + '\n' \
              + indent*' ' + '}'
      return '\n'.join(cases_str) + '\n'
      
  def uniquify(self, env: dict[str, Any], ctx: UniquifyContext) -> Cases:
    new_subject = self.subject.uniquify(env, ctx)
    new_cases = []
    for (label, formula, proof) in self.cases:
      body_env = {x:y for (x,y) in env.items()}
      new_formula = formula.uniquify(env, ctx) if formula else None
      new_label = generate_name(label, ctx)
      overwrite(body_env, label, new_label, self.location)
      new_proof = proof.uniquify(body_env, ctx)
      new_cases.append((new_label, new_formula, new_proof))
    return Cases(self.location, new_subject, new_cases)
      
@dataclass
class ModusPonens(Proof):
  implication: Proof
  arg: Proof

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self):
      return 'apply ' + str(self.implication) + ' to ' + str(self.arg)

@dataclass
class ImpIntro(Proof):
  label: str
  premise: Optional[Formula]
  body: Proof

  def pretty_print(self, indent: int) -> str:
    return indent*' ' + 'assume ' + str(self.label) + \
      (': ' + str(self.premise) if self.premise else '') + '\n'\
      + maybe_pretty_print(self.body, indent)
  
  def __str__(self):
    return 'assume ' + str(self.label) + \
      (': ' + str(self.premise) if self.premise else '') + \
      ('{' + str(self.body) + '}' if self.body else '')

  def uniquify(self, env: dict[str, Any], ctx: UniquifyContext) -> ImpIntro:
    new_premise = self.premise.uniquify(env, ctx) if self.premise else None
    body_env = copy_dict(env)
    new_label = generate_name(self.label, ctx)
    overwrite(body_env, self.label, new_label, self.location)
    new_body = self.body.uniquify(body_env, ctx)
    return ImpIntro(self.location, new_label, new_premise, new_body)

@dataclass
class AllIntro(Proof):
  var: Tuple[str,Type]
  # Position (s, e), where
  #  e : The number of vars in the all intro list
  #  s : The variable's index in the list, starting from the last var
  pos: Tuple[int, int]
  body: Proof

  def arbitrary_str(self) -> str:
    s, e = self.pos
    x, t = self.var
    res = ''
    if s + 1 == e:
      res += 'arbitrary '
    res += f"{x} : {str(t)}"
    if s == 0:
      res += ";"
    else:
      res += ","
    return res

  def pretty_print(self, indent: int) -> str:
      return indent*' ' + self.arbitrary_str() + '\n' \
          + maybe_pretty_print(self.body, indent)
  
  def __str__(self):
    return self.arbitrary_str() + maybe_str(self.body)

  def uniquify(self, env: dict[str, Any], ctx: UniquifyContext) -> AllIntro:
    body_env = copy_dict(env)
    x, ty = self.var
    new_t = ty.uniquify(body_env, ctx)
    new_x = generate_name(x, ctx)
    overwrite(body_env, x, new_x, self.location)
    new_body = self.body.uniquify(body_env, ctx)
    return AllIntro(self.location, (new_x, new_t), self.pos, new_body)

  def set_body(self, new_body: Proof) -> None:
    if self.body:
      cast(AllIntro, self.body).set_body(new_body)
    else:
      self.body = new_body
    
@dataclass
class AllElimTypes(Proof):
  univ: Proof
  arg: Type
  # Position (s, e), where
  #  e : The number of vars in the block
  #  s : The variable's index in the list, starting from the first var
  pos: Tuple[int, int]

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self):
    s, e = self.pos
    res = str(self.univ)
    if s == 0:
      res += f"<{self.arg}"
    else:
      res += f", {self.arg}"

    if s + 1 == e:
      res += ">"

    return res

@dataclass
class AllElim(Proof):
  univ: Proof
  arg: Term
  # Position (s, e), where
  #  e : The number of vars in the list
  #  s : The variable's index in the list, starting from the first var
  pos: Tuple[int, int]

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self):
    s, e = self.pos
    res = str(self.univ)
    if s == 0:
      res += f"[{self.arg}"
    else:
      res += f", {self.arg}"

    if s + 1 == e:
      res += "]"

    return res

@dataclass
class SomeIntro(Proof):
  witnesses: List[Term]
  body: Proof

  def pretty_print(self, indent: int) -> str:
    return indent*' ' + 'choose ' + ",".join([str(t) for t in self.witnesses]) + '\n' \
        + maybe_pretty_print(self.body, indent)

  def __str__(self):
    return 'choose ' + ",".join([str(t) for t in self.witnesses]) \
        + '; ' + maybe_str(self.body)

@dataclass
class SomeElim(Proof):
  witnesses: List[str]
  label: str
  prop: Optional[Formula]
  some: Proof
  body: Proof

  def pretty_print(self, indent: int) -> str:
    return indent*' ' + 'obtain ' + ",".join(self.witnesses) \
      + ' where ' + self.label \
      + (' : ' + str(self.prop) if self.prop else '') \
      + ' from ' + str(self.some)  + '\n'\
      + maybe_pretty_print(self.body, indent)

  def __str__(self):
    return 'obtain ' + ",".join(self.witnesses) \
      + ' where ' + self.label \
      + (' : ' + str(self.prop) if self.prop else '') \
      + ' from ' + str(self.some) \
      + '; ' + maybe_str(self.body)
  
  def uniquify(self, env: dict[str, Any], ctx: UniquifyContext) -> SomeElim:
    new_some = self.some.uniquify(env, ctx)
    body_env = copy_dict(env)
    new_witnesses = []
    for x in self.witnesses:
      new_x = generate_name(x, ctx)
      new_witnesses.append(new_x)
      overwrite(body_env, x, new_x, self.location)
    new_label = generate_name(self.label, ctx)
    overwrite(body_env, self.label, new_label, self.location)
    new_prop = self.prop.uniquify(body_env, ctx) if self.prop else None
    new_body = self.body.uniquify(body_env, ctx)
    return SomeElim(self.location, new_witnesses, new_label,
                    new_prop, new_some, new_body)
    
@dataclass
class PTuple(Proof):
  args: List[Proof]

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self):
    return ', '.join([str(arg) for arg in self.args])

def extract_tuple(pf: Proof) -> List[Proof]:
    match pf:
      case PTuple(_, pfs):
        return pfs
      case _:
       return [pf]
   
@dataclass
class PAndElim(Proof):
  which: int
  subject: Proof

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self):
    return 'conjunct ' + str(self.which) + ' of ' + str(self.subject)

@dataclass
class PTrue(Proof):

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self):
    return '.'

@dataclass
class PReflexive(Proof):

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self):
    return 'reflexive'

@dataclass
class PHole(Proof):

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self):
      return '?'

@dataclass
class PSorry(Proof):

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self):
      return 'sorry'

@dataclass
class PHelpUse(Proof):
  proof : Proof

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self):
      return 'help ' + str(self.proof)

@dataclass
class PSymmetric(Proof):
  body: Proof

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self):
    return 'symmetric ' + str(self.body)

@dataclass
class PTransitive(Proof):
  first: Proof
  second: Proof

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self):
    return 'transitive ' + str(self.first) + ' ' + str(self.second)

@dataclass
class PInjective(Proof):
  constr: Type
  body: Proof

  def pretty_print(self, indent: int) -> str:
    return indent*' ' + 'injective ' + str(self.constr) + '\n' \
        + maybe_pretty_print(self.body, indent)

  def __str__(self):
    return 'injective ' + str(self.constr) + '; ' + maybe_str(self.body)

@dataclass
class PExtensionality(Proof):
  body: Proof

  def pretty_print(self, indent: int) -> str:
    return indent*' ' + 'extensionality\n' \
        + maybe_pretty_print(self.body, indent)

  def __str__(self):
    return 'extensionality\n' + maybe_str(self.body)

@dataclass
class IndCase(AST):
  pattern: Pattern
  induction_hypotheses: list[Tuple[str,Formula]]
  body: Proof

  def pretty_print(self, indent: int) -> str:
    return indent*' ' + 'case ' + str(self.pattern) \
      + ' assume ' + ', '.join([x + ': ' + str(f) for (x,f) in self.induction_hypotheses]) \
      + '{\n' \
      + self.body.pretty_print(indent+2) \
      + indent*' ' + '}\n'
      
  def __str__(self):
    return 'case ' + str(self.pattern) \
      + ' assume ' + ', '.join([x + ': ' + str(f) for (x,f) in self.induction_hypotheses]) \
      + '{' + str(self.body) + '}'

  def uniquify(self, env: object, ctx: object) -> IndCase:
    env_map = cast(dict[str, Any], env)
    uniq_ctx = cast(UniquifyContext, ctx)
    body_env = copy_dict(env_map)
    pattern = cast(Any, self.pattern)

    new_params = [generate_name(x, uniq_ctx) for x in pattern.parameters]
    for (old, new) in zip(pattern.parameters, new_params):
      overwrite(body_env, old, new, self.location)

    new_hyp_labels = [generate_name(x, uniq_ctx) for (x, _) in self.induction_hypotheses]
    for ((old, _), new) in zip(self.induction_hypotheses, new_hyp_labels):
      overwrite(body_env, old, new, self.location)

    new_hyps: list[Tuple[str, Formula]] = []
    for ((_, f), new_label) in zip(self.induction_hypotheses, new_hyp_labels):
      new_f = f.uniquify(body_env, uniq_ctx) if f else None
      new_hyps.append((new_label, cast(Formula, new_f)))

    new_pat = pattern.with_bindings(new_params).uniquify(body_env, uniq_ctx)
    new_body = self.body.uniquify(body_env, uniq_ctx)
    return IndCase(self.location, new_pat, new_hyps, new_body)

@dataclass
class Induction(Proof):
  typ: Type
  cases: List[IndCase]

  def pretty_print(self, indent: int) -> str:
    return indent*' ' + 'induction ' + str(self.typ) + '\n' \
      + '\n'.join([c.pretty_print(indent) for c in self.cases])

  def __str__(self):
    return 'induction ' + str(self.typ) + '\n' \
      + '\n'.join([str(c) for c in self.cases])

@dataclass
class RuleInductionCase(AST):
  # `case <rule_name> { <proof> }` from a `rule induction` block.
  # The body is a complete proof of the rule's M-augmented conjunct of
  # `<pred>_rule_induction`'s `rules_hyp` (the user's `arbitrary` and
  # `assume` happen inside the body).
  rule_name: str
  body: Proof

  def pretty_print(self, indent: int) -> str:
    return indent*' ' + 'case ' + base_name(self.rule_name) + ' {\n' \
        + self.body.pretty_print(indent+2) + '\n' + indent*' ' + '}'

  def __str__(self):
    return 'case ' + base_name(self.rule_name) + ' { ' \
        + str(self.body) + ' }'

  def uniquify(self, env: object, ctx: object) -> RuleInductionCase:
    env_map = cast(dict[str, Any], env)
    uniq_ctx = cast(UniquifyContext, ctx)
    # Resolve the rule name against the env so we can match against the
    # uniquified rule names later. Wrong names are reported with a
    # did-you-mean message.
    if self.rule_name not in env_map.keys():
      from edit_distance import edit_distance
      from math import ceil
      close = [v for v in env_map.keys()
               if edit_distance(self.rule_name, v)
                  <= ceil(len(self.rule_name) / 5)]
      hint = '\n\tdid you intend: ' + ', '.join(close) if close else ''
      user_error(self.location,
                 "no such rule '" + self.rule_name + "'" + hint)
    resolved = env_map[self.rule_name]
    new_rule_name = self.rule_name
    if isinstance(resolved, list) and len(resolved) >= 1:
      new_rule_name = resolved[0]
    return RuleInductionCase(self.location, new_rule_name,
                             self.body.uniquify(env_map, uniq_ctx))

@dataclass
class RuleInduction(Proof):
  # `rule induction <pred> case <r1> { ... } ...`
  # Desugars to `apply <pred>_rule_induction[<motive>] to (<case_1>, ...,
  # <case_k>)`. The motive is inferred from the goal, which must have
  # the shape `all xs. if <pred>(xs) then Q(xs)`.
  hyp_name: str
  cases: List[RuleInductionCase]

  def pretty_print(self, indent: int) -> str:
    return indent*' ' + 'rule induction ' + base_name(self.hyp_name) + '\n' \
        + '\n'.join([c.pretty_print(indent) for c in self.cases])

  def __str__(self):
    return 'rule induction ' + base_name(self.hyp_name) + ' ' \
        + ' '.join([str(c) for c in self.cases])

  def uniquify(self, env: object, ctx: object) -> RuleInduction:
    env_map = cast(dict[str, Any], env)
    uniq_ctx = cast(UniquifyContext, ctx)
    if self.hyp_name not in env_map.keys():
      from edit_distance import edit_distance
      from math import ceil
      close = [v for v in env_map.keys()
               if edit_distance(self.hyp_name, v)
                  <= ceil(len(self.hyp_name) / 5)]
      hint = '\n\tdid you intend: ' + ', '.join(close) if close else ''
      user_error(self.location,
                 "rule induction: no such predicate '"
                 + self.hyp_name + "'" + hint)
    resolved = env_map[self.hyp_name]
    new_hyp_name = self.hyp_name
    if isinstance(resolved, list) and len(resolved) >= 1:
      new_hyp_name = resolved[0]
    return RuleInduction(self.location, new_hyp_name,
                         [c.uniquify(env_map, uniq_ctx) for c in self.cases])

@dataclass
class RuleInversion(Proof):
  # `rule inversion <pred> case <r1> { ... } ...`
  # Same shape as RuleInduction, but desugars to applying the
  # `<pred>_rule_inversion` theorem instead — the cases prove the
  # *non*-augmented rule conjuncts (no induction hypothesis).
  hyp_name: str
  cases: List[RuleInductionCase]

  def pretty_print(self, indent: int) -> str:
    return indent*' ' + 'rule inversion ' + base_name(self.hyp_name) + '\n' \
        + '\n'.join([c.pretty_print(indent) for c in self.cases])

  def __str__(self):
    return 'rule inversion ' + base_name(self.hyp_name) + ' ' \
        + ' '.join([str(c) for c in self.cases])

  def uniquify(self, env: object, ctx: object) -> RuleInversion:
    env_map = cast(dict[str, Any], env)
    uniq_ctx = cast(UniquifyContext, ctx)
    if self.hyp_name not in env_map.keys():
      from edit_distance import edit_distance
      from math import ceil
      close = [v for v in env_map.keys()
               if edit_distance(self.hyp_name, v)
                  <= ceil(len(self.hyp_name) / 5)]
      hint = '\n\tdid you intend: ' + ', '.join(close) if close else ''
      user_error(self.location,
                 "rule inversion: no such predicate '"
                 + self.hyp_name + "'" + hint)
    resolved = env_map[self.hyp_name]
    new_hyp_name = self.hyp_name
    if isinstance(resolved, list) and len(resolved) >= 1:
      new_hyp_name = resolved[0]
    return RuleInversion(self.location, new_hyp_name,
                         [c.uniquify(env_map, uniq_ctx) for c in self.cases])

@dataclass
class SwitchProofCase(AST):
  pattern: Pattern
  assumptions: list[Tuple[str,Formula]]
  body: Proof

  def pretty_print(self, indent: int) -> str:
    return indent*' ' + 'case ' + str(self.pattern) + '{\n' \
        + self.body.pretty_print(indent+2) \
        + indent*' ' + '}\n'

  def __str__(self):
    return 'case ' + str(self.pattern) + '{' + str(self.body) + '}'

  def uniquify(self, env: object, ctx: object) -> SwitchProofCase:
    env_map = cast(dict[str, Any], env)
    uniq_ctx = cast(UniquifyContext, ctx)
    body_env = copy_dict(env_map)
    pattern = cast(Any, self.pattern)

    new_params = [generate_name(x, uniq_ctx) for x in pattern.bindings()]
    for (old, new) in zip(pattern.bindings(), new_params):
      overwrite(body_env, old, new, self.location)

    new_assumption_labels = [generate_name(x, uniq_ctx) for (x, _) in self.assumptions]
    for ((old, _), new) in zip(self.assumptions, new_assumption_labels):
      overwrite(body_env, old, new, self.location)

    new_assumptions: list[Tuple[str, Formula]] = []
    for ((_, f), new_label) in zip(self.assumptions, new_assumption_labels):
      new_f = f.uniquify(body_env, uniq_ctx) if f else None
      new_assumptions.append((new_label, cast(Formula, new_f)))

    new_pat = pattern.with_bindings(new_params).uniquify(body_env, uniq_ctx)
    new_body = self.body.uniquify(body_env, uniq_ctx)
    return SwitchProofCase(self.location, new_pat,
                           new_assumptions, new_body)

@dataclass
class SwitchProof(Proof):
  subject: Term
  cases: List[SwitchProofCase]

  def pretty_print(self, indent: int) -> str:
      return indent*' ' + 'switch ' + str(self.subject) + '{\n' \
          + '\n'.join([c.pretty_print(indent+2) for c in self.cases]) \
          + indent*' ' + '}\n'

  def __str__(self):
      return 'switch ' + str(self.subject) \
        + '{' + '\n'.join([str(c) for c in self.cases]) + '}'

@dataclass
class EvaluateGoal(Proof):

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self):
    return 'evaluate'

@dataclass
class EvaluateFact(Proof):
  subject: Proof

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self):
    return 'evaluate in ' + str(self.subject)

@dataclass
class SimplifyGoal(Proof):
  body: Proof
  givens: List[Proof]

  def __str__(self):
      return 'simplify ' + ' | '.join([str(p) for p in self.givens]) + '\n' \
          + str(self.body)


@dataclass
class SimplifyFact(Proof):
  subject: Proof
  givens: List[Proof]

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self):
    return 'simplify ' \
        + ' | '.join([str(p) for p in self.givens]) \
        + ' in ' + str(self.subject)

@dataclass
class ApplyDefsGoal(Proof):
  definitions: List[Term]
  body: Proof

  def __str__(self):
      return 'expand ' + ' | '.join([str(d) for d in self.definitions]) \
        + ' ' + str(self.body)

@dataclass
class ApplyDefsFact(Proof):
  definitions: List[Term]
  subject: Proof

  def __str__(self):
      return 'expand ' + ' | '.join([str(d) for d in self.definitions]) \
        + ' in ' + str(self.subject)

@dataclass
class RewriteGoal(Proof):
  equations: List[Proof]
  body: Proof

  def __str__(self):
      return 'replace ' + '|'.join([str(eqn) for eqn in self.equations]) \
        + '\n' + str(self.body)

@dataclass
class RewriteFact(Proof):
  subject: Proof
  equations: List[Proof]

  def __str__(self):
      return 'replace ' + ','.join([str(eqn) for eqn in self.equations]) \
        + ' in ' + str(self.subject)

################ Statements ######################################

## Updates the environment with a name, creating overloads
def extend(env: dict[str, Any], name: str, new_name: str, loc: Meta) -> None:
  if name in env['no overload']:
    ty = env['no overload'][name]
    user_error(loc, f"Cannot overload {ty} names. {name} is already defined as a {ty}")

  if name in env.keys():
      if not new_name in env[name]:
          env[name].append(new_name)
  else:
    env[name] = [new_name]

## Overwrites a value in the environment, with a warning
def overwrite(env: dict[str, Any], name: str, new_name: str, loc: Meta) -> None:
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
  
  def __str__(self):
    return 'postulate ' + self.name + ': ' + str(self.what) + '\n\n'

  def uniquify(self, env: object, ctx: object) -> Postulate:
    env_map = cast(dict[str, Any], env)
    uniq_ctx = cast(UniquifyContext, ctx)
    if self.name in env_map.keys():
      user_error(self.location, "theorem names may not be overloaded")
    new_what = self.what.uniquify(env_map, uniq_ctx)
    new_name = generate_name(self.name, uniq_ctx)
    overwrite(env_map, self.name, new_name, self.location)
    env_map['no overload'][self.name] = 'theorem'
    return Postulate(self.location, new_name, new_what,
                     visibility=self.visibility)

  def collect_exports(self, export_env: dict[str, Any], importing_module: str) -> None:
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
  
  def __str__(self):
    return ('lemma ' if self.isLemma else 'theorem ') \
      + self.name + ': ' + str(self.what) \
      + '\nproof\n' + self.proof.pretty_print(2) + '\nend\n'

  def uniquify(self, env: object, ctx: object) -> Theorem:
    env_map = cast(dict[str, Any], env)
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

  def collect_exports(self, export_env: dict[str, Any], importing_module: str) -> None:
    if importing_module == get_current_module() or not self.isLemma:
      export_env[base_name(self.name)] = [self.name]
    
@dataclass
class Constructor(AST):
  name: str
  parameters: List[Type]

  def pretty_print(self, indent):
      return indent*' ' + str(self)
  
  def uniquify(self, env, body_env, ctx):
    new_params = [ty.uniquify(body_env, ctx) for ty in self.parameters]
    new_name = generate_name(self.name, ctx)
    extend(env, self.name, new_name, self.location)
    return Constructor(self.location, new_name, new_params)

  def __str__(self):
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

  def uniquify(self, env, body_env, ctx):
    new_formula = self.formula.uniquify(body_env, ctx)
    if self.name in env.keys():
      user_error(self.location,
                 "rule names may not be overloaded: " + base_name(self.name))
    new_name = generate_name(self.name, ctx)
    overwrite(env, self.name, new_name, self.location)
    env['no overload'][self.name] = 'rule'
    return Rule(self.location, new_name, new_formula)

  def __str__(self):
    return base_name(self.name) + ' : ' + str(self.formula)

  def pretty_print(self, indent):
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

  def reduce(self, env):
    return self

  def substitute(self, sub):
    return self

  def uniquify(self, env, ctx):
    if self.name in env.keys():
      user_error(self.location,
                 self.original_keyword + " names may not be overloaded: " \
                 + base_name(self.name))
    new_name = generate_name(self.name, ctx)
    env[self.name] = [new_name]
    env['no overload'][self.name] = self.original_keyword
    base_pred = base_name(self.name)

    # Pre-register the synthesised `<pred>_rule_induction` theorem name so
    # user code referencing it gets resolved correctly during uniquify.
    # The translation pass in proof_checker.py reads `rule_induction_name`
    # off the AST and emits a Theorem with that exact uniquified name.
    rule_ind_base = base_pred + '_rule_induction'
    if rule_ind_base in env.keys():
      user_error(self.location,
                 "name '" + rule_ind_base + "' is already defined; the "
                 + self.original_keyword + " '" + base_pred
                 + "' would auto-generate a theorem with that name")
    rule_ind_unique = generate_name(rule_ind_base, ctx)
    env[rule_ind_base] = [rule_ind_unique]
    env['no overload'][rule_ind_base] = 'theorem'
    # Same treatment for the inversion principle.
    rule_inv_base = base_pred + '_rule_inversion'
    if rule_inv_base in env.keys():
        user_error(self.location,
                   "name '" + rule_inv_base + "' is already defined; the "
                   + self.original_keyword + " '" + base_pred
                   + "' would auto-generate a theorem with that name")
    rule_inv_unique = generate_name(rule_inv_base, ctx)
    env[rule_inv_base] = [rule_inv_unique]
    env['no overload'][rule_inv_base] = 'theorem'

    body_env = copy_dict(env)
    new_type_params = [generate_name(t, ctx) for t in self.type_params]
    for (old, new) in zip(self.type_params, new_type_params):
      extend(body_env, old, new, self.location)

    new_signature = self.signature.uniquify(body_env, ctx)
    new_rules = [rule.uniquify(env, body_env, ctx) for rule in self.rules]

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

  def collect_exports(self, export_env, importing_module):
    if self.visibility == 'private' and importing_module != get_current_module():
      return
    export_env[base_name(self.name)] = [self.name]
    for rule in self.rules:
      extend(export_env, base_name(rule.name), rule.name, self.location)
    if self.rule_induction_name is not None:
      extend(export_env, base_name(self.rule_induction_name),
             self.rule_induction_name, self.location)

  def __str__(self):
    if get_verbose():
      shown_name = self.name
    else:
      shown_name = base_name(self.name)
    header = self.original_keyword + ' ' + shown_name
    if self.type_params:
      header += '<' + ','.join([base_name(t) for t in self.type_params]) + '>'
    body = '\n'.join('  ' + str(r) for r in self.rules)
    return header + ' : ' + str(self.signature) + ' {\n' + body + '\n}'

  def pretty_print(self, indent):
    return indent*' ' + str(self)


@dataclass
class Union(Declaration):
  type_params: List[str]
  alternatives: List[Constructor]
  param_polarities: Optional[List[str]] = None

  def reduce(self, env):
    return self
  
  def uniquify(self, env, ctx):
    if self.name in env.keys():
      user_error(self.location, "union names may not be overloaded")
    new_name = generate_name(self.name, ctx)
    env[self.name] = [new_name]
    env['no overload'][self.name] = 'union'

    body_env = copy_dict(env)
    new_type_params = [generate_name(t, ctx) for t in self.type_params]
    for (old, new) in zip(self.type_params, new_type_params):
      extend(body_env, old, new, self.location)

    new_alts = [con.uniquify(env, body_env, ctx) for con in self.alternatives]
    return Union(self.location, new_name, new_type_params, new_alts,
                 visibility=self.visibility)

  def collect_exports(self, export_env, importing_module):
    if self.visibility == 'private' and importing_module != get_current_module():
      return
    export_env[base_name(self.name)] = [self.name]

    if not self.visibility == 'opaque' or (importing_module == get_current_module()):
      for con in self.alternatives:
        extend(export_env, base_name(con.name), con.name, self.location)
    
  def substitute(self, sub):
    return self
      
  def pretty_print(self, indent):
      header = 'union ' + base_name(self.name) \
          + ('<' + ','.join([base_name(t) for t in self.type_params]) + '>' if len(self.type_params) > 0 \
             else '')
      if self.visibility == 'opaque':
        ret = header + '\n'
      else:
        ret = header + ' {\n' \
                     + '\n'.join([c.pretty_print(indent+2) for c in self.alternatives]) + '\n'\
                     + indent*' ' + '}\n'
      
      return indent*' ' + ret
  
  def __str__(self):
    if get_verbose():
      return 'union ' + self.name + '<' + ','.join(self.type_params) + '> {' \
        + ' '.join([str(c) for c in self.alternatives]) + '}'
    else:
      return base_name(self.name)
  
  
@dataclass
class FunCase(AST):
  rator: Term
  pattern: Pattern
  parameters: List[str]
  body: Term

  def pretty_print(self, indent):
      return indent*' ' + str(self.rator) + '(' + str(self.pattern) \
          + (', ' + ', '.join([base_name(p) for p in self.parameters]) if len(self.parameters) > 0 else '') \
          + ') = ' + self.body.pretty_print(indent+2)
  
  def __str__(self):
      return str(self.rator) + '(' + str(self.pattern) + ',' + ",".join(self.parameters) \
          + ') = ' + str(self.body)

  def uniquify(self, env, fun_name, ctx):
    if self.rator.name != fun_name:
        user_error(self.rator.location, 'expected function name "' + fun_name + \
                   '", not "' + str(self.rator.name) + '"')
    new_rator = self.rator.uniquify(env, ctx)
    new_pat = self.pattern.uniquify(env, ctx)
    body_env = copy_dict(env)

    match new_pat:
      case PatternCons(_, _, parameters):
        new_pat_params = [generate_name(x, ctx) for x in parameters]
        for (old, new) in zip(parameters, new_pat_params):
          overwrite(body_env, old, new, self.location)
        new_pat = new_pat.with_bindings(new_pat_params)
      case PatternBool(_, _):
        pass

    new_params = [generate_name(x, ctx) for x in self.parameters]
    for (old, new) in zip(self.parameters, new_params):
      overwrite(body_env, old, new, self.location)

    new_body = self.body.uniquify(body_env, ctx)
    return FunCase(self.location, new_rator, new_pat, new_params, new_body)


@dataclass
class RecFun(Declaration):
  type_params: List[str]
  params: List[Type]
  returns: Type
  cases: List[FunCase]

  def uniquify(self, env, ctx):
    old_name = self.name
    new_name = generate_name(self.name, ctx)
    extend(env, self.name, new_name, self.location)

    body_env = copy_dict(env)
    new_type_params = [generate_name(t, ctx) for t in self.type_params]
    for (old, new) in zip(self.type_params, new_type_params):
      extend(body_env, old, new, self.location)

    new_params = [ty.uniquify(body_env, ctx) for ty in self.params]
    new_returns = self.returns.uniquify(body_env, ctx)
    new_cases = [c.uniquify(body_env, old_name, ctx) for c in self.cases]

    return RecFun(self.location, new_name, new_type_params,
                  new_params, new_returns, new_cases,
                  visibility=self.visibility)
      
  def collect_exports(self, export_env, importing_module):
    if self.visibility == 'private' and importing_module != get_current_module():
      return
    extend(export_env, base_name(self.name), self.name, self.location)

  def __str__(self):
    if get_verbose():
      return '`' + name2str(self.name)
    else:
      return name2str(self.name)
    
  def to_string(self):
    return 'recursive ' + self.name + '<' + ','.join([name2str(t) for t in self.type_params]) + '>' \
      + '(' + ','.join([str(ty) for ty in self.params]) + ')' \
      + ' -> ' + str(self.returns) + '{\n' \
      + '\n'.join([str(c) for c in self.cases]) \
      + '\n}'

  def pretty_print(self, indent):
    header = complete_name(self.name) \
        + ('<' + ','.join([name2str(t) for t in self.type_params]) + '>' \
           if len(self.type_params) > 0 else '') \
      + '(' + ','.join([str(ty) for ty in self.params]) + ')' \
      + ' -> ' + str(self.returns)
    if self.visibility == 'opaque':
      ret = 'fun ' + header + '\n'
    else:
      ret = 'recursive ' + header + '{\n' \
      + '\n'.join([c.pretty_print(indent+2) for c in self.cases]) + '\n' \
      + '}\n'

    return indent*' ' + ret 

  def __eq__(self, other):
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

  def reduce(self, env):
    return self

  def substitute(self, sub):
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

def pretty_print_function(name, type_params, params, body):
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

  def uniquify(self, env, ctx):
    new_name = generate_name(self.name, ctx)
    extend(env, self.name, new_name, self.location)

    body_env = copy_dict(env)
    terminates_env = copy_dict(env)
    new_type_params = [generate_name(t, ctx) for t in self.type_params]
    for (old, new) in zip(self.type_params, new_type_params):
      extend(body_env, old, new, self.location)
      extend(terminates_env, old, new, self.location)

    new_returns = self.returns.uniquify(body_env, ctx)

    new_var_types = [t.uniquify(body_env, ctx) if t else None
                     for (_, t) in self.vars]
    new_vars = [(generate_name(x, ctx), nt)
                for ((x, _), nt) in zip(self.vars, new_var_types)]
    for ((old, _), (new, _)) in zip(self.vars, new_vars):
      overwrite(body_env, old, new, self.location)

    new_measure = self.measure.uniquify(body_env, ctx)
    new_measure_ty = self.measure_ty.uniquify(env, ctx)
    new_terminates = self.terminates.uniquify(terminates_env, ctx)
    new_body = self.body.uniquify(body_env, ctx)

    return GenRecFun(self.location, new_name, new_type_params,
                     new_vars, new_returns, new_measure,
                     new_measure_ty, new_body, new_terminates,
                     self.trusted_terminates, visibility=self.visibility)
    
  def collect_exports(self, export_env, importing_module):
    if self.visibility == 'private' and (importing_module != get_current_module()):
      return
    extend(export_env, base_name(self.name), self.name, self.location)

  def __str__(self):
    if get_verbose():
      return self.to_string()
    else:
      return self.name if get_unique_names() else base_name(self.name)
    
  def to_string(self):
    return 'recfun ' + self.name + '<' + ','.join(self.type_params) + '>' \
        + '(' + ', '.join([x + ':' + str(t) if t else x\
                           for (x,t) in self.vars]) + ')' \
        + ' -> ' + str(self.returns) + '\n' \
        + '\tmeasure ' + str(self.measure) \
        + ' {\n' + str(self.body) + '\n}\n' \
        + 'terminates {\n' + str(self.terminates) + '\n}\n'

  def pretty_print(self, indent):
    header = complete_name(self.name) \
        + ('<' + ','.join([name2str(t) for t in self.type_params]) + '>' \
           if len(self.type_params) > 0 else '') \
      + '(' + ', '.join([base_name(x) + ':' + str(t) if t else x for (x,t) in self.vars])\
      + ') -> ' + str(self.returns) \
      + '\nmeasure\t' + str(self.measure) + ' '
    
    if self.visibility == 'opaque':
      ret = 'fun ' + header + '\n'
    else:
      ret = 'recfun ' + header + ' {' + self.body.pretty_print(indent+2) + '\n}\n'

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
    elif isinstance(other, GenRecFun):
      return self.name == other.name
    else:
      return False
  
  def reduce(self, env: object) -> GenRecFun:
    return self

  def substitute(self, sub: object) -> GenRecFun:
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
    env = cast(dict[str, Any], env)
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
      pattern = cast(Any, c.pattern)
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

  def collect_exports(self, export_env: dict[str, Any], importing_module: str) -> None:
    if self.visibility == 'private' and (importing_module != get_current_module()):
      return
    extend(export_env, base_name(self.name), self.name, self.location)

  def __str__(self):
    return self.name if get_unique_names() else base_name(self.name)

  def pretty_print(self, indent: int) -> str:
    header = complete_name(self.name) \
        + ('<' + ','.join([name2str(t) for t in self.type_params]) + '>' \
           if len(self.type_params) > 0 else '') \
      + '(' + ', '.join([base_name(x) + ':' + str(t) if t else x for (x,t) in self.vars])\
      + ') -> ' + str(self.returns)
    ret = 'viewrec ' + header + '\nview ' + base_name(self.view_name) \
      + '(' + str(self.view_subject) + ')\n' \
      + '\n'.join([cast(str, cast(Any, c).pretty_print(indent+2))
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

  def uniquify(self, env: object, ctx: object) -> ViewDecl:
    env = cast(dict[str, Any], env)
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
    return ViewDecl(self.location, new_name, new_type_params,
                    new_source, new_target, new_into, new_out,
                    new_roundtrip, visibility=self.visibility)

  def collect_exports(self, export_env: dict[str, Any], importing_module: str) -> None:
    if self.visibility == 'private' and (importing_module != get_current_module()):
      return
    extend(export_env, base_name(self.name), self.name, self.location)

  def __str__(self):
    return self.name if get_unique_names() else base_name(self.name)

  def pretty_print(self, indent: int) -> str:
    header = complete_name(self.name) \
      + ('<' + ','.join([name2str(t) for t in self.type_params]) + '>' \
         if len(self.type_params) > 0 else '')
    ret = 'view ' + header + ' {\n' \
      + '  source ' + str(self.source) + '\n' \
      + '  target ' + str(self.target) + '\n' \
      + '  into ' + base_name(self.into) + '\n' \
      + '  out ' + base_name(self.out) + '\n' \
      + '  roundtrip ' + base_name(self.roundtrip) + '\n' \
      + '}\n'
    return indent*' ' + ret

@dataclass
class Define(Declaration):
  typ: Optional[Type]
  body: Term

  def str_header(self) -> str:
    if isinstance(self.body, Lambda):
        params = [(base_name(x), t) for (x,t) in self.body.vars]
        return pretty_print_function_header(self.name,[],params)
    elif isinstance(self.body, Generic) \
         and isinstance(self.body.body, Lambda):
        typarams = self.body.type_params
        params = [(base_name(x), t) for (x,t) in self.body.body.vars]
        return pretty_print_function_header(self.name, typarams, params)
    else:
        return 'define ' + complete_name(self.name) \
            + (' : ' + str(self.typ) if self.typ else '') + '\n'
  
  def __str__(self):
    if isinstance(self.body, Lambda):
        params = [(base_name(x), t) for (x,t) in self.body.vars]
        return pretty_print_function(self.name,[],params, self.body.body)
    elif isinstance(self.body, Generic) \
         and isinstance(self.body.body, Lambda):
        typarams = self.body.type_params
        params = [(base_name(x), t) for (x,t) in self.body.body.vars]
        return pretty_print_function(self.name, typarams, params,
                                     self.body.body.body)
    else:
        return 'define ' + complete_name(self.name) \
            + (' : ' + str(self.typ) if self.typ else '') \
            + ' = ' + self.body.pretty_print(4, False) + '\n'
    
  def pretty_print(self, indent: int) -> str:
      if self.visibility == 'opaque':
          return self.str_header()
      else:
          return str(self)
    
  def uniquify(self, env: object, ctx: object) -> Define:
    env = cast(dict[str, Any], env)
    ctx = cast(UniquifyContext, ctx)
    new_typ = self.typ.uniquify(env, ctx) if self.typ else None
    new_body = self.body.uniquify(env, ctx)

    new_name = generate_name(self.name, ctx)
    extend(env, self.name, new_name, self.location)
    return Define(self.location, new_name, new_typ, new_body,
                  visibility=self.visibility)

  def collect_exports(self, export_env: dict[str, Any], importing_module: str) -> None:
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

  def __str__(self):
    return 'assert ' + str(self.formula)

  def collect_exports(self, export_env: dict[str, Any], importing_module: str) -> None:
    pass

@dataclass
class Print(Statement):
  term : Term

  def __str__(self):
    return 'print ' + str(self.term)

  def collect_exports(self, export_env: dict[str, Any], importing_module: str) -> None:
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

  def _filter_clause_str(self):
    if self.using is not None:
      return ' using ' + ' | '.join(self.using)
    if self.hiding is not None:
      return ' hiding ' + ' | '.join(self.hiding)
    return ''

  def __str__(self):
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
    env = cast(dict[str, Any], env)
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
        cast(Any, stmt).collect_exports(env, importing_module)
    set_verbose(old_verbose)
    if get_verbose():
      print('\tuniquify finished import ' + self.name)
    set_current_module(importing_module)
    return Import(self.location, self.name, new_ast,
                  visibility=self.visibility,
                  using=self.using, hiding=self.hiding)

  def collect_exports(self, export_env: dict[str, Any], importing_module: str) -> None:
    module_name = '__module__' + self.name
    if self.visibility == 'public' and not (module_name in export_env.keys()):
      set_current_module(self.name)
      export_env[module_name] = None
      for stmt in cast(List[Statement], self.ast):
        if self._filter_admits(stmt):
          cast(Any, stmt).collect_exports(export_env, importing_module)
      set_current_module(importing_module)

@dataclass
class Auto(Statement):
  name: Term

  def key(self) -> str:
      return str(self.name)

  def print_theorems_statement(self, f: TextIO) -> None:
      print('auto ' + str(self.name) + '\n', file=f)

  def __str__(self):
    return 'auto ' + str(self.name)

  def collect_exports(self, export_env: dict[str, Any], importing_module: str) -> None:
    pass

@dataclass
class Inductive(Statement):
  typ: Type
  thm_name: Term

  def __str__(self):
    return 'inductive ' + str(self.typ) + ' by ' + str(self.thm_name)

  def collect_exports(self, export_env: dict[str, Any], importing_module: str) -> None:
    pass


@dataclass
class Module(Statement):
  name: str

  def pretty_print(self, indent):
      return indent*' ' + 'module ' + self.name + '\n'
  
  def uniquify(self, env, ctx):
      set_current_module(self.name)
      return Module(self.location, self.name)

  def collect_exports(self, export_env, importing_module):
      set_current_module(self.name)

@dataclass
class Export(Statement):
  name: str
  resolved_names: list[str] = field(default_factory=list)

  def pretty_print(self, indent):
      return indent*' ' + 'export ' + self.name + '\n'
  
  def uniquify(self, env, ctx):
      return Export(self.location, self.name, env[self.name])

  def collect_exports(self, export_env, importing_module):
      for x in self.resolved_names:
          extend(export_env, base_name(x), x, self.location)
      
@dataclass
class Associative(Statement):
  type_params: List[str]
  op: Term
  typeof: Type

  def __str__(self):
    return 'associative ' + str(self.op) \
      + ('<' + ','.join(self.type_params) + '>' if len(self.type_params) > 0 else '') \
      + ' ' + str(self.typeof)

  def uniquify(self, env, ctx):
    new_op = self.op.uniquify(env, ctx)
    body_env = {x:y for (x,y) in env.items()}
    new_type_params = [generate_name(x, ctx) for x in self.type_params]
    for (old, new) in zip(self.type_params, new_type_params):
      overwrite(body_env, old, new, self.location)
    new_typeof = self.typeof.uniquify(body_env, ctx)
    return Associative(self.location, new_type_params, new_op, new_typeof)

  def collect_exports(self, export_env, importing_module):
    opname = self.op.get_name()
    full_name = '__associative_' + opname
    base = base_name(opname)
    full_base_name = '__associative_' + base
    export_env[full_base_name] = [full_name]

@dataclass
class Trace(Statement):
  rec_fun: Var

  def __str__(self):
    return 'trace ' + str(self.rec_fun)

  def reduce(self, env):
    # Side-effecting: drives the runtime trace flag via `Var.reduce`'s
    # env-lookup path. Returns None on purpose; the default
    # `_map_children`-based `reduce` would build a fresh Trace node,
    # which is not what callers want here.
    self.rec_fun.reduce(env)

# ---------------------
# Auxiliary Functions
  
def mkEqual(loc, arg1, arg2):
  ret = Call(loc, None, ResolvedVar(loc, None, '='), [arg1, arg2])
  return ret

def split_equation(loc: Meta, equation: Term, env: Env) -> tuple[Term, Term]:
  if isinstance(equation, TLet):
    equation = equation.reduceLets(env)
    
  match equation:
    case Call(_, _, rator, [L, R]) if isinstance(rator, VarRef) and rator.get_name() == '=':
      return (L, R)
    case All(_, _, _, _, body):
      return split_equation(loc, body, env)
    case _:
      internal_error(loc, 'expected an equality, not ' + str(equation))

def equation_vars(formula: Formula) -> list[Term]:
  match formula:
    case Call(loc1, _, rator, [_, _]) if isinstance(rator, VarRef) and rator.get_name() == '=':
      return []
    case All(loc1, _, var, _, body):
      x, t = var
      v = ResolvedVar(loc1, None, x)
      v.typeof = t
      return [v] + equation_vars(body)
    case _:
      raise InternalError('equation_vars unhandled ' + str(formula))
      
def is_equation(formula):
  match formula:
    case Call(_, _, rator, [_, _]) if isinstance(rator, VarRef) and rator.get_name() == '=':
      return True
    case All(_, _, _, _, body):
      return is_equation(body)
    case _:
      return False

def isUInt(t: Term) -> bool:
  match t:
    case (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)) if base_name(n) == 'bzero':
      return True
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)), [arg]) \
      if base_name(n) == 'inc_dub':
        return isUInt(arg)
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)), [arg]) \
      if base_name(n) == 'dub_inc':
        return isUInt(arg)
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)), [arg]) \
      if base_name(n) == 'fromNat':
        return isNat(arg)
    case _:
      return False

def isBZero(t):
  match t:
    case (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)) if base_name(n) == 'bzero':
      return True
    case _:
      return False
  
def isDubInc(t):
  match t:
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)), [_]) \
      if base_name(n) == 'dub_inc':
        return True
    case _:
      return False
  
def isIncDub(t):
  match t:
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)), [_]) \
      if base_name(n) == 'inc_dub':
        return True
    case _:
      return False

def get_arg(t):
  match t:
    case Call(_, _, _, [arg]):
      return arg
    case _:
      raise InternalError('get_arg')
  
def mkBZero(loc, zname='bzero', ty=None):
  return ResolvedVar(loc, ty, zname)

def mkIncDub(loc, arg, cname='inc_dub', ty=None):
  return Call(loc, ty, ResolvedVar(loc, None, cname), [arg])

def mkDubInc(loc, arg, cname='dub_inc', ty=None):
  return Call(loc, ty, ResolvedVar(loc, None, cname), [arg])

def uint_inc(loc, x):
    if isBZero(x):
        return mkIncDub(loc, x)
    elif isDubInc(x):
        return mkIncDub(loc, uint_inc(loc, get_arg(x)))
    elif isIncDub(x):
        return mkDubInc(loc, get_arg(x))
    else:
        internal_error(loc, 'not a UInt constructor: ' + str(x))

def isSuc(t):
  match t:
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)), [_]) \
         if base_name(n) == 'suc':
      return True
    case _:
      return False

def _array_index_predecessor(pos, env):
    """Compute the predecessor of `pos` as an AST, for the index-shift
    rule in `ArrayGet.reduce` (#469).  Returns None when no decrement
    can be produced -- in which case the caller leaves the array access
    unreduced.

    Handles these positive-shape positions:
      * `1 + j` / `j + 1` (UInt) -> j  (the form produced by
        `induction UInt` / `case with i'. 1 + i'`)
      * `dub_inc(j)`      (UInt) -> `inc_dub(j)`
      * `inc_dub(j)`      (UInt) -> 2*j, computed via `_uint_double`
      * `suc(j)`          (Nat)  -> j
    """
    one_plus_arg = _try_match_one_plus(pos)
    if one_plus_arg is not None:
      return one_plus_arg
    loc = pos.location
    if isSuc(pos):
      return get_arg(pos)
    if isDubInc(pos):
      inc_dub_name = env.base_to_unique('inc_dub')
      if inc_dub_name is None:
        return None
      return mkIncDub(loc, get_arg(pos), cname=inc_dub_name)
    if isIncDub(pos):
      return _uint_double(loc, get_arg(pos), env)
    return None

def _try_match_one_plus(t):
    """If `t` is `1 + x` or `x + 1` (a Call to `+` with a numeric `1`
    on either side), return the non-`1` argument.  Otherwise return None.
    """
    if not isinstance(t, Call) or len(t.args) != 2:
      return None
    name = callable_name(t.rator)
    if name is None or base_name(name) != '+':
      return None
    a, b = t.args
    if (isUInt(a) and uintToInt(a) == 1) \
       or (isNat(a) and natToInt(a) == 1):
      return b
    if (isUInt(b) and uintToInt(b) == 1) \
       or (isNat(b) and natToInt(b) == 1):
      return a
    return None

def _uint_double(loc, x, env):
    """Return `2 * x` as a UInt AST.  Tries to reduce structurally
    (handling the three UInt constructor shapes); for a symbolic `x`
    falls back to a `Call` to the private library helper `dub` if it
    is reachable in `env`.  Returns None if neither path works.
    """
    if isBZero(x):
      bzero_name = env.base_to_unique('bzero')
      if bzero_name is None:
        return None
      return mkBZero(loc, zname=bzero_name)
    if isDubInc(x):
      # 2 * dub_inc(k) = dub_inc(inc_dub(k))
      dub_inc_name = env.base_to_unique('dub_inc')
      inc_dub_name = env.base_to_unique('inc_dub')
      if dub_inc_name is None or inc_dub_name is None:
        return None
      return mkDubInc(loc, mkIncDub(loc, get_arg(x), cname=inc_dub_name),
                      cname=dub_inc_name)
    if isIncDub(x):
      # 2 * inc_dub(k) = dub_inc(2 * k)
      inner = _uint_double(loc, get_arg(x), env)
      if inner is None:
        return None
      dub_inc_name = env.base_to_unique('dub_inc')
      if dub_inc_name is None:
        return None
      return mkDubInc(loc, inner, cname=dub_inc_name)
    dub_name = env.base_to_unique('dub')
    if dub_name is None:
      return None
    return Call(loc, None, ResolvedVar(loc, None, dub_name), [x])

# The parsers use this function to create unsigned integer literals.
def intToUInt(loc, n, bzero='bzero', dubinc='dub_inc',
              incdub='inc_dub', uint_ty=None):
    if n == 0:
        return mkBZero(loc, bzero, uint_ty)
    else:
        return uint_inc(loc, intToUInt(loc, n - 1, bzero, dubinc, incdub, uint_ty))
    
def mkZero(loc: Meta, zname: str | bool = 'zero',
           ty: Type | None = None) -> VarRef:
  # Use OverloadedVar when the name is already uniquified (contains
  # '.'), otherwise a pre-uniquify Var. Fast-arithmetic call sites
  # in the type checker pass uniquified names extracted from the
  # existing AST; parser call sites pass the bare source name.
  zname = str(zname)
  if '.' in zname:
    return ResolvedVar(loc, ty, zname)
  return Var(loc, ty, zname)

def mkSuc(loc: Meta, arg: Term, sname: str | bool = 'suc',
          ty: Type | None = None) -> Call:
  sname = str(sname)
  rator: VarRef
  if '.' in sname:
    rator = ResolvedVar(loc, None, sname)
  else:
    rator = Var(loc, None, sname)
  return Call(loc, ty, rator, [arg])

def intToNat(
    loc: Meta,
    n: int,
    zname: str | bool = 'zero',
    sname: str | bool = 'suc',
    ty: Type | None = None,
) -> Term:
  if n <= 0:
    return mkZero(loc, zname=zname, ty=ty)
  else:
    return mkSuc(loc, intToNat(loc, n - 1, zname=zname, sname=sname, ty=ty),
                 sname=sname, ty=ty)

def isNat(t: Term) -> bool:
  match t:
    case (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)) if base_name(n) == 'zero':
      return True
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)), [arg]) \
         if base_name(n) == 'suc':
      return isNat(arg)
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)), [arg]) \
         if base_name(n) == 'lit':
      return isNat(arg)
    case _:
      return False

def isLitNat(t):
  match t:
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)), [arg]) \
         if base_name(n) == 'lit':
      return isNat(arg)
    case _:
      return False

def isLitUInt(t):
  match t:
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)), [arg]) \
         if base_name(n) == 'fromNat':
      return isLitNat(arg)
    case _:
      return False
  
def isInt(t):
  match t:
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)), [arg]) \
      if base_name(n) == 'pos':
      return isUInt(arg)
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)), [arg]) \
      if base_name(n) == 'negsuc':
      return isUInt(arg)
    case _:
      return False
  
def getZero(t: Term) -> str | bool:
  match t:
    case (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)) if base_name(n) == 'zero':
      return n
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)), [arg]) \
      if base_name(n) == 'suc':
      return getZero(arg)
    case _:
      return False

def getSuc(t: Term) -> str | bool:
  match t:
    case (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)) if base_name(n) == 'zero':
      return False
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)), [_]) \
      if base_name(n) == 'suc':
      return n
    case _:
      return False

def natToInt(t: Term) -> int:
  match t:
    case (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)) if base_name(n) == 'zero':
      return 0
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)), [arg]) \
      if base_name(n) == 'suc':
      return 1 + natToInt(arg)
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)), [arg]) \
      if base_name(n) == 'lit':
      return natToInt(arg)
    case _:
      raise InternalError('natToInt: not a Nat: ' + str(t))

def uintToInt(t: Term) -> int:
  match t:
    case (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)) if base_name(n) == 'bzero':
      return 0
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)), [arg]) \
      if base_name(n) == 'dub_inc':
      return 2 * (1 + uintToInt(arg))
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)), [arg]) \
      if base_name(n) == 'inc_dub':
      return 1 + 2 * uintToInt(arg)
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)), [arg]) \
      if base_name(n) == 'fromNat':
      return natToInt(arg)
    case _:
      raise InternalError('uintToInt: not a uint ' + str(t))

def _same_numeric_literal(t1: Any, t2: Any) -> bool:
  if isNat(t1) and isNat(t2):
    return natToInt(t1) == natToInt(t2)
  if isUInt(t1) and isUInt(t2):
    return uintToInt(t1) == uintToInt(t2)
  return False

def formulas_equal_modulo_numeric_literals(frm1: Any, frm2: Any) -> bool:
  if frm1 == frm2 or _same_numeric_literal(frm1, frm2):
    return True
  match (frm1, frm2):
    case (Call(_, _, rator1, args1), Call(_, _, rator2, args2)) \
         if len(args1) == len(args2):
      return formulas_equal_modulo_numeric_literals(rator1, rator2) \
          and all(formulas_equal_modulo_numeric_literals(arg1, arg2)
                  for (arg1, arg2) in zip(args1, args2))
    case (And(_, _, args1), And(_, _, args2)) if len(args1) == len(args2):
      return all(formulas_equal_modulo_numeric_literals(arg1, arg2)
                 for (arg1, arg2) in zip(args1, args2))
    case (Or(_, _, args1), Or(_, _, args2)) if len(args1) == len(args2):
      return all(formulas_equal_modulo_numeric_literals(arg1, arg2)
                 for (arg1, arg2) in zip(args1, args2))
    case (IfThen(_, _, prem1, conc1), IfThen(_, _, prem2, conc2)):
      return formulas_equal_modulo_numeric_literals(prem1, prem2) \
          and formulas_equal_modulo_numeric_literals(conc1, conc2)
    case (All(_, _, _, _, body1), All(_, _, _, _, body2)):
      return formulas_equal_modulo_numeric_literals(body1, body2)
    case (Some(_, _, vars1, body1), Some(_, _, vars2, body2)) \
         if len(vars1) == len(vars2):
      return formulas_equal_modulo_numeric_literals(body1, body2)
    case (TermInst(_, _, subject1, tyargs1, _),
          TermInst(_, _, subject2, tyargs2, _)) \
         if len(tyargs1) == len(tyargs2):
      return formulas_equal_modulo_numeric_literals(subject1, subject2) \
          and all(formulas_equal_modulo_numeric_literals(tyarg1, tyarg2)
                  for (tyarg1, tyarg2) in zip(tyargs1, tyargs2))
    case (TermInst(_, _, subject, _, _), _):
      return formulas_equal_modulo_numeric_literals(subject, frm2)
    case (_, TermInst(_, _, subject, _, _)):
      return formulas_equal_modulo_numeric_literals(frm1, subject)
    case (TAnnote(_, _, subject1, _), _):
      return formulas_equal_modulo_numeric_literals(subject1, frm2)
    case (_, TAnnote(_, _, subject2, _)):
      return formulas_equal_modulo_numeric_literals(frm1, subject2)
    case _:
      return False

def mkUIntLit(loc, num):
    return Call(loc, None, Var(loc, None, 'fromNat'),
                [Call(loc, None, Var(loc, None, 'lit'),
                      [intToNat(loc, num)])])
  
def mkPos(loc, arg):
  return Call(loc, None, Var(loc, None, 'pos'), [arg])

def mkNeg(loc, arg):
  return Call(loc, None, Var(loc, None, 'negsuc'), [arg])

# The following is used in the parser.
def mkIntLit(loc, n, sign):
  if sign == 'PLUS':
    return mkPos(loc, mkUIntLit(loc, n))
  else:
    return mkNeg(loc, mkUIntLit(loc, n - 1))

def isDeduceInt(t: Term) -> bool:
  match t:
    case Call(_, _, (Var(_, _, name) | OverloadedVar(_, _, [name, *_]) | ResolvedVar(_, _, name)), [arg]) if base_name(name) == 'pos':
      return isUInt(arg)
    case Call(_, _, (Var(_, _, name) | OverloadedVar(_, _, [name, *_]) | ResolvedVar(_, _, name)), [arg]) if base_name(name) == 'negsuc':
      return isUInt(arg)
    case _:
      return False

def deduceIntToInt(t: Term) -> str:
  match t:
    case Call(_, _, (Var(_, _, name) | OverloadedVar(_, _, [name, *_]) | ResolvedVar(_, _, name)), [arg]) if base_name(name) == 'pos':
      return '+' + str(uintToInt(arg))
    case Call(_, _, (Var(_, _, name) | OverloadedVar(_, _, [name, *_]) | ResolvedVar(_, _, name)), [arg]) if base_name(name) == 'negsuc':
      return '-' + str(1 + uintToInt(arg))
    case _:
      internal_error(t.location, 'deduceIntToInt: expected an int, not ' + str(t))

def is_constructor(constr_name, env):
  for (name,binding) in env.dict.items():
    if isinstance(binding, TypeBinding):
      match binding.defn:
        case Union(_, _, _, alts):
          for constr in alts:
            if constr.name == constr_name:
              return True
        case _:
          continue
  return False

def is_constr_term(term, env):
  if isinstance(term, VarRef):
    return is_constructor(term.get_name(), env)
  match term:
    case TermInst(_, _, body):
      return is_constr_term(body, env)
    case _:
      return False

def constr_name(term):
  if isinstance(term, VarRef):
    return term.get_name()
  match term:
    case TermInst(_, _, body):
      return constr_name(body)
    case _:
      raise InternalError('constr_name unhandled ' + str(term))
    
def constructor_conflict(term1, term2, env):
  match (term1, term2):
    case (Call(_, _, rator1, rands1),
          Call(_, _, rator2, rands2)) if is_constr_term(rator1, env) and is_constr_term(rator2, env):
     if constr_name(rator1) != constr_name(rator2):
       return True
     else:
       return any([constructor_conflict(rand1, rand2, env) \
                   for (rand1, rand2) in zip(rands1, rands2)])
    case (Call(_, _, rator1, rands1), term2) if is_constr_term(rator1, env) and is_constr_term(term2, env):
      if constr_name(rator1) != constr_name(term2):
        return True
    case (term1, term2) if is_constr_term(term1, env) and is_constr_term(term2, env):
      if constr_name(term1) != constr_name(term2):
        return True
    case (term1, Call(_, _, rator2, rands2)) if is_constr_term(term1, env) and is_constr_term(rator2, env):
      if constr_name(term1) != constr_name(rator2):
        return True
    case (Bool(_, _, True), Bool(_, _, False)):
      return True
    case (Bool(_, _, False), Bool(_, _, True)):
      return True
  return False

def _is_named(node: object, base: str) -> bool:
  if isinstance(node, OverloadedVar):
    return base_name(node.resolved_names[0]) == base
  if isinstance(node, ResolvedVar):
    return base_name(node.name) == base
  return False

def isNodeList(t: Term) -> bool:
  match t:
    case TermInst(_, _, ctor, _, _) if _is_named(ctor, 'empty'):
      return True
    case Call(_, _, TermInst(_, _, ctor, _, _),
              [_, ls]) if _is_named(ctor, 'node'):
      return isNodeList(ls)
    case _:
      return False

def nodeListToList(t: Term) -> list[Term]:
  match t:
    case TermInst(_, _, ctor, _, _) if _is_named(ctor, 'empty'):
      return []
    case Call(_, _, TermInst(_, _, ctor, _, _),
              [arg, ls]) if _is_named(ctor, 'node'):
      return [arg] + nodeListToList(ls)
    case _:
      raise InternalError('nodeListToList: not a node list: ' + str(t))

def nodeListToString(t):
  match t:
    case TermInst(_, _, ctor, _, _) if _is_named(ctor, 'empty'):
      return ''
    case Call(_, _, TermInst(_, _, ctor, _, _),
              [arg, ls]) if _is_named(ctor, 'node'):
      return str(arg) + ', ' + nodeListToString(ls)

def mkEmpty(loc):
  return Var(loc, None, 'empty')

def mkNode(loc, arg, ls):
  return Call(loc, None, Var(loc, None, 'node'), [arg, ls])

def listToNodeList(loc, lst):
  if len(lst) == 0:
    return mkEmpty(loc)
  else:
    return mkNode(loc, lst[0], listToNodeList(loc, lst[1:]))

def isEmptySet(t):
  match t:
    case Call(_, _, fun,
              [Lambda(_, _, _, Bool(_, _, False))]) \
              if (name := callable_name(fun)) is not None \
              and base_name(name) == 'char_fun':
      return True
    case _:
      return False

@dataclass(kw_only=True)
class Binding(AST):
  module : str
  visibility : str = 'public'

@dataclass
class TypeBinding(Binding):
  defn : Optional[AST] = None

  def __str__(self):
    return str(self.defn)

@dataclass
class TermBinding(Binding):
  typ : Type
  defn : Optional[Term] = None
  local : bool = False
  
  def __str__(self):
    return str(self.typ) + (' = ' + str(self.defn) if self.defn else '')

@dataclass
class ProofBinding(Binding):
  formula : Formula
  local : bool
  
  def __str__(self):
    return str(self.formula)

@dataclass
class AutoEquationBinding(Binding):
  equations : dict[str, list[Formula]]
  fallback_equations : list[Formula] = field(default_factory=list)
  
  def __str__(self):
    head_equations = [e for equations in self.equations.values() for e in equations]
    return ', '.join([str(e) for e in head_equations + self.fallback_equations])

@dataclass
class ViewBinding(Binding):
  view: ViewDecl

  def __str__(self):
    return str(self.view)


def type_params_str(type_params):
  if len(type_params) > 0:
    return '<' + ','.join(type_params) + '>'
  else:
    return ''
  
@dataclass
class AssociativeBinding(Binding):
  opname: str
  types: List[Tuple[List[str], Type]]

  def __str__(self):
    return 'associative ' + self.opname \
      + ' ' + ', '.join(type_params_str(type_params) + str(t) \
                        for (type_params, t) in self.types)

class Env:
  def __init__(self, env: Optional[dict[str, Any]] = None) -> None:
    if env:
      self.dict = copy_dict(env)
    else:
      self.dict = {}

  # This is a hack. Not reliable. Added for GenRecFun.
  def base_to_unique(self, name):
    for k in self.dict.keys():
      if base_name(k) == name:
        return k
    return None

  def base_to_overloads(self, name):
    overloads = []
    for k in self.dict.keys():
      if base_name(k) == name:
        overloads.append(k)
    return overloads

  def __str__(self):
    return ',\n'.join(['\t' + name2str(k) + ': ' + str(v) \
                       for (k,v) in reversed(self.dict.items())])

  def __contains__(self, item):
    return item in self.dict.keys()
    
  def proofs_str(self):
    return ',\n'.join(['\t' + name2str(k) + ': ' + str(v) \
                       for (k,v) in reversed(self.dict.items()) \
                       if isinstance(v,ProofBinding) and (v.local or get_verbose() == VerboseLevel.FULL)])

  def term_vars_str(self):
    return ',\n'.join(['\t' + base_name(k) + ': ' + str(v.typ) \
                       for (k,v) in reversed(self.dict.items()) \
                       if isinstance(v,TermBinding) and v.local])
  
  def declare_type(self, loc, name, vis = 'public'):
    new_env = Env(self.dict)
    new_env.dict[name] = TypeBinding(loc, module=self.get_current_module(), visibility=vis)
    return new_env

  def declare_type_vars(self, loc, type_vars):
    new_env = self
    for x in type_vars:
      new_env = new_env.declare_type(loc, x)
    return new_env
  
  def define_type(self, loc, name, defn, visibility = 'public'):
    if defn == None:
      internal_error(loc, 'None not allowed in define_type')
    new_env = Env(self.dict)
    new_env.dict[name] = TypeBinding(loc, defn, module=self.get_current_module(), visibility=visibility)
    return new_env

  def declare_view(self, loc, view, visibility='public'):
    new_env = Env(self.dict)
    new_env.dict[view.name] = ViewBinding(loc, view,
                                          module=self.get_current_module(),
                                          visibility=visibility)
    return new_env
  
  def declare_term_var(self, loc, name, typ, local = False, visibility='public'):
    if typ == None:
      internal_error(loc, 'None not allowed as type of variable in declare_term_var')
    new_env = Env(self.dict)
    new_env.dict[name] = TermBinding(loc, typ, module=self.get_current_module(), visibility=visibility)
    new_env.dict[name].local = local
    return new_env

  def declare_assoc(self, loc, opname, typarams, typ):
    #print('declaring assoc ' + opname + ' ' + str(typ))
    new_env = Env(self.dict)
    full_name = '__associative_' + opname
    if full_name in new_env:
      old = new_env.dict[full_name]
      new_env.dict[full_name] = AssociativeBinding(loc, opname, [(typarams, typ)] + old.types,
                                                   module=self.get_current_module())
    else:
      new_env.dict[full_name] = AssociativeBinding(loc, opname, [(typarams, typ)],
                                                   module=self.get_current_module())
    return new_env

  def declare_auto_rewrite(self, loc, equation):
    new_env = Env(self.dict)
    full_name = '__auto__'
    (lhs,rhs) = split_equation(loc, equation, new_env)
    head_lhs = call_head_name(lhs)
    #print('declare auto: ' + head_lhs + '\n\t' + str(equation))
    if full_name in self.dict:
        old = cast(AutoEquationBinding, self.dict[full_name])
        new_equations = {head: [*equations]
                         for (head, equations) in old.equations.items()}
        new_fallback_equations = [*old.fallback_equations]
    else:
        new_equations = {}
        new_fallback_equations = []
    if head_lhs is None:
        new_fallback_equations.append(equation)
    else:
        new_equations.setdefault(head_lhs, []).append(equation)
    new_env.dict[full_name] = AutoEquationBinding(loc, new_equations,
                                                  new_fallback_equations,
                                                  module=self.get_current_module())
    return new_env

  def get_auto_rewrites(self, head: str | None) -> list[Formula]:
    full_name = '__auto__'
    if full_name in self.dict.keys():
        binding = cast(AutoEquationBinding, self.dict[full_name])
        if head is None:
            return binding.fallback_equations
        return binding.equations.get(head, binding.fallback_equations)
    else:
      return []

  def declare_inductive(self, loc, ind_dict, thm):
    new_env = Env(self.dict)
    full_name = '__inductive__'
    typ = ind_dict["ind_ty"]
    ind_dict["thm"] = thm
    type_name = get_type_name(typ).name

    if full_name in new_env.dict:
      if type_name in new_env.dict[full_name]:
        pass
      else:
        new_env.dict[full_name][type_name] = ind_dict
      # Check for type, overwrite/ add to existing
      pass
    else:
      new_env.dict[full_name] = {}
      new_env.dict[full_name][type_name] = ind_dict
    
    return new_env

  def get_inductive(self, typ):
    full_name = '__inductive__'
    type_name = get_type_name(typ).name
    if full_name in self.dict:
      if type_name in self.dict[full_name]:
        return self.dict[full_name][type_name]

    return None

  def declare_term_vars(self, loc, xty_pairs, local = False):
    new_env = self
    for (x,ty) in xty_pairs:
      new_env = new_env.declare_term_var(loc, x, ty, local)
    return new_env
  
  def define_term_var(self, loc, name, typ, val, visibility='public'):
    if False and typ == None:
      internal_error(loc, 'None not allowed as type in define_term_var')
    if val == None:
      internal_error(loc, 'None not allowed as value in define_term_var')
    new_env = Env(self.dict)
    new_env.dict[name] = TermBinding(loc, typ, val, module=self.get_current_module(),
                                     visibility=visibility)
    return new_env

  def define_term_vars(self, loc, xv_pairs):
    new_env = self
    for (x,v) in xv_pairs:
      new_env = new_env.define_term_var(loc, x, None, v)
    return new_env
  
  def declare_proof_var(self, loc, name, frm):
    new_env = Env(self.dict)
    new_env.dict[name] = ProofBinding(loc, frm, False, module=self.get_current_module())
    return new_env

  def declare_local_proof_var(self, loc, name, frm):
    new_env = Env(self.dict)
    new_env.dict[name] = ProofBinding(loc, frm, True, module=self.get_current_module())
    return new_env

  def declare_module(self, module):
    new_env = Env(self.dict)
    new_env.dict['__current_module__'] = module
    return new_env
  
  def declare_tracing(self, function_name: str) -> Env:
    new_env = Env(self.dict)
    if 'tracing' not in new_env.dict:
      new_env.dict['tracing'] = set()
    new_env.dict['tracing'].add(function_name)
    return new_env

  def get_current_module(self):
      return self.dict['__current_module__']
  
  def _def_of_type_var(self, curr, name):
    if name in curr.keys():
      binding = curr[name]
      if isinstance(binding, ViewBinding):
        return binding.view.source
      return binding.defn
    else:
      raise Exception('variable not in env: ' + name)
  

  def _type_of_term_var(self, curr, name):
    if name in curr.keys():
      binding = curr[name]
      if isinstance(binding, TermBinding):
        return binding.typ
      elif isinstance(binding, TypeBinding):
        return TypeType(None)
      elif isinstance(binding, ViewBinding):
        raise Exception('expected a term or type variable, not view ' + base_name(name))
      else:
        raise Exception('expected a term or type variable, not ' + base_name(name))
    else:
      return None

  def _term_var_defined(self, curr, name):
    if name in curr.keys():
      binding = curr[name]
      if isinstance(binding, TermBinding) or isinstance(binding, TypeBinding):
        return True
    return False

  def _value_of_term_var(self, curr, name):
    if name in curr.keys(): # the name '=' is not in the env
      return curr[name].defn
    else:
      return None
  
  def _formula_of_proof_var(self, curr, name):
    if name in curr.keys():
      match curr[name]:
        case ProofBinding(_, formula):
          return formula
        case TermBinding(_, FunctionType()):
          raise UserError('expected a proof but instead got term `' + base_name(name) + '`.'\
                        + '\nPerhaps you meant `expand ' + base_name(name) + '`?')
        case TermBinding():
          raise UserError('expected a proof but instead got term `' + base_name(name) + '`.'\
                        + '\nPerhaps you meant `recall ' + base_name(name) + '`?')
        case TypeBinding():
          raise UserError('expected a proof but instead got type ' + base_name(name))
        case _:
          raise UserError('expected a proof but instead got ' + base_name(name))
    else:
      return None
    
  def type_var_is_defined(self, tyname):
    if isinstance(tyname, VarRef):
      return tyname.get_name() in self.dict.keys()
    raise Exception('expected a type name, not ' + str(tyname))

  def term_var_is_defined(self, tvar):
    match tvar:
      case OverloadedVar(_, _, resolved_names):
        return any([self._term_var_defined(self.dict, x) for x in resolved_names])
      case ResolvedVar(_, _, name):
        return self._term_var_defined(self.dict, name)
      case Var(_, _, name):
        return self._term_var_defined(self.dict, name)
        
  def proof_var_is_defined(self, pvar):
    match pvar:
      case PVar(_, name):
        if self._formula_of_proof_var(self.dict, name):
          return True
        else:
          return False
      case _:
        raise Exception('expected proof var, not ' + str(pvar))

  def get_assoc_types(self, opname: str) -> list[Tuple[List[str], Type]]:
    full_name = '__associative_' + opname
    if full_name in self.dict.keys():
      return cast(AssociativeBinding, self.dict[full_name]).types
    else:
      return []
      
  def get_def_of_type_var(self, var):
    if isinstance(var, VarRef):
      return self._def_of_type_var(self.dict, var.get_name())
    raise Exception('get_def_of_type_var: unexpected ' + str(var))

  def get_view(self, name):
    if isinstance(name, VarRef):
      name = name.get_name()
    if name in self.dict and isinstance(self.dict[name], ViewBinding):
      return self.dict[name].view
    return None
      
  def get_formula_of_proof_var(self, pvar):
    match pvar:
      case PVar(_, name):
        return self._formula_of_proof_var(self.dict, name)
      case _:
        raise Exception('get_formula_of_proof_var: expected PVar, not ' + str(pvar))
          
  def get_type_of_term_var(self, tvar):
    match tvar:
      case OverloadedVar(loc, _, resolved_names):
        looked_up = [(x, self._type_of_term_var(self.dict, x)) for x in resolved_names]
        # Drop candidates not in env (e.g., overloads from modules
        # that haven't been imported here).
        overloads = [(x, ty) for (x, ty) in looked_up if ty is not None]
        if len(overloads) == 0:
          return None
        if len(overloads) > 1:
          return OverloadType(loc, overloads)
        return overloads[0][1]
      case ResolvedVar(loc, _, name):
        return self._type_of_term_var(self.dict, name)
      case Var(loc, _, name):
        return self._type_of_term_var(self.dict, name)

  def get_value_of_term_var(self, tvar):
    if isinstance(tvar, VarRef):
      return self._value_of_term_var(self.dict, tvar.get_name())
      
  def get_tracing(self, function_name: str) -> bool:
    return 'tracing' in self.dict and function_name in self.dict['tracing']

  def local_proofs(self):
    return [b.formula for (name, b) in self.dict.items() \
            if isinstance(b, ProofBinding) and b.local]

  def proofs(self):
    return [b.formula for (name, b) in self.dict.items() \
            if isinstance(b, ProofBinding)]

collected_imports: set[str] = set()

def collect_public(s: Statement, to_print: list[TheoremFilePrinting]) -> None:
    global collected_imports
    if isinstance(s, Theorem):
      if not s.isLemma:
        to_print.append(s)
    elif isinstance(s, Postulate):
      to_print.append(s)
    elif isinstance(s, Auto):
      to_print.append(s)
    elif isinstance(s, Import):
      if s.name in collected_imports:
          return
      collected_imports.add(s.name)
      if s.ast != None and s.visibility == 'public':
        for stmt in s.ast:
            collect_public(stmt, to_print)
    elif isinstance(s, Declaration) and not s.visibility == 'private':
      to_print.append(s)
      
def print_theorems(filename: str, ast: List[Statement]) -> None:
  global collected_imports
  collected_imports = set()
  fullpath = Path(filename)
  theorem_filename = fullpath.with_suffix('.thm')
  to_print: list[TheoremFilePrinting] = []
  
  for s in ast:
    collect_public(s, to_print)
  
  if len(to_print) == 0:
    return
  
  with open(theorem_filename, 'w', encoding='utf-8') as theorem_file:
    print('This file was automatically generated by Deduce.', file=theorem_file)
    print('This file summarizes the theorems proved in the file:\n\t' + filename, file=theorem_file)
    print('', file=theorem_file)
    for item in sorted(to_print, key=lambda s: s.key()):
      item.print_theorems_statement(theorem_file)

############# Marks for controlling rewriting and definitions ##################

default_mark_LHS = True

def set_default_mark_LHS(b):
  global default_mark_LHS
  default_mark_LHS = b
  
def get_default_mark_LHS():
  global default_mark_LHS
  return default_mark_LHS

@dataclass
class MarkException(BaseException):
    subject: Term

def count_marks(formula: AST) -> int:
  match formula:
    case Mark(_, _, subject):
      return 1 + count_marks(subject)
    case TermInst(_, _, subject, _, _):
      return count_marks(subject)
    case Var() | OverloadedVar() | ResolvedVar():
      return 0
    case Bool(_, _, _):
      return 0
    case And(_, _, args):
      return sum([count_marks(arg) for arg in args])
    case Or(_, _, args):
      return sum([count_marks(arg) for arg in args])
    case IfThen(_, _, prem, conc):
      return count_marks(prem) + count_marks(conc)
    case All(_, _, _, _, frm2):
      return count_marks(frm2)
    case Some(_, _, _, frm2):
      return count_marks(frm2)
    case Call(_, _, rator, args):
      return count_marks(rator) + sum([count_marks(arg) for arg in args])
    case Switch(_, _, subject, cases):
      ls : list[int] = [count_marks(c) for c in cases]
      return count_marks(subject) + sum(ls)
    case SwitchCase(_, _, body):
      return count_marks(body)
    case RecFun(_, _, _, _, _, cases):
      return 0
    case GenRecFun(_, _, _, _, _, _, _, body, _):
      return 0
    case Conditional(_, _, cond, thn, els):
      return count_marks(cond) + count_marks(thn) + count_marks(els)
    case Lambda(_, _, _, body):
      return count_marks(body)
    case Generic(_, _, _, body):
      return count_marks(body)
    case TAnnote(_, _, subject, _):
      return count_marks(subject)
    case TLet(_, _, _, rhs, body):
      return count_marks(rhs) + count_marks(body)
    case Hole(_, _):
      return 0
    case Omitted(_, _):
      return 0
    case ArrayGet(_, _, arr, ind):
      return count_marks(arr) + count_marks(ind)
    case Array(_, _, elements):
      return sum([count_marks(elt) for elt in elements])
    case MakeArray(_, _, subject):
      return count_marks(subject)
    case _:
      internal_error(formula.location, 'in count_marks function, unhandled ' + str(formula))

def find_mark(formula: AST) -> None:
  match formula:
    case Mark(_, _, subject):
      raise MarkException(subject)
    case TermInst(_, _, subject, _, _):
      find_mark(subject)
    case Var() | OverloadedVar() | ResolvedVar():
      pass
    case Bool(_, _, _):
      pass
    case And(_, _, args):
      for and_arg in args:
          find_mark(and_arg)
    case Or(_, _, args):
      for or_arg in args:
          find_mark(or_arg)
    case IfThen(_, _, prem, conc):
      find_mark(prem)
      find_mark(conc)
    case All(_, _, _, _, frm2):
      find_mark(frm2)
    case Some(_, _, _, frm2):
      find_mark(frm2)
    case Call(_, _, rator, args):
      find_mark(rator)
      for call_arg in args:
          find_mark(call_arg)
    case Switch(_, _, subject, cases):
      find_mark(subject)
      for c in cases:
          find_mark(c)
    case SwitchCase(_, _, body):
      find_mark(body)
    case RecFun(_, _, _, _, _, cases):
      pass
    case Conditional(_, _, cond, thn, els):
      find_mark(cond)
      find_mark(thn)
      find_mark(els)
    case Lambda(_, _, _, body):
      find_mark(body)
    case Generic(_, _, _, body):
      find_mark(body)
    case TAnnote(_, _, subject, _):
      find_mark(subject)
    case TLet(_, _, _, rhs, body):
      find_mark(rhs)
      find_mark(body)
    case Hole(_, _):
      pass
    case ArrayGet(_, _, arr, ind):
      find_mark(arr)
      find_mark(ind)
    case Array(_, _, elements):
      for elt in elements:
          find_mark(elt)
    case MakeArray(_, _, subject):
      find_mark(subject)
    case _:
      internal_error(formula.location, 'in find_mark function, unhandled ' + str(formula))

@overload
def replace_mark(formula: Formula, replacement: Formula) -> Formula: ...

@overload
def replace_mark(formula: Formula, replacement: Term) -> Formula: ...

@overload
def replace_mark(formula: Term, replacement: Formula) -> Term: ...

@overload
def replace_mark(formula: Term, replacement: Term) -> Term: ...

@overload
def replace_mark(formula: SwitchCase, replacement: Term) -> SwitchCase: ...

def replace_mark(formula: Term | SwitchCase, replacement: Term) -> Term | SwitchCase:
  match formula:
    case Mark(loc2, tyof, subject):
      return replacement
    case TermInst(loc2, tyof, subject, tyargs, inferred):
      return TermInst(loc2, tyof, replace_mark(subject, replacement), tyargs, inferred)
    case Var() | OverloadedVar() | ResolvedVar():
      return formula
    case Bool(loc2, tyof, _):
      return formula
    case And(loc2, tyof, args):
      return And(loc2, tyof, [replace_mark(and_arg, replacement) \
                              for and_arg in args])
    case Or(loc2, tyof, args):
      return Or(loc2, tyof, [replace_mark(or_arg, replacement) \
                             for or_arg in args])
    case IfThen(loc2, tyof, prem, conc):
      return IfThen(loc2, tyof, replace_mark(prem, replacement),
                    replace_mark(conc, replacement))
    case All(loc2, tyof, var, pos, frm2):
      return All(loc2, tyof, var, pos, replace_mark(frm2, replacement))
    case Some(loc2, tyof, vars, frm2):
      return Some(loc2, tyof, vars, replace_mark(frm2, replacement))
    case Call(loc2, tyof, rator, args):
      return Call(loc2, tyof, replace_mark(rator, replacement),
                  [replace_mark(arg, replacement) for arg in args])
    case Switch(loc2, tyof, subject, cases):
      return Switch(loc2, tyof, replace_mark(subject, replacement),
                    [replace_mark(c, replacement) for c in cases])
    case SwitchCase(loc2, pat, body):
      return SwitchCase(loc2, pat, replace_mark(body, replacement))
    case RecFun(_, _, typarams, _, _, cases):
      return formula
    case Conditional(loc2, tyof, cond, thn, els):
      return Conditional(loc2, tyof, replace_mark(cond, replacement),
                         replace_mark(thn, replacement),
                         replace_mark(els, replacement))
    case Lambda(loc2, tyof, vars, body):
      return Lambda(loc2, tyof, vars, replace_mark(body, replacement))
    case Generic(loc2, tyof, typarams, body):
      return Generic(loc2, tyof, typarams, replace_mark(body, replacement))
    case TAnnote(loc2, typof, subject, typ):
      return TAnnote(loc2, typof, replace_mark(subject, replacement), typ)
    case TLet(loc2, tyof, var, rhs, body):
      return TLet(loc2, tyof, var, replace_mark(rhs, replacement),
                  replace_mark(body, replacement))
    case Hole(loc2, tyof):
      return formula
    case ArrayGet(loc2, tyof, arr, ind):
      return ArrayGet(loc2, tyof, replace_mark(arr, replacement), replace_mark(ind, replacement))
    case Array(loc2, tyof, elements):
      return Array(loc2, tyof,
                   [replace_mark(elt, replacement) for elt in elements])
    case MakeArray(loc2, tyof, subject):
      return MakeArray(loc2, tyof, replace_mark(subject, replacement))
    case _:
      internal_error(formula.location, 'in replace_mark function, unhandled ' + str(formula))

def remove_mark(formula: Formula) -> Formula:
  num_marks = count_marks(formula)
  if num_marks == 0:
      return formula
  else:
        try:
            find_mark(formula)
            loc:Meta = formula.location
            internal_error(loc, 'in remove_mark, find_mark failed on formula:\n\t' + str(formula))
        except MarkException as ex:
            return replace_mark(formula, ex.subject)
      
def extract_and(frm):
    match frm:
      case And(_, _, args):
        return args
      case _:
       return [frm]

def extract_or(frm):
    match frm:
      case Or(_, _, args):
        return args
      case _:
       return [frm]

# --------------------------------------------------------------------------
# AST sanity checks
#
# Phase invariants encoded by the class hierarchy:
#   - parser produces ``Var`` (source-name only)
#   - ``uniquify`` produces ``OverloadedVar`` (uniquified candidates)
#   - type checking narrows ``OverloadedVar`` to ``ResolvedVar`` (single
#     chosen name) where it can; genuinely-unresolved overloads stay
#     as multi-candidate ``OverloadedVar``
#
# These walkers verify the invariants by visiting every AST descendant
# of a top-level statement list. They're meant to run after each phase
# during development, and fail fast on stray pre-uniquify ``Var`` nodes
# left behind by helper functions that haven't been migrated to the
# new class hierarchy.
# --------------------------------------------------------------------------

def _walk_ast_descendants(roots: object) -> Iterator[object]:
  """Yield every AST descendant reachable from ``roots`` (a single
  node or an iterable). Memoized by ``id()`` so shared sub-ASTs
  (e.g. cached imported-module statements) aren't revisited."""
  from dataclasses import fields, is_dataclass
  seen: set[int] = set()
  stack: list[object] = []
  if isinstance(roots, list) or isinstance(roots, tuple):
    stack.extend(roots)
  else:
    stack.append(roots)
  while stack:
    node = stack.pop()
    nid = id(node)
    if nid in seen:
      continue
    seen.add(nid)
    yield node
    if isinstance(node, list) or isinstance(node, tuple):
      stack.extend(node)
      continue
    if isinstance(node, dict):
      stack.extend(node.values())
      continue
    if isinstance(node, AST) and is_dataclass(node):
      for f in fields(node):
        child = getattr(node, f.name, None)
        if child is None:
          continue
        # Skip strings explicitly — the bound-name lists in Lambda /
        # All / Some are str values that should not be walked.
        if isinstance(child, str):
          continue
        if isinstance(child, (int, bool)):
          continue
        stack.append(child)

def check_post_uniquify_invariants(ast_list: Sequence[Statement]) -> None:
  """Assert that the AST is in canonical post-uniquify shape: every
  variable reference is an ``OverloadedVar`` or ``ResolvedVar``; no
  pre-uniquify ``Var`` survives. ``ResolvedVar`` is allowed because
  some construction helpers (mkSuc/mkZero etc. for runtime
  arithmetic) already produce a fully-narrowed reference, and that's
  fine — it just means there's nothing for type-check to do.

  Raises ``Exception`` listing up to 20 offending nodes on failure."""
  bad = []
  for node in _walk_ast_descendants(ast_list):
    if type(node) is Var:
      bad.append((getattr(node, 'location', None), node.name))
  if bad:
    msgs = []
    for (loc, name) in bad[:20]:
      loc_str = ''
      try:
        if loc is not None and not getattr(loc, 'empty', True):
          loc_str = f'{loc.filename}:{loc.line}: '
      except Exception:
        pass
      msgs.append(f'  {loc_str}pre-uniquify Var({name!r})')
    suffix = f'\n  ... and {len(bad) - 20} more' if len(bad) > 20 else ''
    raise Exception(
      'Post-uniquify AST sanity check failed: pre-uniquify `Var` '
      'nodes still present.\n'
      'Each one is a leftover construction site that wasn\'t migrated '
      'to OverloadedVar/ResolvedVar.\n' + '\n'.join(msgs) + suffix)

def check_post_typecheck_invariants(ast_list):
  """Post-typecheck invariants. Hard error on any pre-uniquify ``Var``.
  Single-candidate ``OverloadedVar`` is currently a soft warning:
  the type checker doesn't visit proof bodies yet, so those leak
  OverloadedVars even when they aren't actually overloaded. The
  invariant will go strict once ``check_proof_of`` is refactored to
  rebuild proof ASTs (tracked separately).

  Multi-candidate ``OverloadedVar`` is permitted (genuine unresolved
  overload).
  """
  def loc_prefix(loc):
    try:
      if loc is not None and not getattr(loc, 'empty', True):
        return f'{loc.filename}:{loc.line}: '
    except Exception:
      pass
    return ''
  bad_var = []
  for node in _walk_ast_descendants(ast_list):
    if type(node) is Var:
      bad_var.append((getattr(node, 'location', None), node.name))
  if bad_var:
    msgs = [f'  {loc_prefix(loc)}pre-uniquify Var({name!r})'
            for (loc, name) in bad_var[:20]]
    raise Exception(
      'Post-typecheck AST sanity check failed: pre-uniquify `Var` '
      'nodes still present.\n' + '\n'.join(msgs))

def uniquify_deduce(ast: Sequence[Statement], ctx: UniquifyContext) -> list[Statement]:
  """Uniquify ``ast`` against ``ctx``'s counter, returning the
  post-uniquify AST.

  ``ctx`` is required and threaded through every recursive
  ``uniquify`` call so the counter is explicit at every step --
  no module-level shared state.  Two calls on the same AST with a
  fresh ``UniquifyContext`` each produce byte-equal output.

  Production callers (the LSP pipeline, the CLI) typically share
  a context across the prelude bootstrap and the user's file so
  freshly generated user-file names never collide with cached
  prelude names.  Tests typically pass a fresh context for
  reproducibility.

  Each top-level statement gets its own scope segment (``"sN_"``
  appended to the caller's scope, ``name_id`` reset to ``0``) so
  edits confined to statement *N* don't perturb the bound-name
  suffixes in statement *M > N*.  That edit-invariance is what
  Phase-3 Step 14's dependency-aware cache invalidation relies on
  -- without it, the structural hash of every downstream statement
  drifts on every edit and the cache is useless.
  """
  env: dict[str, Any] = {}
  env['≠'] = ['≠']
  env['='] = ['=']
  # Using a space in the name to not collide with deduce identifiers
  env['no overload'] = {}
  outer_scope = ctx.scope
  outer_name_id = ctx.name_id
  result = []
  for i, stmt in enumerate(ast):
    ctx.scope = outer_scope + 's' + str(i) + '_'
    ctx.name_id = 0
    result.append(stmt.uniquify(env, ctx))
  # Restore the caller's scope/counter -- the per-statement reset is
  # purely local to this call.  The caller's snapshot (e.g. the LSP
  # post-prelude baseline) sees the same state it passed in, and a
  # nested ``uniquify_deduce`` (called from ``Import.uniquify``)
  # leaves no residue in the surrounding statement's scope.
  ctx.scope = outer_scope
  ctx.name_id = outer_name_id
  check_post_uniquify_invariants(result)
  return result

def make_switch_for(meta, defs, subject, cases):
  new_cases = [SwitchProofCase(c.location, c.pattern, c.assumptions,
                               ApplyDefsGoal(meta, [ResolvedVar(meta, None, t) for t in defs],
                                             c.body)) \
               for c in cases]
  return SwitchProof(meta, subject, new_cases)

@overload
def explicit_term_inst(term: Term) -> Term: ...

@overload
def explicit_term_inst(term: SwitchCase) -> SwitchCase: ...

def explicit_term_inst(term: Term | SwitchCase) -> Term | SwitchCase:
  match term:
    case TermInst(loc2, tyof, subject, tyargs, _):
      return TermInst(loc2, tyof, subject, tyargs, False)
    case Switch(loc2, tyof, subject, cases):
      return Switch(loc2, tyof, explicit_term_inst(subject),
                    [explicit_term_inst(c) for c in cases])
    case SwitchCase(loc2, pat, body):
      return SwitchCase(loc2, pat, explicit_term_inst(body))
    case Lambda(loc2, tyof, vars, body):
      return Lambda(loc2, tyof, vars, explicit_term_inst(body), env=term.env)
    case Mark(loc2, tyof, subject):
      return Mark(loc2, tyof, explicit_term_inst(subject))
    case Conditional(loc2, tyof, cond, thn, els):
      return Conditional(loc2, tyof, explicit_term_inst(cond),
                         explicit_term_inst(thn),
                         explicit_term_inst(els))
    case Generic(loc2, tyof, typarams, body):
      return Generic(loc2, tyof, typarams, explicit_term_inst(body))
    case TLet(loc2, tyof, var, rhs, body):
      return TLet(loc2, tyof, var, rhs,
                  explicit_term_inst(body))
    case _:
      return term

num_rewrites = 0
rewrite_debug: bool = False

def reset_num_rewrites():
    global num_rewrites
    num_rewrites = 0

def inc_rewrites() -> None:
    global num_rewrites
    num_rewrites = 1 + num_rewrites

def get_num_rewrites() -> int:
    global num_rewrites
    return num_rewrites

@overload
def rewrite_aux(loc: Meta, formula: Formula, equation: Formula, env: Env,
                depth: int = -1) -> Formula: ...

@overload
def rewrite_aux(loc: Meta, formula: Term, equation: Formula, env: Env,
                depth: int = -1) -> Term: ...

@overload
def rewrite_aux(loc: Meta, formula: SwitchCase, equation: Formula, env: Env,
                depth: int = -1) -> SwitchCase: ...

def rewrite_aux(loc: Meta, formula: Term | SwitchCase, equation: Formula,
                env: Env, depth: int = -1) -> Term | SwitchCase:
  if depth == 0:
      return formula
  try:
    rhs = try_rewrite(loc, formula, equation, env)
    inc_rewrites()
    return rhs
  except MatchFailed:
    if get_verbose():
      print('\tno match')
    pass
  match formula:
    case TermInst(loc2, tyof, subject, tyargs, inferred):
      return TermInst(loc2, tyof, rewrite_aux(loc, subject, equation, env, depth - 1),
                      tyargs, inferred)
    case OverloadedVar() | ResolvedVar() | Var():
      return formula
    case Bool(loc2, tyof, _):
      return formula
    case And(loc2, tyof, args):
      return And(loc2, tyof, [rewrite_aux(loc, arg, equation, env, depth - 1) for arg in args])
    case Or(loc2, tyof, args):
      return Or(loc2, tyof, [rewrite_aux(loc, arg, equation, env, depth - 1) for arg in args])
    case IfThen(loc2, tyof, prem, conc):
      return IfThen(loc2, tyof, rewrite_aux(loc, prem, equation, env, depth - 1),
                    rewrite_aux(loc, conc, equation, env, depth - 1))
    case All(loc2, tyof, var, pos, frm2):
      return All(loc2, tyof, var, pos, rewrite_aux(loc, frm2, equation, env, depth - 1))
    case Some(loc2, tyof, vars, frm2):
      return Some(loc2, tyof, vars, rewrite_aux(loc, frm2, equation, env, depth - 1))
    case Call(loc2, tyof, rator, args):
      assoc_name = callable_name(rator)
      is_assoc = assoc_name is not None \
          and is_associative(loc2, assoc_name, formula.typeof, env)
      if get_verbose():
          print('is_assoc? ' + str(is_assoc))
      if is_assoc:
          assert assoc_name is not None
          args = flatten_assoc_list(assoc_name, args)
      new_rator = rewrite_aux(loc, rator, equation, env, depth - 1)
      new_args = [rewrite_aux(loc, arg, equation, env, depth - 1) for arg in args]
      if rewrite_debug and get_verbose():
          print('while trying to rewrite ' + str(formula) + '\n\twith equation ' + str(equation))
          print('new_args: ' + ', '.join([str(arg) for arg in new_args]))
      (lhs,rhs) = split_equation(loc2, equation, env)
      arity = call_arity(lhs)
      if get_verbose():
          print('lhs = ' + str(lhs) + '\n\tarity: ' + str(arity)) 
      if is_assoc and len(new_args) > arity and arity > 1:
        # try to rewrite each arity-number of adjacent terms
        i = 0
        output_terms = []
        while i + arity <= len(new_args):
            call_args = new_args[i : i + arity]
            tmp = Call(loc2, tyof, new_rator, call_args)
            old_num_rewrites = get_num_rewrites()
            try:
               new_tmp = rewrite_aux(loc, tmp, equation, env, depth)
            except MatchFailed:
               new_tmp = tmp
            new_num_rewrites = get_num_rewrites()
            if new_num_rewrites == old_num_rewrites:
                if get_verbose():
                    print('replace using: ' + str(equation) \
                          + '\n\tdid not match: ' + str(tmp))
                output_terms.append(new_args[i])
                i = i + 1
            else:
                assert assoc_name is not None
                flat_tmp = flatten_assoc(assoc_name, new_tmp)
                if get_verbose():
                    print('rewrote: ' + str(tmp) + '\n\tinto: ' \
                          + ', '.join([str(a) for a in flat_tmp]))
                output_terms += flat_tmp
                i = i + arity
        if i < len(new_args):
            output_terms += new_args[i:]
        if len(output_terms) > 1:
            return Call(loc2, tyof, new_rator, output_terms)
        else:
            return output_terms[0]
      else: # not an associative rator
        return Call(loc2, tyof, new_rator, new_args)
  
    case Switch(loc2, tyof, subject, cases):
      return Switch(loc2, tyof, rewrite_aux(loc, subject, equation, env, depth - 1),
                    [rewrite_aux(loc, c, equation, env, depth - 1) for c in cases])
    case SwitchCase(loc2, pat, body):
      return SwitchCase(loc2, pat, rewrite_aux(loc, body, equation, env, depth - 1))
    case RecFun(loc, _, typarams, _, _, cases):
      return formula
    case Conditional(loc2, tyof, cond, thn, els):
      return Conditional(loc2, tyof, rewrite_aux(loc, cond, equation, env, depth - 1),
                         rewrite_aux(loc, thn, equation, env, depth - 1),
                         rewrite_aux(loc, els, equation, env, depth - 1))
    case Lambda(loc2, tyof, vars, body):
      return Lambda(loc2, tyof, vars, rewrite_aux(loc, body, equation, env, depth - 1))
  
    case Generic(loc2, tyof, typarams, body):
      return Generic(loc2, tyof, typarams, rewrite_aux(loc, body, equation, env, depth - 1))
  
    case TAnnote(loc2, tyof, subject, typ):
      return TAnnote(loc, tyof, rewrite_aux(loc, subject, equation, env, depth - 1), typ)

    case ArrayGet(loc2, tyof, arr, ind):
      return ArrayGet(loc, tyof, rewrite_aux(loc, arr, equation, env, depth - 1),
                      rewrite_aux(loc, ind, equation, env, depth - 1))

    case Array(loc2, tyof, elements):
      return Array(loc, tyof,
                   [rewrite_aux(loc, elt, equation, env, depth - 1)
                    for elt in elements])

    case MakeArray(loc2, tyof, subject):
      return MakeArray(loc, tyof,
                       rewrite_aux(loc, subject, equation, env, depth - 1))
  
    case TLet(loc2, tyof, var, rhs, body):
      return TLet(loc2, tyof, var, rewrite_aux(loc, rhs, equation, env, depth - 1),
                  rewrite_aux(loc, body, equation, env, depth - 1))
  
    case Hole(loc2, tyof):
      return formula

    case Omitted(loc2, tyof):
      return formula
  
    case Mark(loc, tyof, subject):
      return Mark(loc, tyof, rewrite_aux(loc, subject, equation, env, depth - 1))
  
    case _:
      internal_error(loc, 'internal error in rewrite function, unhandled ' + str(formula))

def try_rewrite(
    loc: Meta,
    formula: Term | SwitchCase,
    equation: Formula,
    env: Env,
) -> Term:
  (lhs, rhs) = split_equation(loc, equation, env)
  if rewrite_debug and get_verbose():
      print('try rewrite? ' + str(formula) + '\n\twith equation ' + str(equation))
  matching: dict[str, Term] = {}
  eq_vars = equation_vars(equation)
  formula_match(loc, eq_vars, lhs, formula, matching, Env())
  # print('rewriting using: ' + str(equation) + '\n' \
  #       + '\t' + str(formula) \
  #       + '\t==> ' + str(rhs.substitute(matching)) + '\n')
  if rewrite_debug and get_verbose():
      print('\tmatched LHS, rewriting to the RHS: ' + str(rhs.substitute(matching)))
  return rhs.substitute(matching).reduce(env)

def formula_match(
    loc: Meta,
    vars: list[Term],
    pattern_frm: Any,
    frm: Any,
    matching: dict[str, Term],
    env: Env,
    numeric_literals: bool = False,
) -> None:
  if rewrite_debug and get_verbose():
    print("formula_match:\n\t" + str(pattern_frm) + "\n\t" + str(frm) + "\n")
    print("\tin  " + ','.join([str(x) for x in vars]))
    print("\twith " + ','.join([x + ' := ' + str(f) for (x,f) in matching.items()]))
  match (pattern_frm, frm):
    case (TermInst(_, _, subject1, tyargs1, _),
          TermInst(_, _, subject2, tyargs2, _)) \
          if len(tyargs1) == len(tyargs2):
      try:
        matching2 = dict(matching)
        for (t1,t2) in zip(tyargs1, tyargs2):
          formula_match(loc, vars, t1, t2, matching2, env,
                        numeric_literals)
        formula_match(loc, vars, subject1, subject2, matching2, env,
                      numeric_literals)
        matching.clear()
        matching.update(matching2)
      except MatchFailed:
        formula_match(loc, vars, subject1, frm, matching, env,
                      numeric_literals)
        
    case (TermInst(_, _, subject, _, _), _):
      formula_match(loc, vars, subject, frm, matching, env,
                    numeric_literals)
      
    case (_, TermInst(_, _, subject, _, _)):
      formula_match(loc, vars, pattern_frm, subject, matching, env,
                    numeric_literals)
      
    case _ if isinstance(pattern_frm, VarRef) and isinstance(frm, VarRef) \
              and pattern_frm.get_name() == frm.get_name():
      pass
    case _ if isinstance(pattern_frm, VarRef) and pattern_frm in vars:
      tyvar_name = pattern_frm.get_name()
      if tyvar_name in matching.keys():
        formula_match(loc, vars, matching[tyvar_name], frm, matching, env,
                      numeric_literals)
      else:
        if get_verbose():
            print("formula_match, " + base_name(tyvar_name) + ' := ' + str(frm))
        matching[tyvar_name] = frm
        
    case (Call(_, _, goal_rator, goal_rands),
          Call(loc3, tyof3, rator, rands)):
      if rewrite_debug and get_verbose():
          print("matching Call with Call\n\trator pattern: " + str(goal_rator) + '\n'\
                + '\trator formula: ' + str(rator))
      formula_match(loc, vars, goal_rator, rator, matching, env,
                    numeric_literals)
      if len(rands) >= len(goal_rands):
        while len(rands) > 0:
          # What is the following for? -Jeremy
          rand: Term
          if len(goal_rands) == 1 and len(rands) > 1:
              rand = Call(loc3, tyof3, rator, rands)
              rands = []
          else:
              rand = rands[0]
              rands = rands[1:]
              
          goal_rand = goal_rands[0]
          goal_rands = goal_rands[1:]
            
          new_goal_rand = goal_rand.substitute(matching)
          formula_match(loc, vars, new_goal_rand, rand, matching, env,
                        numeric_literals)
          
      else:
        match_failed(loc, "formula: " + str(frm) + "\n" \
                     + "does not match expected formula: " + str(pattern_frm))
        
    case (And(_, _, goal_args),
          And(loc3, tyof3, args)):
      for (goal_arg, arg) in zip(goal_args, args):
          new_goal_arg = goal_arg.substitute(matching)
          formula_match(loc, vars, new_goal_arg, arg, matching, env,
                        numeric_literals)
    case (Or(_, _, goal_args),
          Or(loc3, tyof3, args)):
      for (goal_arg, arg) in zip(goal_args, args):
          new_goal_arg = goal_arg.substitute(matching)
          formula_match(loc, vars, new_goal_arg, arg, matching, env,
                        numeric_literals)
    case (IfThen(_, _, goal_prem, goal_conc),
          IfThen(loc3, tyof3, prem, conc)):
      formula_match(loc, vars, goal_prem, prem, matching, env,
                    numeric_literals)
      new_goal_conc = goal_conc.substitute(matching)
      formula_match(loc, vars, new_goal_conc, conc, matching, env,
                    numeric_literals)
    # UNDER CONSTRUCTION
    case _:
      red_pattern = pattern_frm.reduce(env)
      red_frm = frm.reduce(env)
      if numeric_literals:
        matched = formulas_equal_modulo_numeric_literals(red_pattern, red_frm)
      else:
        matched = red_pattern == red_frm
      if not matched:
          match_failed(loc, "formula: " + str(red_frm) + "\n" \
                       + "does not match expected formula: " + str(red_pattern))

def call_arity(call: Term) -> int:
    match call:
      case Call(_, _, _, args):
        return len(args)
      case _:
        return 1 #raise Exception('call_arity: not a call ' + str(call))

def call_head_name(term: Term) -> str | None:
    match term:
      case Call(_, _, rator, _):
          name = callable_name(rator)
          return base_name(name) if name is not None else None
      case _:
          return None
    
def auto_rewrites(term: Term, env: Env) -> Term:
    # Iterate until we can't rewrite anymore (to a fixed point)
    while True:
        current = get_num_rewrites()
        # Grab all the equations that are applicable to the head constructor
        equations = env.get_auto_rewrites(call_head_name(term))
        # Rewrite using the first equation that matches 
        for eq in equations:
            current_eq = get_num_rewrites()
            term = rewrite_aux(term.location, term, eq, env, 1)
            if current_eq < get_num_rewrites():
               break
        if current == get_num_rewrites():
            break
    return term        

################################################################################
# Alpha Equivalence
################################################################################

def alpha_equiv(t1: object, t2: object) -> bool:
  """Test alpha-equivalence between two ASTs.

  Uses a parallel walk with a two-sided binding environment: each
  side tracks ``name -> fresh tag`` for the names it has bound. At
  a variable reference, look up the name in the side's environment:
  if bound on both sides, the tags must match; if bound on one side
  only, the terms are not alpha-equivalent; if free on both, the
  names must match (modulo the pre/post-uniquify isolation that
  ``Var.__eq__`` already encodes).

  Used by ``Lambda.__eq__`` / ``All.__eq__`` / ``Some.__eq__`` /
  ``TLet.__eq__``. Replaces the older approach of substituting one
  body to rename binders before comparing -- that approach was
  per-comparison O(|body|) allocation and got the asymmetric case
  (``Lambda(y, Var(x))`` vs ``Lambda(x, Var(x))``, the constant-x
  function vs the identity function) wrong in one direction.
  """
  return _alpha_equiv(t1, t2, {}, {})


def _alpha_equiv(t1: object, t2: object,
                 env1: dict[str, object], env2: dict[str, object]) -> bool:
  # TermInst / TAnnote are transparent for equality -- existing
  # __eq__ methods unwrap them. Unwrap on both sides so the rest of
  # this function only deals with the wrapped term.
  while isinstance(t1, (TermInst, TAnnote)):
    t1 = t1.subject
  while isinstance(t2, (TermInst, TAnnote)):
    t2 = t2.subject
  # Fast path: top-level (no renaming in scope). Defer to existing
  # __eq__ which encodes the leaf-level cross-class semantics.
  if not env1 and not env2:
    return bool(t1 == t2)
  if not isinstance(t1, AST):
    return bool(t1 == t2)
  if isinstance(t1, (Var, OverloadedVar, ResolvedVar, RecFun, GenRecFun)):
    return _alpha_equiv_varref(t1, t2, env1, env2)
  if isinstance(t1, Lambda):
    if not isinstance(t2, Lambda):
      return False
    return _alpha_equiv_lambda(t1, t2, env1, env2)
  if isinstance(t1, All):
    if not isinstance(t2, All):
      return False
    return _alpha_equiv_all(t1, t2, env1, env2)
  if isinstance(t1, Some):
    if not isinstance(t2, Some):
      return False
    return _alpha_equiv_some(t1, t2, env1, env2)
  if isinstance(t1, TLet):
    if not isinstance(t2, TLet):
      return False
    return _alpha_equiv_tlet(t1, t2, env1, env2)
  if isinstance(t1, FunctionType):
    return _alpha_equiv_function_type(t1, t2, env1, env2)
  # Default: structural walk. TermInst/TAnnote already unwrapped, so
  # a class mismatch here is real.
  if type(t1) is not type(t2):
    return False
  for fld in dc_fields(t1):
    if fld.name in t1._NON_STRUCTURAL_FIELDS:
      continue
    if not _alpha_equiv_value(getattr(t1, fld.name),
                              getattr(t2, fld.name), env1, env2):
      return False
  return True


def _alpha_equiv_value(v1: object, v2: object,
                       env1: dict[str, object], env2: dict[str, object]) -> bool:
  if isinstance(v1, AST):
    return _alpha_equiv(v1, v2, env1, env2)
  if isinstance(v1, list):
    if not isinstance(v2, list) or len(v1) != len(v2):
      return False
    return all(_alpha_equiv_value(a, b, env1, env2) for a, b in zip(v1, v2))
  if isinstance(v1, tuple):
    if not isinstance(v2, tuple) or len(v1) != len(v2):
      return False
    return all(_alpha_equiv_value(a, b, env1, env2) for a, b in zip(v1, v2))
  return bool(v1 == v2)


def _alpha_equiv_varref(
    t1: Var | OverloadedVar | ResolvedVar | RecFun | GenRecFun,
    t2: object,
    env1: dict[str, object],
    env2: dict[str, object],
) -> bool:
  # Names of comparable kinds. If t2 is not a comparable kind, fail.
  if not isinstance(t2, (Var, OverloadedVar, ResolvedVar, RecFun, GenRecFun)):
    return False
  n1 = named_callable_name(t1)
  n2 = named_callable_name(t2)
  in1 = n1 in env1
  in2 = n2 in env2
  if in1 != in2:
    # One bound, the other free -- not equal.
    return False
  if in1:
    # Both bound -- tags must match (i.e. same binder pair).
    if env1[n1] is not env2[n2]:
      return False
  else:
    # Both free -- names must match.
    if n1 != n2:
      return False
  # Phase isolation, mirroring the existing __eq__ rules:
  #   * Var (pre-uniquify) only matches Var / RecFun / GenRecFun
  #   * OverloadedVar / ResolvedVar (post-uniquify) match each other
  #     and RecFun / GenRecFun, never Var
  #   * RecFun / GenRecFun match any variant by name (no phase)
  if isinstance(t1, (RecFun, GenRecFun)):
    return True
  if isinstance(t1, Var):
    return isinstance(t2, (Var, RecFun, GenRecFun))
  return isinstance(t2, (OverloadedVar, ResolvedVar, RecFun, GenRecFun))


def _alpha_equiv_binder_types(vars1: List[Tuple[str,Type]],
                              vars2: List[Tuple[str,Type]],
                              env1:dict[str,object],
                              env2:dict[str,object]) -> bool:
  # Shared by Lambda / Some: matched (name, type) pairs where `None`
  # types match any concrete type. Types are compared under the
  # *outer* envs -- the inner binder names are added only for the
  # body. This matters when a type annotation references an outer
  # bound name (e.g. `Set<T>` in `all T:type. all A:Set<T>. ...`).
  if len(vars1) != len(vars2):
    return False
  for ((_, t1), (_, t2)) in zip(vars1, vars2):
    if t1 is not None and t2 is not None and not _alpha_equiv(t1, t2, env1, env2):
      return False
  return True


def _bind(env: dict[str, object], name: str, tag: object) -> dict[str, object]:
  new = dict(env)
  new[name] = tag
  return new


def _bind_all(env: dict[str, object],
              pairs: list[tuple[str, object]]) -> dict[str, object]:
  new = dict(env)
  for (name, tag) in pairs:
    new[name] = tag
  return new


def _alpha_equiv_lambda(t1:Lambda, t2:Lambda,
                        env1:dict[str,object], env2:dict[str,object]) -> bool:
  if not _alpha_equiv_binder_types(t1.vars, t2.vars, env1, env2):
    return False
  tags = [object() for _ in t1.vars]
  new_env1 = _bind_all(env1, [(x, tag) for ((x, _), tag) in zip(t1.vars, tags)])
  new_env2 = _bind_all(env2, [(y, tag) for ((y, _), tag) in zip(t2.vars, tags)])
  return _alpha_equiv(t1.body, t2.body, new_env1, new_env2)


def _alpha_equiv_all(t1:All, t2:All,
                     env1:dict[str,object], env2:dict[str,object]) -> bool:
  (x, tx) = t1.var
  (y, ty) = t2.var
  if tx is not None and ty is not None and not _alpha_equiv(tx, ty, env1, env2):
    return False
  tag = object()
  return _alpha_equiv(t1.body, t2.body, _bind(env1, x, tag), _bind(env2, y, tag))


def _alpha_equiv_some(t1:Some, t2:Some,
                      env1:dict[str,object], env2:dict[str,object]) -> bool:
  if not _alpha_equiv_binder_types(t1.vars, t2.vars, env1, env2):
    return False
  tags = [object() for _ in t1.vars]
  new_env1 = _bind_all(env1, [(x, tag) for ((x, _), tag) in zip(t1.vars, tags)])
  new_env2 = _bind_all(env2, [(y, tag) for ((y, _), tag) in zip(t2.vars, tags)])
  return _alpha_equiv(t1.body, t2.body, new_env1, new_env2)


def _alpha_equiv_tlet(t1:TLet, t2:TLet,
                      env1:dict[str,object], env2:dict[str,object]) -> bool:
  if not _alpha_equiv(t1.rhs, t2.rhs, env1, env2):
    return False
  tag = object()
  return _alpha_equiv(t1.body, t2.body,
                      _bind(env1, t1.var, tag),
                      _bind(env2, t2.var, tag))


def _alpha_equiv_function_type(t1: FunctionType, t2: object,
                               env1: dict[str, object],
                               env2: dict[str, object]) -> bool:
  # The only `Type`-level binder: `type_params` is a list of names
  # bound in `param_types` and `return_type`. Same parallel-walk
  # pattern as `_alpha_equiv_lambda`, but `type_params` carries no
  # per-parameter type annotation -- it's just names.
  if not isinstance(t2, FunctionType):
    return False
  if len(t1.type_params) != len(t2.type_params):
    return False
  if len(t1.param_types) != len(t2.param_types):
    return False
  tags = [object() for _ in t1.type_params]
  new_env1 = _bind_all(env1, list(zip(t1.type_params, tags)))
  new_env2 = _bind_all(env2, list(zip(t2.type_params, tags)))
  for (p1, p2) in zip(t1.param_types, t2.param_types):
    if not _alpha_equiv(p1, p2, new_env1, new_env2):
      return False
  return _alpha_equiv(t1.return_type, t2.return_type, new_env1, new_env2)

################################################################################

# Back-pointers from a predicate's uniquified name to its Predicate AST
# node. Populated during Predicate.uniquify and read by the proof checker
# when desugaring `rule induction`. Persisted across check_deduce
# invocations because uniquify happens once per file.
_predicate_decls_by_unique_name: dict[str, Predicate] = {}

def get_predicate_decl(unique_name:str) -> Predicate | None:
  return _predicate_decls_by_unique_name.get(unique_name)
