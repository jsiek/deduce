"""Concrete ``Term``, ``Formula``, ``Type``, and ``Pattern`` AST nodes.

Scope: every dataclass node whose category is a value-level expression, a
type expression, a formula (logical connective/quantifier), or a pattern.
This includes the variable family (``Var``, ``OverloadedVar``,
``ResolvedVar``), ``Lambda``, ``Call``, ``Switch``/``SwitchCase``,
``TermInst``, ``MakeArray``/``ArrayGet``, ``TLet``, ``Mark``, ``Hole``,
``Omitted``; the ``Type`` nodes (``BoolType``, ``TypeType``,
``FunctionType``, ``ArrayType``, ``TypeInst``, ``GenericUnknownInst``,
...); the patterns (``PatternBool``, ``PatternCons``, ``PatternTerm``);
and the formula nodes (``Bool``, ``And``, ``Or``, ``IfThen``, ``All``,
``Some``).

Also houses the module-level mutable reduction flags
(``reduce_only``/``reduce_all``/``dont_reduce_opaque``/``eval_all``/
``reduced_defs``) and small helpers tied to term shape (``is_match``,
operator-name predicates).

Goes here:
  * a new concrete ``Term``/``Formula``/``Type``/``Pattern`` dataclass
  * helpers whose signature is purely over term-level shapes

Does NOT go here:
  * proof nodes (``proofs``), top-level statements (``declarations``)
  * literal recognizers/builders for ``zero``/``suc``/``bzero``/lists
    (``literals``)
  * whole-AST passes (``ops``) or rewrite-mark machinery (``rewrite``)
"""

from __future__ import annotations

from contextlib import contextmanager
from typing import TYPE_CHECKING

from .core import *

if TYPE_CHECKING:
    from .concepts import WhereClause, where_body, where_params
    from .declarations import FunCase, GenRecFun, RecFun, Union, overwrite
    from .env import Env, TermBinding
    from .literals import (
        _array_index_predecessor,
        _is_named,
        constructor_conflict,
        deduceIntToInt,
        getSuc,
        getZero,
        intToNat,
        isBZero,
        isDeduceInt,
        isLitNat,
        isLitUInt,
        isNat,
        isNodeList,
        isUInt,
        natToInt,
        nodeListToList,
        nodeListToString,
        ratToStr,
        try_fast_lit_nat_arith,
        try_fast_uint_arith,
        uintToInt,
    )
    from .ops import (
        _alpha_equiv_all,
        _alpha_equiv_binders,
        _alpha_equiv_function_type,
        _alpha_equiv_tlet,
        callable_name,
        explicit_term_inst,
        flatten_assoc_list,
        is_associative,
    )
    from .rewrite import auto_rewrites

################ Types ######################################

@dataclass
class IntType(Type):

  def __str__(self) -> str:
    return 'int'

  def __eq__(self, other: object) -> bool:
    return eq_fields(self, other)

  def free_vars(self) -> Set[str]:
    return set()

@dataclass
class BoolType(Type):

  def __str__(self) -> str:
    return 'bool'

  def __eq__(self, other: object) -> bool:
    return eq_fields(self, other)

  def free_vars(self) -> Set[str]:
    return set()

@dataclass
class TypeType(Type):

  def __str__(self) -> str:
    return 'type'

  def __eq__(self, other: object) -> bool:
    return eq_fields(self, other)

  def free_vars(self) -> Set[str]:
    return set()

@dataclass
class OverloadType(Type):
  types: List[Tuple[str,Type]]

  def __str__(self) -> str:
    return '(' + ' & '.join([base_name(x) + ': ' + str(ty) \
                             for (x,ty) in self.types]) + ')'

  def __eq__(self, other: object) -> bool:
    # ``&'' is an unordered set of overloads, so equality is size-sensitive
    # but order-independent: the two must have the same number of members and
    # every member type of one must appear in the other, and vice versa.
    match other:
      case OverloadType(_, types2):
        ts1 = [t for (_, t) in self.types]
        ts2 = [t for (_, t) in types2]
        return len(ts1) == len(ts2) \
           and all(any(a == b for b in ts2) for a in ts1) \
           and all(any(b == a for a in ts1) for b in ts2)
      case _:
        return False

  def free_vars(self) -> Set[str]:
    fvs = [t.free_vars() for (x,t) in self.types]
    return set().union(*fvs)


@dataclass
class FunctionType(Type):
  type_params: List[str]
  param_types: List[Type]
  return_type: Type
  # F^G's `∀t̄ where c̄. fn(τ̄) -> τ` (#1282): the concepts the type
  # parameters must model. A type application looks up their models and
  # passes their operations (see `TermInst.dicts`).
  where: Optional[WhereClause] = field(default=None, kw_only=True)

  def __str__(self) -> str:
    if len(self.type_params) > 0:
      typarams = '<' + ','.join([(x if get_verbose() else base_name(x)) for x in self.type_params]) + '> '
    else:
      typarams = ''
    if self.where is not None:
      typarams += str(self.where) + ' '
    params_str = ', '.join([str(ty) for ty in self.param_types])
    if len(self.param_types) >= 2:
      params_str = '(' + params_str + ')'
    return '(' + 'fn ' + typarams + params_str \
      + ' -> ' + str(self.return_type) + ')'

  def __eq__(self, other: object) -> bool:
    if not isinstance(other, FunctionType):
      return False
    return _alpha_equiv_function_type(self, other, {}, {})

  def free_vars(self) -> Set[str]:
    fvs = [pt.free_vars() for pt in self.param_types] \
      + [self.return_type.free_vars()]
    return set().union(*fvs) - set(self.type_params)

  def uniquify(self, env: UniquifyEnv, ctx: UniquifyContext) -> FunctionType:
    body_env, new_type_params = uniquify_type_params(
        env, self.type_params, ctx, self.location, overwrite)
    where = self.where.bind(body_env, ctx) if self.where else None
    new_param_types = [p.uniquify(body_env, ctx) for p in self.param_types]
    new_return_type = self.return_type.uniquify(body_env, ctx)
    return FunctionType(self.location, new_type_params,
                        new_param_types, new_return_type, where=where)

  def instantiate(self, tyargs: List[Type]) -> FunctionType:
    """Replace this function type's `type_params` with `tyargs`, returning a
    flat (non-generic) function type. With no type parameters, returns a
    structurally equivalent copy."""
    if not self.type_params:
      return FunctionType(self.location, [], list(self.param_types),
                          self.return_type)
    sub: dict[str, Type] = {x: t for (x, t) in zip(self.type_params, tyargs)}
    return FunctionType(
        self.location, [],
        [t.substitute(sub) for t in self.param_types],
        self.return_type.substitute(sub),
    )

@dataclass
class ArrayType(Type):
  elt_type: Type

  def __str__(self) -> str:
    return '[' + str(self.elt_type) + ']'

  def __eq__(self, other: object) -> bool:
    return eq_fields(self, other, 'elt_type')

  def free_vars(self) -> Set[str]:
    return self.elt_type.free_vars()

@dataclass
class MutableArrayType(Type):
  elt_type: Type

  def __str__(self) -> str:
    return '[' + str(self.elt_type) + ']!'

  def __eq__(self, other: object) -> bool:
    return eq_fields(self, other, 'elt_type')

  def free_vars(self) -> Set[str]:
    return self.elt_type.free_vars()

@dataclass
class TypeInst(Type):
  typ: Type
  arg_types: List[Type]

  def __str__(self) -> str:
    return str(self.typ) + \
      '<' + ','.join([str(arg) for arg in self.arg_types]) + '>'

  def __eq__(self, other: object) -> bool:
    match other:
      case TypeInst(_, typ, arg_types):
        return self.typ == typ and \
          len(self.arg_types) == len(arg_types) and \
          all([t1 == t2 for (t1, t2) in zip(self.arg_types, arg_types)])
      # case GenericUnknownInst(loc, typ):
      #   return self.typ == typ
      case _:
        return False

  def free_vars(self) -> Set[str]:
    return set().union(*[at.free_vars() for at in self.arg_types])

# This is the type of a constructor such as 'empty' of a generic union
# when we do not yet know the type arguments.
@dataclass
class GenericUnknownInst(Type):
  typ: Type

  def __str__(self) -> str:
    return str(self.typ) + '<?>'

  def __eq__(self, other: object) -> bool:
    match other:
      # case TypeInst(l, typ, arg_types):
      #   return self.typ == typ
      case GenericUnknownInst(_, typ):
        return self.typ == typ
      case _:
        return False

  def free_vars(self) -> Set[str]:
    return set()

  # The inner `typ` is the bare constructor name from a generic union
  # whose type arguments haven't been resolved yet -- substituting
  # through it would mistake the constructor for a substitutable
  # variable. Hand-roll a no-op `substitute` to override the default.
  def substitute(self, sub: object) -> Self:
    return self

def get_type_name(ty: Type | VarRef) -> Type | VarRef:
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
  def substitute(self, sub: Mapping[str, Term | Type | RecFun | GenRecFun]) -> Pattern:
    return self

  def reduce(self, env: Env) -> Pattern:
    return self

  def bindings(self) -> list[str]:
    return []

  def with_bindings(self, new_bindings: list[str]) -> Pattern:
    return self

@dataclass
class PatternBool(Pattern):
  value : bool

  def __str__(self) -> str:
      return "true" if self.value else "false"

  def bindings(self) -> list[str]:
    return []

  def with_bindings(self, new_bindings: list[str]) -> PatternBool:
    return self

@dataclass
class PatternCons(Pattern):
  constructor : Term         # typically a Var
  parameters : List[str]

  def bindings(self) -> list[str]:
    return self.parameters

  def with_bindings(self, params: list[str]) -> PatternCons:
    return PatternCons(self.location, self.constructor, params)

  def __str__(self) -> str:
      # A pattern's constructor must print as a constructor, never as the
      # value rendering `ResolvedVar._special_str` gives some constructors:
      # `case 0` would reparse as the `Nat` `zero` pattern, not UInt's
      # `bzero`, and `case rat(+0)` is not a pattern at all (Rat's `rzero`).
      # (`empty`->`[]` is not such a rendering: it reparses as the nil
      # pattern.)
      if isinstance(self.constructor, ResolvedVar) \
         and self.constructor._special_str() is not None:
        return name2str(self.constructor.name)
      if len(self.parameters) > 0:
        ctor = applied_head_str(self.constructor) or str(self.constructor)
        return ctor \
          + '(' + ', '.join([base_name(p) for p in self.parameters]) + ')'
      else:
        return str(self.constructor)

@dataclass
class PatternTerm(Pattern):
  term: Term
  parameters: list[str]

  def bindings(self) -> list[str]:
    return self.parameters

  def with_bindings(self, params: list[str]) -> PatternTerm:
    return PatternTerm(self.location, self.term, params)

  def __str__(self) -> str:
    if len(self.parameters) > 0:
      return 'with ' + ', '.join([base_name(p) for p in self.parameters]) \
        + '. ' + str(self.term)
    return str(self.term)
    
################ Terms ######################################

@dataclass
class Generic(Term):
  type_params: List[str]
  body: Term
  # A where clause on the type parameters of a `fun` (#1282). Uniquify
  # adds the operations of its refinement closure as extra parameters of
  # the body (a `Lambda`).
  where: Optional[WhereClause] = field(default=None, kw_only=True)

  def free_vars(self) -> Set[str]:
    return self.body.free_vars() - set(self.type_params)

  def _shown_body(self) -> Term:
    """The body as written: without the operations of the where clause,
    which uniquify added as parameters of the body (#1282)."""
    k = len(self.where.operations()) if self.where else 0
    if k and isinstance(self.body, Lambda):
      return Lambda(self.body.location, self.body.typeof,
                    self.body.vars[:len(self.body.vars) - k], self.body.body)
    return self.body

  def _head(self) -> str:
    return 'generic ' + ', '.join([(t if get_verbose() else base_name(t))
                                   for t in self.type_params]) \
      + (' ' + str(self.where) if self.where else '')

  def __str__(self) -> str:
    return self._head() + " { " + str(self._shown_body()) + " }"

  def pretty_print(self, indent: int, afterNewline: bool = False) -> str:
    return (indent*' ' if afterNewline else '') + self._head() \
      + ' {\n' + self._shown_body().pretty_print(indent+2, True) + '\n' \
      + indent*' ' + '}'

  def __eq__(self, other: object) -> bool:
      if not isinstance(other, Generic):
          return False
      if len(self.type_params) != len(other.type_params):
          return False
      ren = {x: ResolvedVar(self.location, None, y) \
             for (x,y) in zip(self.type_params, other.type_params) }
      new_body = self.body.substitute(ren)
      return new_body == other.body

  def uniquify(self, env: UniquifyEnv, ctx: UniquifyContext) -> Generic:
    body_env, new_type_params = uniquify_type_params(
        env, self.type_params, ctx, self.location, overwrite)
    where = self.where.bind(body_env, ctx) if self.where else None
    body = self.body.uniquify(body_env, ctx)
    if where is not None:
      if not isinstance(body, Lambda):
        static_error(self.location, 'a where clause needs a function')
      body = Lambda(body.location, body.typeof,
                    body.vars + cast(List[Tuple[str, Optional[Type]]],
                                     where_params(where)),
                    body.body)
    return Generic(self.location, self.typeof, new_type_params, body,
                   where=where)


@dataclass
class Conditional(Term):
  cond: Term
  thn: Term
  els: Term

  def __str__(self) -> str:
      return show(self)

  def pretty_print(self, indent: int, afterNewline: bool = False) -> str:
      # The then branch is followed by `else`, so an open-ended form
      # there, such as an `if` without `else`, is grouped.
      thn = (indent+2)*' ' + show(self.thn, 0, False) if _open_ended(self.thn) \
        else self.thn.pretty_print(indent+2, True)
      return ('' if afterNewline else '\n') + indent*' ' + 'if ' + show(self.cond, 0, False) \
          + ' then\n' + thn + '\n'\
          + indent*' ' + 'else\n' \
          + self.els.pretty_print(indent+2, True)

  def __eq__(self, other: object) -> bool:
    if not isinstance(other, Conditional):
      return False
    return self.cond == other.cond and self.thn == other.thn and self.els == other.els

  def reduce(self, env: Env) -> Term:
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

  def __str__(self) -> str:
      return show(self)

  def reduce(self, env: Env) -> Term:
    return self.subject.reduce(env)

  def __eq__(self, other: object) -> bool:
    if isinstance(other, TAnnote):
      return self.subject == other.subject
    return self.subject == other


@dataclass
class VarRef(Term):
  # Abstract base for variable references. Concrete subclasses are
  # `Var` (post-parse, holds a source identifier), `OverloadedVar`
  # (post-uniquify, holds uniquified candidate names), and `ResolvedVar`
  # (post-overload-resolution, holds a single chosen name). Code that
  # wants to operate on any variant should `isinstance(node, VarRef)` and
  # call `get_name()` rather than reach for a `name` field — the
  # subclasses store names differently on purpose.
  #
  # `copy`, `substitute`, `__str__`, and (for the post-uniquify forms)
  # `reduce` are shared here, driven by `get_name()` plus per-subclass
  # hooks — `_rebuild` (reconstruct with a new `typeof`),
  # `_unique_names_str` (the `--unique-names` brace form), and
  # `_special_str` (optional literal rendering, e.g. UInt `bzero` as `0`).
  #
  # The models in scope, recorded by uniquify: using a function with a
  # where clause as a value instantiates it, passing their operations
  # (#1282).
  models: List[str] = field(default_factory=list, kw_only=True)

  _NON_STRUCTURAL_FIELDS = frozenset({'location', 'typeof', 'models'})

  def get_name(self) -> str:
    internal_error(self.location, 'get_name not implemented on VarRef base')

  def free_vars(self) -> Set[str]:
    return {self.get_name()}

  def operator_str(self) -> str:
    return name2str(self.get_name())

  def _rebuild(self, typeof: Optional[Type]) -> Self:
    # Reconstruct this reference carrying a (possibly new) type
    # annotation. Each subclass rebuilds its own class with whatever
    # name payload it stores.
    internal_error(self.location, '_rebuild not implemented on VarRef base')

  def _unique_names_str(self) -> str:
    # The `name{...}` brace form shown under --unique-names. Subclasses
    # fill in the brace contents from their name payload.
    internal_error(self.location,
                   '_unique_names_str not implemented on VarRef base')

  def _special_str(self) -> str | None:
    # A subclass may render itself as a special literal (e.g. the UInt
    # zero value `bzero` as `0`); `None` means fall through to the normal
    # name / brace forms. Only overridden by `ResolvedVar`.
    return None

  def _post_uniquify_eq(self, other: object) -> bool:
    # Shared equality for the post-uniquify forms (`OverloadedVar` /
    # `ResolvedVar`): two references are equal iff their canonical names
    # match. A named callable (`RecFun` / `GenRecFun`) matches by its
    # name too, `TermInst` / `TAnnote` wrappers are transparent, and a
    # pre-uniquify `Var` (or anything else) never matches.
    if isinstance(other, (OverloadedVar, ResolvedVar, RecFun, GenRecFun)):
      return self.get_name() == other.name
    elif isinstance(other, (TermInst, TAnnote)):
      return self == other.subject
    else:
      return False

  def copy(self) -> Self:
    return self._rebuild(self.typeof)

  def substitute(self, sub: Mapping[str, Term | Type | RecFun | GenRecFun]) -> Term | RecFun | GenRecFun:
    name = self.get_name()
    if name in sub:
      trm = cast(Term | RecFun | GenRecFun, sub[name])
      if not isinstance(trm, RecFun) and not isinstance(trm, GenRecFun):
        add_reduced_def(name)
      return trm
    else:
      new_typeof = self.subst_typeof(sub)
      if new_typeof is self.typeof:
        return self
      return self._rebuild(new_typeof)

  def __str__(self) -> str:
    name = self.get_name()
    if base_name(name) == 'empty' and not get_unique_names() and not get_verbose():
      return '[]'
    special = self._special_str()
    if special is not None:
      return special
    elif get_unique_names():
      return self._unique_names_str()
    elif is_var_operator(self):
      return 'operator ' + name2str(name)
    else:
      return name2str(name)

  def reduce(self, env: Env) -> Term | RecFun | GenRecFun:  # type: ignore[override]
    # Post-uniquify references (OverloadedVar / ResolvedVar) resolve
    # against the runtime environment. `Var` is pre-uniquify and
    # overrides this to a no-op.
    if get_reduce_all() or (self in get_reduce_only()):
      name = self.get_name()
      if get_dont_reduce_opaque() and name in env.dict.keys():
        binding = env.dict[name]
        if isinstance(binding, TermBinding) \
           and binding.visibility == 'opaque' \
           and binding.module != env.get_current_module():
            return self if get_eval_all() else auto_rewrites(self, env)

      res = env.get_value_of_term_var(self)
      if res:
        if get_verbose():
          print('\t var ' + name + ' ===> ' + str(res))
        if isinstance(res, Union):
          return self if get_eval_all() else auto_rewrites(self, env)
        return res.reduce(env)
      else:
        return self if get_eval_all() else auto_rewrites(self, env)
    else:
      return self if get_eval_all() else auto_rewrites(self, env)


@dataclass
class Var(VarRef):
  # A source-level variable reference, before name resolution.
  # `name` is the identifier as written by the user. After uniquify
  # this node is replaced by `OverloadedVar`, which carries the
  # uniquified candidate names and is what the rest of the pipeline
  # operates on.
  name: str

  def get_name(self) -> str:
    return self.name

  def _rebuild(self, typeof: Optional[Type]) -> Var:
    return Var(self.location, typeof, self.name)

  def _unique_names_str(self) -> str:
    return name2str(self.name) + '{}'

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

  def reduce(self, env: Env) -> Self:
      # Pre-uniquify Vars don't appear in the runtime environment, so
      # they reduce to themselves. The post-uniquify forms
      # (`OverloadedVar` / `ResolvedVar`) use the shared VarRef.reduce.
      return self

  def uniquify(self, env: UniquifyEnv, ctx: UniquifyContext) -> OverloadedVar:  # type: ignore[override]
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

      hint = did_you_mean_hint(self.name, env.keys())
      mispell_advice = hint + '\n' if hint else ''
      static_error(self.location, 'undefined variable: ' + self.name
                   + mispell_advice + env_str)

    return OverloadedVar(self.location, self.typeof, env[self.name],
                         models=env.get(MODELS_KEY, []))


@dataclass
class OverloadedVar(VarRef):
  # A variable reference after uniquify. `resolved_names` is the
  # non-empty list of uniquified candidate names this reference could
  # resolve to. The canonical chosen name is `resolved_names[0]`;
  # overload resolution during type checking narrows the list to
  # length 1. There is *no* source-name field on this class — recover
  # it via `base_name(self.get_name())` when you need to display it.
  resolved_names: list[str]

  def __post_init__(self) -> None:
    if len(self.resolved_names) == 0:
      internal_error(self.location,
            'OverloadedVar must have at least one resolved name')

  @property
  def name(self) -> str:
    # Derived, read-only. Always equal to the canonical chosen name.
    # Exposed so ``.name`` access works uniformly with `Var`, but
    # there is no `name` field that could drift out of sync with
    # `resolved_names`.
    return self.resolved_names[0]

  def get_name(self) -> str:
    return self.resolved_names[0]

  def _rebuild(self, typeof: Optional[Type]) -> OverloadedVar:
    return OverloadedVar(self.location, typeof, list(self.resolved_names),
                         models=self.models)

  def _unique_names_str(self) -> str:
    return name2str(self.resolved_names[0]) \
           + '{' + ','.join(self.resolved_names) + '}'

  def __eq__(self, other: object) -> bool:
    return self._post_uniquify_eq(other)

  def uniquify(self, env: UniquifyEnv, ctx: UniquifyContext) -> OverloadedVar:
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

  def get_name(self) -> str:
    return self.name

  def _rebuild(self, typeof: Optional[Type]) -> ResolvedVar:
    return ResolvedVar(self.location, typeof, self.name, models=self.models)

  def _unique_names_str(self) -> str:
    return name2str(self.name) + '{' + self.name + '}'

  def __eq__(self, other: object) -> bool:
    return self._post_uniquify_eq(other)

  def _special_str(self) -> str | None:
    # UInt zero is the value `bzero`; render it as the decimal literal `0`,
    # matching the `Call.__str__` UInt branch that already prints nonzero
    # binary values (inc_dub/dub_inc trees) back as decimals. Only the
    # resolved form is special-cased (see VarRef._special_str), matching
    # the pre-consolidation behavior of #1062.
    if isBZero(self) and not get_verbose():
      return '0'
    if not get_verbose():
      return ratToStr(self)
    return None

  def uniquify(self, env: UniquifyEnv, ctx: UniquifyContext) -> ResolvedVar:
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

  def __str__(self) -> str:
    return str(self.value)


@dataclass
class Lambda(Term):
  vars: List[Tuple[str, Type | None]]
  body: Term
  # Captured runtime environment, populated by `Lambda.reduce` under
  # `--eval-all` so the closure can be applied later. `None` for an
  # un-reduced lambda.
  env: Optional['Env'] = None

  def free_vars(self) -> Set[str]:
    return (self.body.free_vars() - {x for x, _ in self.vars}).union(
      *(t.free_vars() for _, t in self.vars if t is not None))

  def __str__(self) -> str:
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
      return _alpha_equiv_binders(self, other, {}, {})

  def reduce(self, env: Env) -> Lambda:
    if get_eval_all():
      return Lambda(self.location, self.typeof, self.vars, self.body,
                    env=self.env if self.env is not None else env)
    else:
      return Lambda(self.location, self.typeof, self.vars,
                    self.body.reduce(env))

  def uniquify(self, env: UniquifyEnv, ctx: UniquifyContext) -> Lambda:
    body_env = {x:y for (x,y) in env.items()}
    new_var_types = [t.uniquify(env, ctx) if t else None
                     for (x,t) in self.vars]
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

def full_reduce(term: Term, env: Env) -> Term:
  """Reduce `term` with reduce_all and eval_all forced on, restoring the
  previous flag settings afterward."""
  old_reduce_all = get_reduce_all()
  old_eval_all = get_eval_all()
  try:
    set_reduce_all(True)
    set_eval_all(True)
    return term.reduce(env)
  finally:
    set_eval_all(old_eval_all)
    set_reduce_all(old_reduce_all)

# Definitions that were reduced.
reduced_defs: set[str] = set()

def reset_reduced_defs() -> None:
  global reduced_defs
  reduced_defs = set()

def get_reduced_defs() -> set[str]:
  global reduced_defs
  return reduced_defs

def add_reduced_def(df: str) -> None:
  global reduced_defs
  reduced_defs.add(df)

def complete_name(name: str) -> str:
    if is_operator_name(name):
        return 'operator ' + base_name(name)
    else:
        return name2str(name)
    
def is_operator_name(name: str) -> bool:
    return base_name(name) in infix_precedence.keys() \
        or base_name(name) in prefix_precedence.keys() \
        or base_name(name) in sugar_operators
    
    
def is_var_operator(trm: Term) -> bool:
  # `Var.__str__` / `OverloadedVar.__str__` use this without recursing
  # through `is_operator_callable`, which would loop on TermInst(Var(...)).
  return isinstance(trm, VarRef) and is_operator_name(trm.get_name())

def applied_head_str(rator: Term) -> Optional[str]:
  """Printed name of a var that *heads an application* (a `Call` with
  arguments, or a `PatternCons` with parameters), or `None` if `rator`
  is not such a var. The `empty` -> `[]` list-nil sugar (`Var.__str__`
  et al.) must be suppressed here: `empty` applied to arguments is a
  user constructor that merely shares the name of `List`'s nil, and
  `[](x)` does not reparse. Only the sugar differs from the ordinary
  var spelling in the non-unique, non-verbose mode where it fires, so
  outside that mode `str(rator)` is already correct and this returns
  `None`."""
  if not isinstance(rator, VarRef) or get_unique_names() or get_verbose():
    return None
  name = rator.get_name()
  if base_name(name) != 'empty':
    return None
  if is_var_operator(rator):
    return 'operator ' + name2str(name)
  return name2str(name)

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

# Printing with only the parentheses the grammar needs (#1283).
#
# Binding levels of the grammar (Deduce.lark), loosest first. `and`, `or`
# and the annotation `:` share a level; every binary level groups to the
# left; `if`, `all`, `some`, `define` and the conditional are atoms whose
# last part extends as far right as it can.
_IFF, _LOGIC, _SEP, _POINTS_TO, _EQUAL, _COMPARE, _ADD, _MULT, _EXPT, ATOM \
  = range(1, 11)
_INFIX_LEVEL = {'=': _EQUAL, '^': _EXPT}
_INFIX_LEVEL.update({op: _COMPARE for op in ('<', '>', '≤', '≥', '⊆', '∈', '≲', '≈')})
_INFIX_LEVEL.update({op: _ADD for op in ('+', '-', '∪', '∩', '⨄', '++', '∸', '⊝')})
_INFIX_LEVEL.update({op: _MULT for op in ('*', '/', '%', '∘')})

def _infix_level(trm: Call) -> int | None:
  if len(trm.args) >= 2 and is_infix_operator(trm.rator):
    return _INFIX_LEVEL.get(base_name(operator_display_name(trm.rator)))
  return None

def _connective_args(trm: And | Or) -> list[Formula | tuple[Formula, Formula]]:
  """The operands of ``trm``, with each ``if P then Q`` that is followed
  by ``if Q then P`` in an ``and`` merged into the pair ``(P, Q)``, which
  prints as ``P ⇔ Q``."""
  if isinstance(trm, Or):
    return list(trm.args)
  ret: list[Formula | tuple[Formula, Formula]] = []
  i = 0
  while i < len(trm.args):
    arg = trm.args[i]
    if isinstance(arg, IfThen) and i + 1 < len(trm.args) and not _is_negation(arg) \
       and trm.args[i + 1] == IfThen(arg.location, arg.typeof, arg.conclusion, arg.premise):
      ret.append((arg.premise, arg.conclusion))
      i += 2
    else:
      ret.append(arg)
      i += 1
  return ret

def _is_negation(trm: Term) -> bool:
  return isinstance(trm, IfThen) and isinstance(trm.conclusion, Bool) \
    and not trm.conclusion.value

def _not_equal_sides(trm: IfThen) -> tuple[Term, Term] | None:
  """``(a, b)`` when ``trm`` is ``not (a = b)``, printed ``a ≠ b``."""
  prem = trm.premise
  if _is_negation(trm) and isinstance(prem, Call) and len(prem.args) == 2:
    name = callable_name(prem.rator)
    if name is not None and base_name(name) == '=':
      return prem.args[0], prem.args[1]
  return None

def _level(trm: Term) -> int:
  match trm:
    case Call() if (level := _infix_level(trm)) is not None:
      return level
    case IfThen() if _not_equal_sides(trm) is not None:
      return _EQUAL
    case IfThen() if _is_negation(trm):
      # The grammar's `not` takes an atom, so `not y = x` is
      # `(not y) = x`; but readers take it as `not (y = x)`, so a `not`
      # is grouped where it is an operand of `=` or tighter.
      return _SEP
    case And() | Or():
      args = _connective_args(trm)
      if len(args) == 1:
        return _IFF if isinstance(args[0], tuple) else _level(args[0])
      return _LOGIC
    case TAnnote():
      return _LOGIC
    case SepConj():
      return _SEP
    case PointsTo():
      return _POINTS_TO
  return ATOM

def _open_ended(trm: Term) -> bool:
  """Whether ``trm`` starts a form whose last part extends as far right
  as it can, so that it must be last in its context."""
  match trm:
    case All() | Some() | Conditional() | TLet():
      return True
    case IfThen():
      return not _is_negation(trm)
    case And() | Or():
      args = _connective_args(trm)
      return len(args) == 1 and not isinstance(args[0], tuple) and _open_ended(args[0])
  return False

def show(trm: Term, level: int = 0, last: bool = True) -> str:
  """``trm`` printed where the context needs a term binding at least as
  tightly as ``level``, parenthesized only if the grammar needs it.
  ``last`` says whether ``trm`` ends its context, so that an open-ended
  form there needs no parentheses."""
  if _level(trm) < level or (_open_ended(trm) and not last):
    return '(' + _show(trm, True) + ')'
  return _show(trm, last)

def _show(trm: Term, last: bool) -> str:
  match trm:
    case Call(_, _, rator, args) if (level := _infix_level(trm)) is not None:
      # Left-associative: the first operand may bind as loosely as the
      # operator, the others must bind tighter. Different operators of
      # one level are grouped anyway, as in `(a * b) % m`.
      name = operator_display_name(rator)
      first = args[0]
      same = isinstance(first, Call) and _infix_level(first) == level \
        and operator_display_name(first.rator) == name
      op = ' ' + name + ' '
      return show(first, level if same else level + 1, False) + op \
        + op.join(show(arg, level + 1, last and i == len(args) - 2)
                  for i, arg in enumerate(args[1:]))
    case Call(_, _, rator, [arg]) if is_prefix_operator(rator):
      return operator_display_name(rator) + ' ' + show(arg, ATOM, last)
    case IfThen(_, _, prem, conc):
      if (sides := _not_equal_sides(trm)) is not None:
        return show(sides[0], _EQUAL, False) + ' ≠ ' + show(sides[1], _EQUAL + 1, last)
      if _is_negation(trm):
        return 'not ' + show(prem, ATOM, last)
      return 'if ' + show(prem, 0, False) + ' then ' + show(conc)
    case And() | Or():
      operands = _connective_args(trm)
      if len(operands) == 1 and not isinstance(operands[0], tuple):
        return _show(operands[0], last)
      # Mixed `and`/`or`, nested connectives and `⇔` are always
      # grouped: the grammar would group them left to right, but
      # readers expect `and` to bind tighter than `or`.
      def operand(arg: Formula | tuple[Formula, Formula], ends: bool) -> str:
        if isinstance(arg, tuple):
          iff = show(arg[0], _LOGIC + 1, False) + ' ⇔ ' + show(arg[1], _LOGIC + 1, ends)
          return iff if len(operands) == 1 else '(' + iff + ')'
        return show(arg, _LOGIC + 1, ends)
      conn = ' and ' if isinstance(trm, And) else ' or '
      return conn.join(operand(arg, last and i == len(operands) - 1)
                       for i, arg in enumerate(operands))
    case TAnnote(_, _, subject, typ):
      return show(subject, _LOGIC + 1, False) + ':' + str(typ)
    case SepConj(_, _, left, right):
      return show(left, _SEP, False) + ' ** ' + show(right, _SEP + 1, last)
    case PointsTo(_, _, address, value):
      return show(address, _POINTS_TO + 1, False) + ' |-> ' \
        + show(value, _POINTS_TO + 1, last)
    case Conditional(_, _, cond, thn, els):
      return 'if ' + show(cond, 0, False) + ' then ' + show(thn, 0, False) \
        + ' else ' + show(els)
  return trm._atomic_str()


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
  ret: Term | None = None
  if get_eval_all() and len(args) == 2  and isNat(args[0]) and isNat(args[1]):
    op = base_name(name)
    arg_x = natToInt(args[0])
    arg_y = natToInt(args[1])
    # This is a really hack-y fix
    sname = getSuc(args[0])
    sname = sname if sname else getSuc(args[1])
    zname = getZero(args[0])
    ty = return_type
    if op == '+':
      ret = intToNat(loc, arg_x + arg_y, sname=sname, zname=zname, ty=ty)
    elif op == '-':
      ret = intToNat(loc, arg_x - arg_y, sname=sname, zname=zname, ty=ty)
    elif op == '/':
      ret = intToNat(loc, arg_x // arg_y, sname=sname, zname=zname, ty=ty)
    elif op == '*':
      ret = intToNat(loc, arg_x * arg_y, sname=sname, zname=zname, ty=ty)
    elif op == '^':
      ret = intToNat(loc, arg_x ** arg_y, sname=sname, zname=zname, ty=ty)
    if ret: 
      if get_verbose():
        print(f"Doing fast arithmetic on call {arg_x} {op} {arg_y}.")
      ret.typeof = return_type
      fast_call = True

  if not fast_call:    
    body_env = env
    for (type_param, type_arg) in zip(type_params, type_args):
      subst[type_param] = type_arg
    for (param, arg) in zip(params, args):
      subst[param] = arg

    for subst_value in subst.values():
      if isinstance(subst_value, TermInst):
        subst_value.inferred = False

    if get_reduce_all() and get_eval_all():
      if get_verbose():
        print("Fast evaluate", body)
      for k, subst_value in subst.items():
        if k in type_params:
          env = env.define_type(loc, k, cast(Type, subst_value))
        else:
          trm = cast(Term, subst_value)
          # A recursive function passed as an argument has no `typeof`.
          env = env.define_term_var(loc, k, getattr(trm, 'typeof', None), trm)

      ret = body.reduce(env)
    else:
      new_fun_case_body = cast(Term, body.substitute(subst))
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
  assert ret is not None
  return explicit_term_inst(ret)


@dataclass
class Call(Term):
  rator: Term
  args: list[Term]
  # The models in scope, recorded by uniquify: a call that instantiates a
  # function with a where clause passes their operations (#1282).
  models: List[str] = field(default_factory=list, kw_only=True)

  _NON_STRUCTURAL_FIELDS = frozenset({'location', 'typeof', 'models'})

  def __str__(self) -> str:
    return show(self)

  def uniquify(self, env: UniquifyEnv, ctx: UniquifyContext) -> Call:
    ret = super().uniquify(env, ctx)
    ret.models = env.get(MODELS_KEY, [])
    return ret

  def _atomic_str(self) -> str:
    if is_infix_operator(self.rator) and len(self.args) >= 2:
      # An infix operator without a printing level (`and`, `or`, `⇔`
      # used as a function).
      op_str = ' ' + operator_display_name(self.rator) + ' '
      return '(' + op_str.join(show(arg, ATOM) for arg in self.args) + ')'
    elif isDeduceInt(self):
      return deduceIntToInt(self)
    elif (rat := ratToStr(self)) is not None and not get_verbose():
      return rat
    elif isLitNat(self): # and not get_verbose():
      return 'ℕ' + str(natToInt(self))
    # elif isNat(self): # and not get_verbose():
    #   return '`' + str(natToInt(self))
    elif isLitUInt(self): # and not get_verbose():
      return str(uintToInt(self))
    elif isUInt(self) and not get_verbose():
      return str(uintToInt(self))
    elif isNodeList(self):
      node_list = nodeListToString(self)
      assert node_list is not None
      return '[' + node_list[:-2] + ']'
    else:
      rator_str = applied_head_str(self.rator) or str(self.rator)
      # The parser parses a Call's rator at the `parse_array_get` level,
      # which only accepts atoms, array accesses, and chained calls. An
      # operator-call rator (e.g. `f ∘ g`) must be parenthesized so the
      # printed form reparses as `Call(Call(∘, f, g), [args])` instead of
      # `Call(∘, f, Call(g, [args]))`.
      if _level(self.rator) < ATOM or _open_ended(self.rator):
        rator_str = "(" + rator_str + ")"
      return rator_str + "(" \
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

  def reduce(self, env: Env) -> Term:
    fun = cast(Term | RecFun | GenRecFun, self.rator.reduce(env))
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
    # Fast path: arithmetic/comparison on `lit`-wrapped Nat literals
    # collapses to a single literal (or Bool) without unfolding the
    # step-by-step auto-rewrite rules (lit_suc_mult, lit_suc_add,
    # le_lit_suc, lit_expt_suc, ...).  Those rules are correct but
    # O(N^2) for N-digit operands, which makes proofs that touch a
    # concrete `P(10)` instance take minutes (see #746).
    if not get_eval_all():
      fast = try_fast_lit_nat_arith(self.location, self.rator, args, self.typeof,
                                    env)
      if fast is not None:
        return auto_rewrites(fast, env)
    else:
      fast_uint = try_fast_uint_arith(self.location, self.rator, args,
                                      self.typeof, env)
      if fast_uint is not None:
        return fast_uint
    ret: Term | None = None
    match fun:
      case Var(loc, _, '=') | OverloadedVar(loc, _, ['=']) | ResolvedVar(loc, _, '='):
        if args[0] == args[1]:
          ret = Bool(loc, BoolType(loc), True)
        elif constructor_conflict(args[0], args[1], env):
          ret = Bool(loc, BoolType(loc), False)
        else:
          ret = Call(self.location, self.typeof, cast(Term, fun), args)
      case (OverloadedVar() | ResolvedVar()) if is_assoc:
        assert assoc_name is not None
        ret = Call(self.location, self.typeof, cast(Term, fun),
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

        subst: dict[str, Term | Type] = {k: v for ((k,t),v) in zip(params, args)}
        ret = do_function_call(loc, name, [], [], [x for (x,t) in params], args,
                               body, subst, env, None,
                               display_args=args)

      case TermInst(loc, _, subject, type_args) if isinstance(subject, GenRecFun):
        gen_fun = cast(GenRecFun, subject)
        name = gen_fun.name
        typarams = gen_fun.type_params
        params = gen_fun.vars
        body = gen_fun.body
        subst2: dict[str, Term | Type] = {k: v for ((k,t),v) in zip(params, args)}
        ret = do_function_call(loc, name, typarams, type_args, [x for (x,t) in params], args,
                               body, subst2, env, None,
                               display_args=args)
    
      case RecFun(loc, name, [], params, returns, cases):
        ret = self.do_recursive_call(loc, name, cast(Term | RecFun, fun), [], [], params, args,
                                     returns, cases, is_assoc, env)
      case TermInst(loc, _, subject, type_args) if isinstance(subject, RecFun):
        rec_fun = cast(RecFun, subject)
        name = rec_fun.name
        typarams = rec_fun.type_params
        params = rec_fun.params
        returns = rec_fun.returns
        cases = rec_fun.cases
        # The operations for a where clause come after the arguments
        # (#1282); a call that doesn't reduce keeps them in `fun`.
        dicts = fun.dicts
        ret = self.do_recursive_call(loc, name, cast(Term | RecFun, fun), typarams, type_args,
                                     params, args + dicts, returns, cases,
                                     is_assoc and not dicts, env)
        if dicts and isinstance(ret, Call) and ret.rator is fun:
          ret = Call(self.location, self.typeof, ret.rator,
                     ret.args[:len(ret.args) - len(dicts)])
      case Generic(_, _, typarams, body):
        internal_error(self.location, 'in reduction, call to generic\n\t' + str(self))
      case _:
        ret = Call(self.location, self.typeof, cast(Term, fun), args)

    if not get_eval_all():
        assert ret is not None
        ret = auto_rewrites(ret, env)
    
    assert ret is not None
    return ret

  def do_call(self, loc: Meta, vars: list[tuple[str, Type | None]],
              body: Term, args: list[Term], env: Env,
              name: str = "anonymous") -> Term:
    # because of associativity, args can be longer than vars.
    # ``name`` is the source-visible name of the function being
    # called -- caller passes the result of ``callable_name(self.rator)``
    # so debugger traps and trace output see ``foo`` rather than
    # ``anonymous`` when the lambda came from a named binding.
    subst: dict[str, Term | Type] = {k: v for ((k,t),v) in zip(vars, args)}
    return do_function_call(loc, name, [], [], [], [], body, subst, env, None,
                            display_args=args)

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
          subst: dict[str, Term] = {}
          if is_match(fun_case.pattern, first_arg, subst):
              # Pass the matched case's own location to
              # ``do_function_call``, not the RecFun's overall
              # location.  This is what surfaces in the debugger's
              # ``-> call ... at L:C`` line and what ``list`` points
              # the ``->`` arrow at -- the user wants the *matched
              # case body* (line 13/14 for ``count_down``'s base /
              # inductive case), not the bare ``recursive`` header
              # on line 12.
              subst_for_call: dict[str, Term | Type] = dict(subst)
              return do_function_call(fun_case.location, name,
                                      type_params, type_args,
                                      fun_case.parameters, rest_args,
                                      fun_case.body, subst_for_call, env, returns,
                                      display_args=args)
    if is_assoc:
      if get_verbose():
        print('not reducing recursive call to associative ' + str(fun))
      return Call(self.location, self.typeof, cast(Term, fun),
                 flatten_assoc_list(name, args))
    else:
      if get_verbose():
        print('not reducing recursive call to ' + str(fun))
      return Call(self.location, self.typeof, cast(Term, fun), args)
  
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
    new_args: list[Term] = []
    worklist: list[Term] = args
    while len(worklist) > 1:
      first_arg = worklist[0]; worklist = worklist[1:]
      did_call = False
      for fun_case in cases:
          subst: dict[str, Term] = {}
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
              subst_for_call: dict[str, Term | Type] = dict(subst)
              result = do_function_call(fun_case.location, name,
                                        type_params, type_args,
                                        fun_case.parameters, rest_args,
                                        fun_case.body, subst_for_call, env, returns,
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
      return Call(self.location, self.typeof, cast(Term, fun), flat_results)


@dataclass
class SwitchCase(AST):
  pattern: Pattern
  body: Term

  def __str__(self) -> str:
      return 'case ' + str(self.pattern) + ' { ' + str(self.body) + ' }'

  def pretty_print(self, indent: int, afterNewline: bool = False) -> str:
      return indent*' ' + 'case ' + str(self.pattern) + ' {\n' \
          + (indent+2)*' ' + str(self.body) + '\n'\
          + indent*' ' + '}'

  def uniquify(self, env: UniquifyEnv, ctx: UniquifyContext) -> SwitchCase:
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
        if len(params1) != len(params2):
          return False
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

  def free_vars(self) -> Set[str]:
    return self.subject.free_vars().union(
      *(c.body.free_vars() - set(c.pattern.bindings()) for c in self.cases))

  def __str__(self) -> str:
      return 'switch ' + str(self.subject) + ' { ' \
          + ' '.join([str(c) for c in self.cases]) \
          + ' }'

  def pretty_print(self, indent: int, afterNewline: bool = False) -> str:
      return ('' if afterNewline else '\n') + indent*' '+ 'switch ' + str(self.subject) + ' {\n' \
          + '\n'.join([c.pretty_print(indent+2) for c in self.cases]) + '\n'\
          + indent*' ' + '}'

  def reduce(self, env: Env) -> Term:
      new_subject = self.subject.reduce(env)
      for c in self.cases:
          subst: dict[str, Term] = {}
          if is_match(c.pattern, new_subject, subst):
            if get_verbose():
              print('switch, matched ' + str(c.pattern) + ' and ' \
                    + str(new_subject))
            if get_eval_all():
              for k, v in subst.items():
                env = env.define_term_var(self.location, k, v.typeof, v)
              ret = c.body.reduce(env)
            else:
              new_body = cast(Term, c.body.substitute(subst))
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
    eq_cases = len(self.cases) == len(other.cases) \
      and all([c1 == c2 for (c1,c2) in zip(self.cases, other.cases)])
    return eq_subject and eq_cases

# The instances (by `_inst_key`) of where functions whose operations
# print: those that would otherwise print alike in the formulas being
# shown, but pass different operations (#1294).
shown_operations: frozenset[str] = frozenset()

def _inst_key(inst: TermInst) -> str:
  # How the instance prints without operations, whatever
  # `shown_operations` is at the moment: an instance nested in this one
  # must not change its key.
  global shown_operations
  shown = shown_operations
  shown_operations = frozenset()
  try:
    return str(inst.subject) + '<' + ','.join(str(ty) for ty in inst.type_args) + '>'
  finally:
    shown_operations = shown

def _insts_with_operations(t: AST) -> Iterator[TermInst]:
  if isinstance(t, TermInst) and t.dicts:
    yield t
  for c in t._children():
    yield from _insts_with_operations(c)

@contextmanager
def distinct_operations(terms: Iterable[AST]) -> Iterator[None]:
  """While printing ``terms``, print the operations of the instances of
  a where function that differ only in their operations, such as
  ``@msum<Int>{operator+, +0}`` and ``@msum<Int>{operator*, +1}``."""
  global shown_operations
  ops: dict[str, list[TermInst]] = {}
  for t in terms:
    for inst in _insts_with_operations(t):
      ops.setdefault(_inst_key(inst), []).append(inst)
  old = shown_operations
  shown_operations = old | {k for (k, insts) in ops.items()
                            if any(i.dicts != insts[0].dicts for i in insts)}
  try:
    yield
  finally:
    shown_operations = old

@dataclass
class TermInst(Term):
  subject: Term
  type_args: List[Type]
  inferred : bool = True
  # F^G's type application to a function with a where clause (#1282):
  # the operations of the models of its concepts at ``type_args``, which
  # the checker looks up among ``models`` (the models in scope, recorded
  # by uniquify) and passes after the function's own arguments.
  dicts: List[Term] = field(default_factory=list, kw_only=True)
  models: List[str] = field(default_factory=list, kw_only=True)

  _NON_STRUCTURAL_FIELDS = frozenset({'location', 'typeof', 'models'})

  def __eq__(self, other: object) -> bool:
    if self.dicts:
      # Instances that pass different operations are different
      # functions, even at the same types.
      return isinstance(other, TermInst) \
        and len(self.dicts) == len(other.dicts) \
        and all(d1 == d2 for (d1, d2) in zip(self.dicts, other.dicts)) \
        and self.subject == other.subject \
        and len(self.type_args) == len(other.type_args) \
        and all([t1 == t2 for (t1,t2) in zip(self.type_args, other.type_args)])
    if isinstance(other, TermInst) and other.dicts:
      return False
    if isinstance(other, RecFun):
      return self.subject == other
    elif isinstance(other, TermInst):
      return self.subject == other.subject \
        and len(self.type_args) == len(other.type_args) \
        and all([t1 == t2 for (t1,t2) in zip(self.type_args, other.type_args)])
    else:
      return self.subject == other

  def uniquify(self, env: UniquifyEnv, ctx: UniquifyContext) -> TermInst:
    ret = super().uniquify(env, ctx)
    ret.models = env.get(MODELS_KEY, [])
    return ret

  def __str__(self) -> str:
    if self.dicts and _inst_key(self) in shown_operations:
      return '@' + str(self.subject) + '<' + ','.join(str(ty) for ty in self.type_args) \
        + '>{' + ', '.join(str(d) for d in self.dicts) + '}'
    if self.inferred and not get_verbose():
      return str(self.subject)
    else:
      return '@' + str(self.subject) + '<' + ','.join([str(ty) for ty in self.type_args]) + '>'

  def reduce(self, env: Env) -> Term:
    subject_red = self.subject.reduce(env)
    type_args_red = [t.reduce(env) for t in self.type_args]
    dicts_red = [d.reduce(env) for d in self.dicts]
    match subject_red:
      case Generic(_, _, typarams, body):
        sub: dict[str, Term | Type] = {x:t for (x,t) in zip(typarams, type_args_red)}
        if dicts_red and isinstance(body, Lambda):
          # Pass the operations for the where clause's parameters, which
          # come after the function's own (#1282).
          n = len(body.vars) - len(dicts_red)
          sub.update({x: d for ((x, _), d) in zip(body.vars[n:], dicts_red)})
          return Lambda(body.location, self.typeof, body.vars[:n],
                        cast(Term, body.body.substitute(sub)))
        return cast(Term, body.substitute(sub))
      case _:
        return TermInst(self.location, self.typeof, subject_red,
                        type_args_red, self.inferred, dicts=dicts_red,
                        models=self.models)

@dataclass
class Array(Term):
  elements: List[Term]

  def __eq__(self, other: object) -> bool:
    return eq_arg_list(self, other, 'elements')

  def __str__(self) -> str:
    return 'array(' + ', '.join([str(elt) for elt in self.elements]) + ')'

@dataclass
class MakeArray(Term):
  subject: Term

  def __eq__(self, other: object) -> bool:
    return eq_fields(self, other, 'subject')

  def __str__(self) -> str:
    return 'array(' + str(self.subject) + ')'

  def reduce(self, env: Env) -> Term:
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
    return eq_fields(self, other, 'subject', 'position')

  def __str__(self) -> str:
    return show(self.subject, ATOM, False) + '[' + str(self.position) + ']'

  def reduce(self, env: Env) -> Term:
    subject_red = self.subject.reduce(env)
    position_red = self.position.reduce(env)
    index = None
    if isNat(position_red):
      index = natToInt(position_red)
    elif isUInt(position_red):
      index = uintToInt(position_red)
    match subject_red:
      case ArraySet(_, _, arr, wpos, wval):
        # Read-over-write (issue #1118, Phase 2i). `wpos`/`wval` are already
        # reduced because `subject.reduce` reduced the `ArraySet`'s children.
        # A read at the written index yields the written value; a read at a
        # provably different index (both concrete) sees through the write to
        # the prior array (recursing composes stacked writes); otherwise the
        # access stays symbolic.
        if position_red == wpos:
          return wval
        write_index = _array_position_int(wpos)
        if index is not None and write_index is not None \
           and index != write_index:
          return ArrayGet(self.location, self.typeof,
                          arr, position_red).reduce(env)
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
              new_pos = _array_index_predecessor(position_red, env)
              if new_pos is not None:
                new_subject = MakeArray(loc2, marr_ty, tl)
                new_get = ArrayGet(self.location, self.typeof,
                                   new_subject, new_pos)
                return new_get.reduce(env)
    return ArrayGet(self.location, self.typeof, subject_red, position_red)

def _array_position_int(term: Term) -> Optional[int]:
  # The concrete integer value of an array index, or None when the index is
  # symbolic. Used by `ArrayGet.reduce` to decide read-over-write cases.
  if isNat(term):
    return natToInt(term)
  if isUInt(term):
    return uintToInt(term)
  return None

@dataclass
class ArraySet(Term):
  # The mutable array `subject` with index `position` updated to `value`, a
  # verifier-only functional-update node (issue #1118, Phase 2i). Produced
  # only by the imperative verifier to model an `a[i] := v` write in symbolic
  # state; it is never parsed, so both parsers still see the surface program
  # unchanged. `ArrayGet.reduce` implements read-over-write against it, and
  # `ArrayLength.reduce` sees through it (a write preserves array length).
  subject: Term
  position: Term
  value: Term

  def __eq__(self, other: object) -> bool:
    return eq_fields(self, other, 'subject', 'position', 'value')

  def __str__(self) -> str:
    return show(self.subject, ATOM, False) + '[' + str(self.position) + ' := ' \
        + str(self.value) + ']'

@dataclass
class ArrayLength(Term):
  # `length(a)` for a mutable-array handle (or a pure array). Produced only
  # by the type checker when `length` is applied to an array-typed argument
  # (issue #1117, Phase 2h); it is never parsed, so both parsers still see
  # the surface `length(a)` as an ordinary `Call`. In Phase 2 an array's
  # length is immutable for the lifetime of the handle, so a write leaves it
  # unchanged: `reduce` sees through any `ArraySet` wrapper (issue #1118) so
  # `length(a[i := v])` and `length(a)` reduce to the same symbolic term.
  subject: Term

  def __eq__(self, other: object) -> bool:
    return eq_fields(self, other, 'subject')

  def __str__(self) -> str:
    return 'length(' + str(self.subject) + ')'

  def reduce(self, env: Env) -> Term:
    subject_red = self.subject.reduce(env)
    while isinstance(subject_red, ArraySet):
      subject_red = subject_red.subject
    return ArrayLength(self.location, self.typeof, subject_red)

@dataclass
class TLet(Term):
  var: str
  rhs: Term
  body: Term

  def free_vars(self) -> Set[str]:
    return self.rhs.free_vars() | (self.body.free_vars() - {self.var})

  def __str__(self) -> str:
    return 'define ' + base_name(self.var) + ' = ' + str(self.rhs) + ';' \
      + '\n\t' + show(self.body)

  def reduce(self, env: Env) -> Term:
    new_body = self.body.substitute({self.var: self.rhs})
    return cast(Term, new_body.reduce(env))

  def reduceLets(self, env: Env) -> Term:
    new_body = self.body.substitute({self.var: self.rhs})
    if isinstance(new_body, TLet):
      return new_body.reduceLets(env)
    else:
      return cast(Term, new_body)

  def uniquify(self, env: UniquifyEnv, ctx: UniquifyContext) -> TLet:
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

def reduce_lets(term: Term, env: Env) -> Term:
  """Collapse a leading ``TLet`` binding via ``reduceLets``; pass other terms through."""
  return term.reduceLets(env) if isinstance(term, TLet) else term

@dataclass
class Hole(Term):

  def __str__(self) -> str:
      return '?'

@dataclass
class Omitted(Term):

  def __str__(self) -> str:
      return '__'

@dataclass
class Mark(Term):
  subject: Term

  def __eq__(self, other: object) -> bool:
    if isinstance(other, Mark):
      return self.subject == other.subject
    else:
      return self.subject == other

  def __str__(self) -> str:
    return '#' + str(self.subject) + '#'

################ Formulas ######################################
  
@dataclass
class Bool(Formula):
  value: bool

  def __eq__(self, other: object) -> bool:
      if not isinstance(other, Bool):
          return False
      return self.value == other.value
  def __str__(self) -> str:
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

def _reduce_connective(
    formula: And | Or, env: Env,
    flatten: Callable[[Sequence[Formula]], list[Formula]],
    identity: bool,
    cls: type[And] | type[Or],
) -> Formula:
  """Normalize an ``and``/``or`` monoid: reduce and flatten the arguments,
  drop the identity constant (``true`` for ``and``, ``false`` for ``or``), and
  short-circuit on the absorbing constant (``false``/``true``). Returns the
  sole survivor unwrapped, the identity ``Bool`` when none survive, or a
  rebuilt ``cls`` node."""
  new_args = flatten([arg.reduce(env) for arg in formula.args])
  newer_args = []
  for arg in new_args:
    match arg:
      case Bool(_, _, val):
        if val == identity:  # identity element: throw this away
          pass
        else:                # absorbing element: the whole thing collapses to it
          return arg
      case _:
        newer_args.append(arg)
  if len(newer_args) == 0:
    return Bool(formula.location, BoolType(formula.location), identity)
  elif len(newer_args) == 1:
    return newer_args[0]
  else:
    return cls(formula.location, formula.typeof, newer_args)

@dataclass
class And(Formula):
  args: list[Formula]

  def __str__(self) -> str:
    return show(self)

  def __eq__(self, other: object) -> bool:
    return eq_arg_list(self, other)

  def reduce(self, env: Env) -> Formula:
    return _reduce_connective(self, env, flatten_and, True, And)

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

  def __str__(self) -> str:
    return show(self)
  
  def __eq__(self, other: object) -> bool:
    return eq_arg_list(self, other)

  def reduce(self, env: Env) -> Formula:
    return _reduce_connective(self, env, flatten_or, False, Or)

@dataclass
class IfThen(Formula):
  premise: Formula
  conclusion : Formula

  def __str__(self) -> str:
    return show(self)

  def __eq__(self, other: object) -> bool:
    return eq_fields(self, other, 'premise', 'conclusion')
  
  def reduce(self, env: Env) -> Formula:
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

################ Resource (separation-logic) formulas ###########
#
# Parser/AST only (experimental imperative layer, issue #854 Phase 1h).
# These nodes carry the separation-resource surface syntax -- `emp`, the
# separating conjunction `P ** Q`, the points-to `lhs |-> rhs`, and the
# field-access address form `p.f` used on the left of a points-to. They
# are gated behind `--experimental-imperative` at parse time and rejected
# before proof checking; there is no ownership accounting, separating-
# conjunction proof rule, or resource folding here. The default `uniquify`
# / `substitute` / `reduce` walkers recurse into the ordinary `Term`
# subparts, so bound variables inside a resource formula still resolve.

@dataclass
class FieldAccess(Term):
  # `subject.field`, only reachable as the address of a points-to today.
  subject: Term
  field: str

  def __str__(self) -> str:
    return show(self.subject, ATOM, False) + '.' + base_name(self.field)

@dataclass
class Emp(Formula):
  # The empty-heap resource assertion, written `emp`.

  def __eq__(self, other: object) -> bool:
    return eq_fields(self, other)

  def __str__(self) -> str:
    return 'emp'

@dataclass
class PointsTo(Formula):
  # `address |-> value`: the single-cell resource assertion.
  address: Term
  value: Term

  def __eq__(self, other: object) -> bool:
    return eq_fields(self, other, 'address', 'value')

  def __str__(self) -> str:
    return show(self)

@dataclass
class SepConj(Formula):
  # `left ** right`: separating conjunction. Left-associative, so
  # `a ** b ** c` nests as `SepConj(SepConj(a, b), c)`.
  left: Formula
  right: Formula

  def __eq__(self, other: object) -> bool:
    return eq_fields(self, other, 'left', 'right')

  def __str__(self) -> str:
    return show(self)

@dataclass
class All(Formula):
  var: Tuple[str,Type]
  # Position (s, e), where
  #  s : The variable's index in the list, starting from the last var
  #  e : The number of vars in the block
  pos: Tuple[int, int]
  body: Formula
  # On the last variable of a binding list: the where clause, whose
  # members are bound by ``body`` (see ``abstract_syntax/concepts.py``).
  where: Optional[WhereClause] = field(default=None, kw_only=True)

  def free_vars(self) -> Set[str]:
    x, ty = self.var
    return (self.body.free_vars() - {x}) | ty.free_vars()

  def __str__(self) -> str:
    v, t = self.var
    v = name2str(v)

    (s, e) = self.pos

    result = ''
    if s + 1 == e:
      result += "all "
    result += f"{v}:{str(t)}"
    if self.where is not None:
      result += ' ' + str(self.where)
    if s == 0:
      result += ". " + show(where_body(self))
    else:
      result += ", " + str(where_body(self))
    return result

  def reduce(self, env: Env) -> Formula:
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
                   new_body, where=self.where)

  def __eq__(self, other: object) -> bool:
    if not isinstance(other, All):
      return False
    return _alpha_equiv_all(self, other, {}, {})

  def uniquify(self, env: UniquifyEnv, ctx: UniquifyContext) -> All:
    body_env = {x:y for (x,y) in env.items()}
    (x, ty) = self.var
    new_t = ty.uniquify(body_env, ctx)
    new_x = generate_name(x, ctx)
    overwrite(body_env, x, new_x, self.location)
    new_where = self.where.bind(body_env, ctx) if self.where else None
    new_body = self.body.uniquify(body_env, ctx)
    return All(self.location, self.typeof, (new_x, new_t),
               self.pos, new_body, where=new_where)

@dataclass
class Some(Formula):
  vars: list[Tuple[str,Type]]
  body: Formula

  def free_vars(self) -> Set[str]:
    return (self.body.free_vars() - {x for x, _ in self.vars}).union(
      *(t.free_vars() for _, t in self.vars))

  def __str__(self) -> str:
      return 'some ' + ",".join([(v if get_verbose() else base_name(v)) + ":" + str(t) \
                                 for (v,t) in self.vars]) \
        + '. ' + show(self.body)
  
  def reduce(self, env: Env) -> Formula:
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

  def uniquify(self, env: UniquifyEnv, ctx: UniquifyContext) -> Some:
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
    return _alpha_equiv_binders(self, other, {}, {})
  
