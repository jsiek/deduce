"""AST foundation for the abstract_syntax package.

Scope: the abstract base classes that every concrete AST node inherits from
(``AST``, ``Type``, ``Term``, ``Formula``, ``Proof``, ``Statement``), the
shared dataclass plumbing they rely on (generic ``copy``/``_ast_map``), and
the uniquify-time bookkeeping (``UniquifyContext``, ``generate_name``,
``name2str``, ``current_module``) that downstream modules consume.

Goes here:
  * a new top-level AST supertype (a new sibling of ``Term``/``Proof``/...)
  * dataclass machinery or naming helpers that every node uses
  * the ``UniquifyContext`` and module-name globals

Does NOT go here:
  * concrete node dataclasses — those live in ``terms``, ``proofs``,
    ``declarations``, or ``env`` depending on category
  * passes over whole AST trees (those live in ``ops``)
"""

from __future__ import annotations

from dataclasses import dataclass, field, fields as dc_fields
from lark.tree import Meta
from typing import Any, Callable, Iterator, Tuple, List, Mapping, Optional, Protocol, Set, Self, overload, TextIO, Sequence, cast, Iterable, NotRequired, TypedDict, TYPE_CHECKING
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
    lookup_view_source_alias,
    pop_suppress_view_alias,
    push_suppress_view_alias,
    set_check_imports as set_check_imports,
    set_recursive_descent as set_recursive_descent,
    set_verbose,
    view_aliasing_suppressed,
)
from pathlib import Path
from edit_distance import did_you_mean_hint, edit_distance
from math import ceil
import os

if TYPE_CHECKING:
    from .declarations import GenRecFun, RecFun
    from .env import Env

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
    if not view_aliasing_suppressed():
        aliased = lookup_view_source_alias(s)
        if aliased is not None:
            return base_name(aliased)
    return base_name(s)

# current_module is used during uniquify and collect_exports
current_module = 'none'

def get_current_module() -> str:
    global current_module
    return current_module

def set_current_module(name: str) -> None:
    global current_module
    current_module = name

# The name-resolution environment is intentionally heterogeneous while
# uniquify spans parsed names, overload lists, and module sentinels.
UniquifyEnv = dict[str, Any]

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
    cls = cast(Callable[..., Self], type(self))
    non_struct = self._NON_STRUCTURAL_FIELDS
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

  def uniquify(self, env: UniquifyEnv, ctx: UniquifyContext) -> Self:
    return self._map_children(lambda x: x.uniquify(env, ctx))

  def substitute(self, sub: Mapping[str, Term | Type | RecFun | GenRecFun]) -> AST:
    return self._map_children(lambda x: x.substitute(sub))

  def reduce(self, env: Env) -> AST:
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

  def uniquify(self, env: UniquifyEnv, ctx: UniquifyContext) -> Type:
    return super().uniquify(env, ctx)

  def substitute(self, sub: Mapping[str, Term | Type | RecFun | GenRecFun]) -> Type:
    return cast(Type, super().substitute(sub))

  def reduce(self, env: Env) -> Type:
    return cast(Type, super().reduce(env))


@dataclass
class Term(AST):
  typeof: Optional[Type]

  _NON_STRUCTURAL_FIELDS = frozenset({'location', 'typeof'})

  def subst_typeof(self, sub: Mapping[str, Term | Type | RecFun | GenRecFun]) -> Optional[Type]:
    # Apply `sub` to the cached `typeof` annotation. Kept as a named
    # helper because a handful of bespoke `substitute` methods (Var,
    # OverloadedVar, ResolvedVar) call it directly to short-circuit
    # when the annotation didn't actually change.
    return self.typeof.substitute(sub) if self.typeof is not None else None

  def substitute(self, sub: Mapping[str, Term | Type | RecFun | GenRecFun]) -> Term | RecFun | GenRecFun:
    return self._map_children(
      lambda x: x.substitute(sub),
      on_typeof=lambda t: t.substitute(sub) if t is not None else None,
    )

  def reduce(self, env: Env) -> Term:
    return self._map_children(lambda x: x.reduce(env))

  def pretty_print(self, indent: int, afterNewline: bool = False) -> str:
      if afterNewline:
          return indent*' ' + str(self)
      else:
          return str(self)

@dataclass
class Formula(Term):
  def reduce(self, env: Env) -> Formula:
    return cast(Formula, super().reduce(env))

@dataclass
class Proof(AST):

  def pretty_print(self, indent: int) -> str:
      return str(self)

@dataclass
class Statement(AST):

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def collect_exports(self, export_env: UniquifyEnv, importing_module: str) -> None:
    internal_error(self.location, 'collect_exports not implemented')

class InductiveInfo(TypedDict):
  tys: list[str]
  conjuncts: list[Formula]
  fun: str
  ind_ty: Type
  fun_ty: Type
  thm: NotRequired[Proof | Term]

class TheoremFilePrinting(Protocol):
  def key(self) -> str: ...

  def print_theorems_statement(self, f: TextIO) -> None: ...

################ Miscellaneous Functions #####################

def copy_dict[T](d: dict[str, T]) -> dict[str, T]:
  return {k: v for k, v in d.items()}


def maybe_str(o: Proof | str | None, default: str = '') -> str:
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
