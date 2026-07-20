"""Recognizers, builders, and conversions for built-in literal shapes.

Scope: the helpers that bridge between Python-level values and the
constructor stacks the language uses for its literals. Covers:
  * ``Nat`` (``zero``/``suc``): ``mkZero``, ``mkSuc``, ``intToNat``,
    ``isNat``/``isLitNat``, ``natToInt``, ``getZero``/``getSuc``.
  * ``UInt`` (``bzero``/``inc_dub``/``dub_inc``): ``mkBZero``,
    ``mkIncDub``, ``mkDubInc``, ``intToUInt``, ``isUInt``/``isLitUInt``,
    ``uintToInt``.
  * ``Int`` (``pos``/``neg`` over ``UInt``): ``mkPos``/``mkNeg``,
    ``mkIntLit``, ``isDeduceInt``, ``deduceIntToInt``.
  * Lists (``empty``/``node``): ``mkEmpty``/``mkNode``,
    ``listToNodeList``, ``isNodeList``, ``nodeListToList``,
    ``nodeListToString``.
  * Equation shape (``mkEqual``, ``split_equation``, ``is_equation``,
    ``equation_vars``) and small constructor-name predicates
    (``is_constructor``, ``constr_name``, ``constructor_conflict``).

Goes here:
  * a new literal form whose surface syntax desugars to a constructor
    stack (e.g. a new numeric encoding, a new collection literal)
  * an equality/literal-shape recognizer used by checker passes

Does NOT go here:
  * generic term/formula AST nodes (``terms``)
  * rewriting/marking machinery (``rewrite``)
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from .core import *
from .terms import *
from .proofs import *
from .declarations import *
from .env import *

if TYPE_CHECKING:
    from .ops import callable_name

# ---------------------
# Auxiliary Functions

@dataclass(frozen=True)
class AutoRewriteRule:
  equation: Formula
  variables: list[Term]
  premises: list[Formula]
  lhs: Term
  rhs: Term
  
def mkEqual(loc: Meta, arg1: Term, arg2: Term) -> Formula:
  # Post-uniquify/post-typecheck constructor.  Callers in the proof
  # checker (e.g. transitivity, symmetry, extensionality) build new
  # goal formulas with this helper, and those goals are then compared
  # against already-uniquified terms without a fresh type-check pass,
  # so the rator must already be a ``ResolvedVar`` to match.
  #
  # The *parser* paths that build an ``equations``-block claim do NOT
  # use this helper -- they construct ``Call(Var('='), ...)`` directly
  # so the AST matches the ordinary infix-`=` parsing path and the
  # pretty-print/parse round-trip succeeds (issue #945).
  ret = Call(loc, None, ResolvedVar(loc, None, '='), [arg1, arg2])
  return cast(Formula, ret)

def mkEqualVar(loc: Meta, arg1: Term, arg2: Term) -> Formula:
  # Pre-uniquify constructor for parser use.  Matches the AST shape
  # the ordinary infix-`=` path produces (``Call(Var('='), ...)``) so
  # the two surface forms for ``a = b`` converge at parse time (see
  # issue #945).  Downstream phases narrow this to ``OverloadedVar``
  # / ``ResolvedVar`` the same way they do for every other operator.
  ret = Call(loc, None, Var(loc, None, '='), [arg1, arg2])
  return cast(Formula, ret)

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

def split_auto_rule(loc: Meta, equation: Formula, env: Env) -> AutoRewriteRule:
  variables: list[Term] = []
  premises: list[Formula] = []
  body = equation
  if isinstance(body, TLet):
    body = cast(Formula, body.reduceLets(env))

  while isinstance(body, All):
    x, typ = body.var
    v = ResolvedVar(body.location, typ, x)
    variables.append(v)
    body = body.body

  if isinstance(body, IfThen):
    premises.extend(list_of_and(body.premise))
    body = body.conclusion

  match body:
    case Call(_, _, rator, [L, R]) if isinstance(rator, VarRef) and rator.get_name() == '=':
      return AutoRewriteRule(equation, variables, premises, L, R)
    case _:
      internal_error(
        loc,
        'an auto rule must be `lhs = rhs` or `if P then lhs = rhs`, '
        + 'optionally under `all` quantifiers; got: ' + str(equation),
      )

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
      
def is_equation(formula: Formula) -> bool:
  match formula:
    case Call(_, _, rator, [_, _]) if isinstance(rator, VarRef) and rator.get_name() == '=':
      return True
    case All(_, _, _, _, body):
      return is_equation(body)
    case _:
      return False

def isUInt(t: Term) -> bool:
  # Value-type recognizer: only matches the *post-uniquify* shape.
  # Pre-uniquify, the UInt-literal path goes through ``isLitUInt`` /
  # ``mkUIntLit`` instead, so accepting plain ``Var`` here would let
  # ``Call.__str__`` collapse user-written ``pos(N)`` / ``negsuc(N)``
  # (via ``isDeduceInt``) into ``+N`` / ``-(N+1)`` — which then re-parses
  # to a unary-minus AST rather than the original constructor and breaks
  # the round-trip (see int1.pf).
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

def isBZero(t: Term) -> bool:
  match t:
    case (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)) if base_name(n) == 'bzero':
      return True
    case _:
      return False

def isDubInc(t: Term) -> bool:
  match t:
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)), [_]) \
      if base_name(n) == 'dub_inc':
        return True
    case _:
      return False

def isIncDub(t: Term) -> bool:
  match t:
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)), [_]) \
      if base_name(n) == 'inc_dub':
        return True
    case _:
      return False

def get_arg(t: Term) -> Term:
  match t:
    case Call(_, _, _, [arg]):
      return arg
    case _:
      raise InternalError('get_arg')
  
def mkBZero(loc: Meta, zname: str = 'bzero', ty: Type | None = None) -> ResolvedVar:
  return ResolvedVar(loc, ty, zname)

def mkIncDub(loc: Meta, arg: Term, cname: str = 'inc_dub',
             ty: Type | None = None) -> Call:
  return Call(loc, ty, ResolvedVar(loc, None, cname), [arg])

def mkDubInc(loc: Meta, arg: Term, cname: str = 'dub_inc',
             ty: Type | None = None) -> Call:
  return Call(loc, ty, ResolvedVar(loc, None, cname), [arg])

def isSuc(t: Term) -> bool:
  match t:
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n)), [_]) \
         if base_name(n) == 'suc':
      return True
    case _:
      return False

def _array_index_predecessor(pos: Term, env: Env) -> Term | None:
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

def _try_match_one_plus(t: Term) -> Term | None:
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

def _uint_double(loc: Meta, x: Term, env: Env) -> Term | None:
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

# Build the compact binary (``bzero``/``inc_dub``/``dub_inc``)
# representation of ``n``. Recursion depth and node count are both
# O(log n), via a direct odd/even decomposition:
#   n odd  ->  inc_dub((n-1)/2)   [ 1 + 2k ]
#   n even ->  dub_inc(n/2 - 1)   [ 2(1 + k) ]
# NOTE: the parsers do *not* currently use this -- ``Binary``'s
# constructors are ``private`` to the UInt module, so a user file
# cannot name them and literals go through ``mkUIntLit`` (``fromNat``
# of a unary ``Nat``) instead. Switching literals to this compact form
# is the end-to-end fix tracked in issue #1021.
def intToUInt(loc: Meta, n: int, bzero: str = 'bzero',
              dubinc: str = 'dub_inc',
              incdub: str = 'inc_dub',
              uint_ty: Type | None = None) -> Term:
    if n <= 0:
        return mkBZero(loc, bzero, uint_ty)
    elif n % 2 == 1:
        return mkIncDub(loc, intToUInt(loc, (n - 1) // 2, bzero, dubinc,
                                       incdub, uint_ty), cname=incdub)
    else:
        return mkDubInc(loc, intToUInt(loc, n // 2 - 1, bzero, dubinc,
                                       incdub, uint_ty), cname=dubinc)
    
def _resolved_or_var(loc: Meta, ty: Type | None, name: str) -> VarRef:
  # A ``ResolvedVar`` when ``name`` is already uniquified (contains a
  # '.'), otherwise a pre-uniquify ``Var``. Fast-arithmetic call sites
  # in the type checker pass uniquified names extracted from the
  # existing AST; parser call sites pass the bare source name.
  if '.' in name:
    return ResolvedVar(loc, ty, name)
  return Var(loc, ty, name)

def mkZero(loc: Meta, zname: str | bool = 'zero',
           ty: Type | None = None) -> VarRef:
  return _resolved_or_var(loc, ty, str(zname))

def mkSuc(loc: Meta, arg: Term, sname: str | bool = 'suc',
          ty: Type | None = None) -> Call:
  return Call(loc, ty, _resolved_or_var(loc, None, str(sname)), [arg])

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
  # Value-type recognizer — see the comment on ``isUInt`` for why
  # plain ``Var`` is intentionally excluded.
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

def isRawNat(t: Term) -> bool:
  # ``zero`` / ``suc(zero)`` / ... with no ``lit`` wrapping. Used by
  # ``isLitNat`` so that ``lit(ℕn)`` (which the parser desugars to
  # ``lit(lit(suc^n(zero)))``) is NOT collapsed to ``ℕn``: that
  # surface form has an extra ``lit`` wrapper the pretty-printer
  # must preserve so the AST round-trips.
  match t:
    case (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n) | Var(_, _, n)) if base_name(n) == 'zero':
      return True
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n) | Var(_, _, n)), [arg]) \
         if base_name(n) == 'suc':
      return isRawNat(arg)
    case _:
      return False

def isLitNat(t: Term) -> bool:
  match t:
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n) | Var(_, _, n)), [arg]) \
         if base_name(n) == 'lit':
      return isRawNat(arg)
    case _:
      return False

def isLitUInt(t: Term) -> bool:
  match t:
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n) | Var(_, _, n)), [arg]) \
         if base_name(n) == 'fromNat':
      return isLitNat(arg)
    case _:
      return False
  
def isInt(t: Term) -> bool:
  # Value-type recognizer — see the comment on ``isUInt`` for why
  # plain ``Var`` is intentionally excluded.
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
    case (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n) | Var(_, _, n)) if base_name(n) == 'zero':
      return 0
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n) | Var(_, _, n)), [arg]) \
      if base_name(n) == 'suc':
      return 1 + natToInt(arg)
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n) | Var(_, _, n)), [arg]) \
      if base_name(n) == 'lit':
      return natToInt(arg)
    case _:
      raise InternalError('natToInt: not a Nat: ' + str(t))

def uintToInt(t: Term) -> int:
  match t:
    case (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n) | Var(_, _, n)) if base_name(n) == 'bzero':
      return 0
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n) | Var(_, _, n)), [arg]) \
      if base_name(n) == 'dub_inc':
      return 2 * (1 + uintToInt(arg))
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n) | Var(_, _, n)), [arg]) \
      if base_name(n) == 'inc_dub':
      return 1 + 2 * uintToInt(arg)
    case Call(_, _, (OverloadedVar(_, _, [n, *_]) | ResolvedVar(_, _, n) | Var(_, _, n)), [arg]) \
      if base_name(n) == 'fromNat':
      return natToInt(arg)
    case _:
      raise InternalError('uintToInt: not a uint ' + str(t))

def _extract_lit_nat_names(t: Term) -> tuple[str, str | None, str] | None:
  # If `t` is `lit(suc(suc(...zero)))`, return the uniquified
  # `(lit_name, suc_name_or_None, zero_name)` extracted from its nodes.
  # `suc_name` is None when the value is 0 (no `suc` in the AST).
  if not isLitNat(t):
    return None
  assert isinstance(t, Call) and isinstance(t.rator, VarRef)
  inner = t.args[0]
  zname = getZero(inner)
  if not isinstance(zname, str):
    return None
  sname = getSuc(inner)
  return (t.rator.get_name(),
          sname if isinstance(sname, str) else None,
          zname)

def try_fast_lit_nat_arith(loc: Meta, rator: Term, args: list[Term],
                           ty: Type | None) -> Term | None:
  # Compute `op` on `lit`-wrapped Nat literals directly, bypassing the
  # step-by-step auto-rewrite rules (lit_suc_mult, lit_suc_add, etc.)
  # whose recursive unfolding is O(N^2) or worse for N-digit operands.
  # Returns the result as a literal Nat (or Bool for comparisons), or
  # None if the fast path does not apply.
  if len(args) < 2:
    return None
  if not isinstance(rator, (Var, OverloadedVar, ResolvedVar)):
    return None
  op = base_name(rator.get_name())
  if op not in ('+', '*', '^', '∸', '/', '%', '≤', '<'):
    return None
  values: list[int] = []
  lit_name: str | None = None
  suc_name: str | None = None
  zero_name: str | None = None
  for arg in args:
    comp = _extract_lit_nat_names(arg)
    if comp is None:
      return None
    ln, sn, zn = comp
    values.append(natToInt(arg))
    if lit_name is None:
      lit_name = ln
    if suc_name is None:
      suc_name = sn
    if zero_name is None:
      zero_name = zn
  if lit_name is None or zero_name is None:
    return None
  if len(values) > 2 and op not in ('+', '*'):
    return None
  if op == '+':
    result_int = sum(values)
  elif op == '*':
    result_int = 1
    for v in values:
      result_int *= v
  elif op == '^':
    if values[1] > 4096:
      return None
    result_int = values[0] ** values[1]
  elif op == '∸':
    result_int = max(0, values[0] - values[1])
  elif op == '/':
    if values[1] == 0:
      return None
    result_int = values[0] // values[1]
  elif op == '%':
    if values[1] == 0:
      return None
    result_int = values[0] % values[1]
  elif op == '≤':
    return Bool(loc, ty, values[0] <= values[1])
  elif op == '<':
    return Bool(loc, ty, values[0] < values[1])
  else:
    return None
  if result_int > 0 and suc_name is None:
    return None
  inner = intToNat(loc, result_int, zname=zero_name,
                   sname=suc_name or 'suc')
  return Call(loc, ty, _resolved_or_var(loc, None, lit_name), [inner])

def _uint_binary_name(env: Env) -> str | None:
  # Unique name of the UInt library's private ``Binary`` representation
  # type. It is ``private`` to the UInt module, so a user file cannot
  # name it: a call whose result type is this ``Binary`` is therefore a
  # library UInt operation, which is what lets the fast path tell the
  # built-in UInt conversion/arithmetic apart from a same-named user
  # overload (e.g. ``fun fromNat(n:Nat) -> Nat``).
  return env.base_to_unique('Binary')

def _is_uint_binary_type(ty: Type | VarRef | None, env: Env) -> bool:
  # A named type such as ``Binary`` is represented as a ``VarRef`` node.
  binary_name = _uint_binary_name(env)
  return binary_name is not None \
      and isinstance(ty, VarRef) \
      and ty.get_name() == binary_name

def _mk_uint_from_int(loc: Meta, n: int, ty: Type | None, env: Env) -> Term | None:
  # Build the compact ``Binary`` value for ``n`` using the environment's
  # uniquified constructor names, so the result is structurally identical
  # to what the opaque recursive reduction would produce.
  bz = env.base_to_unique('bzero')
  di = env.base_to_unique('dub_inc')
  idd = env.base_to_unique('inc_dub')
  if bz is None or di is None or idd is None:
    return None
  return intToUInt(loc, n, bzero=bz, dubinc=di, incdub=idd, uint_ty=ty)

def try_fast_uint_arith(loc: Meta, rator: Term, args: list[Term],
                        ty: Type | None, env: Env) -> Term | None:
  # Full-evaluation (``assert``/``evaluate``) fast path for UInt.  A UInt
  # literal enters the evaluator as ``fromNat(<unary Nat of depth N>)``,
  # whose opaque unfolding is O(N); and the recursive ``Binary`` division
  # operator is O(N/M).  Both make ``assert`` on large literals take tens
  # of seconds (issue #1050).  Here we compute the result with Python ints
  # and emit the compact ``Binary`` value directly.  Returns None unless
  # every operand is a concrete UInt literal, so symbolic terms fall
  # through to normal reduction.  Only sound under ``eval_all``, where the
  # ``fromNat``/``Binary``-operator shape that proof automation keys on is
  # already being reduced away.
  #
  # To avoid hijacking a same-named user overload (issue #1050 review),
  # value-producing operations require the call's result type to be the
  # UInt library's private ``Binary`` -- unspoofable by user code -- so a
  # user ``fromNat : Nat -> Nat`` (or any op not returning UInt) is left
  # to normal reduction.  Comparisons return ``bool``, so they instead
  # rely on both operands being genuine UInt values (built from the
  # private UInt constructors), the same operand-type guard the Nat fast
  # path uses.
  if not isinstance(rator, (Var, OverloadedVar, ResolvedVar)):
    return None
  op = base_name(rator.get_name())
  if op == 'fromNat':
    if len(args) == 1 and isNat(args[0]) and _is_uint_binary_type(ty, env):
      return _mk_uint_from_int(loc, natToInt(args[0]), ty, env)
    return None
  if op not in ('+', '*', '∸', '/', '%', '<', '≤'):
    return None
  if len(args) != 2 or not (isUInt(args[0]) and isUInt(args[1])):
    return None
  a = uintToInt(args[0])
  b = uintToInt(args[1])
  if op == '<':
    return Bool(loc, ty, a < b)
  if op == '≤':
    return Bool(loc, ty, a <= b)
  if not _is_uint_binary_type(ty, env):
    return None
  if op == '+':
    result_int = a + b
  elif op == '*':
    result_int = a * b
  elif op == '∸':
    result_int = max(0, a - b)
  elif op == '/':
    # UInt division truncates and defines n / 0 = 0 (lib/UIntDiv.pf).
    result_int = a // b if b != 0 else 0
  else:  # '%' : n % m = n ∸ (n / m) * m, so n % 0 = n (lib/UIntDiv.pf).
    result_int = a % b if b != 0 else a
  return _mk_uint_from_int(loc, result_int, ty, env)

def _same_numeric_literal(t1: AST, t2: AST) -> bool:
  if not isinstance(t1, Term) or not isinstance(t2, Term):
    return False
  if isNat(t1) and isNat(t2):
    return natToInt(t1) == natToInt(t2)
  if isUInt(t1) and isUInt(t2):
    return uintToInt(t1) == uintToInt(t2)
  return False

def formulas_equal_modulo_numeric_literals(frm1: AST, frm2: AST) -> bool:
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

def check_literal_size(loc: Meta, num: int) -> None:
    # Reject a literal whose value is so large its unary desugaring
    # would overflow the recursion limit mid-check. Raising a located
    # ``ParseError`` here turns an opaque "maximum recursion depth
    # exceeded" crash into a beginner-friendly diagnostic (issue #1021).
    from flags import MAX_LITERAL
    from error import ParseError
    if abs(num) > MAX_LITERAL:
        raise ParseError(
            loc,
            f'numeric literal {num} is too large: Deduce represents '
            f'numbers as unary terms whose depth equals the value, so it '
            f'only supports literals up to {MAX_LITERAL}.',
        )

def mkLitNat(loc: Meta, num: int) -> Term:
    # The ``lit(ℕnum)`` surface form shared by the parsers' Nat literals
    # and the Nat payload of a UInt literal (below). The size guard lives
    # here so every literal path (Nat, UInt, and Int via mkUIntLit) is
    # covered by one check.
    check_literal_size(loc, num)
    return Call(loc, None, Var(loc, None, 'lit'), [intToNat(loc, num)])

def mkUIntLit(loc: Meta, num: int) -> Term:
    return Call(loc, None, Var(loc, None, 'fromNat'), [mkLitNat(loc, num)])
  
def mkPos(loc: Meta, arg: Term) -> Term:
  return Call(loc, None, Var(loc, None, 'pos'), [arg])

def mkNeg(loc: Meta, arg: Term) -> Term:
  return Call(loc, None, Var(loc, None, 'negsuc'), [arg])

# The following is used in the parser.
def mkIntLit(loc: Meta, n: int, sign: str) -> Term:
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

def is_constructor(constr_name: str, env: Env) -> bool:
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

def is_constr_term(term: Term, env: Env) -> bool:
  if isinstance(term, VarRef):
    return is_constructor(term.get_name(), env)
  match term:
    case TermInst(_, _, body):
      return is_constr_term(body, env)
    case _:
      return False

def constr_name(term: Term) -> str:
  if isinstance(term, VarRef):
    return term.get_name()
  match term:
    case TermInst(_, _, body):
      return constr_name(body)
    case _:
      raise InternalError('constr_name unhandled ' + str(term))
    
def constructor_conflict(term1: Term, term2: Term, env: Env) -> bool:
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

def nodeListToString(t: Term) -> str | None:
  match t:
    case TermInst(_, _, ctor, _, _) if _is_named(ctor, 'empty'):
      return ''
    case Call(_, _, TermInst(_, _, ctor, _, _),
              [arg, ls]) if _is_named(ctor, 'node'):
      rest = nodeListToString(ls)
      return str(arg) + ', ' + rest if rest is not None else None
    case _:
      return None

def mkEmpty(loc: Meta) -> Term:
  return Var(loc, None, 'empty')

def mkNode(loc: Meta, arg: Term, ls: Term) -> Term:
  return Call(loc, None, Var(loc, None, 'node'), [arg, ls])

def listToNodeList(loc: Meta, lst: Sequence[Term]) -> Term:
  if len(lst) == 0:
    return mkEmpty(loc)
  else:
    return mkNode(loc, lst[0], listToNodeList(loc, lst[1:]))

