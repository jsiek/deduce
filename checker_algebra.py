"""The `algebra` tactic: ring normalization (#1190) over the types that
model ``CommSemiring``, ``CommRing``, or ``Field`` (lib/Algebra.pf,
lib/Ring.pf), and linear arithmetic (#1189) over the types that model
``LinearArith`` (lib/Linear.pf).

The tactic is untrusted search; the checker's own instantiation and
reduction do the proof.

An equation whose sides are equal polynomials is proved by ring
normalization: read each side as an ``RExpr`` over atoms (the maximal
subterms that are not sums, products, constants, powers with a UInt
literal exponent, or, in a ring, differences and negations), instantiate
``ring_prove`` (in a ring) or ``semiring_prove`` at the goal's type,
evaluate its premise, that the normal forms are equal, to ``true``, and
reduce its conclusion to the goal, unfolding only the denotation of
lib/Ring.pf. In a field (#1322), an equation with inverses, quotients,
or fraction constants is proved by ``field_prove`` instead, whose
second premise, that the inverted factors are nonzero, reduces to side
conditions proved from the givens.

Otherwise, linear arithmetic:

1. Read the goal and the givens (with any ``with`` facts) as linear
   facts ``a ≤ b``, ``a < b``, ``a = b`` over the goal's type, writing
   each side as a ``Lin`` expression over atoms (the maximal subterms
   that are not sums, differences, negations, multiples by a constant,
   or constants).
2. Find a certificate by Fourier-Motzkin elimination: coefficients for
   the facts (and for ``0 < unit``, and the negated goal) whose
   combination is ``0 < 0``.
3. Instantiate ``lin_prove``, ``lin_disprove``, or ``lin_refute`` at the
   goal's type, the atoms, the facts, and the certificate, and reduce
   it, unfolding only the definitions of lib/Linear.pf. The certificate
   check reduces to ``true``, and the facts and conclusion to the givens
   and the goal as the user wrote them; anything else is an error.
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass
from fractions import Fraction
from math import gcd, lcm
from typing import Any, Callable, cast

from abstract_syntax import (
    LINEAR_DEFS, RING_DEFS, AlgebraGoal, AllElim, AllElimTypes, And, Bool, Call,
    ConceptRef, Env, Formula, FunctionType, IfThen, OverloadedVar, PVar, Proof,
    ResolvedVar, Term, TermInst, Type, Var, VarRef, base_name, full_reduce,
    get_dont_reduce_opaque, get_reduce_only, intToNat, isNat, isUInt, mkIntLit,
    mkUIntLit, natToInt, remove_mark, set_dont_reduce_opaque,
    set_reduce_only, uintToInt,
)
from abstract_syntax.literals import _mk_uint_from_int
from checker_concepts import find_model
from error import UserError, user_error
from flags import record_implicit_use
from lark.tree import Meta

# A linear expression, mirroring `Lin` in lib/Linear.pf:
#   ('var', i)  ('const', q, term)  ('zero',)  ('add', a, b)  ('sub', a, b)
#   ('neg', a)  ('scale', q, term, a)
# where ``term`` is the user's Rat literal for ``q`` (None: build one).
Lin = tuple[Any, ...]

# A linear form: the coefficient of each atom, with UNIT for `unit`.
UNIT = -1
Form = dict[int, Fraction]


def _name(t: Term) -> str | None:
  if isinstance(t, TermInst):
    t = t.subject
  if isinstance(t, VarRef):
    return cast(str, base_name(t.get_name()))
  return None


def _call(t: Term) -> tuple[str, list[Term]] | None:
  if isinstance(t, Call) and (n := _name(t.rator)) is not None:
    return n, t.args
  return None


def _int_value(t: Term) -> int | None:
  """The value of a UInt or Int literal (such as `-2`, the negation of a
  UInt literal)."""
  if isUInt(t):
    return cast(int, uintToInt(t))
  match _call(t):
    case ('pos', [u]) if isUInt(u):
      return cast(int, uintToInt(u))
    case ('negsuc', [u]) if isUInt(u):
      return -cast(int, uintToInt(u)) - 1
    case ('-', [u]) if (v := _int_value(u)) is not None:
      return -v
  return None


def _literal(t: Term) -> Fraction | None:
  """The value of a rational, real, or angle literal: ``rat(n)``,
  ``frac(n, d)``, ``real(n)``, ``real(q)``, ``deg(n)``, or ``deg(q)``."""
  match _call(t):
    case ('rat', [n]):
      v = _int_value(n)
      return None if v is None else Fraction(v)
    case ('frac', [n, d]):
      a, b = _int_value(n), _int_value(d)
      if a is None or b is None:
        return None
      return Fraction(0) if b == 0 else Fraction(a, b)
    case ('real' | 'deg', [x]):
      v = _int_value(x)
      return Fraction(v) if v is not None else _literal(x)
  return None


def _is_rat(t: Term) -> bool:
  return isinstance(t.typeof, VarRef) and base_name(t.typeof.get_name()) == 'Rat'


def _uint_lit(t: Term) -> int | None:
  """The value of a UInt literal, as written (``fromNat(lit(n))``) or
  evaluated."""
  if isUInt(t):
    return cast(int, uintToInt(t))
  match _call(t):
    case ('fromNat', [n]) if (c := _call(n)) is not None and c[0] == 'lit' \
        and isNat(c[1][0]):
      return cast(int, natToInt(c[1][0]))
  return None


def _ring_const(t: Term) -> Lin | None:
  """``t`` as a constant of lib/Ring.pf, ``('const', n, lit)`` with ``lit``
  the UInt literal for ``n`` (or None to build one), possibly negated:
  ``2``, ``+2``, ``-2``, ``rat(+2)``, ``real(+2)``, or the ring's
  ``zero`` or ``one``."""
  if (v := _uint_lit(t)) is not None:
    return ('const', v, t)
  match _call(t):
    case ('pos', [u]) if (v := _uint_lit(u)) is not None:
      return ('const', v, u)
    case ('negsuc', [u]) if (v := _uint_lit(u)) is not None:
      return ('neg', ('const', v + 1, None))
    case ('-', [u]) if (v := _uint_lit(u)) is not None:
      # An Int literal such as `-2` written as the negation of a UInt
      # literal.
      return ('neg', ('const', v, u))
    case ('rat' | 'real', [i]) if (c := _call(i)) is not None \
        and c[0] in ('pos', 'negsuc', '-'):
      return _ring_const(i)
  match _name(t):
    case 'zero':
      return ('zero',)
    case 'one':
      return ('one',)
  return None


def _frac_literal(n: Term, d: Term) -> Lin | None:
  """The fraction constant ``frac(n, d)``, ``('frac', n, d)`` for Nat
  values, possibly negated, if ``n`` and ``d`` are literals and ``d`` is
  positive."""
  a, b = _int_value(n), _int_value(d)
  if a is None or b is None or b <= 0:
    return None
  return ('neg', ('frac', -a, b)) if a < 0 else ('frac', a, b)


class _Reifier:
  """Reads terms as ``Lin`` or ``RExpr`` expressions, numbering the
  atoms."""

  def __init__(self, subtract: bool = False, divide: bool = False) -> None:
    # In ``ring``: whether differences and negations (in a ring), and
    # inverses and quotients (in a field), are normalized.
    self.subtract, self.divide = subtract, divide
    self.atoms: list[Term] = []

  def atom(self, t: Term) -> Lin:
    for i, a in enumerate(self.atoms):
      if a == t:
        return ('var', i)
    self.atoms.append(t)
    return ('var', len(self.atoms) - 1)

  def lin(self, t: Term) -> Lin:
    q = _literal(t)
    if q is not None:
      return ('const', q, t if _is_rat(t) else None)
    match _call(t):
      case ("+", [a, b]):
        return ('add', self.lin(a), self.lin(b))
      case ("-", [a, b]):
        return ('sub', self.lin(a), self.lin(b))
      case ("-", [a]):
        return ('neg', self.lin(a))
      case ("*", [c, a]) if (q := _literal(c)) is not None:
        return ('scale', q, c if _is_rat(c) else None, self.lin(a))
    return self.atom(t)

  def ring(self, t: Term) -> Lin:
    """``t`` as an ``RExpr`` of lib/Ring.pf: ('var', i), ('zero',),
    ('one',), ('const', n, lit), ('add', a, b), ('mul', a, b), ('pow', a,
    k, lit) for the UInt literal ``lit`` of value ``k``, in a ring (not a
    semiring) ('sub', a, b) and ('neg', a), and in a field ('inv', a) and
    ('div', a, b). Sums and products may be flattened by
    associativity."""
    if (c := _ring_const(t)) is not None and (self.subtract or c[0] != 'neg'):
      return c
    match _call(t):
      case ("+" | "*" as op, [a, *bs]) if bs:
        e = self.ring(a)
        for b in bs:
          e = ('add' if op == '+' else 'mul', e, self.ring(b))
        return e
      case ("-", [a, b]) if self.subtract:
        return ('sub', self.ring(a), self.ring(b))
      case ("-", [a]) if self.subtract:
        return ('neg', self.ring(a))
      case ('frac', [n, d]) if self.divide and (c := _frac_literal(n, d)):
        return c
      case ('real', [q]) if self.divide and (c := _call(q)) is not None \
          and c[0] == 'frac' and (f := _frac_literal(*c[1])):
        return f
      case ("/", [a, b]) if self.divide:
        return ('div', self.ring(a), self.ring(b))
      case ("inv", [a]) if self.divide:
        return ('inv', self.ring(a))
      case ("^", [a, k]) if isUInt(k) and uintToInt(k) <= _MAX_EXPONENT:
        e = ('pow', self.ring(a), uintToInt(k), k)
        if all(len(_poly(p, True)) <= _MAX_TERMS for p in _frac(e)):
          return e
    return self.atom(t)


# lib/Ring.pf multiplies out a power one factor at a time, so a power
# with a larger exponent, or whose expansion has more monomials, is left
# as an atom: checking `x ^ 200 * y = y * x ^ 200` takes 2.6 seconds,
# and `(x - y) ^ 20 = (y - x) ^ 20` (21 monomials) 7 seconds.
_MAX_EXPONENT = 256
_MAX_TERMS = 16


# A polynomial: the coefficient of each monomial, a monomial being the
# exponents of the atoms (without trailing zeros), as in lib/Ring.pf.
Poly = dict[tuple[int, ...], Fraction]


def _poly(e: Lin, unsigned: bool = False) -> Poly:
  """The polynomial of ``e``; if ``unsigned``, with each `-` read as `+`,
  which bounds the monomials lib/Ring.pf computes along the way. Nothing
  cancels then, so a power stops expanding past ``_MAX_TERMS``."""
  match e:
    case ('var', i):
      return {(0,) * i + (1,): Fraction(1)}
    case ('zero',):
      return {}
    case ('one',):
      return {(): Fraction(1)}
    case ('const', c, _):
      return {(): Fraction(abs(c) if unsigned else c)} if c else {}
    case ('add', a, b):
      return _plus(_poly(a, unsigned), _poly(b, unsigned), 1)
    case ('sub', a, b):
      return _plus(_poly(a, unsigned), _poly(b, unsigned), 1 if unsigned else -1)
    case ('neg', a):
      return _plus({}, _poly(a, unsigned), 1 if unsigned else -1)
    case ('mul', a, b):
      return _times(_poly(a, unsigned), _poly(b, unsigned))
    case ('pow', a, k, _):
      pa = _poly(a, unsigned)
      out: Poly = {(): Fraction(1)}
      for _ in range(k):
        out = _times(pa, out)
        if unsigned and len(out) > _MAX_TERMS:
          break
      return out
  raise ValueError(e)


def _times(p: Poly, q: Poly) -> Poly:
  out: Poly = {}
  for (m, c), (n, d) in itertools.product(p.items(), q.items()):
    mn = tuple(i + j for i, j in itertools.zip_longest(m, n, fillvalue=0))
    out = _plus(out, {mn: c * d}, 1)
  return out


# The fraction of an expression, as `field_frac` of lib/Ring.pf computes
# it (the checker passes the side conditions, which lib/Ring.pf compares
# with `field_conds`, so the two must agree).
_ONE: Lin = ('one',)


def _fmul(a: Lin, b: Lin) -> Lin:
  return b if a == _ONE else a if b == _ONE else ('mul', a, b)


def _frac(e: Lin) -> tuple[Lin, Lin]:
  match e:
    case ('add' | 'sub' as op, a, b):
      (na, da), (nb, db) = _frac(a), _frac(b)
      return (op, _fmul(na, db), _fmul(nb, da)), _fmul(da, db)
    case ('neg', a):
      na, da = _frac(a)
      return ('neg', na), da
    case ('mul', a, b):
      (na, da), (nb, db) = _frac(a), _frac(b)
      return _fmul(na, nb), _fmul(da, db)
    case ('pow', a, k, t):
      na, da = _frac(a)
      return ('pow', na, k, t), ('pow', da, k, t)
    case ('inv', a):
      na, da = _frac(a)
      return da, na
    case ('div', a, b):
      (na, da), (nb, db) = _frac(a), _frac(b)
      return _fmul(na, db), _fmul(da, nb)
    case ('frac', n, d):
      return ('const', n, None), ('const', d, None)
  return e, _ONE


def _factors(e: Lin) -> list[Lin]:
  match e:
    case ('mul', a, b):
      return _factors(a) + _factors(b)
    case ('pow', a, k, _):
      return [] if k == 0 else _factors(a)
    case ('neg', a):
      return _factors(a)
  return [] if e == _ONE else [e]


def _conds(e: Lin) -> list[Lin]:
  """The expressions that must be nonzero, as `field_conds`."""
  match e:
    case ('inv', a):
      return _factors(_frac(a)[0]) + _conds(a)
    case ('div', a, b):
      return _factors(_frac(b)[0]) + _conds(a) + _conds(b)
    case ('frac', _, d):
      return [('const', d, None)]
    case (_, *args):
      return [c for a in args if isinstance(a, tuple) for c in _conds(a)]
  raise ValueError(e)


def _divides(e: Lin) -> bool:
  return e[0] in ('inv', 'div', 'frac') or any(isinstance(a, tuple) and _divides(a)
                                       for a in e[1:])


def _show_poly(p: Poly, atoms: list[Term]) -> str:
  out = ''
  for m in sorted(p, key=lambda m: (-sum(m), [-k for k in m])):
    factors = [str(atoms[i]) + ('^' + str(k) if k > 1 else '')
               for i, k in enumerate(m) if k]
    c = abs(p[m])
    term = '·'.join(([str(c)] if c != 1 or not factors else []) + factors)
    out += (' - ' if p[m] < 0 else ' + ') + term if out \
        else ('-' if p[m] < 0 else '') + term
  return out or '0'


def form(e: Lin) -> Form:
  """The linear form of ``e``."""
  match e:
    case ('var', i):
      return {i: Fraction(1)}
    case ('const', q, _):
      return {UNIT: q} if q else {}
    case ('zero',):
      return {}
    case ('add', a, b):
      return _plus(form(a), form(b), 1)
    case ('sub', a, b):
      return _plus(form(a), form(b), -1)
    case ('neg', a):
      return _plus({}, form(a), -1)
    case ('scale', q, _, a):
      return _plus({}, form(a), q)
  raise ValueError(e)


def _plus[K](f: dict[K, Fraction], g: dict[K, Fraction],
             c: Fraction | int) -> dict[K, Fraction]:
  out = dict(f)
  for (k, v) in g.items():
    out[k] = out.get(k, Fraction(0)) + c * v
    if out[k] == 0:
      del out[k]
  return out


################ Fourier-Motzkin ################

@dataclass
class _Row:
  # form ≥ 0, or form > 0 when strict; cert gives the coefficient of
  # each fact in the combination that derives it.
  form: Form
  strict: bool
  cert: dict[int, Fraction]


MAX_ROWS = 4000


def certificate(facts: list[tuple[str, Lin, Lin]]) -> list[Fraction] | None:
  """Coefficients for ``facts`` (fact 0 being ``0 < unit``) whose
  combination of ``b - a`` is zero, nonnegative for the inequalities and
  positive for some strict one; None if there are none."""
  rows: list[_Row] = []
  for i, (rel, a, b) in enumerate(facts):
    d = _plus(form(b), form(a), -1)
    rows.append(_Row(d, rel == 'lt', {i: Fraction(1)}))
    if rel == 'eq':
      rows.append(_Row(_plus({}, d, -1), False, {i: Fraction(-1)}))
  while True:
    for r in rows:
      if not r.form and r.strict:
        return [r.cert.get(i, Fraction(0)) for i in range(len(facts))]
    rows = [r for r in rows if r.form]
    variables = {v for r in rows for v in r.form}
    if not variables:
      return None
    def cost(v: int) -> int:
      pos = sum(1 for r in rows if r.form.get(v, 0) > 0)
      neg = sum(1 for r in rows if r.form.get(v, 0) < 0)
      return pos * neg - pos - neg
    v = min(variables, key=cost)
    pos = [r for r in rows if r.form.get(v, 0) > 0]
    neg = [r for r in rows if r.form.get(v, 0) < 0]
    rows = [r for r in rows if v not in r.form]
    for (p, n) in itertools.product(pos, neg):
      cp, cn = p.form[v], -n.form[v]
      rows.append(_Row(_plus(_plus({}, p.form, cn), n.form, cp),
                       p.strict or n.strict,
                       _plus(_plus({}, p.cert, cn), n.cert, cp)))
    if len(rows) > MAX_ROWS:
      return None


def _integral(cs: list[Fraction]) -> list[Fraction]:
  """``cs`` scaled to the smallest integers: Deduce's literals are unary,
  so large ones are slow and deep."""
  m = lcm(*(c.denominator for c in cs))
  d = gcd(*(int(c * m) for c in cs)) or 1
  return [c * m / d for c in cs]


################ Building the proof ################

class _Builder:
  def __init__(self, loc: Meta, names: dict[str, list[str]], env: Env):
    self.loc = loc
    self.names = names
    self.env = env

  def var(self, name: str) -> Term:
    if name not in self.names:
      user_error(self.loc, 'algebra needs ' + name
                 + ' from lib/Linear.pf; add `import Linear`')
    return OverloadedVar(self.loc, None, self.names[name])

  def call(self, name: str, *args: Term) -> Term:
    return Call(self.loc, None, self.var(name), list(args))

  def uint(self, n: int) -> Term:
    # A binary UInt value, not a literal `fromNat(lit(n))` (a unary Nat
    # inside, as deep as its value).
    t = _mk_uint_from_int(self.loc, n, None, self.env)
    assert t is not None
    return t

  def nat(self, n: int) -> Term:
    # A raw numeral (not a `lit`), so that the patterns of lib/Linear.pf
    # match it.
    return self._resolve(intToNat(self.loc, n))

  def _resolve(self, t: Term) -> Term:
    """Resolve the base names in a literal built by the parser's helpers."""
    if isinstance(t, (Var, ResolvedVar)) and t.get_name() in self.names:
      return self.var(t.get_name())
    if isinstance(t, Call):
      return Call(t.location, None, self._resolve(t.rator),
                  [self._resolve(a) for a in t.args])
    return t

  def rat(self, q: Fraction) -> Term:
    num = self._resolve(mkIntLit(self.loc, abs(q.numerator),
                                 'PLUS' if q >= 0 else 'MINUS'))
    if q.denominator == 1:
      return self.call('rat', num)
    return self.call('frac', num,
                     self._resolve(mkUIntLit(self.loc, q.denominator)))

  def lin(self, e: Lin) -> Term:
    match e:
      case ('var', i):
        return self.call('lvar', self.nat(i))
      case ('const', q, t):
        return self.call('lconst', t if t is not None else self.rat(q))
      case ('zero',):
        return self.var('lzero')
      case ('add', a, b):
        return self.call('ladd', self.lin(a), self.lin(b))
      case ('sub', a, b):
        return self.call('lsub', self.lin(a), self.lin(b))
      case ('neg', a):
        return self.call('lneg', self.lin(a))
      case ('scale', q, t, a):
        return self.call('lscale', t if t is not None else self.rat(q),
                         self.lin(a))
    raise ValueError(e)

  def rexpr(self, e: Lin) -> Term:
    match e:
      case ('var', i):
        return self.call('rvar', self.nat(i))
      case ('zero' | 'one' as c,):
        return self.var('r' + c)
      case ('neg', ('const', n, t)):
        # A literal, as written (or built), so that the auto rules for
        # Int literals take `- pos(3)` to the goal's `-3`, `negsuc(2)`.
        return self.call('rneg', self.call(
            'rconst', t if t is not None
            else self._resolve(mkUIntLit(self.loc, n))))
      case ('neg', ('frac', n, d)):
        # Literals, so that the auto rules take `- frac(+1, 3)` to the
        # goal's `frac(-1, 3)`.
        return self.call('rneg', self.call(
            'rfrac', self._resolve(mkUIntLit(self.loc, n)),
            self._resolve(mkUIntLit(self.loc, d))))
      case ('const', n, _):
        return self.call('rconst', self.uint(n))
      case ('pow', a, _, t):
        return self.call('rpow', self.rexpr(a), t)
      case ('frac', n, d):
        return self.call('rfrac', self.uint(n), self.uint(d))
      case (op, *args):
        return self.call('r' + op, *[self.rexpr(a) for a in args])
    raise ValueError(e)

  def fact(self, f: tuple[str, Lin, Lin]) -> Term:
    rel, a, b = f
    return self.call('lin_fact', self.var('r' + rel), self.lin(a), self.lin(b))

  def list(self, items: list[Term]) -> Term:
    out = self.var('empty')
    for t in reversed(items):
      out = self.call('node', t, out)
    return out


################ The tactic ################

_RELS = {"≤": "le", "<": "lt", "=": "eq"}
_FLIPPED = {"≥": "le", ">": "lt"}


def _relation(frm: Formula) -> tuple[str, Term, Term] | None:
  """``frm`` as ``a R b`` with R one of le, lt, eq."""
  match _call(frm):
    case (op, [a, b]) if op in _RELS:
      return _RELS[op], a, b
    case (op, [a, b]) if op in _FLIPPED:
      return _FLIPPED[op], b, a
  return None


def _conjuncts(frm: Formula) -> list[Formula]:
  if isinstance(frm, And):
    return [c for a in frm.args for c in _conjuncts(a)]
  return [frm]


def _negation(frm: Formula) -> Formula | None:
  if isinstance(frm, IfThen) and isinstance(frm.conclusion, Bool) \
     and frm.conclusion.value is False:
    return frm.premise
  return None


def check_algebra(proof: AlgebraGoal, goal: Formula, env: Env,
                  check_proof: Callable[[Proof, Env], Formula]) -> None:
  loc = proof.location
  goal = remove_mark(goal)
  ring_note = _check_ring(proof, goal, env, check_proof)
  if ring_note is None:
    return
  negated = _negation(goal)
  target = _relation(negated if negated is not None else goal)
  is_false = isinstance(goal, Bool) and goal.value is False
  if target is None and not is_false:
    user_error(loc, 'algebra proves an equation or inequality (=, ≤, <, ≥,'
               ' >), its negation, or false, not\n\t' + str(goal))

  givens = env.local_proofs() + [check_proof(p, env) for p in proof.givens]
  available = [c for g in givens for c in _conjuncts(g)]
  relations = [r for c in available if (r := _relation(c)) is not None]
  if target is not None:
    ty = target[1].typeof
  elif relations:
    # Refute at the first type of the givens that `algebra` works at.
    tys = [r[1].typeof for r in relations]
    ty = next((t for t in tys if _has_model(proof, env, 'LinearArith', t)), tys[0])
  else:
    user_error(loc, 'algebra found no equations or inequalities among the'
               ' givens')
  assert ty is not None
  if not _has_model(proof, env, 'LinearArith', ty):
    if ring_note:
      user_error(loc, 'algebra could not prove\n\t' + str(goal) + '\n' + ring_note)
    if 'LinearArith' not in proof.names:
      user_error(loc, 'algebra needs lib/Linear.pf; add `import Linear`')
    ring = 'CommSemiring (such as UInt, Int, Rat, and Real) or ' \
        if target is not None and target[0] == 'eq' and negated is None else ''
    user_error(loc, 'algebra works at the types that model ' + ring
               + 'LinearArith (such as Rat, Real, and Angle), not ' + str(ty))

  reifier = _Reifier()
  hyps = [(rel, reifier.lin(a), reifier.lin(b))
          for (rel, a, b) in relations if a.typeof == ty]
  unit_fact = ('lt', ('zero',), ('const', Fraction(1), None))

  def refute(extra: list[tuple[str, Lin, Lin]]) -> list[Fraction]:
    cert = certificate([unit_fact] + extra + hyps)
    if cert is None:
      _fail(loc, target, hyps, reifier, ring_note)
    assert cert is not None
    return _integral(cert)

  b = _Builder(loc, proof.names, env)
  if target is not None and negated is None:
    rel, x, y = target
    g = (rel, reifier.lin(x), reifier.lin(y))
    cs2: list[Fraction] = []
    if rel == 'le':
      cs1 = refute([('lt', g[2], g[1])])
    elif rel == 'lt':
      cs1 = refute([('le', g[2], g[1])])
    else:
      cs1 = refute([('lt', g[1], g[2])])
      cs2 = refute([('lt', g[2], g[1])])
    theorem, args = 'lin_prove', [b.fact(g), b.list([b.fact(h) for h in hyps]),
                                  b.list([b.rat(c) for c in cs1]),
                                  b.list([b.rat(c) for c in cs2])]
  elif target is not None:
    rel, x, y = target
    g = (rel, reifier.lin(x), reifier.lin(y))
    cs = refute([g])
    theorem, args = 'lin_disprove', [b.fact(g),
                                     b.list([b.fact(h) for h in hyps]),
                                     b.list([b.rat(c) for c in cs])]
  else:
    cs = refute([])
    theorem, args = 'lin_refute', [b.list([b.fact(h) for h in hyps]),
                                   b.list([b.rat(c) for c in cs])]
  frm = _instance(proof, theorem, ty, [b.list(reifier.atoms)] + args, env,
                  check_proof)
  # The premise is the certificate's check, which is closed, so it
  # evaluates, and the facts, which must be givens (up to unfolding ≥
  # and >).
  assert isinstance(frm, IfThen) and isinstance(frm.premise, And)
  check, hold = frm.premise.args
  _check_closed(loc, check, env)
  ops = _scale_op(frm)
  facts = [f for c in available for f in _forms(c, env)]
  for p in _conjuncts(_reduce(loc, hold, proof.names, LINEAR_DEFS, ops, env)):
    if not (isinstance(p, Bool) and p.value is True) and p not in facts:
      user_error(loc, 'algebra: the certificate needs\n\t' + str(p)
                 + '\nwhich is not a given')
  concl = _reduce(loc, frm.conclusion, proof.names, LINEAR_DEFS, ops, env)
  if concl not in _forms(goal, env):
    user_error(loc, 'algebra proved\n\t' + str(concl)
               + '\ninstead of\n\t' + str(goal))


def _check_ring(proof: AlgebraGoal, goal: Formula, env: Env,
                check_proof: Callable[[Proof, Env], Formula]) -> str | None:
  """Prove ``goal`` by ring normalization, returning None. If it is not
  an equation at a type that models CommRing or CommSemiring, return '';
  if the sides are different polynomials, return their normal forms."""
  match _call(goal):
    case ('=', [lhs, rhs]):
      pass
    case _:
      return ''
  ty = lhs.typeof
  assert ty is not None
  if 'ring_prove' in proof.names and _has_model(proof, env, 'CommRing', ty):
    ring, theorem = True, 'ring_prove'
  elif 'semiring_prove' in proof.names and _has_model(proof, env, 'CommSemiring', ty):
    ring, theorem = False, 'semiring_prove'
  else:
    return ''
  field = ring and 'field_prove' in proof.names \
      and _has_model(proof, env, 'Field', ty)
  reifier = _Reifier(ring, field)
  a, b = reifier.ring(lhs), reifier.ring(rhs)
  if _divides(a) or _divides(b):
    return _check_field(proof, goal, env, check_proof, ty, reifier, a, b)
  pa, pb = _poly(a), _poly(b)
  if pa != pb:
    monus = not ring and any((c := _call(t)) is not None and c[0] in ('-', '∸')
                             for t in reifier.atoms)
    return ('as polynomials, the two sides are\n\t'
            + _show_poly(pa, reifier.atoms) + '\nand\n\t'
            + _show_poly(pb, reifier.atoms)
            + ('\n(' + str(ty) + ' is a semiring, so subtraction is not'
               ' normalized)' if monus else ''))
  loc = proof.location
  bld = _Builder(loc, proof.names, env)
  frm = _instance(proof, theorem, ty,
                  [bld.list(reifier.atoms), bld.rexpr(a), bld.rexpr(b)],
                  env, check_proof)
  assert isinstance(frm, IfThen)
  _check_closed(loc, frm.premise, env)
  _check_conclusion(proof, frm.conclusion, goal, env)
  return None


def _check_field(proof: AlgebraGoal, goal: Formula, env: Env,
                 check_proof: Callable[[Proof, Env], Formula], ty: Type,
                 reifier: _Reifier, a: Lin, b: Lin) -> str | None:
  """Prove ``goal``, an equation ``a = b`` with inverses or quotients, by
  bringing each side to a fraction and comparing the cross products
  (``field_prove``). The side conditions, that the inverted factors are
  nonzero, must be givens or follow by `algebra`'s linear mode."""
  (na, da), (nb, db) = _frac(a), _frac(b)
  if _poly(('mul', na, db)) != _poly(('mul', nb, da)):
    return ('as fractions, the two sides are\n\t'
            + _show_frac(na, da, reifier.atoms) + '\nand\n\t'
            + _show_frac(nb, db, reifier.atoms))
  conds: list[Lin] = []
  for c in _conds(a) + _conds(b):
    if c not in conds:
      conds.append(c)
  loc = proof.location
  bld = _Builder(loc, proof.names, env)
  frm = _instance(proof, 'field_prove', ty,
                  [bld.list(reifier.atoms), bld.rexpr(a), bld.rexpr(b),
                   bld.list([bld.rexpr(c) for c in conds])],
                  env, check_proof)
  assert isinstance(frm, IfThen) and isinstance(frm.conclusion, IfThen)
  _check_closed(loc, frm.premise, env)
  side = _reduce(loc, frm.conclusion.premise, proof.names, RING_DEFS, [], env)
  unproved = [p for p in _conjuncts(side)
              if not (isinstance(p, Bool) and p.value is True)
              and not _side_condition(proof, p, env, check_proof)]
  if unproved:
    user_error(loc, 'algebra needs the denominators to be nonzero, but could'
               ' not prove\n\t' + '\n\t'.join(str(p) for p in unproved)
               + '\nfrom the givens')
  _check_conclusion(proof, frm.conclusion.conclusion, goal, env)
  return None


def _side_condition(proof: AlgebraGoal, p: Formula, env: Env,
                    check_proof: Callable[[Proof, Env], Formula]) -> bool:
  """Whether ``p`` is a given (or a `with` fact), follows from them by
  `algebra` (its linear mode, as for `not (y = real(+0))` from
  `real(+0) < y`), or, for a constant, evaluates to `true` (as
  `not (real(+2) = real(+0))`)."""
  v = full_reduce(p, env)
  if isinstance(v, Bool) and v.value is True:
    return True
  givens = env.local_proofs() + [check_proof(g, env) for g in proof.givens]
  available = [f for g in givens for c in _conjuncts(g) for f in _forms(c, env)]
  if p in available:
    return True
  # A given `not (b = a)`.
  if (n := _negation(p)) is not None and (r := _relation(n)) is not None \
     and any((m := _negation(c)) is not None and _relation(m) == ('eq', r[2], r[1])
             for c in available):
    return True
  try:
    check_algebra(proof, p, env, check_proof)
    return True
  except UserError:
    return False


def _check_closed(loc: Meta, premise: Formula, env: Env) -> None:
  """The premise, that the normal forms are equal (or that the linear
  certificate checks), is about closed expressions, so it evaluates
  (fast) to `true`."""
  premise = full_reduce(premise, env)
  if not (isinstance(premise, Bool) and premise.value is True):
    user_error(loc, 'algebra: the check did not evaluate to true\n\t'
               + str(premise))


def _check_conclusion(proof: AlgebraGoal, frm: Formula, goal: Formula,
                      env: Env) -> None:
  frm = _reduce(proof.location, frm, proof.names, RING_DEFS, [], env)
  # Compare with the goal as written first: reducing it may compute
  # with its literals in unary. A goal may also reduce to `true` (as
  # `inv(x ^ 0) = real(+1)`).
  if not _same(frm, goal) \
     and not any(_same(frm, g) or (isinstance(g, Bool) and g.value is True)
                 for g in _forms(goal, env)):
    user_error(proof.location, 'algebra proved\n\t' + str(frm)
               + '\ninstead of\n\t' + str(goal))


def _same(a: Term, b: Term) -> bool:
  """Whether ``a`` and ``b`` are equal, comparing UInt numerals by value:
  the instance's positive constants are binary UInt values, the goal's
  literals `fromNat(lit(n))`, with a unary Nat as deep as its value
  (too deep for `==`)."""
  if isUInt(a) and isUInt(b):
    return cast(int, uintToInt(a)) == cast(int, uintToInt(b))
  match a, b:
    case Call(_, _, r1, args1), Call(_, _, r2, args2):
      return len(args1) == len(args2) and _same(r1, r2) \
          and all(_same(x, y) for x, y in zip(args1, args2))
    case IfThen(_, _, p1, c1), IfThen(_, _, p2, c2):
      return _same(p1, p2) and _same(c1, c2)
  return bool(a == b)


def _show_frac(n: Lin, d: Lin, atoms: list[Term]) -> str:
  pn, pd = _show_poly(_poly(n), atoms), _show_poly(_poly(d), atoms)
  if pd == '1':
    return pn
  return ' / '.join('(' + s + ')' if ' ' in s else s for s in (pn, pd))


def _has_model(proof: AlgebraGoal, env: Env, concept: str, ty: Type) -> bool:
  if concept not in proof.names:
    return False
  try:
    find_model(env, ConceptRef(proof.location, proof.names[concept][0], [ty]),
               proof.models, proof.location)
    return True
  except UserError:
    return False


def _instance(proof: AlgebraGoal, theorem: str, ty: Type, args: list[Term],
              env: Env, check_proof: Callable[[Proof, Env], Formula]) -> Formula:
  """The formula of ``theorem`` instantiated at ``ty`` and ``args``."""
  loc = proof.location
  # The proof uses the theorem, though the source doesn't name it
  # (for `--postulates`).
  record_implicit_use(proof.names[theorem][0])
  inst: Proof = AllElimTypes(loc, PVar(loc, proof.names[theorem][0]), ty,
                             (0, 1), models=proof.models)
  for i, arg in enumerate(args):
    inst = AllElim(loc, inst, arg, (i, len(args)))
  return check_proof(inst, env)


def _reduce(loc: Meta, frm: Formula, names: dict[str, list[str]],
            def_names: tuple[str, ...], ops: list[Term], env: Env) -> Formula:
  """Unfold the definitions ``def_names`` and the operations ``ops`` in
  ``frm``."""
  defs: list[Term] = [ResolvedVar(loc, None, n)
                      for name in def_names for n in names.get(name, [])]
  defs += ops
  # A pass unfolds each recursive call once, so repeat to a fixed point.
  while True:
    new_frm = _with_reduce(defs, frm, env)
    if new_frm == frm:
      return frm
    frm = new_frm


def _scale_op(frm: Term) -> list[Term]:
  """The `scale` operation passed for the where clause of a function of
  lib/Linear.pf (say, `lin_holds`) in ``frm``, to unfold it (say, Real's
  `real_scale` to `real(q) * x`)."""
  match frm:
    case Call(_, _, TermInst(_, _, subject, _, _, dicts=dicts), _) if dicts:
      funty = subject.typeof
      assert isinstance(funty, FunctionType) and funty.where is not None
      ops = funty.where.operations()
      i = next(i for i, wm in enumerate(ops) if base_name(wm.member) == 'scale')
      return [dicts[i]] if isinstance(dicts[i], VarRef) else []
    case Call(_, _, rator, args):
      return [v for a in [rator] + args for v in _scale_op(a)][:1]
    case And(_, _, args):
      return [v for a in args for v in _scale_op(a)][:1]
    case IfThen(_, _, premise, conclusion):
      return (_scale_op(premise) + _scale_op(conclusion))[:1]
  return []


def _forms(frm: Formula, env: Env) -> list[Formula]:
  """``frm``, reduced, and with ≥ and > unfolded to ≤ and <: the forms a
  premise or conclusion of the instance may take."""
  forms = [frm, frm.reduce(env)]
  match frm:
    case Call(_, _, rator, _) if _name(rator) in _FLIPPED:
      forms.append(_with_reduce([rator], frm, env))
  return forms


def _with_reduce(defs: list[Term], frm: Formula, env: Env) -> Formula:
  old_defs, old_opaque = get_reduce_only(), get_dont_reduce_opaque()
  set_reduce_only(old_defs + defs)
  set_dont_reduce_opaque(True)
  try:
    return frm.reduce(env)
  finally:
    set_reduce_only(old_defs)
    set_dont_reduce_opaque(old_opaque)


def _show(e: Lin, atoms: list[Term]) -> str:
  match e:
    case ('var', i):
      return str(atoms[i])
    case ('const', q, _):
      return str(q)
    case ('zero',):
      return '0'
    case ('add', a, b):
      return '(' + _show(a, atoms) + ' + ' + _show(b, atoms) + ')'
    case ('sub', a, b):
      return '(' + _show(a, atoms) + ' - ' + _show(b, atoms) + ')'
    case ('neg', a):
      return '-' + _show(a, atoms)
    case ('scale', q, _, a):
      return str(q) + '·' + _show(a, atoms)
  return str(e)


def _fail(loc: Meta, target: tuple[str, Term, Term] | None,
          hyps: list[tuple[str, Lin, Lin]], reifier: _Reifier,
          ring_note: str) -> None:
  sym = {'le': '≤', 'lt': '<', 'eq': '='}
  lines = ['\t' + _show(a, reifier.atoms) + ' ' + sym[r] + ' '
           + _show(b, reifier.atoms) for (r, a, b) in hyps]
  goal = 'false' if target is None else \
      str(target[1]) + ' ' + sym[target[0]] + ' ' + str(target[2])
  user_error(loc, 'algebra could not prove\n\t' + goal
             + '\nby a linear combination of the givens'
             + (':\n' + '\n'.join(lines) if lines else ' (there are none)')
             + ('\n' + ring_note if ring_note else ''))
