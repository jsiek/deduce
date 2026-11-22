# Standard Library

This section provides links to the theorems defined in the Deduce standard library along with the source files for the Deduce standard library.

Only the top-level module files (such as `UInt.pf`) are listed below. Each module may be split internally across several private helper files (for example, `UIntAdd.pf`, `UIntMult.pf`, ...) that are publicly imported from the main module file; users should import the module by its top-level name.

- ([`Algebra.thm`](../lib/Algebra.thm), [`Algebra.pf`](../lib/Algebra.pf)): The
  [concepts](./Reference.md#concept-statement) `AddCommGroup`,
  `OrderedAddCommGroup`, and `OrderedQVectorSpace` (an ordered abelian
  group with scaling by rationals), with models for `Rat` and `Real`,
  and `CommSemiring` (a commutative semiring that reads integer
  constants), with models for `UInt`, `Int`, `Rat`, and `Real`,
  and `CommRing`, with models for `Int`, `Rat`, and `Real`. Prove a theorem once under
  `where { OrderedQVectorSpace<T> }` and use it at `Rat` or `Real`.
- ([`Angle.thm`](../lib/Angle.thm), [`Angle.pf`](../lib/Angle.pf)): Angle
  measures. Write `deg(n)` for n degrees (an `Int` or a `Rat`), e.g.
  `deg(+90)` or `deg(frac(+45, 2))`. Angles can be added, negated,
  subtracted, scaled by a rational (`frac(+1, 2) * a`), and compared;
  concrete arithmetic on `deg` values is computed automatically.
  `Angle` models `LinearArith`, so the
  [`algebra`](./Reference.md#algebra-proof) tactic proves linear facts
  about angles, such as that supplements of the same angle are equal.
- ([`Base.thm`](../lib/Base.thm), [`Base.pf`](../lib/Base.pf)): Base proofs about propositional and predicate logic
- ([`BigO.thm`](../lib/BigO.thm), [`BigO.pf`](../lib/BigO.pf)): Big-O asymptotic analysis on `fn UInt -> UInt`
- ([`Int.thm`](../lib/Int.thm), [`Int.pf`](../lib/Int.pf)): Integers
- ([`Linear.thm`](../lib/Linear.thm), [`Linear.pf`](../lib/Linear.pf)): The
  certificates of the [`algebra`](./Reference.md#algebra-proof) tactic,
  and the concept `LinearArith` (an `OrderedQVectorSpace` with a
  positive `unit`) of the types it works at, with models for `Rat` and
  `Real`.
- ([`List.thm`](../lib/List.thm), [`List.pf`](../lib/List.pf)): Lists.
  Higher-order list functions use collection-first order:
  `map(xs, f)`, `filter(xs, P)`, `foldr(xs, u, c)`, and
  `foldl(xs, u, c)`.
- ([`Maps.thm`](../lib/Maps.thm), [`Maps.pf`](../lib/Maps.pf)): Functional maps
- ([`MultiSet.thm`](../lib/MultiSet.thm), [`MultiSet.pf`](../lib/MultiSet.pf)): Multisets
- ([`Nat.thm`](../lib/Nat.thm), [`Nat.pf`](../lib/Nat.pf)): Natural numbers
- ([`Option.pf`](../lib/Option.pf)): Optional values
- ([`Pair.pf`](../lib/Pair.pf)): Pairs
- ([`Point.thm`](../lib/Point.thm), [`Point.pf`](../lib/Point.pf)): Points
  of the plane, for coordinate geometry. `point(x, y)` is the point
  with `Real` coordinates `x` and `y`, read back with `xcoord` and
  `ycoord`; the representation is private. `dist2(A, B)` is the
  squared distance, `midpoint(A, B)` the midpoint, `dot(O, A, B)` and
  `cross(O, A, B)` the dot and cross products of OA and OB,
  `collinear(A, B, C)` means `cross(A, B, C) = real(+0)`, and
  `seg_congruent(A, B, C, D)` means `dist2(A, B) = dist2(C, D)`.
  `expand` any of these for its coordinate formula. Theorems include
  the Pythagorean theorem and its converse (`point_pythagoras`) and
  that the midpoint is equidistant from the endpoints.
- ([`Rat.thm`](../lib/Rat.thm), [`Rat.pf`](../lib/Rat.pf)): Rational numbers.
  Write `frac(n, d)` for the rational `n / d` (an `Int` over a `UInt`)
  and `rat(n)` for an integer, e.g. `frac(+3, 4) + rat(+1) = frac(+7, 4)`.
  The representation is canonical, so `=` is equality of rationals.
  Division by zero gives zero: `x / rat(+0) = rat(+0)`.
- ([`Real.thm`](../lib/Real.thm), [`Real.pf`](../lib/Real.pf)): Real numbers,
  axiomatized as a real closed field. All assumptions are in
  [`RealAxioms.pf`](../lib/RealAxioms.pf). Write
  `real(n)` for an integer and `real(q)` for a rational, e.g.
  `real(frac(+1, 2))`; concrete arithmetic on these is computed
  automatically. `python deduce.py --postulates file.pf` lists the
  axioms a file depends on.
- ([`Ring.thm`](../lib/Ring.thm), [`Ring.pf`](../lib/Ring.pf)): Ring
  normalization for the [`algebra`](./Reference.md#algebra-proof)
  tactic: it proves an equation whose sides are equal as polynomials
  over any type that models `CommSemiring`, such as
  `(x + y) * (x + y) = x * x + real(+2) * x * y + y * y`.
- ([`Set.thm`](../lib/Set.thm), [`Set.pf`](../lib/Set.pf)): Sets
- ([`UInt.thm`](../lib/UInt.thm), [`UInt.pf`](../lib/UInt.pf)): Unsigned integers
- ([`WellFounded.thm`](../lib/WellFounded.thm), [`WellFounded.pf`](../lib/WellFounded.pf)):
  The concept `WellFounded` of well-founded orders, whose `<` admits
  strong induction. A [`recfun`](./Reference.md#recfun-statement)'s
  measure decreases along the `<` of a model of it; `Nat` and `UInt`
  have models.
