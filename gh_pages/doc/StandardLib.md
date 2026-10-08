# Standard Library

This section provides links to the theorems defined in the Deduce standard library along with the source files for the Deduce standard library.

Only the top-level module files (such as `UInt.pf`) are listed below. Each module may be split internally across several private helper files (for example, `UIntAdd.pf`, `UIntMult.pf`, ...) that are publicly imported from the main module file; users should import the module by its top-level name.

- ([`Base.thm`](../lib/Base.thm), [`Base.pf`](../lib/Base.pf)): Base proofs about propositional and predicate logic
- ([`BigO.thm`](../lib/BigO.thm), [`BigO.pf`](../lib/BigO.pf)): Big-O asymptotic analysis on `fn UInt -> UInt`
- ([`Int.thm`](../lib/Int.thm), [`Int.pf`](../lib/Int.pf)): Integers
- ([`List.thm`](../lib/List.thm), [`List.pf`](../lib/List.pf)): Lists.
  Higher-order list functions use collection-first order:
  `map(xs, f)`, `filter(xs, P)`, `foldr(xs, u, c)`, and
  `foldl(xs, u, c)`.
- ([`Maps.thm`](../lib/Maps.thm), [`Maps.pf`](../lib/Maps.pf)): Functional maps
- ([`MultiSet.thm`](../lib/MultiSet.thm), [`MultiSet.pf`](../lib/MultiSet.pf)): Multisets
- ([`Nat.thm`](../lib/Nat.thm), [`Nat.pf`](../lib/Nat.pf)): Natural numbers
- ([`Option.pf`](../lib/Option.pf)): Optional values
- ([`Pair.pf`](../lib/Pair.pf)): Pairs
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
- ([`Set.thm`](../lib/Set.thm), [`Set.pf`](../lib/Set.pf)): Sets
- ([`UInt.thm`](../lib/UInt.thm), [`UInt.pf`](../lib/UInt.pf)): Unsigned integers
