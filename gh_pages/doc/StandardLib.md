# Standard Library

This section provides links to the theorems defined in the Deduce standard library along with the source files for the Deduce standard library.

Only the top-level module files (such as `UInt.pf`) are listed below. Each module may be split internally across several private helper files (for example, `UIntAdd.pf`, `UIntMult.pf`, ...) that are publicly imported from the main module file; users should import the module by its top-level name.

- ([`Algebra.thm`](../lib/Algebra.thm), [`Algebra.pf`](../lib/Algebra.pf)): The
  [concepts](./Reference.md#concept-statement) `AddCommGroup`,
  `OrderedAddCommGroup`, and `OrderedQVectorSpace` (an ordered abelian
  group with scaling by rationals), with models for `Rat` and `Real`,
  and `CommSemiring` (a commutative semiring that reads integer
  constants, with powers `x ^ k` for a `UInt` exponent `k`), with models for `UInt`, `Int`, `Rat`, and `Real`,
  `CommRing`, with models for `Int`, `Rat`, and `Real`, and `Field`
  (a commutative ring with `inv` and `/` that reads fraction
  constants), with models for `Rat` and `Real`. Prove a theorem once under
  `where { OrderedQVectorSpace<T> }` and use it at `Rat` or `Real`.
- ([`Angle.thm`](../lib/Angle.thm), [`Angle.pf`](../lib/Angle.pf)): Angle
  measures. Write `deg(n)` for n degrees (an `Int` or a `Rat`), e.g.
  `deg(+90)` or `deg(frac(+45, 2))`. Angles can be added, negated,
  subtracted, scaled by a rational (`frac(+1, 2) * a`), and compared;
  concrete arithmetic on `deg` values is computed automatically.
  `Angle` models `LinearArith`, so the
  [`algebra`](./Reference.md#algebra-proof) tactic proves linear facts
  about angles, such as that supplements of the same angle are equal.
- ([`AngleMeasure.thm`](../lib/AngleMeasure.thm), [`AngleMeasure.pf`](../lib/AngleMeasure.pf)):
  Angle measure, for coordinate geometry. `m_angle(A, B, C)` is the
  measure of angle ABC, an `Angle` from `deg(+0)` to `deg(+180)`,
  computed from the coordinates; `angle_interior(D, A, B, C)`,
  `right_angle`, `angle_congruent`, `angle_bisects`, `complementary`,
  and `supplementary` are defined from it. Theorems include the
  Protractor Postulate (`angle_protractor`, `angle_protractor_unique`),
  the Angle Addition Postulate (`angle_add`), the Linear Pair
  Postulate (`angle_linear_pair`), the Vertical Angles Theorem
  (`angle_vertical`), that an angle is right exactly when its sides
  are perpendicular (`angle_right_perpendicular`), that angles with
  the same dot product and cross products of the same absolute value
  have equal measures (`angle_measure_dot_cross`), that a degenerate
  angle measures 0° or 180° (`angle_measure_collinear`), and that P and Q
  are on opposite sides of a line exactly when segment PQ meets it
  (`line_opposite_sides_between`). The measure rests on four
  postulates about a private function `arg` (the angle of a vector),
  listed at the top of the file.
- ([`Base.thm`](../lib/Base.thm), [`Base.pf`](../lib/Base.pf)): Base proofs about propositional and predicate logic
- ([`Between.thm`](../lib/Between.thm), [`Between.pf`](../lib/Between.pf)):
  Betweenness, segments, rays, and the ruler, for coordinate geometry.
  `between(A, B, C)` says that B is strictly between A and C (so the
  three points are distinct and collinear), `on_segment(P, A, B)` that
  P is A, B, or between them, and `on_ray(P, A, B)` that P is on
  segment AB or B is between A and P. `ruler(A, B, P)` is the
  coordinate of P on the ruler with A at 0 and B at `dist(A, B)`.
  Theorems include the Segment Addition Postulate and its converse
  (`between_seg_add`, `between_seg_add_converse`, and `seg_add`: B is
  on segment AC exactly when AB + BC = AC), the Ruler Postulate
  (`ruler_dist`, `ruler_onto`), point plotting (`ray_point_plotting`,
  `ray_dist_unique`), that exactly one of three distinct collinear
  points is between the other two (`between_trichotomy`,
  `between_unique`), opposite rays (`ray_opposite`), and the
  definition of midpoint (`seg_midpoint_iff`).
- ([`BigO.thm`](../lib/BigO.thm), [`BigO.pf`](../lib/BigO.pf)): Big-O asymptotic analysis on `fn UInt -> UInt`
- ([`Int.thm`](../lib/Int.thm), [`Int.pf`](../lib/Int.pf)): Integers
- ([`Linear.thm`](../lib/Linear.thm), [`Linear.pf`](../lib/Linear.pf)): The
  certificates of the [`algebra`](./Reference.md#algebra-proof) tactic,
  and the concept `LinearArith` (an `OrderedQVectorSpace` with a
  positive `unit`) of the types it works at, with models for `Rat` and
  `Real`.
- ([`Line.thm`](../lib/Line.thm), [`Line.pf`](../lib/Line.pf)): Lines
  of the plane, for coordinate geometry. `line(A, B)` is the line
  through the points `A` and `B`, and `on_line(P, L)` says that `P` is
  on `L`; the representation is private and canonical, so `=` on lines
  is equality of lines. `parallel(L, M)` and `perpendicular(L, M)`
  work for vertical lines too. Theorems include that two distinct
  points determine a unique line (`line_unique`), that P is on line AB
  exactly when A, B, P are collinear (`line_on_collinear`), and that
  AB ∥ CD and AB ⊥ CD exactly when `seg_cross(A, B, C, D)` and
  `seg_dot(A, B, C, D)`, the cross and dot products of the vectors AB
  and CD, are zero (`line_parallel_seg_cross`,
  `line_perpendicular_seg_dot`), or, for lines that are not vertical,
  when the slopes are equal or have product -1
  (`line_parallel_slope`, `line_perpendicular_slope`).
  `same_side(P, Q, L)` and `opposite_sides(P, Q, L)` give the Plane
  Separation Postulate (`line_plane_separation`,
  `line_same_side_trans`, `line_opposite_sides_trans`,
  `line_same_opposite_sides`), and every line is `line(A, B)` for
  some distinct A and B (`line_points`).
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
  `ycoord`; the representation is private. `dist(A, B)` is the
  distance, `sqrt(dist2(A, B))`, and `dist2(A, B)` the squared
  distance, `midpoint(A, B)` the midpoint, `dot(O, A, B)` and
  `cross(O, A, B)` the dot and cross products of OA and OB,
  `collinear(A, B, C)` means `cross(A, B, C) = real(+0)`,
  `seg_congruent(A, B, C, D)` means `dist2(A, B) = dist2(C, D)`, and
  `slope(A, B)` is the slope of AB (meaningful when `xcoord(A) ≠
  xcoord(B)`). `expand` any of these for its coordinate formula.
  Theorems include the Pythagorean theorem and its converse
  (`point_pythagoras`), that the midpoint is equidistant from the
  endpoints, that A, B, C are collinear exactly when AB and AC
  have the same slope (`point_slope_collinear`), and that points C
  and D of line AB are collinear with A (`point_collinear_trans`).
- ([`Rat.thm`](../lib/Rat.thm), [`Rat.pf`](../lib/Rat.pf)): Rational numbers.
  Write `frac(n, d)` for the rational `n / d` (an `Int` over a `UInt`)
  and `rat(n)` for an integer, e.g. `frac(+3, 4) + rat(+1) = frac(+7, 4)`.
  The representation is canonical, so `=` is equality of rationals.
  Division by zero gives zero: `x / rat(+0) = rat(+0)`.
  `x ^ k` is the power with a `UInt` exponent `k`.
- ([`Real.thm`](../lib/Real.thm), [`Real.pf`](../lib/Real.pf)): Real numbers,
  axiomatized as a real closed field. All assumptions are in
  [`RealAxioms.pf`](../lib/RealAxioms.pf). Write
  `real(n)` for an integer and `real(q)` for a rational, e.g.
  `real(frac(+1, 2))`; concrete arithmetic on these is computed
  automatically. `x ^ k` is the power with a `UInt` exponent `k`. `python deduce.py --postulates file.pf` lists the
  axioms a file depends on.
- ([`Ring.thm`](../lib/Ring.thm), [`Ring.pf`](../lib/Ring.pf)): Ring
  normalization for the [`algebra`](./Reference.md#algebra-proof)
  tactic: it proves an equation whose sides are equal as polynomials
  over any type that models `CommSemiring`, such as
  `(x + y) * (x + y) = x * x + real(+2) * x * y + y * y`, and, over
  any type that models `Field`, whose sides are equal as fractions when
  the denominators are nonzero, such as `x / y * y = x`.
- ([`Set.thm`](../lib/Set.thm), [`Set.pf`](../lib/Set.pf)): Sets
- ([`Triangle.thm`](../lib/Triangle.thm), [`Triangle.pf`](../lib/Triangle.pf)):
  Triangles and congruence, for coordinate geometry.
  `triangle(A, B, C)` says that A, B, C are not collinear, and
  `tri_congruent(A, B, C, D, E, F)` that triangles ABC and DEF are
  congruent with A ↔ D, B ↔ E, C ↔ F: their corresponding sides and
  angles (∠CAB, ∠ABC, ∠BCA) are congruent, so CPCTC (`tri_cpctc`)
  unfolds the definition. Theorems include SAS, SSS, ASA, AAS, and HL
  (`tri_sas`, `tri_sss`, `tri_asa`, `tri_aas`, `tri_hl`), the
  Isosceles Triangle Theorem and its converse (`tri_isosceles`,
  `tri_isosceles_converse`), the Triangle Angle Sum Theorem
  (`tri_angle_sum`), the Exterior Angle Theorem
  (`tri_exterior_angle`), the Triangle Inequality (`tri_inequality`,
  `tri_inequality_strict`), and the Alternate Interior Angles Theorem
  and its converse (`line_parallel_alt_interior`). They are proved
  from coordinates, with no new postulates.
- ([`UInt.thm`](../lib/UInt.thm), [`UInt.pf`](../lib/UInt.pf)): Unsigned integers
- ([`WellFounded.thm`](../lib/WellFounded.thm), [`WellFounded.pf`](../lib/WellFounded.pf)):
  The concept `WellFounded` of well-founded orders, whose `<` admits
  strong induction. A [`recfun`](./Reference.md#recfun-statement)'s
  measure decreases along the `<` of a model of it; `Nat` and `UInt`
  have models.
