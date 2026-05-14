# UInt view-based structural recursion plan

## Background

`UInt` is implemented with private binary constructors, but the public
library presents users with the familiar zero/successor view:

```deduce
theorem uint_induction: all P:fn UInt -> bool.
  if P(0) and (all m:UInt. if P(m) then P(1 + m))
  then all n : UInt. P(n)
```

Today, proofs can use that view directly with `induction UInt`:

```deduce
induction UInt
case 0 { ... }
case with n. 1 + n assume IH { ... }
```

Recursive functions over `UInt` are still written with general recursion
and an explicit measure, usually counting down from `n` to `n ∸ 1` and
using `uint_monus_one_less` as the termination fact.

## Goal

Add a structural-recursion surface for `UInt` that lets beginners define
functions over the same public view used by `uint_induction`, without
mentioning `Nat`, `fromNat`, `toNat`, or the private binary constructors.

For example, a future surface could allow a definition shaped like:

```deduce
viewrec replicate<T>(n : UInt, x : T) -> List<T>
case 0 {
  []
}
case with n'. 1 + n' {
  node(x, replicate(n', x))
}
```

The exact keyword and clause syntax are open design choices. The important
property is that the recursive call is visibly on the predecessor exposed
by the `1 + n'` view.

## Desugaring direction

A first implementation can share the existing custom-induction machinery:

- Use a view theorem with the same zero/successor cases as `uint_induction`.
- Check that each view-recursive clause matches one public view case.
- Desugar the successor clause to a `recfun` with `measure n of UInt`.
- Generate or require the existing termination proof obligation
  `n ∸ 1 < n`, discharged by `uint_monus_one_less` under `not (n = 0)`.

This keeps the runtime representation private and avoids changing `UInt`
constructors. It also gives diagnostics a single source of truth: a bad
case pattern can be explained by showing the expected public view case.

## Acceptance sketch

- `UInt` view recursion accepts base and successor clauses using `0` and
  `with n. 1 + n`.
- Recursive calls in the successor clause are accepted only on the exposed
  predecessor, or on expressions justified by a generated measure proof.
- Error messages name the expected public view cases rather than
  `bzero`, `dub_inc`, or `inc_dub`.
- Existing `recfun ... measure ...` programs continue to work unchanged.
- Existing `induction UInt` behavior remains compatible with the
  zero/successor cases documented in the Reference.
