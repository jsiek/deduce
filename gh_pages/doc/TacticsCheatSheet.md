# Tactics Cheat Sheet

A dense reference for the proof-language constructs in Deduce — every tactic with a one-line meaning, plus the syntactic pitfalls that catch beginners.

This page complements two other documents:

- The [Cheat Sheet](./CheatSheet.md) — strategy advice keyed by the *shape of the goal* ("if my goal is `P and Q`, what do I do?").
- The [Reference Manual](./Reference.md) — the full alphabetical entry for each construct.

If a name on this page is unfamiliar, follow the link in the Reference column for the long-form description.

## Top-level statement forms

| Form | Meaning |
| --- | --- |
| `theorem name: P proof ... end` | A named proof of `P`. **Visible across module boundaries.** |
| `lemma name: P proof ... end` | A named proof of `P`. **Module-private** — references from another module fail with "undefined proof variable". |
| `postulate name: P` | Assume `P` without proof. |
| `auto name` | Register an equation `name : LHS = RHS` as an automatic rewrite. Subsequent goals are simplified silently using it. |
| `associative operator* in T` | Register `*` as associative for `T`; `replace` and `evaluate` will renormalize accordingly. |
| `view V { source S target T into f out g roundtrip thm }` | Declare a checked pattern-matching view. `thm` must prove `f(g(v)) = v` for all viewed values. |
| `recursive f(V, A) -> R { f(C(args), y) = ... }` | If `V` is a view, define a terminating recursive function by matching on `V`'s target constructors. |

## Proof structure

| Form | Effect on the goal |
| --- | --- |
| `arbitrary x:T, y:T` | Introduce universal variables: `∀x:T,y:T. P` becomes `P`. |
| `assume name: P`&nbsp;/&nbsp;`suppose name: P` | Discharge an antecedent: `if P then Q` becomes `Q`, with `name : P` in scope. The two keywords are synonyms. |
| `have name: P by proof` | Add `name : P` to scope without changing the goal. |
| `show P` | Restate the current goal verbatim (must already match — useful for documenting where you are). |
| `suffices Q by reason` | Replace the goal with `Q`, where `reason` is a proof of `Q → original_goal`. Often `Q` is the goal *after* a `replace` or `expand` you want to make explicit. |
| `conclude P by proof` | Discharge the goal `P` with `proof`. Like `have` but the formula must equal the current goal. |

## Equality tactics

| Form | Effect |
| --- | --- |
| `.` (period) | Close the goal trivially: definitional equality, reflexivity, or `true`. |
| `evaluate` | Reduce both sides of the goal to normal form. |
| `expand f \| g` | Unfold the definitions of `f` and `g` in the goal. |
| `replace eq` | Rewrite the **goal** left-to-right using `eq : LHS = RHS`. |
| `replace eq in p` | Rewrite within proof `p`'s formula and return a new proof of the rewritten formula. |
| `replace eq1 \| eq2 \| ...` | Apply rewrites in sequence. |
| `simplify with h` | Like `replace`, but accepts non-equation hypotheses: `h : not P` substitutes `P` with `false` in the goal; `h : P` (bare boolean) substitutes `P` with `true`. Use in the `case false` arm of a boolean `switch`, where `replace` rejects the `not P` hypothesis. |
| `symmetric p` | If `p : a = b`, returns a proof of `b = a`. |
| `transitive p1 p2` | `p1 : a = b` together with `p2 : b = c` gives a proof of `a = c`. |
| `equations a = b by r1   ... = c by r2   ... = d by r3` | Equational chain — a readable form of nested `transitive`. |

## Applying lemmas

| Form | Meaning |
| --- | --- |
| `lemma<T1, T2>` | Instantiate the leading type `∀` variables (when the leading `∀` binds types). |
| `lemma[t1, t2]` | Instantiate the leading term `∀` variables. Produces a proof term. |
| `lemma<T>[t1, t2]` | Combined: instantiate type variables, then term variables. |
| `apply lemma to p` | Modus ponens: given `lemma : if P then Q` and `p : P`, returns a proof of `Q`. |
| `apply lemma to p1, p2` | Same, when the antecedent is `P1 and P2` — the comma builds the conjunction. |
| `apply lemma[t] to p` | Combined instantiation and modus ponens. |
| `recall P` | Refer to an in-scope hypothesis by its formula `P` instead of by label. |

## Case analysis and quantifier elimination

| Form | Use |
| --- | --- |
| `switch x { case ctor(args) { ... } ... }` | Pattern-match on a value of a union type. |
| `switch x { case ctor(args) assume eq { ... } }` | Same, with `eq : x = ctor(args)` available in the branch. |
| `cases p case name: Pi { ... } ...` | Disjunction elimination on `p : P1 or P2 or ...`. |
| `induction T case ctor(args) assume IH { ... }` | Structural induction over the union type `T`. |
| `obtain x where eq: P from p` | Existential elimination: `p : ∃x. P` introduces a fresh `x` together with `eq : P`. |

## Connective introductions

| Goal shape | How to prove |
| --- | --- |
| `P and Q` | Comma: `(proof_of_P, proof_of_Q)`. |
| `P or Q` | Provide a proof of `P` (or of `Q`); the coercion is implicit. `conclude A or B by proof_of_A` works. |
| `if P then Q` | `assume name: P` then prove `Q`. |
| `not P` | `assume name: P` then prove `false`. |
| `false` | `contradict p, np` where `p : P` and `np : not P`. |
| `∀x:T. P` | `arbitrary x:T` then prove `P`. |
| `∃x:T. P` | `choose t` (or `choose t1, t2` for nested existentials) then prove `P[x:=t]`. |

## Destructuring conjunctions

| Form | Meaning |
| --- | --- |
| `conjunct 0 of p` | First conjunct of `p : A and B and C ...` (zero-indexed). |
| `conjunct 1 of p` | Second, etc. |

Use these when `apply lemma to p` doesn't typecheck because `p` is a wider conjunction than the lemma's antecedent expects.

## Common pitfalls

1. **`auto` rules silently change the goal.** A "could not find any matches in `true`" error usually means an auto rule from the prelude (or earlier in the file) has already collapsed the goal. Either drop the now-redundant rewrite or use `suffices` to land on a goal the auto rule won't touch.

2. **`lemma` is private.** A `lemma` in another module is not in scope here, even though it is in `lib/`. Promote it to `theorem` or move the call site into the same module.

3. **`replace` only rewrites left-to-right.** To rewrite `RHS → LHS`, use `replace symmetric eq` — or restate the goal so the equation matches its natural direction.

4. **`replace eq` vs `replace eq in p`.** Without `in`, the rewrite applies to the *goal*. With `in p`, it applies inside the formula carried by proof term `p` and produces a new proof term.

5. **`ℕ0`, `lit(zero)`, and `zero` are not always interchangeable.** They denote the same value but are not always *structurally identical*, and `apply` unifies structurally. When a Nat-level lemma fails to apply, check which form the lemma was stated in and bridge with a local `have ... by evaluate`. (Example: `mult_to_zero` is stated with `zero`, `pos_mult_both_sides_of_less` with `ℕ0`.)

6. **Building vs. destructuring conjunctions.** `apply X to A, B` *constructs* the conjunction `A and B` from two separate proofs — no parentheses needed. To go the other way (decompose a hypothesis already of shape `A and B`), use `conjunct 0/1 of`.

7. **Numeric literals don't always reduce eagerly.** `0:UInt` parses as `fromNat(lit(zero))`, so `toNat(0:UInt)` is not definitionally `ℕ0` — it requires `evaluate` or `expand` to bridge. A common pattern: stash `have toNat_zero: toNat((0:UInt)) = ℕ0 by evaluate` near the top of the proof.

8. **Views need their law before use.** A `view` declaration checks the supplied `roundtrip` theorem exactly. For a target type `T`, prove `all v:T. into(out(v)) = v` before the `view` declaration; for generic views, quantify type parameters first.

9. **`switch P` on a boolean introduces asymmetric assumptions.** `case true assume h { ... }` makes `h : P` available; `case false assume h { ... }` makes `h : not P` available. `simplify with h` works in both branches (it substitutes `P` with `true` or `false` and reduces). If `P` is itself an equation `a = b`, you may also use `replace h` in the `case true` branch; for any other boolean (a predicate call, `≤`, etc.), `replace h` fails with "expected an equation" and you should use `simplify with h`. Also: the introduced formula is `P` (resp. `not P`), not `P = true` (resp. `P = false`) — annotating `assume h: P = true` will fail to match the expected assumption.

## Working tips

- **Read the failure message carefully.** It prints the *current* goal at the point of failure — which may have been transformed by `auto` rules or `suffices` and so differ from what you literally wrote.
- **When stuck on syntax, search the standard library.** `grep` for the lemma you want to invoke, or for a similar tactic, in `lib/*.pf` and copy the working pattern.
- **`?` as a proof** prints the current goal and a suggested next step. A cheap way to inspect the proof state mid-construction.
- **`help L`** on a hypothesis label `L` prints what it can be used for.
- **Both parsers must agree.** When changing parsing or AST, run with both `--recursive-descent` (default) and `--lalr`.
