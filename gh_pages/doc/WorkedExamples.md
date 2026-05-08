# Worked Examples

Concrete short proofs demonstrating each construct in [TacticsCheatSheet.md](./TacticsCheatSheet.md) and [CheatSheet.md](./CheatSheet.md). Each example is self-contained and checks under `deduce.py --no-stdlib` (no prelude required).

If you want to look up "given a goal of shape X, what tactic do I use?" you can search by the heading of the section below, since they're organised by goal shape (matching CheatSheet's lookup table) and then by non-shape-keyed tactics.

---

## Goal: `true`

The trivial proof `.` discharges `true`, reflexive equalities, and any goal that auto-rules have already collapsed to `true`.

```
theorem ex_true: true
proof
  .
end
```

---

## Goal: `false` (via contradiction)

You don't usually prove `false` directly — you derive it from a contradictory pair of hypotheses.

```
theorem ex_false: all P:bool. if P and not P then false
proof
  arbitrary P:bool
  assume both: P and not P
  contradict (conjunct 0 of both), (conjunct 1 of both)
end
```

A hypothesis `H: false` implicitly proves any goal:

```
theorem ex_false_anything: all P:bool. if false then P
proof
  arbitrary P:bool
  assume f: false
  conclude P by f
end
```

---

## Goal: `P and Q` (intro via comma; destructure with `conjunct N of`)

To **prove** `P and Q`, give a comma-separated pair of proofs.

```
theorem ex_and_intro: all P:bool, Q:bool. if P then if Q then P and Q
proof
  arbitrary P:bool, Q:bool
  assume p: P
  assume q: Q
  p, q
end
```

To **use** a hypothesis `pq: P and Q`, destructure it. `conjunct N of pq` is **zero-indexed** — `conjunct 0 of pq : P`, `conjunct 1 of pq : Q`. The comma binds tighter than `conjunct ... of`, so an inline `(conjunct 1 of pq, conjunct 0 of pq)` parses wrong. Use `have ... by` to name the pieces:

```
theorem ex_and_swap: all P:bool, Q:bool. if P and Q then Q and P
proof
  arbitrary P:bool, Q:bool
  assume pq: P and Q
  have q: Q by conjunct 1 of pq
  have p: P by conjunct 0 of pq
  q, p
end
```

---

## Goal: `P or Q` (intro: provide one side; elim: `cases`)

To **prove** `P or Q`, give a proof of either side directly. There is no `or_left`/`or_right`/`inl`/`inr` constructor.

```
theorem ex_or_intro: all P:bool, Q:bool. if P then P or Q
proof
  arbitrary P:bool, Q:bool
  assume p: P
  conclude P or Q by p
end
```

To **use** a hypothesis `pq: P or Q`, case-split with `cases`. Each case's body must prove the goal under that branch's hypothesis.

```
theorem ex_or_swap: all P:bool, Q:bool. if P or Q then Q or P
proof
  arbitrary P:bool, Q:bool
  assume pq: P or Q
  cases pq
  case h_p: P { conclude Q or P by h_p }
  case h_q: Q { conclude Q or P by h_q }
end
```

---

## Goal: `if P then Q` (intro: `assume`/`suppose`; elim: `apply ... to`)

To **prove** `if P then Q`, introduce the antecedent and prove the consequent. `assume` and `suppose` are synonyms.

```
theorem ex_impl_intro: all P:bool. if P then P
proof
  arbitrary P:bool
  assume p: P
  p
end
```

To **use** a hypothesis `H: if P then Q` together with `p: P`, write `apply H to p` (modus ponens). When the antecedent is itself a conjunction `if P1 and P2 then Q`, write `apply H to p1, p2` — the comma constructs the conjunction; no parentheses needed.

```
theorem ex_apply_to: all P:bool, Q:bool, R:bool.
  if (if P then Q) and (if Q then R) then if P then R
proof
  arbitrary P:bool, Q:bool, R:bool
  assume both: (if P then Q) and (if Q then R)
  assume p: P
  have pq: if P then Q  by conjunct 0 of both
  have qr: if Q then R  by conjunct 1 of both
  have q: Q  by apply pq to p
  apply qr to q
end
```

---

## Goal: `not P`

`not P` is sugar for `if P then false`. Prove it the same way.

```
theorem ex_not_intro: all P:bool. if P then not (not P)
proof
  arbitrary P:bool
  assume p: P
  assume np: not P
  contradict p, np
end
```

To **use** `H: not P` together with `p: P`, write `contradict p, H` — that proves `false` (and so any goal).

---

## Goal: `all x:T. P(x)` (intro: `arbitrary` or `induction`; elim: brackets)

For a non-recursive use of the universal, `arbitrary x:T` introduces `x` and the goal becomes `P(x)`:

```
theorem ex_forall_arbitrary: all x:bool. x = x
proof
  arbitrary x:bool
  reflexive
end
```

When `x` appears as the recursion target of a function in the goal, use **induction** instead — see the [Induction over a union type](#induction-over-a-union-type) section below.

To **instantiate** a universal lemma `H: all x:T. P(x)`, write `H[t]` (a proof of `P(t)`). Multiple variables: `H[t1, t2]`.

```
theorem ex_forall_elim:
  if (all x:bool. x = x) then true = true
proof
  assume H: all x:bool. x = x
  H[true]
end
```

---

## Goal: `some x:T. P(x)` (intro: `choose`; elim: `obtain`)

To **prove** `some x:T. P(x)`, pick a witness with `choose t` and prove `P[x:=t]`.

```
theorem ex_exists_intro: some x:bool. x = true
proof
  choose true
  reflexive
end
```

To **use** a hypothesis `H: some x:T. P(x)`, write `obtain x where eq: P from H` — this introduces a fresh `x` and a proof `eq` of `P(x)` into scope.

```
theorem ex_exists_elim:
  if (some x:bool. x = true) then some y:bool. y = true
proof
  assume H: some x:bool. x = true
  obtain x where eq: x = true from H
  choose x
  conclude x = true by eq
end
```

---

## Goal: `e1 = e2` (reflexivity, equations chains, replace)

When the two sides are identical (or reduce to the same normal form), `.` or `reflexive` suffices.

```
theorem ex_eq_refl: all x:bool. x = x
proof
  arbitrary x:bool
  reflexive
end
```

For a non-trivial chain, use `equations`. Each step is justified by a proof of the previous-step-to-this-step equality. `expand fn` unfolds a function's definition by one step.

```
union UN {
  z
  s(UN)
}

recursive plus(UN, UN) -> UN {
  plus(z, m) = m
  plus(s(n), m) = s(plus(n, m))
}

theorem ex_eq_equations: all m:UN. plus(s(z), m) = s(m)
proof
  arbitrary m:UN
  equations
    plus(s(z), m) = s(plus(z, m))   by expand plus.
              ... = s(m)             by expand plus.
end
```

To rewrite the goal using an equality `eq: a = b`, use `replace eq` (rewrites left-to-right, `a → b`). For right-to-left, use `replace symmetric eq`. To rewrite *inside* a proof term, use `replace eq in p` — produces a new proof with the rewritten formula.

`symmetric` and `transitive` build new proofs from existing equalities:

```
theorem ex_eq_symmetric: all P:bool, Q:bool. if P = Q then Q = P
proof
  arbitrary P:bool, Q:bool
  assume eq: P = Q
  symmetric eq
end

theorem ex_eq_transitive:
  all P:bool, Q:bool, R:bool.
  if P = Q and Q = R then P = R
proof
  arbitrary P:bool, Q:bool, R:bool
  assume both: P = Q and Q = R
  have pq: P = Q by conjunct 0 of both
  have qr: Q = R by conjunct 1 of both
  transitive pq qr
end
```

---

## Induction over a union type

Use `induction T` (note: pass the **type** name, not the variable) to do structural induction. Recursive constructors get an induction hypothesis bound by `suppose IH:`. Non-recursive constructors (the base cases) have **no IH** — don't write `suppose IH` on them.

```
union UnaryNat {
  zero
  succ(UnaryNat)
}

recursive add(UnaryNat, UnaryNat) -> UnaryNat {
  add(zero, m) = m
  add(succ(n), m) = succ(add(n, m))
}

theorem ex_induction: all n:UnaryNat. add(n, zero) = n
proof
  induction UnaryNat
  case zero {
    expand add.
  }
  case succ(n') suppose IH: add(n', zero) = n' {
    equations
      add(succ(n'), zero) = succ(add(n', zero))   by expand add.
                      ... = succ(n')               by replace IH.
  }
end
```

Three Deduce-specific tactics from this example:

- `expand <fn>` unfolds the named function's definition by one step on every occurrence in the goal. Append a trailing `.` to discharge the goal if the resulting equation is trivially true.
- `replace IH` rewrites the goal left-to-right using `IH`'s equation.
- `equations LHS = step1 by reason1 ... = end by reasonN` is the readable form of nested `transitive`. Each `... = next` continues the chain.

---

## Using `query_goal` to plan a multi-step proof

For multi-step proofs (especially induction), don't try to write the whole thing in one shot. Build a skeleton with `?` placeholders inside each branch, call `query_goal` to see the goal + givens at each `?`, then fill them in one at a time.

For example, to prove `add(n, zero) = n` by induction:

**Step 1 — write the skeleton.** Each case body is just `?`:

```
induction UnaryNat
case zero { ? }
case succ(n') suppose IH: add(n', zero) = n' { ? }
```

**Step 2 — call `query_goal` on that skeleton.** It splices the partial proof at the hole, finds the first `?` in the result, and returns its goal + givens. For the `case zero` `?`, you'd see:

```
{"goal": "add(zero, zero) = zero", "givens": []}
```

That's discharged by `expand add.`. Update the skeleton:

```
induction UnaryNat
case zero { expand add. }
case succ(n') suppose IH: add(n', zero) = n' { ? }
```

**Step 3 — `query_goal` again.** Now the first remaining `?` is in the `succ` branch:

```
{"goal": "add(succ(n'), zero) = succ(n')",
 "givens": [{"label": "IH", "formula": "add(n', zero) = n'"}]}
```

That's a one-step `equations` chain using `expand add.` then `replace IH.`. Fill it in.

**Step 4 — `validate_proof` the complete proof.** When there are no more `?` markers in the body, hand the whole thing to `validate_proof`.

`query_goal` does not count toward your `validate_proof` budget — call it freely as you refine. The first `?` in the spliced text is what gets reported, so you don't need to remove earlier branches' `?` markers as you fill them; just leave the skeleton structure intact and `query_goal` will walk through them in order on subsequent calls.

---

## `switch` on a term (vs `cases` on a hypothesis)

Use `switch x` to case-split on a value of a union type. `cases p` is for splitting a *hypothesis* of disjunction shape; `switch` is for splitting on an inductive *value*.

```
theorem ex_switch: all b:bool. b or not b
proof
  arbitrary b:bool
  switch b {
    case true { conclude true or not true by . }
    case false {
      have nf: not false by assume f: false  f
      nf
    }
  }
end
```

When you need to remember the equation between the scrutinee and the case's pattern, use `switch x { case ctor(args) assume eq { ... } }` — `eq : x = ctor(args)` is in scope inside the branch.

---

## `have` for forward reasoning

`have name: P by proof` introduces a named fact into scope without changing the goal. Useful for splitting work or naming intermediate results.

```
theorem ex_have: all P:bool, Q:bool. if P and Q then P
proof
  arbitrary P:bool, Q:bool
  assume pq: P and Q
  have p: P by conjunct 0 of pq
  p
end
```

---

## `suffices` for backward reasoning

`suffices Q by reason` replaces the current goal with `Q`, where `reason` proves `Q → originalGoal`. Often `Q` is the goal *after* a rewrite you want to make explicit.

```
theorem ex_suffices: all P:bool. if P then (P and true)
proof
  arbitrary P:bool
  assume p: P
  suffices P by .
  p
end
```

In the above, `(P and true)` reduces to `P`, so `suffices P by .` re-states the goal in the simpler form.

---

## `apply lemma[t] to p` (combined instantiation + modus ponens)

When using a universally-quantified implication, you can instantiate and apply in one step:

```
theorem ex_apply_inst:
  if (all x:bool. if x = true then x or false) then true or false
proof
  assume H: all x:bool. if x = true then x or false
  have eq: true = true by reflexive
  apply H[true] to eq
end
```

`H[true]` instantiates the `all`, giving `if true = true then true or false`. `apply ... to eq` discharges the antecedent.

---

## Predicates and rule induction

The `predicate` keyword (synonym: `relation`) declares an inductively-defined set. Each rule's name doubles as a proof-term: `ev0` is a proof of `even(zero)`; `ev_ss[n]` (instantiated) is a proof of `if even(n) then even(succ(succ(n)))`.

`rule induction P` proves a goal of the form `all x1, ..., xn. if P(x1, ..., xn) then Q(x1, ..., xn)` by induction on `P`'s derivation. Note: the induction sits *before* any `arbitrary`/`assume` — the goal must include the outer `all` and `if P(...)` premise.

```
union N { z  succ(N) }

predicate even : fn N -> bool {
  ev0   : even(z)
  ev_ss : all n:N. if even(n) then even(succ(succ(n)))
}

theorem ex_rule_induction: all n:N. if even(n) then even(n)
proof
  rule induction even
  case ev0 { ev0 }
  case ev_ss {
    arbitrary k:N
    assume hyp: even(k) and even(k)
    apply ev_ss[k] to (conjunct 0 of hyp)
  }
end
```

In the `ev_ss` case, the assumed hypothesis is `even(k) and even(k)` — the rule's recursive premise paired with the motive's induction hypothesis (the motive here is `even` itself, since the goal is `if even(n) then even(n)`).

`rule inversion` has the same shape as `rule induction` but does NOT pair recursive premises with an induction hypothesis. Use it when you need to invert a derivation without the recursive case carrying its own conclusion as IH.
