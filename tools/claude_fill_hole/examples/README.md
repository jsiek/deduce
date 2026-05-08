# Hole-fill examples

Six progressively-harder Deduce theorems for benchmarking LLM
backends through `deduce-fill-hole`.  Each file is a self-contained
proof with one `?` for the model to fill.  Run each level, note
whether the model succeeds and how many attempts it took, and
compare across models.

## How to run

In emacs, with `deduce-fill-hole` configured:

1. `M-x find-file RET tools/claude_fill_hole/examples/01_trivial.pf RET`
2. Move point onto the `?`.
3. `C-c C-a` (`deduce-fill-hole`).
4. Watch for `deduce-fill-hole: filled in N attempt(s)` (success) or
   the failure message + `*deduce-fill-hole debug*` buffer.

Repeat for `02_reflexive.pf` through `06_induction.pf`.

The CLI shape, if you want to drive the sidecar without emacs, is in
`../README.md`.

## Levels

| # | File | Theorem | What it tests | Reference proof |
|---|------|---------|---------------|-----------------|
| 1 | [`01_trivial.pf`](01_trivial.pf) | `true` | "I can write `.`" | `.` |
| 2 | [`02_reflexive.pf`](02_reflexive.pf) | `all P:bool. P = P` (after `arbitrary P`) | Reflexive equality. | `reflexive` (or `.`) |
| 3 | [`03_assumption.pf`](03_assumption.pf) | `all P:bool. if P then P` (after `assume p: P`) | Reading the goal and finding the matching binding in scope. | `p` |
| 4 | [`04_conj_swap.pf`](04_conj_swap.pf) | `if P and Q then Q and P` | Destructure a conjunction (`conjunct N of pq`, zero-indexed) and reconstruct the swapped pair. | `have q: Q by conjunct 1 of pq` then `have p: P by conjunct 0 of pq` then `q, p` |
| 5 | [`05_disj_swap.pf`](05_disj_swap.pf) | `if P or Q then Q or P` | Case-split a disjunction with `cases pq case n: T { ... }` and inject each branch into the swapped goal. | `cases pq` `case p: P { p }` `case q: Q { q }` |
| 6 | [`06_induction.pf`](06_induction.pf) | `all n:UnaryNat. add(n, zero) = n` for a self-defined `UnaryNat` and recursive `add` | Structural `induction T case ctor(args) suppose IH: ... { ... }` and using the IH via `replace IH`. | `induction UnaryNat`, base case `expand add.`, succ case `equations add(succ(n'), zero) = succ(add(n', zero)) by expand add. ... = succ(n') by replace IH.` |

## Difficulty progression

What each level adds over the previous:

- **1 → 2**: introduce a quantifier and the `arbitrary` step (already in
  the file; the model just has to discharge the residual `P = P`).
- **2 → 3**: introduce a hypothesis the model has to read off the
  givens list.
- **3 → 4**: introduce a connective the model has to destructure
  (`conjunct N of`) and reconstruct (`,` for `and`).
- **4 → 5**: switch from a single-proof tactic to a multi-branch
  case split.  Each branch is now its own subgoal.
- **5 → 6**: introduce structural induction over a user-defined type.
  Adds the `induction`, `suppose IH`, `expand`, `replace`, and
  `equations` tactics in one step -- a real jump in tactic
  vocabulary.

## Cleaning up after a model run

`C-c C-a` mutates the buffer.  After running a level, **don't save
the changed buffer** -- to retest, `M-x revert-buffer RET yes RET`
restores the `?`.

If you want to keep a model's answer for comparison, copy the
filled-in proof out of the buffer (or save under a different name)
before reverting.

## Adding more levels

The natural next steps would be:

- **Level 7**: a theorem requiring a hypothesis transformation along
  the way -- e.g. `if (P or Q) and R then (P and R) or (Q and R)`.
- **Level 8**: induction over a type with more than one recursive
  parameter, e.g. binary trees.
- **Level 9**: a proof that needs a `have` lemma stated and discharged
  mid-proof.
- **Level 10**: a proof requiring stdlib lemmas (drop `--no-stdlib`,
  prove something about `Nat` or `List`).

If you add levels, mirror the structure above: each `.pf` is
self-contained, has exactly one `?`, has a reference proof in this
README, and progresses one tactic-vocabulary step from the
previous level.
