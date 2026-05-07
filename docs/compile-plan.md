# Compile-to-C plan

Tracking issue: [#291](https://github.com/jsiek/deduce/issues/291).

**Status:** Phases 1–3 landed (TCO deferred); see the per-step ticks below. The compiler is correct on the executable fragment — `make tests-compile` runs 35 fixtures end-to-end, including the entire prelude path. Phase 4 (peano-`Nat` performance) and Phase 5 (separate compilation, second backend) are still ahead.

## Goal

Compile the executable fragment of a checked Deduce program to a self-contained C program that, when run, produces the same `print` output as `python deduce.py file.pf` does today. (Asserts are not part of the runtime contract — see the [Surface](#surface-to-compile) table.)

C is the first target because it's the lowest common denominator: anything that can host a C compiler and ~200 lines of runtime can run compiled Deduce. Once C works the same lowering retargets to Rust, JavaScript, OCaml, or LLVM IR by swapping the final emit pass.

Non-goals (for v1):
- Proofs at runtime. Theorems, postulates, predicates, `auto`, `inductive`, `associative`, `trace` all erase to nothing.
- Performance parity with hand-written C. Faithful peano `Nat` is exponential; the plan addresses this in [Phase 4](#phase-4--performance-make-it-not-embarrassing), not before.
- Separate compilation. v1 produces one `.c` per top-level `.pf`, with the prelude inlined. Linking multiple modules is Phase 5.
- Foreign function interface. No `extern` declarations, no calling C from Deduce.

## Surface to compile

The executable fragment is what `Print` evaluates against. Concretely:

| AST node | Treatment |
| --- | --- |
| `Union`, `Constructor` | Tagged-union ADT (`{ tag, payload }`) on the heap. |
| `Define` | Top-level binding. If body is `Lambda`/`Generic`-of-`Lambda`, lower to a top-level function; otherwise to a global initialised at startup. |
| `RecFun` | Top-level recursive function. Each `FunCase` is a clause of a switch over the matched constructor. |
| `GenRecFun` | Top-level recursive function. The `terminates` proof is **erased** — termination is the user's problem at runtime. |
| `Lambda` | Closure: function pointer + captured-environment record. |
| `Generic` | Type-erased; the `Generic` wrapper disappears, body lowered as-is. |
| `Call` | Either an ADT constructor application or a function/closure call. Disambiguated by the rator's resolved type (already known after type-check). |
| `Switch`, `SwitchCase`, `PatternCons`, `PatternBool` | C `switch` on the tag plus binders for constructor parameters. |
| `Conditional`, `TLet`, `Var`, `Bool`, `Int` | Trivial. |
| `MakeArray`, `ArrayGet` | Walk the `List<T>` once to fill a heap-allocated `T[]`; index check on `ArrayGet`. |
| `TermInst`, `TAnnote`, `Mark` | Erased. |
| `Print` | `deduce_println` runtime helper that dispatches on tag and walks ctor fields recursively. |
| `Assert` | **Erased.** The interpreter runs `assert` inside `check_proofs` — by the time `compile_file` gets past `check_file`, every assert has already been validated. Re-checking at the binary's startup would be wasted work and would force prelude sanity-check asserts to drag in their dependencies. |
| `Hole`, `Omitted`, `PHole`, `Sorry` | Should not appear in a checked program; emitter aborts if it sees one. |
| `All`, `Some` | **Erased to a runtime panic stub** (`ir.Panic`). They appear in `fun`/`define` bodies in the prelude (e.g. `fun EvenNat(n) { some m. … }`) but are not computational. Pruning drops the stub if no `print`-reachable path actually evaluates it; otherwise the binary aborts with a source-located message. |
| `Theorem`, `Postulate`, `Predicate`, `Auto`, `Inductive`, `Associative`, `Trace`, `Module`, `Export`, `Import` | Erased (imports inlined upstream). |

Anything else lowers to an `ir.Panic` stub with the originating term name in the message — the same robustness story as `Some`/`All`. The pruner removes it if it isn't reached.

## Architecture

Three layers, mirroring `docs/lsp-plan.md`'s reuse boundary:

```
   C backend     JS backend     LLVM backend     ← emitter (target-specific)
       \             |                /
        +------ IR (functional core, closure-converted, type-erased) ------+
                                  |
                  Lowering pass: Deduce AST → IR
                                  |
                 Existing pipeline (parse / uniquify / type-check)
```

The IR is the reuse boundary. It is a small functional core — `Var`, `Bool`, `Int`, `Lam` (top-level only after closure conversion), `MkClosure`, `App`, `Let`, `If`, `Con`, `Match`, `Eq`, `Panic`, `MakeArray`, `ArrayGet` — with no proof or type-system constructs. Backends consume IR; they never import `abstract_syntax`.

The pipeline runs lower → closure-convert → prune → emit. Pruning (added during Phase 2) is the load-bearing piece for prelude inlining: it walks reachability from each `print` and drops everything else, so a small program doesn't pay for the rest of the stdlib.

All new code lives under `compiler/`. The only edits outside it are: (a) a `--compile` / `--no-prune` flag set and `compile_file` entry point in `deduce.py`; (b) the post-typecheck AST surfacing on `lsp.library.CheckResult.ast` (issue #305 / PR #307), which the compiler consumes.

## Runtime

A small C runtime in `compiler/runtime/` provides:

- `deduce_value` — opaque pointer to `struct deduce_obj { tag, payload-union }` on the heap. Tag values: `D_BOOL`, `D_INT`, `D_CTOR`, `D_CLOSURE`, `D_ARRAY`. (No NaN-boxing or pointer tagging — boxed everywhere; compactness work is Phase 4.)
- Allocation: plain `malloc` (via `deduce_alloc`) with no `free`. **No GC**: the original plan called for Boehm GC; in practice the test programs are small and short-lived enough that leaking is fine. Boehm or RC remains a Phase 4 option.
- `deduce_make_bool` returns one of two interned static `struct deduce_obj` instances — bool literals never allocate. Per-program nullary constructors (`zero`, `empty`, `bzero`, …) are unboxed by emit_c into `C_<mangled>` singletons allocated once at startup; `Con(c, [])` references the singleton. (Step 13.)
- `deduce_print` — generic pretty-printer that dispatches on tag and walks ctor fields. (Per-union printers in the original plan turned out unnecessary — names live on the value itself.)
- `deduce_panic`, `deduce_unreachable_value` — `__attribute__((noreturn))` failure paths. Runtime helpers that may panic (`deduce_make_array_from_list`, `deduce_array_get`) take a `const char* loc` and prepend it to their messages so the user sees the original `.pf:line`. (Step 14.)
- `DEDUCE_TRACE_ALLOC=1` env-var mode prints `deduce: N allocations` at exit.

The runtime header (`deduce.h`) is committed; `deduce.c` is committed; nothing is generated at compile time except the user program. The runtime compiles cleanly with `-Werror -Wall -Wextra`.

`make tests-compile` runs every fixture in `test/compile/lower/`, `test/compile/prelude/`, and the prelude-aware allowlist `test/compile-allowlist.txt`. For each fixture it compiles, links against the runtime, runs the binary, and diffs stdout against the interpreter's. CI integration is a remaining task — `make tests-compile` is local-only today.

## Phase 1 — minimum viable backend

Goal: `python3 deduce.py --compile examples/hello.pf -o hello.c && cc -I compiler/runtime hello.c compiler/runtime/deduce.c && ./a.out` works for one hand-written file using `bool`, `Nat`, `+`, and `print`.

**Status:** done. PR [#302](https://github.com/jsiek/deduce/pull/302).

- [x] **Step 1: Decide and document the IR.** Single file, `compiler/ir.py`, dataclasses only, ~150 lines. Match against it with `match`/`case`. Lock the shape before writing any lowering — the IR is the reuse point and churn here costs every backend.
  - *Acceptance:* docstring on each node + a hand-written round-trip pretty-printer for debugging. No tests yet; the next step exercises it.

- [x] **Step 2: Lower a Deduce subset to IR.** New module `compiler/lower.py`. Handle: `Bool`, `Int`, `Var`, `Call` (function application only — no constructors yet), `Conditional`, `TLet`, `Lambda`, `Generic`, `Define`, `Print`, `Assert`. Reject everything else with a clear error.
  - *Acceptance:* hand-written fixture in `test/compile/lower/` with expected IR pretty-printed output.

- [x] **Step 3: Closure-convert.** Pass over the IR that floats every `Lam` to top level and replaces in-body lambdas with `MkClosure(fn_id, captures)`. Free-variable analysis is the work; the rewrite is mechanical.
  - *Acceptance:* fixture-based test asserting no `Lam` appears outside the top-level binding list of the post-pass program.

- [x] **Step 4: Emit C for the Phase 1 subset.** New module `compiler/emit_c.py`. Each top-level `Lam` becomes a `static deduce_value f_<id>(deduce_value env, deduce_value a0, ...)`. `App` of a closure becomes a tail call through the closure's `fn_ptr`. `print` calls `deduce_print_value`.
  - *Acceptance:* round-trip test: lower → close → emit → `cc` → run → diff stdout against interpreter stdout. Three fixtures covering identity, application, and a higher-order function (`λf λx. f(f(x))`).

- [x] **Step 5: Add unions and pattern match.** Extend lowering to `Union`, `Constructor`, `Switch`, `PatternCons`, `PatternBool`. Each `Union` declaration produces, at emit time: a `struct`, an `enum` of tags, allocator stubs `make_<ctor>(args)`, and a `deduce_print_<Union>` pretty-printer that dispatches on tag.
  - *Acceptance:* compile a file defining `Nat` with `zero`/`suc`, `add`, and `print add(suc(zero), suc(suc(zero)))`. Stdout must match the interpreter.

- [x] **Step 6: Add `RecFun`.** Lower each `FunCase` to a clause of a generated `match` over the first matched parameter (the existing checker already enforces a single match column). Default to direct recursion — no TCO yet.
  - *Acceptance:* compile and run any `should-validate` test whose top-level statements are confined to the Phase 1+5+6 subset. Initial target: `test/should-validate/all1.pf` if it qualifies, plus three hand-picked files using `Nat` and `List`.

**Milestone:** small Deduce programs compile and run. End-to-end pipeline works on one toolchain. Stop and try it on three programs you actually want to run before continuing.

## Phase 2 — full executable fragment

**Status:** done. Steps 7–9 + 11 in PR [#304](https://github.com/jsiek/deduce/pull/304); pruning + drop-asserts in PR [#308](https://github.com/jsiek/deduce/pull/308) (added during this phase, not in the original plan); Step 10 (prelude inlining) in PR [#311](https://github.com/jsiek/deduce/pull/311).

- [x] **Step 7: `GenRecFun`.** Same as `RecFun` but the body is a single term, and the `terminates` proof erases. Direct emission, no termination check at runtime.
  - *Acceptance:* compile `gcd` from `lib/Nat.pf` and run a small driver that prints `gcd(12, 8)`.

- [x] **Step 8: Arrays.** Lower `MakeArray` to a runtime helper that walks a `List<T>` and copies into a freshly allocated `deduce_value*`. `ArrayGet` lowers to a bounds-checked index. Document that out-of-bounds is a runtime trap, matching the interpreter.
  - *Acceptance:* `test/should-validate/array1.pf`, `array3.pf` round-trip.

- [x] **Step 9: Generics, fully erased.** Confirm nothing past lowering touches `TermInst`/`Generic`/type parameters. Add an emitter assertion that no IR node carries a non-erased type. This is a defensive step — the erasure already happens in Step 2, but we want a single place where it's enforced.
  - *Acceptance:* compile `lib/List.pf` definitions through to C; a driver calls `length`, `reverse`, `map` and prints results.

- [x] **Step 10: Prelude inlining.** Reuse the existing import machinery: after `uniquify`, walk the same statement list `check_proofs` walks, and feed it to lowering. Anything theorem-shaped is filtered. The output `.c` is self-contained — no separate prelude `.o` to link against in v1.
  - *Acceptance:* compile a file that uses `lib/Nat.pf`'s `+`, `gcd`, `pow2`. Resulting binary runs and prints expected values.

- [x] **Step 11: Bring up `make tests-compile`.** New harness target that runs the compile path across every test the executable fragment can express. Allowlist file (`test/compile-allowlist.txt`) starts with the hand-picked Phase 1+2 set; entries are added as features land.
  - *Acceptance:* `make tests-compile` exists and runs 35 fixtures green; adding a file to the allowlist that fails to compile fails locally. **CI wiring is still pending** — it's a one-line addition to `.github/workflows/` once we agree on a runner with `cc` available.

**Milestone:** every `should-validate` test that doesn't rely on proof-checker reductions at runtime compiles and runs. The compiler is *correct* on the executable fragment, even if slow.

## Phase 3 — quality of compiled output

Items in this phase don't change what compiles; they change how it compiles.

**Status:** Steps 13 + 14 done in PR [#314](https://github.com/jsiek/deduce/pull/314). Step 12 (TCO) deferred.

- [ ] **Step 12: Tail-call optimisation for self-recursion.** Trampoline-based, runtime-supported. Each `RecFun`/`GenRecFun` whose recursive call is in tail position emits a `goto` to the function entry instead of a C call. **Deferred** — no fixture has hit the recursion limit yet; pick this up when a real workload demands it.
  - *Acceptance:* `length` on a 100k-element list does not stack-overflow. Today's interpreter would; that's fine.

- [x] **Step 13: Constructor unboxing for nullary constants.** Bool literals are interned in the runtime (two static `struct deduce_obj` instances). Nullary user constructors are emitted as `C_<mangled>` singletons allocated once at startup.
  - *Acceptance:* `DEDUCE_TRACE_ALLOC=1` runtime mode prints `deduce: N allocations` at exit; the `unbox.pf` fixture asserts the count is 1 (the startup singleton, reused across five `print zero` statements) via an `// expected-allocs: 1` directive.

- [x] **Step 14: Source maps.** With asserts erased, the runtime panics that *can* fire are non-exhaustive `Match`, array OOB, the `Panic` stub for `some`/`all`, and unknown-name references. All of those now print the originating `.pf:line`. Each emitted top-level function carries a `// from foo.pf:42` comment.
  - *Acceptance:* `source_map.pf` triggers an array OOB; the `// expected-runtime-error: source_map.pf:` directive verifies stderr contains the source location.

## Phase 4 — performance: make it not embarrassing

Peano `Nat` is the elephant. `print fact(20)` builds an O(20!)-deep `suc` chain. There are three options:

1. **Do nothing.** Document that `Nat` is for proofs and `UInt`/`Int` are for compute. This is the honest answer and matches what the prelude already nudges users toward.
2. **Extraction map.** A small allowlist of `(Deduce_name, C_implementation)` pairs that the lowering pass swaps in. `Nat`/`zero`/`suc`/`+`/`*`/`≤`/`pred`/`equal` map to `uint64_t` operations. Same idea as Coq/Agda extraction. Risks: silently breaks proofs about overflow; user-defined `Nat` operators don't get the speedup.
3. **Auto-detect.** Statically prove that no `Nat` ever exceeds 2⁶⁴ and lower it to `uint64_t`. Out of scope; this is an optimisation pass, not a Phase 4 feature.

Recommend (1) for v1; reach for (2) only if a real workload shows it's needed.

- [ ] **Step 15: Allocation profiling.** A total-count `DEDUCE_TRACE_ALLOC=1` mode already shipped with Step 13. The remaining work is the **per-tag breakdown** — which tag values dominate (likely `D_CTOR` for `suc` chains). Use it to identify hotspots before doing any cleverness.
  - *Acceptance:* compile a known-slow program (`gcd` on large inputs); profile output shows per-tag counts. Decision point — do we ship the extraction map, or document and move on?

- [ ] **Step 16 (conditional on Step 15): Extraction map.** Only if Step 15 says we need it. Mechanism: a `compiler/extraction.toml` listing `Nat → uint64_t`, `zero → 0`, `suc → +1`, `+ → +`, etc. The lowering pass consults the table when it sees a matching uniquified name. Behavioural equivalence is a *user assertion* — the table is opt-in and documented as unsafe.
  - *Acceptance:* compiled `gcd(1_000_000, 500_000)` finishes in <100 ms.

## Phase 5 — separate compilation and other targets

- [ ] **Step 17: Separate compilation.** Each `.pf` file produces its own `.c`/`.h`/`.o`; `import` becomes a header inclusion; the prelude ships as a pre-built static archive. Detailed design in [`docs/separate-compile-plan.md`](separate-compile-plan.md), which expands this into Steps 25–30.
  - *Acceptance:* recompiling one file out of ten reuses the others' `.o`. Build-system integration left to user (Make example provided).

- [ ] **Step 18: Second backend.** Pick whichever lands first: JavaScript (single file output, easy demos on the GitHub Pages site), or Rust (memory-safe target without GC). Both consume the same IR; the work is the emitter.
  - *Acceptance:* a fixed sample of Phase 2 fixtures runs on the new backend with byte-identical stdout.

## Cross-cutting notes

- **Where to hook in.** `lsp.library.check_file` returns the post-typecheck AST on `CheckResult.ast` (since #307). Lowering reads from there.
- **Type erasure timing.** Erase types in lowering, not before. `proof_checker` still needs them; the IR doesn't.
- **Proofs are not output.** A `.pf` file with only theorems compiles to a `main` that does nothing and exits 0.
- **`make` integration.** `tests-compile` parallels `tests`/`tests-lib`. Default `make` does not depend on it (no `cc` requirement for contributors who only touch the proof checker). CI wiring is still pending.

## How the design drifted from the plan

A few decisions only became obvious once code was hitting real input. Captured here so the divergence isn't surprising:

- **Pruning** wasn't in the original plan; it became necessary for Step 10 (prelude inlining). With pruning in place, "compile then drop" became the right strategy for non-computational terms — the entire prelude can be lowered without paying for what user code doesn't reach.
- **`ir.Panic`** likewise wasn't in the original plan. Lowering for `some`/`all` quantifiers and for references to erased predicates produces a panic stub instead of failing — the surrounding function still compiles, and pruning drops it if it isn't reached.
- **Asserts erase**, instead of being part of the runtime contract. The interpreter validates them at type-check time, so runtime re-checking is wasted work and would force prelude sanity-check asserts to drag in their dependencies.
- **No GC.** The plan called for Boehm GC; in practice plain `malloc` with no `free` has been good enough. Phase 4 may revisit.
- **No NaN-boxing or pointer tagging.** `deduce_value` is a boxed pointer everywhere. Phase 4 may revisit.
