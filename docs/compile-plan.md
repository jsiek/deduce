# Compile-to-C plan

Tracking issue: [#291](https://github.com/jsiek/deduce/issues/291).

**Status:** not started.

## Goal

Compile the executable fragment of a checked Deduce program to a self-contained C program that, when run, produces the same `print` output and exits non-zero on the same `assert` failures as `python deduce.py file.pf` does today.

C is the first target because it's the lowest common denominator: anything that can host a C compiler and ~200 lines of runtime can run compiled Deduce. Once C works the same lowering retargets to Rust, JavaScript, OCaml, or LLVM IR by swapping the final emit pass.

Non-goals (for v1):
- Proofs at runtime. Theorems, postulates, predicates, `auto`, `inductive`, `associative`, `trace` all erase to nothing.
- Performance parity with hand-written C. Faithful peano `Nat` is exponential; the plan addresses this in [Phase 4](#phase-4--performance-make-it-not-embarrassing), not before.
- Separate compilation. v1 produces one `.c` per top-level `.pf`, with the prelude inlined. Linking multiple modules is Phase 5.
- Foreign function interface. No `extern` declarations, no calling C from Deduce.

## Surface to compile

The executable fragment is the union of what `Print`/`Assert` reduce against today. Concretely:

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
| `Print` | Runtime-formatted dump of the value (uses per-union pretty-printers emitted alongside the union). |
| `Assert` | If the formula is `lhs = rhs`, structural compare; otherwise reduce to a `bool` and check it's `true`. Failure prints location + value, exits 1. |
| `Hole`, `Omitted`, `PHole`, `Sorry` | Should not appear in a checked program; emitter aborts if it sees one. |
| `Theorem`, `Postulate`, `Predicate`, `Auto`, `Inductive`, `Associative`, `Trace`, `Module`, `Export`, `Import` | Erased (imports inlined upstream). |

Anything else is a compile-time error in the new pass — explicit allowlist, not a default-fallthrough.

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

The IR is the reuse boundary. It is a small functional core — `Var`, `Lit`, `App`, `Lam` (top-level only after closure conversion), `Let`, `Match`, `Con`, `Prim` — with no proof or type-system constructs. Backends consume IR; they never import `abstract_syntax`.

All new code lives under `compiler/` (subject to rename). The only edits outside it are: (a) a new `--compile` flag and `compile_file` entry point in `deduce.py`; (b) a hook in `proof_checker.py` that, after type-check succeeds, hands the post-uniquify AST to `compiler.lower`.

## Runtime

A small C runtime in `compiler/runtime/` provides:

- `deduce_value` — a tagged pointer (NaN-boxing or `intptr_t` low-bit tag) with cases for `bool`, small int (literals), heap-pointer (everything else).
- `deduce_obj` header — `{ tag, ref_count_or_gc_header, ... payload }`. v1 uses Boehm GC (`-lgc`) — closures and ADTs frequently form non-cyclic trees, but mutual-recursion lambdas plus closures can produce cycles, and reference counting with cycle collection is a Phase 4 problem at the earliest.
- `deduce_closure` — `{ fn_ptr, n_captures, captures[] }`.
- `deduce_print_*` — per-union pretty-printers (emitted with each union).
- `deduce_assert_eq`, `deduce_panic` — failure paths with location strings.

The runtime header (`deduce.h`) is committed; `deduce.c` is committed; nothing is generated at compile time except the user program. CI builds the runtime once with `-Werror -Wall -Wextra`.

`make tests-compile` compiles every `test/should-validate/*.pf` that lies in the executable fragment, runs it, and diffs against the same file checked under the interpreter (`print`/`assert` output should match). Non-executable tests (those whose top-level statements are all theorems/postulates) are skipped, not failed.

## Phase 1 — minimum viable backend

Goal: `python deduce.py --compile examples/hello.pf -o hello.c && cc hello.c runtime/deduce.c -lgc && ./a.out` works for one hand-written file using `bool`, `Nat`, `+`, and `print`.

- [ ] **Step 1: Decide and document the IR.** Single file, `compiler/ir.py`, dataclasses only, ~150 lines. Match against it with `match`/`case`. Lock the shape before writing any lowering — the IR is the reuse point and churn here costs every backend.
  - *Acceptance:* docstring on each node + a hand-written round-trip pretty-printer for debugging. No tests yet; the next step exercises it.

- [ ] **Step 2: Lower a Deduce subset to IR.** New module `compiler/lower.py`. Handle: `Bool`, `Int`, `Var`, `Call` (function application only — no constructors yet), `Conditional`, `TLet`, `Lambda`, `Generic`, `Define`, `Print`, `Assert`. Reject everything else with a clear error.
  - *Acceptance:* hand-written fixture in `test/compile/lower/` with expected IR pretty-printed output.

- [ ] **Step 3: Closure-convert.** Pass over the IR that floats every `Lam` to top level and replaces in-body lambdas with `MkClosure(fn_id, captures)`. Free-variable analysis is the work; the rewrite is mechanical.
  - *Acceptance:* fixture-based test asserting no `Lam` appears outside the top-level binding list of the post-pass program.

- [ ] **Step 4: Emit C for the Phase 1 subset.** New module `compiler/emit_c.py`. Each top-level `Lam` becomes a `static deduce_value f_<id>(deduce_value env, deduce_value a0, ...)`. `App` of a closure becomes a tail call through the closure's `fn_ptr`. `print` calls `deduce_print_value`.
  - *Acceptance:* round-trip test: lower → close → emit → `cc` → run → diff stdout against interpreter stdout. Three fixtures covering identity, application, and a higher-order function (`λf λx. f(f(x))`).

- [ ] **Step 5: Add unions and pattern match.** Extend lowering to `Union`, `Constructor`, `Switch`, `PatternCons`, `PatternBool`. Each `Union` declaration produces, at emit time: a `struct`, an `enum` of tags, allocator stubs `make_<ctor>(args)`, and a `deduce_print_<Union>` pretty-printer that dispatches on tag.
  - *Acceptance:* compile a file defining `Nat` with `zero`/`suc`, `add`, and `print add(suc(zero), suc(suc(zero)))`. Stdout must match the interpreter.

- [ ] **Step 6: Add `RecFun`.** Lower each `FunCase` to a clause of a generated `match` over the first matched parameter (the existing checker already enforces a single match column). Default to direct recursion — no TCO yet.
  - *Acceptance:* compile and run any `should-validate` test whose top-level statements are confined to the Phase 1+5+6 subset. Initial target: `test/should-validate/all1.pf` if it qualifies, plus three hand-picked files using `Nat` and `List`.

**Milestone:** small Deduce programs compile and run. End-to-end pipeline works on one toolchain. Stop and try it on three programs you actually want to run before continuing.

## Phase 2 — full executable fragment

- [ ] **Step 7: `GenRecFun`.** Same as `RecFun` but the body is a single term, and the `terminates` proof erases. Direct emission, no termination check at runtime.
  - *Acceptance:* compile `gcd` from `lib/Nat.pf` and run a small driver that prints `gcd(12, 8)`.

- [ ] **Step 8: Arrays.** Lower `MakeArray` to a runtime helper that walks a `List<T>` and copies into a freshly allocated `deduce_value*`. `ArrayGet` lowers to a bounds-checked index. Document that out-of-bounds is a runtime trap, matching the interpreter.
  - *Acceptance:* `test/should-validate/array1.pf`, `array3.pf` round-trip.

- [ ] **Step 9: Generics, fully erased.** Confirm nothing past lowering touches `TermInst`/`Generic`/type parameters. Add an emitter assertion that no IR node carries a non-erased type. This is a defensive step — the erasure already happens in Step 2, but we want a single place where it's enforced.
  - *Acceptance:* compile `lib/List.pf` definitions through to C; a driver calls `length`, `reverse`, `map` and prints results.

- [ ] **Step 10: Prelude inlining.** Reuse the existing import machinery: after `uniquify`, walk the same statement list `check_proofs` walks, and feed it to lowering. Anything theorem-shaped is filtered. The output `.c` is self-contained — no separate prelude `.o` to link against in v1.
  - *Acceptance:* compile a file that uses `lib/Nat.pf`'s `+`, `gcd`, `pow2`. Resulting binary runs and prints expected values.

- [ ] **Step 11: Bring up `make tests-compile`.** New harness target that runs the compile path across every test the executable fragment can express. Allowlist file (`test/compile-allowlist.txt`) starts with the hand-picked Phase 1+2 set; entries are added as features land.
  - *Acceptance:* CI wires up `tests-compile` as a separate phase. Adding a file to the allowlist that fails to compile fails CI.

**Milestone:** every `should-validate` test that doesn't rely on proof-checker reductions at runtime compiles and runs. The compiler is *correct* on the executable fragment, even if slow.

## Phase 3 — quality of compiled output

Items in this phase don't change what compiles; they change how it compiles.

- [ ] **Step 12: Tail-call optimisation for self-recursion.** Trampoline-based, runtime-supported. Each `RecFun`/`GenRecFun` whose recursive call is in tail position emits a `goto` to the function entry instead of a C call.
  - *Acceptance:* `length` on a 100k-element list does not stack-overflow. Today's interpreter would; that's fine.

- [ ] **Step 13: Constructor unboxing for nullary constants.** `zero`, `empty`, `bzero`, `true`, `false`, etc. are emitted as static globals shared by all uses, not freshly allocated each time. Halves Nat allocation on most programs.
  - *Acceptance:* allocation-counting runtime mode (`DEDUCE_TRACE_ALLOC=1`) confirms zero allocations for `print zero`, `print empty`.

- [ ] **Step 14: Source maps.** Each `assert` failure prints the original `.pf` file:line, not the generated `.c` location. Each emitted top-level function carries a `// from foo.pf:42` comment for debuggers.
  - *Acceptance:* deliberately failing assert produces a diagnostic that names the original `.pf` location.

## Phase 4 — performance: make it not embarrassing

Peano `Nat` is the elephant. `print fact(20)` builds an O(20!)-deep `suc` chain. There are three options:

1. **Do nothing.** Document that `Nat` is for proofs and `UInt`/`Int` are for compute. This is the honest answer and matches what the prelude already nudges users toward.
2. **Extraction map.** A small allowlist of `(Deduce_name, C_implementation)` pairs that the lowering pass swaps in. `Nat`/`zero`/`suc`/`+`/`*`/`≤`/`pred`/`equal` map to `uint64_t` operations. Same idea as Coq/Agda extraction. Risks: silently breaks proofs about overflow; user-defined `Nat` operators don't get the speedup.
3. **Auto-detect.** Statically prove that no `Nat` ever exceeds 2⁶⁴ and lower it to `uint64_t`. Out of scope; this is an optimisation pass, not a Phase 4 feature.

Recommend (1) for v1; reach for (2) only if a real workload shows it's needed.

- [ ] **Step 15: Allocation profiling.** Add a `DEDUCE_TRACE_ALLOC=1` mode to the runtime that dumps per-tag allocation counts at exit. Use it to identify hotspots before doing any cleverness.
  - *Acceptance:* compile a known-slow program (`gcd` on large inputs); profile output shows where allocations come from. Decision point — do we ship the extraction map, or document and move on?

- [ ] **Step 16 (conditional on Step 15): Extraction map.** Only if Step 15 says we need it. Mechanism: a `compiler/extraction.toml` listing `Nat → uint64_t`, `zero → 0`, `suc → +1`, `+ → +`, etc. The lowering pass consults the table when it sees a matching uniquified name. Behavioural equivalence is a *user assertion* — the table is opt-in and documented as unsafe.
  - *Acceptance:* compiled `gcd(1_000_000, 500_000)` finishes in <100 ms.

## Phase 5 — separate compilation and other targets

- [ ] **Step 17: Separate compilation.** Each `.pf` file produces its own `.c`/`.o`; `import` becomes a header inclusion. Need to nail down a stable mangling scheme — uniquified names already work for in-process uniqueness, but emitted symbols must be valid C identifiers (current scheme uses `.`/`<`/`>`).
  - *Acceptance:* recompiling one file out of ten reuses the others' `.o`. Build-system integration left to user (Make example provided).

- [ ] **Step 18: Second backend.** Pick whichever lands first: JavaScript (single file output, easy demos on the GitHub Pages site), or Rust (memory-safe target without GC). Both consume the same IR; the work is the emitter.
  - *Acceptance:* a fixed sample of Phase 2 fixtures runs on the new backend with byte-identical stdout.

## Cross-cutting notes

- **Where to hook in.** After `proof_checker.check_deduce` finishes (success path), the post-uniquify, type-checked AST is in hand. That's the entry point — don't try to compile a parse-only AST, you'll lose `Var.resolved_names` and overload resolution.
- **Type erasure timing.** Erase types in lowering, not before. `proof_checker` still needs them; the IR doesn't.
- **Proofs are not output.** A `.pf` file with only theorems compiles to a `main` that does nothing and exits 0. Document this — a user who expects an error will be confused.
- **Step 5 is the riskiest step.** Constructor representation locks in the runtime ABI; changing it later means re-emitting all unions. Budget a day for "what does `List<T>` look like in C" before writing emitter code.
- **Integration with `test-deduce.py`.** Add `--compile` mode that, for each compilable file, also compiles+runs and diffs stdout. Off by default (needs `cc` + `-lgc`); on in CI.
- **`make` integration.** New target `tests-compile` parallels `tests`/`tests-lib`. Default `make` does not depend on it (no `cc` requirement for contributors who only touch the proof checker).
