# Separate compilation plan

Tracking issue: [#291](https://github.com/jsiek/deduce/issues/291),
Phase 5 / Step 17 of [`docs/compile-plan.md`](compile-plan.md).

**Status:** not started.

## Goal

Each `.pf` file produces its own `.c`, `.h`, and `.o`. `import Foo`
in source becomes `#include "Foo.h"` in the emitted C; the linker
resolves cross-module symbols. Recompiling one `.pf` file out of N
doesn't require recompiling the others, and the standard library
ships as a pre-built static archive (`libdeduce_prelude.a`) that
user programs link against.

The current monolithic `--compile` mode (one self-contained `.c`
per top-level `.pf`, prelude inlined) stays available for
single-file demos and for tests that don't want a build system.

## Why

Today the compiler inlines the entire prelude into every program
and runs a whole-program reachability pass to drop the unused
parts. That works, but:

- Prelude lowering dominates compile time. Every `--compile`
  invocation re-walks ~30 stdlib modules and re-emits the same
  C for the prelude functions the program happens to use.
- The build artefact is one self-contained `.c` that has to be
  re-emitted from scratch on any source edit.
- There's no story for multi-file user programs — the user
  `import`s their own `.pf` files, but the compiler still flattens
  them into one output.

Separate compilation fixes all three: per-file outputs, build-system
friendly, and pre-built prelude.

## Non-goals (v1)

- **Stable runtime ABI.** Bumping `compiler/runtime/deduce.h`
  invalidates every previously-compiled `.o`. Document and live
  with it; ABI stability is its own project.
- **Dynamic linking.** Static only. `.so` / `.dylib` / `.dll` come
  later (or never).
- **Cross-module monomorphization.** Generics stay type-erased and
  uniform-rep, same as today (Phase 2 Step 9). Specialised
  instantiations are a Phase 4 concern.
- **A package manager.** `deduce.py` knows where to find imports
  via the existing `--dir` machinery; the build system uses the
  same paths.

## What changes

The current pipeline:

```
.pf  ─►  parse / type-check  ─►  lower (inlines all imports)
   ─►  closure-convert  ─►  prune  ─►  emit_c  ─►  one .c
```

The new pipeline (toggled by a CLI flag — see Step 21):

```
.pf  ─►  parse / type-check  ─►  lower (NO import inlining)
   ─►  closure-convert  ─►  emit_c  ─►  one .c + one .h per .pf
```

Pruning is dropped from the per-module path: the whole-program
view isn't available, so we can't compute reachability. Instead
the C linker handles dead-code elimination via
`-ffunction-sections -Wl,--gc-sections` (or its platform
equivalent). Document the flag in the user-facing build example.

## Architecture: one `.pf`, three artefacts

For each `foo.pf`:

- **`foo.h`** — public interface. Re-includes headers of every
  `public import`. Declares one C identifier per top-level
  `Define` / `RecFun` / `GenRecFun`, one tag enum per `Union`,
  one extern singleton per nullary constructor, one `void
  foo_init(void)` prototype.
- **`foo.c`** — implementation. Includes `foo.h` plus the headers
  of every `import` (`public` and private). Defines all the
  symbols `foo.h` declared. Defines `foo_init`, which (idempotently)
  initialises this module's nullary-ctor singletons.
- **`foo.o`** — compiled by `cc` from `foo.c` like any other
  translation unit.

A user program's `main` (the file with `print` statements) gets a
generated `void deduce_program_main(void)` that:

1. Calls every transitively-imported module's `_init` once each,
   in topological order.
2. Runs the print statements.

The runtime's `int main(void)` is unchanged — it still calls
`deduce_program_main`.

## Symbol mangling

Today every emitted symbol carries a runtime counter
(`add.5967`), which differs between compiles of the same file.
Separate compilation requires deterministic names that are also
valid C identifiers and free of collisions across modules.

Scheme:

```
<module-stem>__<base_name>__<disambiguator?>
```

- `<module-stem>` is the filename without extension. Multiple
  files declaring the same `module X` are still separate
  compilation units (one `.o` each); cross-file conflicts are a
  source-level concern that the type-checker already enforces.
- `<base_name>` is `abstract_syntax.base_name(name)` — strips
  the uniquify counter.
- `<disambiguator>` is appended only on collision within a
  module — overloaded `+` for `Nat` vs internal helpers — and is
  the post-uniquify counter (`97`, `5965`) cast through
  `_mangle`. Most names won't need one.

Examples:
- `Nat.pf`'s `suc` → `Nat__suc`
- `UIntAdd.pf`'s `+` → `UIntAdd__operator_plus`
- A lambda lifted out of `Nat.pf` line 42 → `Nat__lam_42_3`
  (location-derived, stable across compiles)

The closure-conversion lambda counter is the trickiest piece: it's
currently a per-program integer that varies with iteration order.
Replace it with a hash of the lambda's source location plus a
within-line tiebreaker.

## Phases / steps

The plan splits into six steps. Steps 25 + 26 land first as
groundwork; Step 27 is the integration point where "separate
compilation" becomes real for hand-written test programs; Steps
28–30 are quality-of-life and prelude productisation. Step
numbering continues from `docs/compile-plan.md` (Steps 17 and 18
in that doc become Step 25 expanded out and Step 30 below; the
detail moves here).

### Step 25 — Stable, deterministic symbol mangling

Replace the per-compile counter scheme with the module-prefixed
scheme above. Done as a refactor inside `compiler/emit_c.py`'s
`_mangle` family, with no behavioural change to the existing
monolithic mode. The post-mangle output is a pure function of the
input source.

Acceptance:
- Compile a fixture twice in fresh processes; the two `.c` files
  are byte-identical.
- All 35 `make tests-compile` fixtures still pass.

Risks: the closure-conversion `$lam<N>` counter is the load-bearing
non-deterministic piece. Switch it to a `(file, line, column,
within-line index)` derivation and verify by running closure-heavy
fixtures (`closure.pf`, `generic.pf`) twice.

### Step 26 — Header generation

Extend `emit_c.emit_program` to also produce a `.h`. New entry
point: `emit_module(p) -> (c_source, h_source)`. The `.h` content:

```c
#ifndef DEDUCE_<MODULE>_H
#define DEDUCE_<MODULE>_H
#include "deduce.h"
/* re-includes for public imports */
#include "Foo.h"

/* per-Union: */
enum Bar_tag { Bar__cons1 = 0, Bar__cons2 = 1, /* … */ };
extern deduce_value C_Bar__cons1;
/* … */

/* per-Function: */
deduce_value Module__fname(deduce_value* env, deduce_value* args);
/* … */

/* per-Global: */
extern deduce_value G_Module__gname;

/* module init: */
void Module_init(void);

#endif
```

Private decls (Deduce `private` / `lemma`) are still emitted in
the `.c` but tagged `static` and not in the `.h`.

Acceptance:
- Compiling a small two-file test (one library `.pf`, one user
  `.pf` that imports it) produces a `.h` with the expected shape;
  hand-written `cc` invocations link them together and the binary
  produces the expected stdout.
- The pretty-printed enum and prototypes are inspected against an
  expected fixture (similar to the existing `.ir`/`.cir`/`.pir`
  files, but `.h`/`.c`).

### Step 27 — Per-module compile mode (`--compile-module`)

New CLI: `python3 deduce.py --compile-module foo.pf`.

Differs from `--compile`:

- Imports are **not** inlined. `Import` AST nodes survive into
  lowering. Lowering emits an `IRImport(name)` placeholder; emit_c
  translates that to `#include "<name>.h"` in the `.c` output.
- Pruning is disabled. Cross-module reachability is the linker's
  job (`-Wl,--gc-sections` etc.).
- Every public top-level decl is exported. Private decls stay
  module-local (C `static`).
- The lowering pass writes both `foo.c` and `foo.h`.

`--compile` (the existing monolithic mode) keeps working
unchanged. The two modes share the same lowering and emission code
but differ in (a) whether imports flatten and (b) what's pruned.

Acceptance:
- A two-file test where `lib.pf` defines `add` and `app.pf` imports
  it. `python3 deduce.py --compile-module lib.pf && python3
  deduce.py --compile-module app.pf && cc app.c lib.c
  compiler/runtime/deduce.c -o app && ./app` produces the right
  output.
- Touching `app.pf` and rerunning the build only recompiles
  `app.{c,o}`, not `lib.{c,o}`. Verified by file mtimes.
- All 35 monolithic-mode fixtures still pass via `--compile`.

### Step 28 — Module init orchestration

Each `foo.c` defines `void foo_init(void)` that:

```c
static int foo_inited;
void foo_init(void) {
    if (foo_inited) return;
    foo_inited = 1;
    /* recursively init imported modules first */
    Bar_init();
    /* … */
    /* allocate this module's nullary-ctor singletons */
    C_foo__zero = deduce_make_ctor(foo__zero, "zero", 0, NULL);
    /* … */
    /* run any module-level Globals */
    G_foo__pi = /* … */;
}
```

The user's main module's emission walks the import graph at
emit time and inlines the right calls into `deduce_program_main`.

Diamond imports: the `_inited` guard handles them. Topological
order for the inits is computed at emit time (the import graph is
acyclic — checked by the front-end).

Acceptance:
- A three-file diamond import (A imports B and C; B and C both
  import D) compiles, links, runs without re-initialising D.
- A nullary ctor referenced from multiple modules is allocated
  once.

### Step 29 — Prelude as a static archive

Add `make compile-prelude` that:

1. Runs `--compile-module` on every `lib/*.pf` in topological
   order, producing `lib/*.c` and `lib/*.h`.
2. Compiles each `.c` to `.o` with `cc -ffunction-sections
   -fdata-sections` to enable later dead-code stripping.
3. Archives the `.o`s into `compiler/runtime/libdeduce_prelude.a`.
4. Copies the `.h`s to `compiler/runtime/include/`.

User programs link with `-L compiler/runtime -ldeduce_prelude` and
include with `-I compiler/runtime/include`.

Acceptance:
- Pre-build the prelude. Then a hand-rolled user program that
  imports `Nat` builds with `cc -I compiler/runtime/include
  -L compiler/runtime app.c compiler/runtime/deduce.c
  -ldeduce_prelude -Wl,--gc-sections -o app` and runs.
- A second build of the prelude produces byte-identical `.a`
  contents (deterministic mangling, deterministic archive).
- Build time for a small user program drops from ~1s
  (single-program prelude inlining today) to <100 ms. Measured.

### Step 30 — Build-system documentation

Document a Makefile pattern in
[`gh_pages/doc/Compiler.md`](../gh_pages/doc/Compiler.md):

```make
DEDUCE = python3 deduce.py
RUNTIME = compiler/runtime
CC = cc
CFLAGS = -I$(RUNTIME)/include -ffunction-sections -fdata-sections
LDFLAGS = -L$(RUNTIME) -ldeduce_prelude -Wl,--gc-sections

%.c %.h: %.pf
\t$(DEDUCE) --compile-module $<

%.o: %.c
\t$(CC) $(CFLAGS) -c $<

app: app.o $(RUNTIME)/deduce.o
\t$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)
```

Also document:
- The `--compile` (monolithic) vs. `--compile-module` (separate)
  distinction.
- That the runtime ABI is unstable; rebuild everything together if
  `compiler/runtime/deduce.h` changes.
- The `-Wl,--gc-sections` flag (and `-dead_strip` on macOS) for
  dead-code elimination.

Acceptance: a worked example in the docs that a user can
copy-paste and run end-to-end. Verified by running it.

## Open questions

These are real design choices that I'd like input on before
starting Step 25. None of them block the plan but they shape the
interface.

1. **Module name source.** Use the filename stem
   (`Nat.pf` → `Nat`) or the `module` declaration? They usually
   agree, but `lib/NatAdd.pf` declares `module Nat`. The
   compilation-unit identity is per-file regardless; the question
   is just what prefix the symbols carry. Filename stem is
   simpler and matches what `--dir` searches for; the `module`
   declaration becomes informational for the compiler.

2. **Multiple files declaring the same `module`.** With the
   filename-stem prefix, `Nat.pf` and `NatAdd.pf` produce
   distinct symbols (`Nat__suc`, `NatAdd__operator_plus`) even
   though the source uses them as one module. The user `import
   Nat` gets `Nat.pf`'s contents only — but `Nat.pf` `public
   import`s `NatAdd`, so `Nat.h` re-includes `NatAdd.h`. The
   end result matches the interpreter, just routed through the
   header re-include rather than a flat namespace.

3. **What about user code that has no `module` declaration?**
   Most hand-written `.pf` files don't. Use the filename stem;
   document it.

4. **Header location convention.** Co-located with the source
   (`.h` next to `.pf`), or a separate `include/` directory?
   Co-located is simpler. The user's build system can add
   wherever to its include path.

5. **What does the lifted-lambda location look like across
   compiles?** A function that closes over a variable defined in
   another module needs the closure's name to be stable. Locking
   it to source location plus a within-line index handles
   in-module stability; cross-module is by definition stable
   since the lambda's home module is fixed.

## Estimated cost

- **Step 25** — 1–2 days. Mostly mechanical, but the closure-
  conversion counter is a load-bearing non-determinism that's
  going to surface obscure issues.
- **Step 26** — 2–3 days. New emit-stage code, but the IR is
  ready for it.
- **Step 27** — 3–5 days. Hardest step. Touches the core
  compile_file flow and adds a new mode that has to coexist with
  the existing one.
- **Step 28** — 1–2 days. Straightforward once Step 27 lands.
- **Step 29** — 1 day. A `Makefile` target plus packaging.
- **Step 30** — half a day, with verification.

Total: **~2 weeks** for a focused effort. Step 27 is the milestone;
Steps 28–30 polish it into something usable.

## Cross-cutting

- **The IR is unchanged.** Separate compilation is a
  lowering+emit-stage concern; no IR nodes added or removed.
- **Tests are mostly unchanged.** `make tests-compile` keeps
  using the monolithic mode. New tests for separate-compile mode
  go in `test/compile/separate/` and validate end-to-end build +
  link + run.
- **Determinism is the load-bearing invariant.** Two builds of
  the same source must produce byte-identical output, otherwise
  incremental rebuilds are wrong. Add a determinism check to CI:
  build the prelude twice, diff the archives.
