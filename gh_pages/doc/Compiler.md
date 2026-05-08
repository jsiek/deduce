# Compiling Deduce Programs to C

Deduce ships with an experimental compiler that turns the executable
fragment of a checked `.pf` file into a self-contained C program. Once
compiled, the binary runs without Python and produces the same output
as `python deduce.py file.pf` does.

This page walks through how to use it.

* [Quick start](#quick-start)
* [The CLI flags](#the-cli-flags)
* [Linking against the runtime](#linking-against-the-runtime)
* [Programs that use the standard library](#programs-that-use-the-standard-library)
* [Building larger programs](#building-larger-programs) — per-module compile and the prelude archive
* [What compiles, what doesn't](#what-compiles-what-doesnt)
* [Pruning unused definitions](#pruning-unused-definitions)
* [Allocation tracing](#allocation-tracing)
* [Reading error messages](#reading-error-messages)
* [Performance notes](#performance-notes)
* [Limitations and known issues](#limitations-and-known-issues)

## Quick start

Save this file as `hello.pf`:

```deduce
import UInt
import List

print 1 + 2
print [3, 4, 5]
```

Compile it to C, then build and run the binary. From the Deduce
checkout:

```
$ python3 deduce.py --compile hello.pf
$ cc -I compiler/runtime -o hello hello.c compiler/runtime/deduce.c
$ ./hello
3
[3, 4, 5]
```

That's it. The `--compile` flag tells Deduce to write a `.c` file
next to the source instead of just type-checking it. The C code
links against the small runtime in `compiler/runtime/`, which
provides the allocator, value tags, and pretty-printer.

The example uses `UInt` (Deduce's recommended numeric type for
ordinary computation — see [Performance
notes](#performance-notes)) and a list of `UInt`s. Both render
the way the interpreter does: decimal integers and bracketed
lists.

## The CLI flags

Compile-related flags on `python3 deduce.py`:

| Flag | Effect |
| --- | --- |
| `--compile` | Compile the `.pf` file to a single self-contained `.c` (the prelude and any imports are inlined). Output defaults to a sibling `.c`. |
| `--compile-module` | Per-module compile: write both `<file>.c` and `<file>.h`. Imports become `#include` lines instead of inlined definitions. See [Building larger programs](#building-larger-programs). |
| `--no-main` | Pairs with `--compile-module`. Treat this file as a library — skip emitting `deduce_program_main`. The module's `_init` is still emitted. |
| `-o <path>` | Override the output path. Use `-o -` to write to stdout (`--compile` only — `--compile-module` always writes a sibling `.h` so it needs a real path). |
| `--no-prune` | Skip the dead-code-elimination pass. Useful for debugging emitter issues; otherwise leave it on. (`--compile-module` already skips pruning — cross-module DCE is the linker's job via `-Wl,--gc-sections`.) |
| `--no-stdlib` | Don't auto-import the standard library. Useful when your program defines its own primitives, or when you want to keep the generated C as small as possible. |
| `--suppress-theorems` | Quiet the post-check theorem listing; nice for scripts. |
| `--quiet` | Suppress informational chatter. |

Type-checking happens before lowering — if your program doesn't pass
`python3 deduce.py file.pf`, `--compile` will print the same error
and produce no `.c`.

## Linking against the runtime

The runtime is two files in the Deduce checkout:

```
compiler/runtime/deduce.h
compiler/runtime/deduce.c
```

You always compile and link `deduce.c` alongside the generated `.c`:

```
cc -I compiler/runtime -o my_program my_program.c compiler/runtime/deduce.c
```

`-I compiler/runtime` puts `deduce.h` on the include path so the
generated source's `#include "deduce.h"` resolves. The runtime is
plain C99 with no external dependencies — no Boehm GC, no libraries
to install. It compiles cleanly with `-Wall -Wextra -Werror`.

> **Note on memory.** The runtime allocates with `malloc` and never
> calls `free`. For the small, short-lived programs the compiler is
> currently aimed at, that's intentional. Long-running programs will
> grow without bound; this is a known limitation tracked in the
> compile plan's Phase 4.

## Programs that use the standard library

When your `.pf` file `import`s a module from the prelude, the
compiler walks every imported module and inlines the definitions it
finds; the pruner then drops everything that isn't reached from a
`print` statement. The full standard library has hundreds of
definitions, but a small program ends up with a small `.c`.

```deduce
import Nat

print ℕ2 + ℕ3
print pow2(ℕ4)
print gcd(ℕ12, ℕ8)
```

Compile:

```
$ python3 deduce.py --compile hello_nat.pf
$ cc -I compiler/runtime -o hello_nat hello_nat.c compiler/runtime/deduce.c
$ ./hello_nat
suc(suc(suc(suc(suc(zero)))))
suc(suc(suc(suc(suc(suc(suc(suc(suc(suc(suc(suc(suc(suc(suc(suc(zero))))))))))))))))
suc(suc(suc(suc(zero))))
```

Despite using `+`, `pow2`, and `gcd` from `lib/Nat.pf`, the generated
`.c` for this program is well under 400 lines — pruning drops every
other prelude definition.

If your program defines its own primitives and doesn't need the
prelude, pass `--no-stdlib` to skip auto-importing. The generated
output is smaller and the compile is faster.

## Building larger programs

`--compile` produces one big self-contained `.c` per source file.
That's the simplest path and the right default for short
programs, but as a project grows you'll want to:

1. compile each `.pf` file into its own `.c` and `.h`, and
2. link against a pre-built archive of the standard library
   instead of inlining it into every binary.

Both are supported.

### Per-module compile (`--compile-module`)

`--compile-module` produces a `.c` and `.h` next to each `.pf`,
each containing only that file's definitions. Imports become
`#include "<other>.h"` lines and the linker stitches the modules
together at link time.

A minimal two-file example (no stdlib involved):

```deduce
// lib.pf
union MyNat {
  zero
  suc(MyNat)
}

fun two() {
  suc(suc(zero))
}
```

```deduce
// app.pf
import lib

print two()
print suc(two())
```

```
$ python3 deduce.py --compile-module --no-main --no-stdlib --dir . lib.pf
$ python3 deduce.py --compile-module --no-stdlib --dir . app.pf
$ cc -I . -I compiler/runtime app.c lib.c compiler/runtime/deduce.c -o app
$ ./app
suc(suc(zero))
suc(suc(suc(zero)))
```

Programs that use the standard library follow the same shape but
link against the pre-built prelude archive — see the next section.

Two extra flags pair with `--compile-module`:

| Flag | Effect |
| --- | --- |
| `--compile-module` | Per-module compile mode. Both `<file>.c` and `<file>.h` are written; imported `.h`s are `#include`d. |
| `--no-main` | This file is a library, not the entry point. Skip emitting `deduce_program_main` and the `print` body. The module's `_init` function is still emitted so other modules can call it. |

Each module's `<Module>_init()` is **idempotent**: it allocates
the module's nullary-constructor singletons, runs its
module-level globals, and recursively initialises its direct
imports. The main module's `deduce_program_main()` calls its own
`_init` once at startup. Diamond imports are safe — each module
inits exactly once regardless of how many transitive paths reach
it.

Symbols are mangled as `<Module>__<name>_<seq>` where `<seq>` is
a per-module ordinal computed from the source file. The mangling
is stable across compilation contexts: a module produces the
same C symbol names whether it was compiled standalone or
walked-through-imports as part of another module's compile.

### The prelude as a static archive (`make compile-prelude`)

For larger programs, building the standard library once into a
static archive saves work on every subsequent build.

```
$ make compile-prelude
built compiler/runtime/libdeduce_prelude.a (134064 bytes, 32 modules)
```

This produces:

- `compiler/runtime/libdeduce_prelude.a` — every prelude module
  pre-compiled, packaged as an `ar` archive.
- `compiler/runtime/include/*.h` — the matching headers.

The archive is **reproducible**: a second run produces a
byte-identical `.a`.

A user program that imports stdlib modules then links against
the archive instead of inlining the prelude:

```
$ cat > app.pf <<'PF'
import Nat
import UInt

print 0
print 1 + 2
print 3 * 4
PF
$ python3 deduce.py --compile-module --no-stdlib --dir lib -o app.c app.pf
$ cc -I compiler/runtime/include -I compiler/runtime \
     -L compiler/runtime \
     app.c compiler/runtime/deduce.c -ldeduce_prelude \
     -o app
$ ./app
0
3
12
```

Adding `-ffunction-sections -fdata-sections` to your `cc` flags
and `-Wl,--gc-sections` (Linux) or `-Wl,-dead_strip` (macOS) to
the linker lets the toolchain drop archive members your program
doesn't reference, so the binary stays small.

### A reusable Makefile

Drop this into your project (alongside your `.pf` files) to drive
the per-module flow. Set `DEDUCE_ROOT` to wherever the Deduce
checkout lives — it points at `lib/`, `compiler/runtime/`, and
the prelude archive you built with `make compile-prelude`.

```make
DEDUCE_ROOT ?= ../deduce
DEDUCE       = python3 $(DEDUCE_ROOT)/deduce.py
LIB          = $(DEDUCE_ROOT)/lib
RUNTIME      = $(DEDUCE_ROOT)/compiler/runtime
CC           = cc
CFLAGS       = -I$(RUNTIME)/include -I$(RUNTIME) \
               -ffunction-sections -fdata-sections
LDFLAGS      = -L$(RUNTIME) -ldeduce_prelude -Wl,--gc-sections
# macOS uses -dead_strip instead of --gc-sections:
#   LDFLAGS = -L$(RUNTIME) -ldeduce_prelude -Wl,-dead_strip

.DEFAULT_GOAL := app

# Library modules: pass --no-main so deduce_program_main isn't
# emitted. Each rule must explicitly list its .pf so make picks
# the right --no-main set.
lib.c lib.h: lib.pf
	$(DEDUCE) --compile-module --no-main --no-stdlib \
	          --dir $(LIB) --dir . -o lib.c lib.pf

# Main module: depends on every library .h it imports.
app.c app.h: app.pf lib.h
	$(DEDUCE) --compile-module --no-stdlib \
	          --dir $(LIB) --dir . -o app.c app.pf

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

# Compile the runtime locally so we don't pollute the Deduce
# checkout with a .o.
deduce_runtime.o: $(RUNTIME)/deduce.c
	$(CC) -I$(RUNTIME) -ffunction-sections -fdata-sections \
	      -c -o $@ $<

app: app.o lib.o deduce_runtime.o
	$(CC) -o $@ $^ $(LDFLAGS)

clean:
	rm -f *.c *.h *.o app
```

One-time setup: in the Deduce checkout, run `make compile-prelude`
(this produces the archive + headers). Then in your project,
`make` builds and links incrementally — touching `app.pf` only
recompiles the app, the prelude archive is reused untouched.

### When to use which mode

| You're | Use |
| --- | --- |
| Sketching a one-file program | `--compile` (monolithic) |
| Building a multi-file project | `--compile-module` per file + the Makefile above |
| Iterating on a single module | `--compile-module` + `make` (incremental) |
| Shipping a binary | either; `--compile-module` + `--gc-sections` produces smaller binaries |

Both modes produce identical output for the same source — they
only differ in where the prelude lives at link time.

## What compiles, what doesn't

The compiler handles the **executable** fragment of Deduce — the part
that has runtime meaning. Logical and proof-related constructs are
erased.

**Compiles, runs as expected:**

| Feature | Notes |
| --- | --- |
| `union` declarations | Constructors are tagged. |
| `recursive` and `fun` | Top-level functions, including operators (`+`, `*`, etc.). |
| `recfun … measure … terminates` | The measure expression and `terminates` proof both erase. |
| `define` | Bindings to functions, lambdas, or values. |
| `λ` lambdas | Closure-converted automatically; capture surrounding variables. |
| `if … then … else` | At the term level. |
| `switch` with constructor or `bool` patterns | Compiled to a C `switch` on the constructor tag. |
| Generics (`<T>`) | Type-erased; functions are uniform over T. |
| `not`, `and`, `or`, `≠` | Lowered as boolean expressions. |
| `=` | Structural equality at runtime. |
| `array(...)` and `arr[i]` | List → flat heap-allocated array. Indices may be `Nat` or `UInt`. |
| `print` | Calls into the runtime pretty-printer. |
| `import` | Inlined transitively. |

**Erased silently** (present in source, not in the compiled binary):

- `theorem`, `lemma`, `postulate`, `predicate`, `relation`,
  `auto`, `inductive`, `associative`, `trace`, `module`, `export`
- `assert` — the type-checker has already validated every assertion
  by the time the compiler runs, so re-checking at runtime is wasted
  work. A program with only asserts compiles but produces no output.

**Surfaces a runtime panic if reached:**

- `some` and `all` quantifiers in `fun`/`define` bodies. They have no
  computational meaning; the compiler emits a panic stub. Pruning
  drops it if no `print`-reachable path actually evaluates the
  quantifier — so most prelude predicates compile fine, even though
  they're built out of these.
- References to predicate names (the predicate itself is erased; the
  call site becomes a runtime panic). Same pruning story.

## Pruning unused definitions

By default the compiler runs a **reachability pass** between closure
conversion and code emission. Starting from the `print` statements,
it walks the call graph and keeps only the definitions, globals, and
unions that can transitively be reached. Everything else is dropped
before any C is written.

This is what makes prelude inlining practical. A "hello world" that
calls `+` from `lib/Nat.pf` doesn't drag in `gcd`, `summation`, or any
of the operator implementations for `UInt`/`Int`.

Pass `--no-prune` to disable the pass and keep every lowered
definition in the output:

```
python3 deduce.py --compile --no-prune hello.pf
```

You generally don't want this — it's there for when you're debugging
a code-emission issue and want to inspect what the compiler did with a
specific definition that the pruner would otherwise have removed.

## Allocation tracing

The runtime can report how many heap allocations the program
performed. Set `DEDUCE_TRACE_ALLOC=1` in the environment and the
program prints one line of summary to stderr at exit:

```
$ DEDUCE_TRACE_ALLOC=1 ./hello
suc(suc(suc(zero)))
deduce: 9 allocations
```

(The program's normal output stays on stdout. The allocation line is
on stderr so it doesn't disturb shell pipelines.)

This is most useful for spot-checking the compiler's optimisations.
For example, nullary constructors like `zero` or `empty` are
*unboxed* — the compiler emits one shared instance at startup and
every site that constructs `zero` references that instance instead of
allocating a new one. So this program:

```deduce
union MyNat {
  zero
  suc(MyNat)
}

print zero
print zero
print zero
```

…reports `deduce: 1 allocations` regardless of how many `print zero`
lines you add. The single allocation is the startup singleton.

## Reading error messages

If type-checking fails, you get the same error you'd see from
`python3 deduce.py file.pf` — no C is written.

If type-checking succeeds but the binary panics at runtime, the panic
message includes the originating `.pf:line` so you can navigate to the
source. For example, an array index that's out of bounds:

```
deduce: hello.pf:21: array index out of range
```

Every emitted top-level function also carries a `// from foo.pf:42`
comment in the generated C, so a debugger like `lldb` or `gdb` (or a
human reading the C) can map back to the source.

## Performance notes

**Use `UInt` or `Int` for arithmetic, not `Nat`.** Deduce's `Nat`
type is the canonical Peano numeral: `4` is `suc(suc(suc(suc(zero))))`,
which is four heap allocations to construct and four pointer
dereferences to inspect. The compiler currently faithfully reproduces
this representation. A program that does `print fact(20)` in `Nat`
will allocate on the order of 20! values; the same program in `UInt`
runs in milliseconds.

The standard library is structured to nudge you toward `UInt`/`Int`
for compute. `Nat` is intended for proofs, not for performance.

(Faster `Nat` is on the roadmap but isn't implemented yet — see
[`docs/compile-plan.md`](../../docs/compile-plan.md) Phase 4.)

## Limitations and known issues

These are the rough edges to be aware of:

- **No GC.** The runtime allocates and never frees. Fine for short
  programs; not fine for anything long-running.
- **No tail-call optimisation.** A function recursing 100,000 deep
  will stack-overflow. The interpreter has the same limit (it's a
  Python recursion-depth thing); the compiled binary inherits a
  similar limit from the C stack.
- **Peano `Nat` is slow** — see above.
- **The runtime ABI is unstable.** `compiler/runtime/deduce.h` may
  change between commits. Rebuild every `.o` and the prelude
  archive together when you upgrade Deduce — don't carry old
  objects forward.
- **Only C output.** The IR is intentionally retargetable, but C is
  the only emitter implemented today. JavaScript and Rust backends
  are planned.

The compile plan in [`docs/compile-plan.md`](../../docs/compile-plan.md)
tracks the open performance/runtime items, and the separate-compile
plan in [`docs/separate-compile-plan.md`](../../docs/separate-compile-plan.md)
covers the per-module / archive workflow described above.
