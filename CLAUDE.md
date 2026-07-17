# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

Deduce is a proof checker and small functional language for teaching logic, written in Python. Source `.pf` files contain definitions, theorems, and proofs; running `deduce.py file.pf` either prints `... is valid` or fails with an error. The standard library lives in `lib/` and is auto-imported as a prelude unless `--no-stdlib` is passed.

Single dependency: `lark==1.2.2` (Python 3.12+, Makefile uses 3.13).

## Code style

This repository is closed-world: nothing outside this repo depends on its Python API, and the `.pf` source language is the only stable surface. **Backwards compatibility within the repo's own internals is not a concern** — when refactoring, delete old shims rather than carrying them forward.

Smaller code is better. Prefer the change that removes lines over the one that adds them. When two paths are functionally equivalent, pick the one with less surface area. Don't leave deprecation aliases, legacy fallbacks, or "just in case" branches around — if a thing is unused, delete it; if it's needed later, recover it from git.

This applies to refactors especially: when a global goes away, the module-level alias for it goes away too. When a function's signature changes, every caller updates in the same PR — no overload that accepts both shapes.

## Filing bugs you notice in passing

When you spot a bug — or a strong-suspicion bug — while doing something else, **file it as a GitHub issue before declaring your current task done**. Do not just mention it in your reply summary; the reply gets thrown away, the issue persists. **If you noticed a bug, the task is not done until the issue exists.**

Trigger this when any of the following hold:

- A test, sweep, or experiment surfaced concrete evidence of a defect (failing fixture, divergent output, crash, wrong AST, broken round-trip).
- Reading the code, you saw a clear logic error a fix-this-now ticket would describe.
- A documented invariant is violated in code you read.

Do **not** file for: vague code smells, "could be cleaner," missing features, or hunches without a concrete repro.

Each issue must include:

- One sentence stating the bug.
- A minimal repro (source file or shell command — prefer pulling an existing in-tree file over fabricating one).
- Observed vs. expected behavior.
- A link back to where you found it (PR, sweep script, file path).

Group related defects into one issue with categorized sub-bugs (see #931 for the shape) rather than spamming N tiny issues. Cross-reference any umbrella issue the bug sits under with `Refs #N`.

Default to filing without asking first. The exception is when the "bug" might be intentional design — in that case, file anyway but lead the body with "Is this intentional? If so, close." Better to over-file with a quick close than to silently drop a real bug.

## Running and testing

```sh
# Check a single file (uses recursive-descent parser by default)
python deduce.py path/to/file.pf

# Pick a parser explicitly
python deduce.py --recursive-descent file.pf
python deduce.py --lalr file.pf

# Make targets run static checks and BOTH parsers across the test/lib tree
make static       # ruff + mypy + token/grammar checks (matches CI "static checks")
make tests        # static + should-validate + should-error + should-warn
make tests-lib    # checks the stdlib itself
make              # static + token checks + tests (default)
```

`test-deduce.py` is the higher-level harness used in CI:

```sh
python test-deduce.py                  # default: lib + should-validate + should-error + should-warn + prelude + parser equivalence
python test-deduce.py --lib            # only ./lib
python test-deduce.py --passable       # only test/should-validate
python test-deduce.py --errors         # only test/should-error (diff vs .err files)
python test-deduce.py --warns          # only test/should-warn (valid + diff vs .warn files)
python test-deduce.py --equiv          # compare RD/LALR ASTs for a curated grammar corpus
python test-deduce.py --equiv-full     # opt-in: pretty-print round-trip over EVERY accepted-syntax .pf (not in CI)
python test-deduce.py --parser         # only test/parse (parser-error fixtures)
python test-deduce.py --site           # generates and checks doc code from gh_pages/doc

# Regenerate the expected stderr fixture for a should-error test
python test-deduce.py --generate-error test/should-error/foo.pf
python test-deduce.py --regenerate-errors      # all of them

# Regenerate the expected warning fixture for a should-warn test
python test-deduce.py --generate-warn test/should-warn/foo.pf
python test-deduce.py --regenerate-warns       # all of them
```

The test harness runs under the active Python interpreter, which must be Python 3.12+ with `lark` installed. Both parsers must pass — when changing parsing or AST, run with `--lalr` and `--recursive-descent`.

Useful `deduce.py` flags while debugging: `--verbose` (or `--verbose full`), `--unique-names`, `--trace <function>`, `--traceback`, `--quiet`, `--suppress-theorems`, `-r` (recurse into directories).

## Architecture

The pipeline lives in five Python files. The flow for one file is in `deduce.py:deduce_file`:

1. **Parse** — either `parser.py` (lark, grammar in `Deduce.lark`) or `rec_desc_parser.py` (hand-written recursive descent). Both produce the same AST. The default is recursive descent (`flags.py:recursive_descent = True`); `--lalr` switches to lark.
2. **uniquify** (`proof_checker.uniquify_deduce`) — alpha-rename every binding to a globally unique name. `Var.resolved_names` is filled in here (a list, because of overloading).
3. **process_declarations** — collect the type environment for top-level statements.
4. **type_check_stmt** — type-check function bodies; resolve overloads using types.
5. **collect_env** — build the proof environment (label → formula) and runtime environment (name → value).
6. **check_proofs** — verify proofs against the rules of logic; execute `print`/`assert`.

Steps 3–6 all run inside `proof_checker.check_deduce`. The four-phase comment at the top of `proof_checker.py` is the canonical reference.

`abstract_syntax/` defines every AST node as a dataclass under base classes `AST`, `Type`, `Term` (with `Formula` as a subclass), `Proof`, `Statement`, plus `Pattern`. The package is split into cohesive modules for core primitives, terms/formulas, proofs, declarations, environments, literals, rewriting, cross-cutting operations, and theorem printing. `abstract_syntax/__init__.py` is the compatibility facade for existing callers. `docs/knowledge-base/abstract-syntax.md` documents the major nodes.

`flags.py` holds all global compiler state (verbosity, unique-name display, parser choice, import directories, quiet mode). `error.py` defines the exception types (`Exception` for normal errors, `IncompleteProof`, `StaticError`, `MatchFailed`, `ParseError`) and the location-prefixed message format.

### Imports and the prelude

`init_import_directories` seeds `.` plus anything in `~/.config/deduce/libraries`. `--dir <path>` adds another. The stdlib at `lib/` is auto-added unless the file being checked already lives in `lib/` (handled by `check_in_prelude`) or `--no-stdlib` is passed; when included, every `.pf` file in `lib/` is prepended as a private `Import` statement (the prelude) before checking. `lib/*.thm` and `test/**/*.thm` are generated artifacts — they are gitignored and `make clean` removes them.

### Tests directory layout

- `test/should-validate/` — must check successfully.
- `test/should-error/` — must produce an error whose stdout matches the sibling `*.pf.err` file (diffed with `--ignore-space-change`). Update fixtures via `--generate-error`.
- `test/should-warn/` — must check successfully AND emit warning text matching the sibling `*.pf.warn` file (same diff semantics as `should-error`). Update fixtures via `--generate-warn`.
- `test/parse/` — same idea but for parser-error messages (only run via `--parser`).
- `test/test-imports/` — auxiliary modules referenced by `should-validate`/`should-error` tests; passed in as `--dir` so cross-module behavior can be exercised.
- `test/prelude/` — files that exercise the auto-prelude behavior.

## When changing syntax

Per `docs/knowledge-base/what-to-update.md`, a syntax change touches: `Deduce.lark`, `parser.py`, `rec_desc_parser.py`, `abstract_syntax/`, `gh_pages/scripts/keywords.py`, `gh_pages/js/codeUtils.js`, `gh_pages/js/sandbox.js`. The in-tree editor integrations at `editor/emacs/` and `editor/vscode/` may also need updates — neither ships syntax highlighting today, but those additions will live alongside the existing files.

## Stdlib naming convention

`lib/README.md`: theorem names are lowercase snake_case; first word is the type (`uint`, `nat`, `list`, …), second the main operator/function, third the secondary one if any, then a descriptor.

## Writing proofs

When the task is to write or modify a `.pf` proof, read [`gh_pages/doc/TacticsCheatSheet.md`](gh_pages/doc/TacticsCheatSheet.md) first — it lists every tactic with a one-line meaning and documents the syntactic pitfalls (auto-rule goal collapse, `lemma` privacy, `replace` direction, `ℕ0`/`zero` non-unification, conjunction destructuring with `conjunct N of`, etc.) that otherwise have to be discovered by trial. The companion [`gh_pages/doc/CheatSheet.md`](gh_pages/doc/CheatSheet.md) gives goal-shape-keyed strategy advice; [`gh_pages/doc/Reference.md`](gh_pages/doc/Reference.md) is the long-form reference manual.

### Use the deduce MCP server, not the edit-and-revalidate loop

When the `mcp__deduce__*` tools are available in the session, they are the default workflow for `.pf` work — not a fallback. The `python deduce.py file.pf` cycle is slow, gives errors at the wrong granularity, and burns turns on parse-error churn that the MCP tools surface inline.

In particular:

- **`mcp__deduce__goal_at`** at any hole or proof position is the answer to "what does the goal look like here?" Use it *before* writing the next step, not after a failed `replace` tells you the goal had already been auto-collapsed.
- **`mcp__deduce__available_lemmas_at`** ranks in-scope lemmas against the current goal. Use it instead of grepping `lib/*.pf` for "what theorem says `m^(1+k) = m * m^k`".
- **`mcp__deduce__preview_replace_at` / `preview_expand_at` / `preview_conclude_at`** dry-run a tactic against the live goal. Use them before committing to a `replace` chain — they catch "no need for replace because this equation is handled automatically" without a full re-check.
- **`mcp__deduce__refine_at`** suggests the next step. Use it when stuck rather than guessing.
- **`mcp__deduce__check_file`** is the in-MCP equivalent of running `deduce.py`; faster than spawning a fresh interpreter.

Keep `python deduce.py file.pf` for the final pre-commit smoke check and for `--lalr` parity. Skip it as the inner loop.

## Profiling

`./profile.sh file.pf` runs cProfile + gprof2dot and opens a PNG (requires `dot`).
