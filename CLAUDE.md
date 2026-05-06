# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

Deduce is a proof checker and small functional language for teaching logic, written in Python. Source `.pf` files contain definitions, theorems, and proofs; running `deduce.py file.pf` either prints `... is valid` or fails with an error. The standard library lives in `lib/` and is auto-imported as a prelude unless `--no-stdlib` is passed.

Single dependency: `lark==1.2.2` (Python 3.11+, CI uses 3.12, Makefile uses 3.13).

## Running and testing

```sh
# Check a single file (uses recursive-descent parser by default)
python deduce.py path/to/file.pf

# Pick a parser explicitly
python deduce.py --recursive-descent file.pf
python deduce.py --lalr file.pf

# Make targets run BOTH parsers across the test/lib tree
make tests        # should-validate + should-error
make tests-lib    # checks the stdlib itself
make              # tests + tests-lib (default)
```

`test-deduce.py` is the higher-level harness used in CI:

```sh
python test-deduce.py                  # default: lib + should-validate + should-error + prelude
python test-deduce.py --lib            # only ./lib
python test-deduce.py --passable       # only test/should-validate
python test-deduce.py --errors         # only test/should-error (diff vs .err files)
python test-deduce.py --parser         # only test/parse (parser-error fixtures)
python test-deduce.py --site           # generates and checks doc code from gh_pages/doc

# Regenerate the expected stderr fixture for a should-error test
python test-deduce.py --generate-error test/should-error/foo.pf
python test-deduce.py --regenerate-errors      # all of them
```

The test harness auto-discovers a python3.11–3.14 with `lark` installed. Both parsers must pass — when changing parsing or AST, run with `--lalr` and `--recursive-descent`.

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

`abstract_syntax.py` (~5000 lines) defines every AST node as a dataclass under base classes `AST`, `Type`, `Term` (with `Formula` as a subclass), `Proof`, `Statement`, plus `Pattern`. Each node implements `copy`, `uniquify`, `substitute`, `reduce` as needed. `docs/knowledge-base/abstract-syntax.md` documents the major nodes.

`flags.py` holds all global compiler state (verbosity, unique-name display, parser choice, import directories, quiet mode). `error.py` defines the exception types (`Exception` for normal errors, `IncompleteProof`, `StaticError`, `MatchFailed`, `ParseError`) and the location-prefixed message format.

### Imports and the prelude

`init_import_directories` seeds `.` plus anything in `~/.config/deduce/libraries`. `--dir <path>` adds another. The stdlib at `lib/` is auto-added unless the file being checked already lives in `lib/` (handled by `check_in_prelude`) or `--no-stdlib` is passed; when included, every `.pf` file in `lib/` is prepended as a private `Import` statement (the prelude) before checking. `lib/*.thm` and `test/**/*.thm` are generated artifacts — they are gitignored and `make clean` removes them.

### Tests directory layout

- `test/should-validate/` — must check successfully.
- `test/should-error/` — must produce an error whose stdout matches the sibling `*.pf.err` file (diffed with `--ignore-space-change`). Update fixtures via `--generate-error`.
- `test/parse/` — same idea but for parser-error messages (only run via `--parser`).
- `test/test-imports/` — auxiliary modules referenced by `should-validate`/`should-error` tests; passed in as `--dir` so cross-module behavior can be exercised.
- `test/prelude/` — files that exercise the auto-prelude behavior.

## When changing syntax

Per `docs/knowledge-base/what-to-update.md`, a syntax change touches: `Deduce.lark`, `parser.py`, `rec_desc_parser.py`, `abstract_syntax.py`, `gh_pages/scripts/keywords.py`, `gh_pages/js/codeUtils.js`, `gh_pages/js/sandbox.js`. The two external editor modes (`deduce-mode` for VS Code and Emacs) also need updates but live in separate repos.

## Stdlib naming convention

`lib/README.md`: theorem names are lowercase snake_case; first word is the type (`uint`, `nat`, `list`, …), second the main operator/function, third the secondary one if any, then a descriptor.

## Writing proofs

When the task is to write or modify a `.pf` proof, read [`gh_pages/doc/TacticsCheatSheet.md`](gh_pages/doc/TacticsCheatSheet.md) first — it lists every tactic with a one-line meaning and documents the syntactic pitfalls (auto-rule goal collapse, `lemma` privacy, `replace` direction, `ℕ0`/`zero` non-unification, conjunction destructuring with `conjunct N of`, etc.) that otherwise have to be discovered by trial. The companion [`gh_pages/doc/CheatSheet.md`](gh_pages/doc/CheatSheet.md) gives goal-shape-keyed strategy advice; [`gh_pages/doc/Reference.md`](gh_pages/doc/Reference.md) is the long-form reference manual.

## Profiling

`./profile.sh file.pf` runs cProfile + gprof2dot and opens a PNG (requires `dot`).
