# LSP / MCP implementation plan

Tracking issue: [#279](https://github.com/jsiek/deduce/issues/279).

**Status:** Phase 2 in progress — Steps 1–9 done.

## Goals

1. IDE integration via LSP (live diagnostics, goal-at-cursor, go-to-def, completion).
2. Faster Claude interaction via MCP (pull-style queries instead of re-running `deduce.py` per turn).

Today the proof-writing inner loop is dominated by ~30s prelude load on every check; both protocols want a long-lived process that loads the prelude once.

## Architecture

Three layers; bottom two shared between protocols:

```
LSP adapter (pygls)     MCP adapter (mcp SDK)    ← protocol-specific
        \                       /
         +--- Query API --------+                ← protocol-neutral
                  |
              Core daemon                        ← prelude env + cache
```

The query API is the reuse boundary. It takes plain dataclasses (`Position`, `Diagnostic`, `Goal`, `SymbolInfo`, `Location`) and never imports `pygls` or `mcp`. Both adapters are thin wire-format translators.

MCP ships first; LSP follows once the API surface is exercised in anger.

All new code lives under `lsp/` (subject to rename). Only exception: Step 1's refactor of `deduce.py:deduce_file`, which is where the library seam has to live.

## Phase 1 — usable MCP server

- [x] **Step 1: Library-mode entry point.** Refactor `deduce.py:deduce_file` so the pipeline can be called from another Python script and returns structured results. Keep the CLI as a thin wrapper.
  - *Acceptance:* `pytest` that runs the library API across `test/should-validate/` and `test/should-error/` and asserts the same outcomes the existing `test-deduce.py` harness produces.
  - *Implementation:* `lsp/library.py` (`check_file`, `CheckResult`); CLI wrapper in `deduce.py`; one parser fix in `parser.py` (replace `print + exit` on parse error with `raise` so library callers aren't killed); 302-test pytest at `test/lsp/test_library.py`.

- [x] **Step 2: Query API surface, no implementations.** Create `lsp/query.py` with dataclasses and function stubs (`check`, `goal_at`, `definition_of`, `list_symbols`). Bodies raise `NotImplementedError`. Lock the contract.
  - *Acceptance:* import test verifying signatures. After this step, any change to `query.py` signatures requires explicit justification in the PR.
  - *Implementation:* `lsp/query.py` with 9 frozen dataclasses/enums (`Position`, `Range`, `Location`, `Diagnostic`, `Given`, `Goal`, `SymbolInfo`, `Severity`, `SymbolKind`) and 4 stub functions; `__all__` declared. `test/lsp/test_query.py` (21 tests) locks signatures, parameter names, return annotations, frozen-ness, `__all__` membership, stub-raises behavior, and statically asserts no protocol imports (`pygls`/`mcp`/`lsprotocol`/`anthropic`). Position convention: 1-indexed (matches Deduce error messages and lark Meta).

- [x] **Step 3: Implement `check`.** Convert raised `Exception` / `StaticError` / `IncompleteProof` into `Diagnostic` objects. Single-diagnostic mode is fine; multi-error collection is Step 10.
  - *Acceptance:* parallel to `test/should-error/*.pf.err` — assert each fixture produces a `Diagnostic` with the right line/severity.
  - *Implementation:* `lsp/query.py:check` calls `check_file(path, content=content)` and translates the captured exception into a `Diagnostic`. Required surfacing structured location/body via `error.py` (added `location`/`message_body` attributes to `error`/`incomplete_error`/`static_error`/`match_failed`/`ParseError`), a new `wrap_error` helper, and patches at six wrap sites in `proof_checker.py` that previously raised bare `Exception(str(e) + ...)` and dropped the location. `lsp/library.py` gained a `content` parameter (bypasses the uniquified-modules cache) and an `exception` field on `CheckResult`. `rec_desc_parser.py` had a pre-existing leak: `check_closest_kwd` was set to `True` on first parse error and never reset, leaking spurious "did you mean" suggestions across calls in library mode — now reset in a `finally`. Acceptance test `test/lsp/test_check.py` runs 158 cases.

- [x] **Step 4: Implement `goal_at`.** Insert a `?` (`PHole`) at the requested position into a copy of the source, run check, capture the printed goal.
  - *Acceptance:* hand-crafted fixtures in `test/lsp/` with `-- expect goal: ...` markers; test reads marker and asserts.
  - *Implementation:* `lsp/query.py:goal_at` rewrites the content from the cursor up to the next `end` keyword as `\n?\n`, then runs `check_file` and parses the resulting `IncompleteProof.message_body` for `Goal:` and `Givens:`. The goal formula is the first non-blank line after `Goal:` (Deduce's `__str__` always emits a single line); givens are pulled from the trailing `Givens:` block split on `,\n`. Returns `None` when the cursor is out of range, the inserted `?` produces a parse error, or the message has no `Goal:` header. Required hardening in `error.py`: `get_location_text_lines` and `error_program_text` previously crashed on `OSError`/empty lines when the path didn't exist on disk — they now return empty source excerpts so in-memory content (LSP/MCP) doesn't break exception formatting. 6-case acceptance test in `test/lsp/test_goal_at.py`.

- [x] **Step 5: Implement `definition_of` and `list_symbols`.** AST walk using `Var.resolved_names` after a successful check; lexical-scope fallback if check failed.
  - *Acceptance:* hand-crafted fixtures with known symbol locations.
  - *Implementation:* both functions consume `check_file`'s post-typecheck AST (issue #305 prerequisite, merged separately). `definition_of` walks the AST via dataclass reflection, finds the smallest `Var` or `PVar` whose range contains the cursor, takes the resolved (uniquified) name (post-typecheck, so `resolved_names[0]` is unambiguous), then locates the matching top-level declaration. Returns `None` for parse failures or symbols defined outside the user's file (e.g. imports, built-ins). `list_symbols` iterates top-level statements and emits a `SymbolInfo` per declaration with kind, location, and a one-line signature; `Auto` declarations are skipped. Lexical-scope fallback for parse failures was deferred — Step 11's multi-error collection will give us a partial AST to walk in those cases. 10-case acceptance test in `test/lsp/test_symbols.py`.

- [x] **Step 6: In-process prelude caching.** Lazily-initialized module-level `_prelude_state`, reused across calls. Risk step — surfaces global-state leaks in `proof_checker.py` (`name_id`, `imported_modules`, `checked_modules`, `dirty_files`, `recursive_call_count`). Lift only the globals the test catches.
  - *Acceptance:* (a) call `check` on the same file twice in one process, results identical; (b) `check(A); check(B); check(A)` — third call matches first.
  - *Implementation:* `lsp/library.py` gained a snapshot/restore layer over the pipeline's module-level containers. On the first call with a given prelude, the old containers are cleared, the prelude bootstraps via `_check_file_impl` on an empty buffer, and the resulting post-prelude state is shallow-copied into `_prelude_snapshot`. Subsequent calls with the same prelude restore from the snapshot — much faster than re-running `lib/`. Counters (e.g. `name_id`) are intentionally **not** restored: letting them increase monotonically guarantees freshly generated names never collide with cached prelude names. Tracked containers are `uniquified_modules`, `_predicate_decls_by_unique_name`, `collected_imports`, `reduce_only`, `reduced_defs` (from `abstract_syntax`); `imported_modules`, `checked_modules`, `modules`, `dirty_files` (from `proof_checker`). The conftest `_reset_state` hack is gone — `check_file` is now self-contained — and a new `reset_prelude_cache()` helper lets long-running daemons or tests force a reload. 6-case acceptance test in `test/lsp/test_state_isolation.py` covers idempotency, interleaving, snapshot reuse, and the reset helper.

- [x] **Step 7: MCP adapter.** `lsp/mcp_server.py` using the Python `mcp` SDK. Each tool is a thin wrapper around a query API function. Stdio transport.
  - *Acceptance:* (a) unit tests via the `mcp` SDK's in-memory test client; (b) end-to-end smoke from Claude Code on a real proof.
  - *Implementation:* `lsp/mcp_server.py` with FastMCP. Four tools (`check_file`, `goal_at`, `definition_of`, `list_symbols`) wrap the corresponding `lsp.query` functions; each reads the file from disk, calls the query helper, and lets FastMCP serialize. Stdio transport via `python3 -m lsp.mcp_server`. Standard library at `lib/` is auto-prepended as the prelude unless `DEDUCE_NO_STDLIB=1`; `DEDUCE_ROOT` overrides where the server looks for `lib/`. **Required contract change** (justified): `lsp.query` functions gained an optional `prelude` parameter (default `()`) so the server can pass the stdlib through; the Step 2 signature test was updated, and a new test pins the default at `()` so existing Step 3-5 callers keep working unchanged. `list_symbols` filters out auto-prepended prelude imports so the outline shows only what the user wrote. 8-case acceptance test in `test/lsp/test_mcp_server.py` exercises tool registration, valid/error file checking, goal lookup with and without active proof, definition lookup with whitespace fallback, and the symbol outline. End-to-end smoke from Claude Code is left for the user to verify with `requirements-lsp.txt` installed.

- [x] **Step 8: Phase 1 latency benchmark.** Measure MCP `check` latency (warm daemon) against baseline `python deduce.py file.pf` latency on a representative set of files. Expected: ~10× speedup (~30s → ~3s).
  - *Acceptance:* benchmark script that reports a side-by-side table for several files. Decision point — if the speedup is well below expected, identify the bottleneck (prelude not actually cached? per-call work that should be amortized?) and address before continuing to Phase 2.
  - *Implementation:* `lsp/benchmark.py` runs each fixture once via subprocess (cold path) and after a single in-process bootstrap (warm path), 3 runs per phase, median reported. Default fixtures cover small/medium/large should-validate files compatible with the auto-prelude.
  - *Results (with `lib/*.thm` cache present, the typical developer state, on Python 3.13):*
    - Cold subprocess: 0.88–1.41s per file (mostly fixed Python+lark+`.thm`-read startup).
    - Warm via daemon: 0.19–0.75s per file.
    - Bootstrap: ~0.75s one-time per process.
    - Per-call speedup: **2–5×**, dominant for small files where startup dwarfs the actual checking work.
  - *Results (no `.thm` cache, fresh checkout, single fixture):* cold 13.8s, bootstrap 13.9s, subsequent warm 0.26s — **~53× per-call speedup** after bootstrap. The plan's ~10× target was based on this baseline; .thm caching was already pre-paying most of the prelude cost in the typical case.
  - *Decision:* proceed to Phase 2. The 2–5× speedup is meaningful for editor latency, the daemon is required for any LSP server architecturally (Step 6's state isolation), and the warm-path cost is independent of `.thm` staleness so the daemon stays fast even when the on-disk caches are invalidated.

**Milestone:** MCP works for Claude at the expected speedup. Shippable. Stop and use it for ~1 week before continuing — usage will tell you which queries actually matter.

## Phase 2 — LSP and robustness

- [x] **Step 9: LSP adapter.** `lsp/lsp_server.py` using `pygls`. Adds open-buffer tracking via `didOpen` / `didChange`; query API itself unchanged.
  - *Acceptance:* `pygls` protocol-level tests; manual VS Code testing via existing `deduce-mode`.
  - *Implementation:* `lsp/lsp_server.py` with pygls 2.1's `LanguageServer`. Document sync uses pygls's built-in workspace (no manual buffer tracking needed). Seven features: `didOpen`/`didSave` push diagnostics; `didChange` is a no-op (buffer-only update — Step 12's per-statement caching is what would make per-keystroke checks affordable); `didClose` clears diagnostics; `textDocument/definition` and `textDocument/documentSymbol` map directly to `query.definition_of` / `query.list_symbols`. LSP has no built-in for "current proof goal", so a custom `deduce/goalAt` request takes a `{textDocument, position}` payload (LSP-shaped) and returns `{formula, givens, range}`. Coordinate translation (LSP's 0-indexed line/character ↔ query's 1-indexed line/column) is centralized in two helpers, exercised by their own unit tests. Bootstrap mirrors `lsp/mcp_server.py` (DEDUCE_ROOT / DEDUCE_NO_STDLIB env knobs, auto-prelude from `lib/`). 14-case acceptance test in `test/lsp/test_lsp_server.py` exercises feature registration, position translation, didOpen/didSave/didClose diagnostics, definition + outline, custom goal-at, and defensive paths (unknown URI, missing position). `pygls>=2.1.0` added to `requirements-lsp.txt`. Manual VS Code smoke (the plan's second acceptance prong) is left for the user to run with `pip install -r requirements-lsp.txt` and a client config pointing at `python3 -m lsp.lsp_server`.

- [ ] **Step 10: Process-lifecycle hardening.** Crash recovery, structured logging, settings, graceful shutdown. Shared between adapters in `lsp/runtime.py`.
  - *Acceptance:* fault-injection tests — kill prelude mid-load, send malformed requests, send a request before `initialize`. Server reports a structured error instead of crashing.

- [ ] **Step 11: Multi-error collection.** Replace `raise` sites in `proof_checker.py` with an error-sink in env. Larger refactor than it looks; defer until actually wanted.
  - *Acceptance:* fixture file with multiple independent errors; all reported.

## Phase 3 — incrementality (optional)

Only if 3s/check turns out to be too slow. None of this is needed for a working LSP/MCP.

- [ ] **Step 12: Deterministic `uniquify`.** Lift `name_id` into a context object passed through. Don't make `uniquify` pure yet — just deterministic.
  - *Acceptance:* call `uniquify` on the same AST twice, byte-equal output.

- [ ] **Step 13: Per-statement env caching.** In `check_deduce`'s three loops, record `(stmt_hash, env_in_hash) → env_out`. Skip cached entries on later runs. No dependency tracking yet.
  - *Acceptance:* edit one statement, recheck; instrumentation confirms untouched statements were cache hits. Sub-second for typical edits.

- [ ] **Step 14: Dependency-aware invalidation.** Walk each statement's post-uniquify AST to collect referenced names; invalidate dependents on edit.
  - *Acceptance:* edit theorem `T1`; assert `T2` (which uses `T1`) is invalidated and rechecked.

## Cross-cutting notes

- Add `lsp/` to the `make tests` target as a separate phase, otherwise it'll bitrot.
- Step 6 is the highest-risk step despite looking small. Budget ~3 extra days; expect to do part of Step 11's work early to make the test pass.
- Two-process-shared-library is the v1 deployment shape (one daemon per protocol, each loading the prelude). A shared-daemon-with-thin-frontends design over a Unix socket is a later option if duplicated startup cost actually hurts.
