# LSP / MCP implementation plan

Tracking issue: [#279](https://github.com/jsiek/deduce/issues/279).

**Status:** not started.

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

- [ ] **Step 1: Library-mode entry point.** Refactor `deduce.py:deduce_file` so the pipeline can be called from another Python script and returns structured results. Keep the CLI as a thin wrapper.
  - *Acceptance:* `pytest` that runs the library API across `test/should-validate/` and `test/should-error/` and asserts the same outcomes the existing `test-deduce.py` harness produces.

- [ ] **Step 2: Query API surface, no implementations.** Create `lsp/query.py` with dataclasses and function stubs (`check`, `goal_at`, `definition_of`, `list_symbols`). Bodies raise `NotImplementedError`. Lock the contract.
  - *Acceptance:* import test verifying signatures. After this step, any change to `query.py` signatures requires explicit justification in the PR.

- [ ] **Step 3: Implement `check`.** Convert raised `Exception` / `StaticError` / `IncompleteProof` into `Diagnostic` objects. Single-diagnostic mode is fine; multi-error collection is Step 10.
  - *Acceptance:* parallel to `test/should-error/*.pf.err` — assert each fixture produces a `Diagnostic` with the right line/severity.

- [ ] **Step 4: Implement `goal_at`.** Insert a `?` (`PHole`) at the requested position into a copy of the source, run check, capture the printed goal.
  - *Acceptance:* hand-crafted fixtures in `test/lsp/` with `-- expect goal: ...` markers; test reads marker and asserts.

- [ ] **Step 5: Implement `definition_of` and `list_symbols`.** AST walk using `Var.resolved_names` after a successful check; lexical-scope fallback if check failed.
  - *Acceptance:* hand-crafted fixtures with known symbol locations.

- [ ] **Step 6: In-process prelude caching.** Lazily-initialized module-level `_prelude_state`, reused across calls. Risk step — surfaces global-state leaks in `proof_checker.py` (`name_id`, `imported_modules`, `checked_modules`, `dirty_files`, `recursive_call_count`). Lift only the globals the test catches.
  - *Acceptance:* (a) call `check` on the same file twice in one process, results identical; (b) `check(A); check(B); check(A)` — third call matches first.

- [ ] **Step 7: MCP adapter.** `lsp/mcp_server.py` using the Python `mcp` SDK. Each tool is a thin wrapper around a query API function. Stdio transport.
  - *Acceptance:* (a) unit tests via the `mcp` SDK's in-memory test client; (b) end-to-end smoke from Claude Code on a real proof.

- [ ] **Step 8: Phase 1 latency benchmark.** Measure MCP `check` latency (warm daemon) against baseline `python deduce.py file.pf` latency on a representative set of files. Expected: ~10× speedup (~30s → ~3s).
  - *Acceptance:* benchmark script that reports a side-by-side table for several files. Decision point — if the speedup is well below expected, identify the bottleneck (prelude not actually cached? per-call work that should be amortized?) and address before continuing to Phase 2.

**Milestone:** MCP works for Claude at the expected speedup. Shippable. Stop and use it for ~1 week before continuing — usage will tell you which queries actually matter.

## Phase 2 — LSP and robustness

- [ ] **Step 9: LSP adapter.** `lsp/lsp_server.py` using `pygls`. Adds open-buffer tracking via `didOpen` / `didChange`; query API itself unchanged.
  - *Acceptance:* `pygls` protocol-level tests; manual VS Code testing via existing `deduce-mode`.

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
