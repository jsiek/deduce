# LSP / MCP implementation plan

Tracking issue: [#279](https://github.com/jsiek/deduce/issues/279).

**Status:** Phase 1, Phase 2 Step 9, Phase 3 Steps 12–14, and Phase 4 Steps 15–19 are done.  Open: Steps 10 (process-lifecycle hardening) and 11 (multi-error collection).

**Related:** [`hole-fill-plan.md`](hole-fill-plan.md) — downstream feature that adds two new LSP requests (`deduce/holeContextAt`, `deduce/validateProof`) and a library-side `validate_theorem` hook, building on this plan's Phase 1–2 deliverables.

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

## Phase 3 — incrementality

Originally framed as optional ("only if 3s/check turns out to be too slow") but landed end-to-end: Step 12 made uniquify deterministic, Step 13 added the per-statement `check_proofs` cache, and Step 14 made invalidation dependency-aware so editing one theorem only re-runs proofs that actually use it.

- [x] **Step 12: Deterministic `uniquify`.** Lift `name_id` into a context object passed through. Don't make `uniquify` pure yet — just deterministic.
  - *Acceptance:* call `uniquify` on the same AST twice, byte-equal output.
  - *Implementation:* `abstract_syntax.UniquifyContext` holds the counter; `generate_name(name, ctx)` reads the counter from the explicit ctx.  Threaded through every `uniquify(self, env, ctx)` method (98 method defs, ~135 call sites in `abstract_syntax.py`) — no module-level scaffolding, no implicit "active context" pointer, no backwards-compat aliases.  `UniquifyContext.snapshot()` forks an independent counter with the same value, used by `lsp/library.py` to capture the post-prelude baseline once and fork a fresh ctx per `check_file` call so user-file uniquify is byte-stable across calls.  7-case acceptance test in `test/lsp/test_uniquify_determinism.py` (byte-equal output, ctx isolation, snapshot semantics).  CLAUDE.md gained a "Code style" section noting the closed-world / no-backwards-compat policy that drove the refactor.

- [x] **Step 13: Per-statement env caching.** In `check_deduce`'s three loops, record `(stmt_hash, env_in_hash) → env_out`. Skip cached entries on later runs. No dependency tracking yet.
  - *Acceptance:* edit one statement, recheck; instrumentation confirms untouched statements were cache hits. Sub-second for typical edits.
  - *Implementation:* cache lives at module scope in `proof_checker.py` (`_stmt_cache`, `_cache_stats`, `reset_stmt_cache`, `get_cache_stats`).  `_hash_ast` is a structural hash that skips the `location` field and memoises the result on each AST node via `__hash_cache__`, so an unchanged statement keeps its hash regardless of where it sits in the file.  Cache scope is just the third of `check_deduce`'s loops (`check_proofs`) — caching loops 1–2 would let `Meta` locations leak across calls and break the `target_hole_location` flag mechanism that `goal_at` / `refine_at` / etc. rely on, surfacing as goal-at-cursor returning `None` when it shouldn't.  The original Step-13 key was `(stmt_hash, chain_hash, target_hole_location, module_name)`; Step 14 replaced `chain_hash` with `deps_fingerprint`.  `lsp/library.py:_clear_containers` resets the cache when the prelude key changes.  Cache stays valid across `check_file` calls within the same prelude.  6-case acceptance test in `test/lsp/test_check_proofs_cache.py` covered all-misses, all-hits, single-stmt edit, comment-only edit, and a stub-instrumented direct check; Step 14 grew it to 9 cases.

- [x] **Step 14: Dependency-aware invalidation.** Walk each statement's post-uniquify AST to collect referenced names; invalidate dependents on edit.
  - *Acceptance:* edit theorem `T1`; assert `T2` (which uses `T1`) is invalidated and rechecked.
  - *Implementation:* `_collect_referenced_names` walks the post-uniquify AST gathering every `VarRef` / `PVar` name; `_collect_defined_names` returns the names a top-level statement introduces (its own name plus union constructors / predicate rules / synthesised induction lemmas). `check_deduce`'s third loop maintains a `defined_to_idx` map and replaces Step 13's `chain_hash` with `deps_fingerprint = hash(tuple(stmt_hashes_so_far[j] for j in sorted(dep_indices)))` — only the prior statements *this* one references contribute. `Import` and `Auto` are treated as global barriers (every later statement implicitly depends on them) since they have effects observable everywhere downstream. `Auto` additionally propagates its referenced names into every later statement's dependency set, so editing an `auto`'d theorem invalidates downstream proofs that rely on the implicit rewrite without textually mentioning it. Required a foundational fix in `uniquify_deduce`: each top-level statement now gets its own `s<N>_` scope segment with `name_id` reset, so an edit confined to statement *N* no longer shifts the bound-name suffixes of statement *M > N* — without that, every downstream statement's stmt_hash drifts on every edit and the cache is useless. Acceptance test in `test/lsp/test_check_proofs_cache.py::test_editing_T1_invalidates_T2_that_uses_it`; complement test pins the negative direction (unrelated downstream stays a hit), plus an `auto`-aware test for the implicit-dep case. Known limitation tracked in [#368](https://github.com/jsiek/deduce/issues/368): `proof_checker.name_id` is still process-monotonic and can perturb stmt hashes for modules that exercise predicate desugaring / induction translation — fold it into a context object or snapshot it via the LSP state machinery.

## Phase 4 — Structured proof-editing operations (Agda-like)

Four productivity features that mirror what Agda exposes via `C-c C-c` (case split), `C-c C-r` (refine), induction-skeleton generation, and `C-c C-e` (eliminate / use-fact). Each is a transformation that takes the current AST + cursor position (and, for elimination, an extra label argument) and produces a `WorkspaceEdit` — exposed to LSP clients as a `textDocument/codeAction` (or a custom request when extra input is needed) and to MCP/Claude as a tool.

These steps share infrastructure (the code-action plumbing in `lsp_server.py`, a transformation API in `lsp/query.py` or a sibling module, and `WorkspaceEdit`-shaped return values in both adapters), so the first one to land pays the wiring cost and the rest reuse it. They're orthogonal to Phase 3 (incrementality) and can be implemented in either order; if the test suite is too slow without incrementality, do Phase 3 first.

The new query-API functions are additive — Step 2's signature lock applies, and these get added to `__all__`.

Steps 15 and 18 are duals: Step 15 is **introduction** (template chosen by the *goal* shape — what to construct), Step 18 is **elimination** (template chosen by the *hypothesis* shape — how to use what's in scope). Step 16 (case split on a variable) and Step 17 (induction on the goal) round out the corners that don't fit the introduction/elimination split — they operate on bound names rather than on the proof position.

- [x] **Step 15: Hole refine.** Given a `?`, propose a refinement template based on the goal shape. The simplest of the three; lays the code-action / WorkspaceEdit plumbing the next two reuse.

  Template selection (reuses the `proof_advice` machinery in `proof_checker.py`):

    - `true` → `.`
    - `P and Q [and R...]` → `?, ?[, ?...]`
    - `if P then Q` → `assume <fresh>: P\n<indent>?`
    - `all x:T. P` → `arbitrary x:T\n<indent>?`
    - `some x:T. P` → `choose ?\n?`
    - reducible equality `e1 = e2` (where `e1.reduce(env) == e2.reduce(env)`) → `reflexive`

  New query API: `refine_at(path, content, pos, prelude=()) -> Optional[WorkspaceEdit]`. `WorkspaceEdit` is a new frozen dataclass — `{path, range, new_text}` — added to `lsp/query.py` and to `__all__`. LSP wiring: `lsp_server.py` gains a `textDocument/codeAction` handler that returns a `CodeAction(kind="refactor.rewrite", edit=...)` when the cursor is on a hole. MCP wiring: a new `refine_at` tool in `mcp_server.py`.

  - *Acceptance:* one fixture per shape plus a "no goal at cursor" None case; assert the produced text matches the expected template literally and that re-running `check` on the post-edit content surfaces a fresh hole at the inner `?` (or, for `reflexive` / `.`, no hole).
  - *Implementation:* `lsp/query.py:refine_at` runs `check` on the buffer with the cursor's `?` flagged via `flags.target_hole_location`, catches `IncompleteProof`, dispatches on the goal AST (`Bool(True)`, `And`, `IfThen`, `All`, `Some`, equality where both sides reduce to the same term), and returns a `WorkspaceEdit` whose `range` covers the `?` token. `WorkspaceEdit` is a new frozen dataclass added to `lsp/query.py` and `__all__`. The `make_unique` helper supplies fresh hypothesis labels. LSP code-action handler emits `CodeAction(kind="refactor.rewrite")` only when `refine_at` returns non-None, matching pygls's contract.  MCP gains a `refine_at` tool.  9-case acceptance test in `test/lsp/test_refine.py` covers each goal shape, the no-goal-at-cursor case, indentation preservation, and the inner-hole assertion.

- [x] **Step 16: Case split.** Given a cursor on a variable inside a hole context, generate the `switch` (term-level union) or `cases` (proof-level disjunction) skeleton. Replaces the surrounding hole with one branch per constructor / disjunct, each containing a fresh `?`.

  Constructor signatures and case labels come from the union declaration's AST (`Union.alternatives`); for proof variables of `or`-type, the cases come from `Or.args`. Variable scope and capture-avoiding renames piggyback on the existing `make_unique` helper.

  New query API: `case_split_at(path, content, pos, variable, prelude=()) -> Optional[WorkspaceEdit]` plus a companion `splittable_vars_at(path, content, pos, prelude=()) -> tuple` so editor clients can offer completion against in-scope splittable variables before issuing the request.

  - *Acceptance:* fixtures for (a) splitting a `Nat` variable, (b) splitting a `List<T>` variable, (c) splitting a custom-union variable with multiple typed parameters, (d) splitting a proof variable of `P or Q`, plus (e) a "cursor not on a variable" None case. Each splitting case asserts: the produced text parses; the case order matches the declaration order; each case body holds a fresh hole; rerunning `check` re-raises an `IncompleteProof` whose location is inside the first case body.
  - *Implementation:* `lsp/query.py:case_split_at` consumes the proof env that `incomplete_error` stashes on the `IncompleteProof` exception (Step 4 plumbing), looks up the named variable, and emits either a `switch` (term variable whose type resolves to a Union or `TypeInst` of one) or `cases` (proof variable whose formula is `Or`).  Constructor parameter names follow `proof_advice`'s convention (first letter of the type, plus a 1-N suffix when there are multiple args), with per-case scope reset so two cases can both have a `b1`.  The hole's source range is found via a forward text scan from the cursor (Deduce's `?` is a single character).  Custom request `deduce/caseSplitAt` (since `textDocument/codeAction` can't carry the variable name) plus a companion `deduce/splittableVarsAt` for completion.  Matching MCP tools `case_split_at` and `splittable_vars_at`.  Emacs binds `C-c C-c` to a command that prompts for the variable via `completing-read` against `deduce/splittableVarsAt`.  13-case acceptance test in `test/lsp/test_case_split.py`.

- [x] **Step 17: Induction skeleton.** Given a goal of the form `all x:T. P(x)` (or analogous on inductive predicates) where `T` is a union, generate

      induction T
        case Cons1(...) { ? }
        case Cons2(...) assume IH1: ... { ? }
        ...

  Reuses `gen_custom_induction_advice` for theorems that ship a custom induction principle. Distinct from Step 16 because (a) it operates on the *goal* rather than a variable, (b) it adds `assume IH<N>: ...` clauses for recursive constructor parameters, and (c) it uses Deduce's `induction` keyword rather than `switch`.

  New query API: `induction_skeleton_at(path, content, pos, prelude=()) -> Optional[WorkspaceEdit]`. Wired same as the previous two.

  - *Acceptance:* fixtures over (a) a `Nat`-quantified theorem (canonical zero/suc cases, IH on suc), (b) a `List<T>`-quantified theorem (empty/node cases, IH on node), and (c) a theorem with a `@induction` custom-induction marker (cases match the conjuncts of the marker). Each asserts: cases appear in declaration order, recursive parameters introduce an `IH<N>` binding, each case body holds a fresh hole.
  - *Implementation:* `lsp/query.py:induction_skeleton_at` runs `check` with the cursor's `?` flagged, inspects the resulting `IncompleteProof.formula` for an `All` whose body's bound variable resolves to a Union, and emits `induction <T>` followed by one case per constructor in declaration order.  Each constructor parameter that is recursive in `T` gets a sibling `assume IH<N>: <body[var := param]>` binding (substituting the parameter for the inducted variable in the goal).  Same UX shape as `refine_at` -- cursor on `?`, no extra input -- so it shares the `textDocument/codeAction` plumbing and surfaces as the "Induction" action alongside "Refine hole".  Matching MCP tool.  7-case acceptance test in `test/lsp/test_induction.py`.

- [x] **Step 18: Eliminate / use-fact.** The dual to Step 15. Given a hypothesis label (`H1`, `pP`, etc.) supplied by the user, generate a tactic that *uses* that fact based on its shape — modus ponens on an implication, instantiation on an `all`, case-split on an `or`, replace on an equality, and so on. The cursor's role is just where to insert; the *label* drives template selection.

  The shape table mirrors `proof_use_advice` in `proof_checker.py` (Deduce's existing `help <proof>` statement walks the same shapes):

    - `H: P and Q [and R...]` → use the conjuncts implicitly (no skeleton needed; the tactic is just `H` itself, optionally with `conjunct N of H` for explicit access). For v1, surface this as a `define <fresh1> = conjunct 1 of H\ndefine <fresh2> = conjunct 2 of H\n?` or skip — the conjuncts are usable without a tactic. Mark this case as no-op-with-message in v1 and revisit.
    - `H: P or Q [or R...]` → `cases H\n  case <fresh1>: P { ? }\n  case <fresh2>: Q { ? }\n  ...` (overlap with Step 16's `or` case; both produce `cases` skeletons but Step 18 is keyed by the hypothesis label, Step 16 by a variable on which to switch — keep them separate so each binding stays single-purpose).
    - `H: if P then Q` → `apply H to ?` (the `?` is a proof of `P`; the result is a proof of `Q`).
    - `H: all x:T [, y:U, ...]. P` → `H[?, ?, ...]` for term arguments or `H<?, ?, ...>` for type arguments (one `?` per quantifier; user fills in the witness terms).
    - `H: some x:T [, y:U, ...]. P` → `obtain <fresh1>[, <fresh2>, ...] where <fresh-label>: P from H\n?`. The fresh names follow the same `make_unique` convention as Step 15's `H<N>` labels.
    - `H: e1 = e2` → `replace H\n?`.
    - `H: true` → message "the `true` fact is useless" (no edit).
    - `H: false` → `H` alone is enough to discharge any goal; surface as inserting `H` at the cursor with no `?` follow-up.

  New query API: `eliminate_at(path, content, pos, label, prelude=()) -> Optional[WorkspaceEdit]`. The extra `label` arg is what differentiates this from the others — `pos` says *where to insert*; `label` says *which hypothesis to use*. Returns `None` when `label` isn't bound at `pos`'s scope, when the hypothesis's shape isn't in the table, or when the cursor isn't in a proof context.

  Wiring is the same shape as Steps 15–17 — additive in `__all__`, plus matching MCP tool `eliminate_at(path, line, column, label)` in `mcp_server.py`. The LSP side is slightly different from the others: `textDocument/codeAction` doesn't carry user input, so this surfaces as a custom server method `deduce/eliminateAt` that the client calls *after* prompting for the label. The MCP side just takes `label` as a tool argument; Claude already has the conversational context to pick a sensible one.

  Editor UX (`editor/emacs/deduce-lsp.el`, beyond the Step 6 keybindings already documented): bind `C-c C-e` to a command that `read-string`s for the label (with completion against the labels currently in scope, computed from the same `goal_at` env walk that powers `C-c C-g`'s givens panel) and then issues `deduce/eliminateAt`. Pressing RET on the empty input cancels.

  - *Acceptance:* fixtures for each shape (and/or/if-then/all/some/equality), keyed by a hypothesis label that the env binds at the cursor. Each asserts: the produced tactic parses; running `check` on the post-edit content surfaces a fresh hole at the inserted `?` (or, for the no-`?` cases like `false`, no hole). Plus boundary cases: a label that isn't in scope at the cursor returns `None`; a label whose formula is `true` returns `None` (or a stub edit with a comment-only template — pick one and pin it); the cursor outside any proof context returns `None`.
  - *Implementation:* `lsp/query.py:eliminate_at(path, content, pos, label, prelude=())` plus a companion `eliminable_vars_at(path, content, pos, prelude=()) -> tuple` for in-scope label completion.  Templates emitted (mirroring `proof_use_advice` in `proof_checker.py`): `P and Q` → `have h1: P by conjunct 1 of H` / `have h2: Q by conjunct 2 of H` / `?`; `P or Q` → `cases H` skeleton; `if P then Q` → `have h: Q by apply H to ?`; `all x:T. P` → `H[?, ?, ...]` (or `H<?, ?, ...>` for type quantifiers); `some x:T. P` → `obtain x1, ... where h: <body[subst]> from H`; `e1 = e2` → `replace H` skeleton; `false` → bare `H`; `true` → `None` ("the `true` fact is useless").  Custom request `deduce/eliminateAt` (label is user input, can't ride on `textDocument/codeAction`) plus `deduce/eliminableVarsAt` for completion.  Matching MCP tools.  Emacs binds `C-c C-e` to a command that `completing-read`s the label against `deduce/eliminableVarsAt` and issues the request; empty-input cancels.  9-case acceptance test in `test/lsp/test_eliminate.py`.

- [x] **Step 19: Fill hole with a given (issue #353).** A narrower sibling of Step 18: where eliminate picks a template by the *shape* of the chosen hypothesis, fill-from-given picks by formula *equality* — the chosen given's formula must equal the goal, and the replacement is just `conclude <goal> by <label>`. The proof checker already does this matching internally (`proof_advice` in `proof_checker.py` walks `env.dict` for `ProofBinding`s whose formula equals the goal); the LSP just surfaces it as an editor command.

  New query API: `fill_from_given_at(path, content, pos, label, prelude=()) -> Optional[WorkspaceEdit]` plus `matching_givens_at(path, content, pos, prelude=()) -> tuple[str, ...]`. Same wire shape as the eliminate pair — custom server methods `deduce/fillFromGivenAt` and `deduce/matchingGivensAt`, matching MCP tools, and an emacs `C-c C-f` binding that auto-applies on a single match (the prompt would just be a confirmation) and prompts via `completing-read` on multiple. Filters to local proof bindings only — theorems are referred to by name directly.

  - *Implementation:* `lsp/query.py:matching_givens_at` walks `IncompleteProof`'s stashed env for `ProofBinding`s whose formula equals the goal and returns the labels in declaration order; `fill_from_given_at` validates that `label` is among them and emits `WorkspaceEdit(... new_text="conclude <goal> by <label>")` covering the `?` token.  Filters out `Theorem`-typed bindings -- those are referred to by name directly, no `conclude … by` wrapping needed.  14-case acceptance test in `test/lsp/test_fill_from_given.py` covering single-match, multi-match completion list, no-match (returns `None`), label-not-in-scope, and the auto-apply / completing-read editor flow.

- [x] **Step 20: List in-scope `auto` rewrite rules (issue #404).**  Pure read-only query, no edit.  When Deduce silently rewrites a goal via an `auto` rule (or rejects a `replace` with *no need for replace because this equation is handled automatically*), the user wants to know which rule fired.  Today the recovery is `grep '^auto ' lib/*.pf`; the post-uniquify state already has the answer.

  New query API: `auto_rules_at(path, content, pos, prelude=()) -> tuple[AutoRule, ...]` plus a new frozen `AutoRule(name, equation, module)` dataclass added to `lsp/query.py` and `__all__`.  Order matches declaration order — the same order ``abstract_syntax.auto_rewrites`` tries equations when several share a head constructor.  MCP-only for v1: the issue notes the editor side is less load-bearing (the diagnostic surface that *needs* the answer is "no need for replace" and the agent can call the tool itself); skip the LSP custom request unless an editor consumer asks.

  - *Implementation:* `lsp/query.py:auto_rules_at` runs `check` once, then walks every module cached in `get_uniquified_modules()` for top-level `Auto` statements (always in scope — they were imported into the env before the user's file ran) and the user file's AST for the same nodes filtered to `location <= pos`.  Each rule's `equation` is resolved by looking up the referenced theorem's `what` in the same walk's `Theorem`/`Postulate` map.  MCP wrapper `auto_rules_at(path, line, column)` in `mcp_server.py`.  7-case acceptance test in `test/lsp/test_auto_rules.py` covering declaration order, position filtering, the empty case, and the dataclass shape; matching MCP wrapper test in `test/lsp/test_mcp_server.py`.

## Phase 5 — Debugger (gdb-style stepper for the functional fragment)

Tracking issue: [#239](https://github.com/jsiek/deduce/issues/239). Prior art: [PR #269](https://github.com/jsiek/deduce/pull/269) (Temperz87, Dec 2025), now stale — predates the `lsp/` infrastructure, in-process prelude caching, the per-statement cache, and the pure-functional uniquify refactor. Treat that PR as a working prototype that validates the hook locations; rebuild on top of today's daemon.

### Scope and non-goals

In scope: stepping through the *functional* fragment of Deduce — top-level statements (`Print` / `Assert`) and user-function calls evaluated during their reduction. Out of scope: stepping through proofs themselves (proofs are static derivations, not a stepwise execution; a future "explain this proof" UI is a tree viewer, not a stepper, and should not be jammed into DAP).

The natural unit of stepping is **one reduction step inside a `print` / `assert`**, plus call/return on user-defined functions. This matches PR #269's instincts and what `gdb` users expect.

### Architecture

```
lsp/
  query.py          ← protocol-neutral query API (Phase 1, locked)
  library.py        ← daemon, prelude cache (Phase 1)
  debugger.py       ← NEW: Debugger core, hook callbacks, REPL
  lsp_server.py     ← pygls (Phase 2)
  mcp_server.py     ← FastMCP (Phase 1)
  dap_server.py     ← NEW: stdio DAP adapter, thin wrapper over Debugger
```

Same shape as the LSP/MCP split: a protocol-neutral `Debugger` class, then thin wire-format adapters. The CLI `--debug` mode is a third client (writing to stdout, reading from stdin) on top of the same core. The DAP server is launched per-debug-session (not shared with the LSP daemon — a debug session blocks reduction, which would freeze any concurrent LSP request on the same process).

### Hook sites (validated by PR #269)

Three places in the existing pipeline need callbacks:

1. **`proof_checker.py:check_proofs`** — before/after each top-level statement. Fires for `Print` and `Assert` (the only statements that reduce user code), plus for `Theorem` if tactic-stepping is enabled (Step 24).
2. **`abstract_syntax.py:do_function_call`** — before/after every user-function reduction. The single layer that catches both `Lambda` and `RecFun` calls; PR #269's fix (also hooking `Call.reduce`'s `Lambda` arm and `do_recursive_call`'s case dispatch) double-fires and should not be carried over.
3. **`abstract_syntax.py:Call.reduce`** — only for `Lambda` literals applied directly. Lambdas don't go through `do_function_call` because they have no name binding; they need their own one-line hook.

All three sites read `flags.get_debugger()`. When it returns `None` (the default in non-debug runs), the callback is a no-op call into the `Debugger` class — measure overhead in PR 1's acceptance test, but expect <1% on the existing test suite. If overhead is measurable, gate the call on a `flags.debug` boolean to skip the function call entirely.

### Phase 5 plan

- [x] **Step 21: Foundation — `Debugger` core, daemon-aware.** Stand up `lsp/debugger.py` with a `Debugger` class owning all state (no module-level globals). Plumb through `lsp/library.py:check_file` as an optional `debugger=None` parameter; thread through `proof_checker.check_deduce` to the three hook sites. Replace PR #269's six-function module-globals API.

  Required interaction with prior phases:
    - **Bypass the per-statement cache** (Steps 13–14) when `debugger is not None`. Cache hits skip `check_proofs`, which would silently skip every debugger trap. Either short-circuit on the cache key or thread a "debugger active" bit into the key — short-circuit is simpler and the cache is valueless during a stepping session anyway.
    - **Prelude is loaded debugger-detached.** The CLI / DAP adapter calls `check_file` once with `debugger=None` to bootstrap the prelude (as today), then attaches the debugger for the user's file. This solves PR #269's "first prelude statement traps" bug without special-casing.
    - **Pure-functional uniquify** (commit bfc498a) means PR #269's uniquify-time `break_at_point` side-effect can't survive — drop the `Breakpoint` AST node entirely and use REPL-set breakpoints only (Step 22).

  CLI mode: `python deduce.py --debug file.pf` instantiates `Debugger(io=sys.stdin/stdout)` and passes it to `check_file`. The `--debug` flag from PR #269 is preserved verbatim.

  - *Acceptance:* `test/lsp/test_debugger.py` scripts the REPL via captured stdio against fixed inputs; `test/should-validate/` and `test/should-error/` runs unchanged (with and without `--debug`); benchmark from `lsp/benchmark.py` shows ≤1% overhead on non-debug runs.
  - *Implementation:* `lsp/debugger.py:Debugger` owns all per-session state (stack, last-command replay, ``stop_on_next_statement`` flag).  `flags.get_debugger()` / ``set_debugger()`` are the daemon-aware accessor pair; hook callsites short-circuit on ``None``.  Hook sites: ``proof_checker.check_proofs`` (top-level statements), ``abstract_syntax.do_function_call`` (every named user-function reduction -- single hook catches RecFun + GenRecFun + recursive case dispatch; PR #269's three-site approach double-fired), and the ``Lambda`` arm of ``Call.reduce``.  ``lsp/library.py:check_file`` gains a ``debugger=`` parameter; attached for the user-file check only (prelude bootstrap stays detached).  ``DebuggerQuit`` is propagated past ``_check_file_impl``'s ``except Exception`` so the outer handler can translate it into a normal failed ``CheckResult``.  Step 13/14 cache is bypassed when ``get_debugger()`` is not None.  CLI flag ``--debug`` constructs a stdio-driven ``Debugger`` and threads it through ``deduce_file`` / ``deduce_directory``.  Step 21's REPL is intentionally tiny -- ``continue`` and ``quit`` only -- so the wiring is independently reviewable; Step 22 adds the full command set.  9-case acceptance test in ``test/lsp/test_debugger.py``.

- [x] **Step 22: Step modes and breakpoints — gdb parity.** REPL commands, all keyed off the `Debugger` instance from Step 21:
    - `continue` / `c` — run until next breakpoint.
    - `step` / `s` — step into next reduction (current statement or function call).
    - `next` / `n` — step over: pause when call-stack depth ≤ depth at command time. (PR #269 keyed step-over on *location*, which re-traps on recursion — fix in this step.)
    - `finish` / `fin` — step out: pause when depth < depth at command time.
    - `break <file:line>` / `b <file:line>` — line breakpoint, resolved against `Meta.line` on first hit. Replaces PR #269's function-name-only `b foo`; function breakpoints stay as `b <name>` for ergonomics, dispatched on whether the arg parses as `name:int`.
    - `print <expr>` / `p <expr>` — parse and reduce arbitrary expression in the current env. Reuses the existing parser + `Term.reduce`.
    - `list` / `l` — show source ±5 lines around current location, reading the `.pf` file by `Meta.filename`.
    - `where` / `bt` — call stack maintained as `on_function` push / `after_function` pop on the `Debugger` instance.
    - `up` / `down` — move within the saved stack to inspect locals.
    - `locals` — dump captured `params_dict` for the current frame.
    - `quit` / `q` — abort the run cleanly (raises a `DebuggerQuit` that `check_file` translates to a normal `CheckResult`).

  Conditional breakpoints (`b foo:42 if x > 0`) are a small extension once `print <expr>` lands; bundle into this step.

  - *Acceptance:* `test/lsp/test_debugger_repl.py` with stdio-driven fixtures per command; recursion test pinning step-over correctness (the PR #269 regression).
  - *Implementation:* ``lsp/debugger.py`` grows a step-mode state machine (``_StepMode.{RUN, STEP, NEXT, FINISH, STOP}``) and a depth counter (``_step_depth``) keyed on ``len(self.stack)``.  ``next`` / ``finish`` set ``_step_depth = depth-at-command`` and compare it against ``len(self.stack)`` at every later hook -- that comparison is what fixes PR #269's location-keyed step-over re-trapping on recursion.  Breakpoints are stored as ``_Breakpoint(id, spec, condition)`` and matched on every hook in ``_should_pause_at_{statement,function}``.  ``spec`` is either ``"file:line"`` (dispatched by the colon) or a bare function name (matched against ``base_name(name)``).  Conditions parse a trailing ``" if <expr>"`` and reuse ``_eval_expr`` against the current env.  ``print`` and conditions both go through ``_eval_expr``: snapshot/restore ``rec_desc_parser``'s module-level state, lex+parse the expression, build a uniquify dict from the proof-checker env (inverting ``env.dict``'s unique-name keys back to base names) plus the current frame's params, uniquify, then ``reduce`` with ``reduce_all + eval_all`` so the printed value matches what ``print`` / ``assert`` would compute.  The recursive-function path's pattern-bound names (``subst``) are now plumbed through ``do_function_call``'s hook so ``locals`` and ``print n'`` work inside a ``double(suc(n'))`` case body.  ``list`` reads ``Meta.filename`` and prints ±5 lines around ``Meta.line``; ``where`` walks ``self.stack`` (gdb-style: frame 0 is innermost); ``up`` / ``down`` move a ``_frame_cursor`` and re-display ``where``; ``locals`` dumps the focused frame's params dict.  Unknown commands surface a typo suggestion via ``edit_distance.closest_keyword``.  20-case acceptance test in ``test/lsp/test_debugger_repl.py`` covers each command; ``test_next_doesnt_retrap_after_first_call`` pins the PR #269 recursion fix.

- [x] **Step 23: REPL UX polish.** Pretty-print values via the existing `__str__`; readline tab-completion for command names and in-scope variable names; persistent input history at `~/.config/deduce/debug_history`; empty-input replays last command (kept from PR #269); friendly error messages on unrecognized commands (suggest closest via `edit_distance`).

  - *Acceptance:* manual smoke test on `test/should-validate/comp_switchcase.pf`; `editor/emacs/test/`-style fixture tests for tab-completion.
  - *Implementation:* GNU ``readline`` is attached only when the REPL is talking to a real terminal (``sys.stdin.isatty()`` and the Debugger's input/output streams are sys.stdin/sys.stdout) -- tests pass ``StringIO`` and fall back to plain stream reads with no filesystem touch.  Completion routes through ``Debugger._complete(text, line, begidx)`` (pure function, tested directly) wrapped by ``_completer`` (the readline-facing entry point).  Context rules: ``begidx == 0`` returns command verbs; otherwise the first token selects the candidate set -- ``print`` / ``break`` get in-scope identifiers (base-name form of the proof-checker env's bindings plus the focused frame's pattern-bound names), ``clear`` gets active breakpoint specs plus in-scope names, ``delete`` gets active breakpoint ids.  Completer delimiters restricted to whitespace so names like ``operator-`` complete.  History stored at ``~/.config/deduce/debug_history`` (path overridable via ``Debugger(history_file=...)``); ``_save_history`` runs in a ``finally`` around the REPL loop so a session that crashes mid-flow doesn't lose history.  Empty-input replay and ``edit_distance``-based typo suggestions for unknown commands were already in place from Step 22.  11-case acceptance test in ``test/lsp/test_debugger_completion.py``.

- [ ] **Step 24: Tactic stepping (opt-in).** Add `--debug=tactics` (CLI) / `"tacticStepping": true` (DAP `launch` arg). When enabled, the `Term.reduce` path used by `evaluate` / `expand` / `replace` / `definition` / `rewrite` traps the same way `Print` reductions do, so users debugging "why didn't `expand` fire" can step in.

  Default off. The existing hooks already cover this — the gating logic lives in `Debugger.should_trap_reduction(env)`, which returns `False` unless tactic-stepping is enabled and the reduction was triggered by a tactic (detect via a stack tag set in `proof_checker.py` around the relevant `reduce` calls).

  - *Acceptance:* fixture proof exercising `expand`, with a scripted REPL session asserting traps fire only with `--debug=tactics`.

- [ ] **Step 25: DAP adapter.** `lsp/dap_server.py` as a sibling of `lsp_server.py` and `mcp_server.py`. Stdio transport, no shared daemon — each `launch` spawns its own process to keep the blocking-during-stepping behavior simple.

  Minimum DAP request set:

  | DAP request | Maps to `Debugger` op |
  | --- | --- |
  | `initialize` | declare capabilities (`supportsConditionalBreakpoints`, `supportsFunctionBreakpoints`, `supportsEvaluateForHovers`) |
  | `launch` | spawn `python deduce.py --debug --dap file.pf`; attach `Debugger(io=DAP)` |
  | `setBreakpoints` | `Debugger.set_file_breakpoints(path, lines, conditions)` |
  | `setFunctionBreakpoints` | `Debugger.set_function_breakpoints(names)` |
  | `configurationDone` | release initial pause |
  | `continue` / `next` / `stepIn` / `stepOut` | the four step modes from Step 22 |
  | `pause` | trip on next hook |
  | `threads` | always one thread (id 1) |
  | `stackTrace` | the stack from Step 22 |
  | `scopes` / `variables` | params from `on_function`, plus `env.get_value_of_term_var` for in-scope names |
  | `evaluate` | `parse_term + reduce(env)` (reuses Step 22's `print`) |
  | `disconnect` / `terminate` | unwind, exit |

  Out of scope for v1: `setExceptionBreakpoints` (Deduce's `MatchFailed` etc. are checker errors, not user-facing), `restart` (just relaunch), `goto` (no jump-to-line semantics).

  - *Acceptance:* `test/lsp/test_dap_server.py` using a small in-memory DAP client (one already exists in [`debugpy`](https://github.com/microsoft/debugpy) as a reference, but a 100-line stdio harness in the test directory is sufficient — DAP is straightforward JSON-RPC). Manual smoke from VS Code with the Step 26 extension.

- [ ] **Step 26: Editor packages.** Wire DAP into both editors:
    - **VS Code**: add a `debuggers` contribution to the existing extension's `package.json` (the extension already declares `deduce` as a language). Default launch config: `{"type": "deduce", "request": "launch", "program": "${file}"}`. Adapter command: `python -m lsp.dap_server`.
    - **Emacs**: `editor/emacs/deduce-dap.el` (~30 lines) registering `deduce` as a `dap-mode` debugger via `dap-register-debug-template`. Parallel to `editor/emacs/deduce-lsp.el`. Tests in `editor/emacs/test/deduce-dap-test.el` mirror the existing LSP test pattern.

  - *Acceptance:* manual smoke (the breakpoint UI is the load-bearing thing and isn't unit-testable). Document the launch flow in `editor/emacs/README.md` (debugger section) and the VS Code extension README.

### LSP integration: do we need protocol extensions?

**No.** LSP and DAP are sibling protocols; every editor that consumes LSP also has a DAP client (VS Code, Emacs `dap-mode`, Neovim `nvim-dap`, IntelliJ). Adding debugger-shaped requests to `lsp_server.py` would re-invent DAP.

The only thing that *could* go in LSP is a `deduce/runnableLines` custom request — a list of lines on which a breakpoint can be set, used by editors to grey out non-runnable gutter slots. Skip in v1; the editor can ask DAP `setBreakpoints` and read back which lines were validated. Add only if a downstream editor consumer asks.

### Cross-cutting notes for Phase 5

- The DAP adapter does **not** share a process with the LSP/MCP daemon. Stepping blocks reduction; a shared process would freeze concurrent LSP requests. Each DAP `launch` is its own process, which also matches how every other DAP server (debugpy, lldb-vscode, java-debug) is deployed.
- Step 21 is the highest-risk step (parallel to Step 6's prelude-cache work). Touches three pipeline files and interacts with two prior phases (cache invalidation, prelude bootstrap). Budget ~3 extra days.
- Steps 22–24 are independent of the DAP adapter and shippable as a CLI-only debugger after Step 23. Use the CLI for ~1 week before starting Step 25 — usage will tell you which commands actually matter and which DAP capabilities to expose.
- PR #269's source-level `break <expr>` keyword is **dropped**: it adds parser / AST / uniquify surface for a feature that REPL-set breakpoints cover better, and source-level markers fight git noise. If demand surfaces later, recover the parser change from PR #269 and integrate the `Breakpoint` AST node properly against today's pure-uniquify (non-trivial — needs `copy`, `substitute`, `__eq__`, type-check arm, and a `reduce` arm that doesn't double-fire with the `do_function_call` hook).

## Cross-cutting notes

- Add `lsp/` to the `make tests` target as a separate phase, otherwise it'll bitrot.
- Step 6 is the highest-risk step despite looking small. Budget ~3 extra days; expect to do part of Step 11's work early to make the test pass.
- Two-process-shared-library is the v1 deployment shape (one daemon per protocol, each loading the prelude). A shared-daemon-with-thin-frontends design over a Unix socket is a later option if duplicated startup cost actually hurts.
- Phase 3 (incrementality) and Phase 4 (structured editing) are independent; either can land first. Phase 4's per-call latency is dominated by the same `check` cost Phase 3 would shave, so doing Phase 3 first makes Phase 4's interactive latency snappier — but isn't a hard prerequisite.
