# Hole-fill plan: Claude proof-completion via emacs + LSP

Tracking issue: TBD.

**Status:** Design complete, no code yet.

**Related:** [`lsp-plan.md`](lsp-plan.md) — this feature consumes the LSP server and adds two new requests to it.

## Goal

A keyboard shortcut in `deduce-mode` (emacs) on a `?` hole sends the goal and givens (via the LSP) to Claude, which iteratively writes a proof, validates it (via the LSP), and inserts the validated text back into the buffer. Async — emacs stays interactive while Claude works.

## Architecture

```
emacs (deduce-mode repo)             Deduce repo
  deduce-fill-hole       ── stdio ──→  tools/claude-fill-hole/
        │                                       │
        │  LSP JSON-RPC                         │  LSP JSON-RPC
        ▼                                       ▼
   deduce/holeContextAt    (NEW)  ──→  lsp/lsp_server.py
   deduce/validateProof    (NEW)  ──→  lsp/query.py
                                       lsp/library.py:validate_theorem  (NEW)
```

The sidecar talks to two parties: stdin/stdout with emacs (one-shot request/response) and JSON-RPC with the LSP daemon (for `deduce/validateProof` on each retry). emacs does not proxy validation traffic.

## Components

1. **LSP request `deduce/holeContextAt`** — returns goal, givens, lemmas-in-scope, and a fingerprint for the hole at the cursor. Sibling to the existing `deduce/goalAt`; richer payload, doesn't disturb the stable contract.
2. **Library hook `validate_theorem`** — revalidates one theorem in a loaded module without re-running the prelude or unrelated declarations. Backed by the incremental proof-checking work being built in a parallel session; falls back to a fresh `check_file` of swapped-in source until incremental lands.
3. **LSP request `deduce/validateProof`** — wraps `validate_theorem` so the sidecar can call it over JSON-RPC.
4. **Sidecar** — Python process under `tools/claude-fill-hole/`, plain `anthropic` SDK with a manual tool-use loop. One model-facing tool: `validate_proof(proof_text)`.
5. **emacs side** — async command in the separate `deduce-mode` repo using `make-process`; marker pair + fingerprint to track holes through async.

## Architectural decisions (locked)

- **Plain `anthropic` SDK, not the Claude Agent SDK.** One tool, ~80 LoC of loop. Doesn't justify the abstraction layer.
- **Sidecar lives under `tools/claude-fill-hole/`, not `lsp/`.** It pulls in `anthropic` (heavy optional dep) and isn't part of the protocol-neutral query API. `tools/` is new but signals "developer tool, optional, may not be installed."
- **System prompt embeds `gh_pages/doc/TacticsCheatSheet.md` + `CheatSheet.md`** verbatim with cache-control. The user message carries the goal, givens, lemmas-in-scope, and a ~30-line excerpt around the hole.
- **First-valid-wins.** As soon as `validate_proof` returns ok, the sidecar emits the proof and exits. No "polish" passes.
- **Marker pair (primary) + goal/givens fingerprint (verification)** for hole identity across async. Marker handles concurrent edits in the same buffer; fingerprint catches the case where the surrounding theorem statement changed.
- **Stale insertion → side buffer.** If marker or fingerprint mismatches at completion time, the proof goes to `*deduce-claude-results*` for manual review, not into the source.

## Phase 1 — LSP support

- [ ] **Step 1: `hole_context_at` query function.** Add `HoleContext`, `LemmaInfo` dataclasses to `lsp/query.py`; implement `hole_context_at(path, content, pos, prelude=(), include_lemmas=True) -> Optional[HoleContext]`. Reuses the existing `_target_hole`, `_find_hole_at`, `_goal_from_exception` machinery (`lsp/query.py:405-423,484-587,910-911`). Lemma list comes from walking the post-typecheck AST for top-level `Theorem`/`Postulate` nodes; uses the same signature-rendering helper as `list_symbols`. Fingerprint is `sha256(goal + sorted-givens)`.
   - *Acceptance:* `test/lsp/test_hole_context.py` covering: hole at cursor with goal/givens, hole + lemmas, no hole at cursor → `None`, fingerprint stable under whitespace edits, fingerprint changes when goal changes, lemma list filtering, `include_lemmas=False` returns empty tuple. ~150 LoC + 8 cases.

- [ ] **Step 2: `deduce/holeContextAt` LSP request.** Add handler in `lsp/lsp_server.py` mirroring the existing `on_goal_at` (`lsp_server.py:131,437-480`). LSP-shaped (0-indexed) coordinates in/out. Don't modify `deduce/goalAt` — it's stable and used by the existing goal panel.
   - *Acceptance:* 4 cases in `test/lsp/test_lsp_server.py` reusing the `FakeServer` pattern: happy path, no-hole returns null, missing URI returns null, lemma list excluded when `includeLemmas=false`. ~80 LoC.

- [ ] **Step 3: `validate_theorem` library hook.** New entry point in `lsp/library.py`: `validate_theorem(module, theorem_name, replacement_proof_text) -> {ok, error}`. Mutates the named theorem's proof in the loaded module, runs only the proof-checking phase on that one theorem, rolls back on the way out. v0 implementation can fall back to a fresh `check_file` of swapped-in source if the incremental work isn't ready; switch to the cheap path once incremental lands. Independent value beyond hole-fill: a "check this theorem only" command in emacs is a natural consumer.
   - *Acceptance:* `test/lsp/test_validate_theorem.py` covering: valid replacement returns ok, invalid replacement returns structured error pointing at the theorem, replacement that breaks an unrelated theorem reports the unrelated error (regression check that scope is correct), idempotency (two valid replacements in a row), rollback (a failed replacement leaves the module re-checkable).

- [ ] **Step 4: `deduce/validateProof` LSP request.** Wraps `validate_theorem`. Params `{textDocument, holeRange, proofText}`, returns `{ok, error?}`. Server applies the proof to its in-memory copy of the module and returns the result without writing to disk.
   - *Acceptance:* 5 cases in `test/lsp/test_lsp_server.py`: valid proof, invalid proof, unknown URI, range that doesn't enclose a hole, `proofText` empty.

## Phase 2 — Sidecar

Both steps live under `tools/claude-fill-hole/`. Layout: `__main__.py`, `agent.py`, `validator.py`, `prompt.py`, `schema.py`, `README.md`, `tests/`.

- [ ] **Step 5: Sidecar scaffolding + `--dry-run`.** `schema.py`, `validator.py` with two pluggable backends (`SubprocessValidator` calling `python deduce.py --quiet` on a tempfile in the user's directory; `LspValidator` calling `deduce/validateProof`), `__main__.py` argparse + stdin reader. **No model calls yet.** `--dry-run` reads stdin, splices a known stub proof, validates, returns. New `requirements-fill-hole.txt` declares `anthropic>=0.40.0`. The `anthropic` import is isolated to `agent.py` (added in Step 6) so this step's tests don't need the dep.
   - *Acceptance:* validator tests against real fixtures (known-good proof → ok; known-bad proof → structured error; tempfile cleanup on subprocess error; timeout handling). Schema round-trip tests. `--dry-run` end-to-end test. ~250 LoC.

- [ ] **Step 6: Model loop.** `agent.py` runs the manual tool-use loop; `prompt.py` assembles the system prompt with cache control on the cheatsheet blocks. `__main__.py` learns the real flow: read stdin, build prompt, run loop, write stdout, NDJSON progress on stderr. Retry budget (default 5), first-valid-wins. Bounded backoff for API 429s independent of the proof-attempt budget.
   - *Acceptance:* `test/test_agent.py` with a fake `anthropic` client covering: success on first attempt, retry success, budget exhausted, model emits no tool call → fail, missing API key → exit 2, tool-result truncation. End-to-end smoke (gated by `RUN_LIVE_TESTS=1`) hits a real fixture against the live API. ~300 LoC + ~150 LoC tests.

### stdin / stdout contract

```json
// stdin
{
  "file": "/abs/path/to/proof.pf",
  "holeRange": { "start": {"line": 10, "character": 4},
                 "end":   {"line": 10, "character": 5} },
  "goal": "P = P",
  "givens": [ {"label": "H", "formula": "P or Q"} ],
  "lemmasInScope": [ {"name": "...", "signature": "...", "kind": "lemma"} ],
  "fingerprint": "sha256:...",
  "lspEndpoint": "stdio:///path/to/socket"   // optional; falls back to subprocess
}

// stdout (success)
{ "ok": true, "proof": "...", "attempts": 3, "fingerprint": "sha256:...",
  "model": "claude-opus-4-7", "elapsedMs": 12345,
  "validations": [ {"attempt": 1, "ok": false, "error": "..."}, ... ] }

// stdout (failure)
{ "ok": false, "error": "...", "attempts": 5, "validations": [...],
  "fingerprint": "sha256:..." }
```

### NDJSON progress events (stderr)

```
{"event": "start", "fingerprint": "...", "maxAttempts": 5}
{"event": "model_request", "attempt": 1}
{"event": "tool_call", "tool": "validate_proof", "attempt": 1, "proofPreview": "..."}
{"event": "tool_result", "attempt": 1, "ok": false, "errorTail": "..."}
{"event": "finish", "ok": true, "attempts": 3}
```

## Phase 3 — emacs (separate `deduce-mode` repo)

- [ ] **Step 7: `deduce-fill-hole` MVP.** Single command, no cancellation, no fallback buffer. Async via `make-process`. Marker pair planted on the hole's range when the request goes out. On completion: marker check + fingerprint check; on success splice in; on mismatch, signal an error message. Customization: `deduce-fill-hole-deduce-root`, `deduce-fill-hole-max-attempts`, `deduce-fill-hole-model`. ~200 LoC of elisp.
   - *Acceptance:* an `ert` test that mocks `make-process` and feeds canned stdout/stderr through the sentinel; asserts the success path inserts text and the marker-mismatch path errors cleanly.

- [ ] **Step 8: Polish.** `deduce-fill-hole-cancel` interactive command. `*deduce-claude-results*` fallback buffer for stale-marker / fingerprint-mismatch cases. Mode-line indicator (`[fill-hole #N attempt M/5]`). Concurrent sessions keyed by request-id. Per-request progress buffer.
   - *Acceptance:* `ert` tests for cancellation (SIGINT exit code routes correctly), concurrent sessions (two requests don't trample each other's markers), fallback buffer is populated correctly when fingerprints diverge.

## Phase 4 — Docs

- [ ] **Step 9: Documentation.** Section in this file marking Phase 1–3 status. README under `tools/claude-fill-hole/` covering the stdin/stdout contract, retry budget, security notes, and how to run the sidecar standalone. Pointer in `lsp-plan.md`'s related-plans section. Brief mention in CLAUDE.md if appropriate.

## Validation backend: subprocess vs. LSP

The sidecar's validator interface is narrow on purpose: `validate(proof_text) -> {ok, error}`. Two backends:

| Backend | When | Cost (warm) | Notes |
|---|---|---|---|
| `SubprocessValidator` | No LSP endpoint provided; offline use | ~0.9–1.4s/attempt warm, ~14s cold (no `.thm` cache) | Forks `python deduce.py --quiet` on a tempfile in the user's directory. Subprocess isolation is the security boundary. |
| `LspValidator` | `lspEndpoint` in stdin payload | bounded by `validate_theorem` cost | Default once Step 4 lands. Drops to near-zero validation time once incremental checking lands on the library side. |

Default: `LspValidator` when an endpoint is provided, `SubprocessValidator` otherwise.

## Risks and open questions

- **Validation cost.** Pre-incremental, 5 subprocess attempts cost 5–7s warm, dominating wall time. Post-incremental + `LspValidator`, validation is near-free; the model dominates. Plan v0 ships with subprocess fallback; switching backends is a one-file change.
- **Cold prelude.** Pre-incremental, no `.thm` cache → ~14s per validation, blowing the budget. Originally planned a fail-fast UX ("run `make tests-lib` first"). With incremental checking handling prelude warming structurally, this UX scaffolding is removed from the plan.
- **Security: model-generated `.pf` text.** Parsed by `deduce.py`, no Python `eval` or shell. Risk surface is (a) tempfile-write of arbitrary text — mitigated by `subprocess.run` with a list (no shell) and a max-length cap on `proof_text`; (b) `import` statements pulling in user `.pf` files — no worse than what the user could write themselves; (c) DOS the type checker — bounded by `--timeout`.
- **Hole identity.** Marker pair handles concurrent edits in the source buffer. Fingerprint catches goal-changed-while-thinking. `sha256(goal + sorted-givens)` deliberately excludes lemma names: a new lemma added between request and response shouldn't invalidate an otherwise valid proof. If this produces confusing results in practice (Claude's answer references a since-deleted lemma), tighten the fingerprint.
- **Concurrent fill-hole requests in the same buffer.** Two `?`s, two requests fired in parallel: each gets its own marker pair; the second's range may shift if the first applies first. Marker check catches this and routes the second result to the fallback buffer. v0 documents the limitation; auto-retry-with-refreshed-context is a follow-up.
- **Lemma list size.** Full `lib/` dump is ~50–100 theorems, ~5–15 kB. Cacheable in the system prompt. Ship the whole list in v0; revisit when it stops fitting in context.

## Test plan (cross-cutting)

Three tiers, mirroring the components:

1. **LSP request tests** (Steps 1–4): `test/lsp/test_hole_context.py`, `test/lsp/test_validate_theorem.py`, additions to `test/lsp/test_lsp_server.py`.
2. **Sidecar isolation tests** (Steps 5–6): under `tools/claude-fill-hole/tests/`. Validator tests use real `deduce.py`; agent tests use a fake `anthropic` client. Live-API smoke gated by `RUN_LIVE_TESTS=1`.
3. **emacs `ert` tests** (Steps 7–8): in the separate `deduce-mode` repo. Mock `make-process`; cover marker behavior, fingerprint mismatch routing, cancellation, concurrent sessions.

## Cross-cutting notes

- The LSP daemon is now responsible for long-running tasks on behalf of clients (the `validateProof` path can take seconds while the model is between attempts). Step 4's handler should be careful not to block other LSP requests — pygls handles concurrency at the protocol level, but `validate_theorem` itself must be safe to call while a `didChange` is in flight. Probably means a per-document mutex.
- The sidecar duplicates the LSP's prelude-loading cost when running via `SubprocessValidator`, since each `deduce.py --quiet` invocation pays the warm cost. With `LspValidator` this disappears. One more reason `LspValidator` is the default.
- Adding `tools/` is a small precedent. If a second tool ever shows up (a CLI front end, a different model integration), it goes alongside.
- Once the incremental proof-checking work is far enough along to expose "revalidate one theorem against the existing env" cleanly, Step 3 should switch from the fallback `check_file`-with-swapped-source implementation to the cheap path. That's a one-PR follow-up, not a redesign.
