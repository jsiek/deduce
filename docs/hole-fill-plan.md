# Hole-fill plan: Claude proof-completion via emacs + LSP

Tracking issue: TBD. PR: [#357](https://github.com/jsiek/deduce/pull/357) (Phase 1 + Phase 2 + Phase 3 Step 7).

**Status:** Phase 1 + Phase 2 + Phase 3 Step 7 done. **Pluggable model backend** added on top: the sidecar now drives either Anthropic (Claude) or any OpenAI-compatible endpoint (Indiana University REALLMs is the recommended default for IU users; real OpenAI and local Ollama also supported). Whole stack end-to-end exercisable. Step 8 polish (cancellation, fallback buffer, mode-line indicator) is the natural next chunk.

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
                                       lsp/query.py:validate_proof_at  (NEW)
```

The sidecar talks to two parties: stdin/stdout with emacs (one-shot request/response) and JSON-RPC with the LSP daemon (for `deduce/validateProof` on each retry). emacs does not proxy validation traffic.

## Components

1. **LSP request `deduce/holeContextAt`** — returns goal, givens, lemmas-in-scope, and a fingerprint for the hole at the cursor. Sibling to the existing `deduce/goalAt`; richer payload, doesn't disturb the stable contract.
2. **Query function `validate_proof_at`** — splices a candidate proof at a hole range and re-runs the checker, returning `{ok, error}`. v0 calls `check_file` (warm-cheap thanks to the prelude snapshot in `lsp.library`); switches to the in-flight incremental-checking path once that lands. Independently useful: a "check this proof only" command in emacs is a natural future consumer.
3. **LSP request `deduce/validateProof`** — wraps `validate_proof_at` so the sidecar can call it over JSON-RPC.
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

- [x] **Step 3: `validate_proof_at` query function.** Added to `lsp/query.py` (not `lsp/library.py` -- mirrors every other `*_at` query, keeps the LSP adapter uniform). v0 splices `proof_text` into `content` at `hole_range` and re-runs `check_file`; the prelude snapshot in `lsp.library` makes that warm-cheap. The narrower `validate_proof_at` signature replaces the plan's original sketched `validate_theorem(loaded_module, theorem_name, replacement_proof_text)` -- the latter shape was for a future incremental "check one theorem in a loaded module" API and remains a follow-up; for the sidecar's needs, the splice-at-range form matches the LSP request shape (`{textDocument, holeRange, proofText}`) directly.
   - *Acceptance:* `test/lsp/test_validate_proof.py` (8 cases): valid proof returns ok, invalid proof returns ok=False with the checker's error message, range not on `?` is rejected, range out of bounds is rejected, two valid calls in a row each succeed (idempotency), failed call doesn't break the next valid call (rollback), end-to-end round-trip with `hole_context_at`, splice actually places the proof at the hole (a hypothesis-using proof works only because the splice is at the hole's range).

- [x] **Step 4: `deduce/validateProof` LSP request.** Wraps `validate_proof_at`. Params `{textDocument, holeRange, proofText}`, returns `{ok, error}`. Server splices the proof into its in-memory copy of the document and returns the result without writing to disk. Always returns a structured outcome (never `null`) so the sidecar has no separate "request failed" path; malformed params surface as `{ok: false, error: ...}`. New `_query_range_from_lsp` helper is the inverse of the existing `_lsp_range_from_query` (0->1 indexed); first request that takes a Range from LSP, so the helper hadn't existed yet.
   - *Acceptance:* 6 cases in `test/lsp/test_lsp_server.py`: valid proof, invalid proof carries the checker's error, unknown URI returns structured error, range not on a `?` is rejected, empty `proofText` is rejected by the checker (parse error, not a special case in the handler), missing URI returns structured error.

## Phase 2 — Sidecar

Both steps live under `tools/claude-fill-hole/`. Layout: `__main__.py`, `agent.py`, `validator.py`, `prompt.py`, `schema.py`, `README.md`, `tests/`.

- [x] **Steps 5 + 6: Sidecar (scaffolding + model loop in one PR slice).** Original plan split these but they're not separately useful: Step 5 alone with `--dry-run` is testable but doesn't do anything you'd actually want, so the work was bundled to give a runnable artifact. Layout: `tools/claude_fill_hole/{__init__.py, __main__.py, agent.py, prompt.py, schema.py, validator.py, README.md}` plus `requirements-fill-hole.txt` at repo root.

   **Naming deviation from plan:** the directory uses underscores (`tools/claude_fill_hole/`) not hyphens, so it's importable as a Python package. `python -m tools.claude_fill_hole` works.

   - `schema.py` — request/response dataclasses with camelCase ↔ snake_case mapping at the JSON boundary so emacs can forward the LSP `holeContextAt` response shape directly.
   - `validator.py` — `Validator` ABC + `SubprocessValidator` (the v0 backend: fork `deduce.py` on a hidden tempfile in the file's directory). `LspValidator` is a placeholder for when the in-flight incremental-checking work lands.
   - `prompt.py` — assembles system prompt from `gh_pages/doc/TacticsCheatSheet.md` + `CheatSheet.md` with `cache_control: {type: "ephemeral"}` so the cheatsheet cost is paid once per 5-minute window, not per attempt. Builds the per-request user message (goal + givens + lemmas + ~30-line excerpt around the hole).
   - `agent.py` — manual tool-use loop. Single tool: `validate_proof(proof_text)`. Uses `claude-opus-4-7`, `thinking={type: "adaptive"}`, `effort: "high"`. First-valid-wins. Duck-typed `client` so tests can inject a fake.
   - `__main__.py` — CLI: read JSON on stdin, run agent (or `--dry-run`), write JSON on stdout, stream NDJSON progress on stderr.
   - *Acceptance:* `test/claude_fill_hole/` with 26 passing tests covering schema round-trips, validator against the real `deduce.py` (success / failure / cleanup / idempotency / rollback / oversize cap / missing executable), the agent loop with a fake `anthropic` client (first-attempt success / retry success / budget exhaustion / no-tool-call / malformed input / API failure / progress callback / required request kwargs), and the `__main__` entry point (`--dry-run`, missing/malformed stdin, missing API key, hole-range OOB).
   - *Manual smoke confirmed:* dry-run pipeline drives `deduce.py --quiet` correctly and returns the structured `incomplete proof` error; `SubprocessValidator.validate("reflexive")` against a `P = P` goal returns `ok=True`.

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

## Phase 3 — emacs (this repo, `editor/emacs/`)

When the original plan was written the `deduce-mode` was a separate
repo; it has since moved into this repo, so Phase 3 lands as part
of the same PR as Phases 1 and 2.

- [x] **Step 7: `deduce-fill-hole` MVP.** [editor/emacs/deduce-fill-hole.el](../editor/emacs/deduce-fill-hole.el). Single command bound to `C-c C-f`, no cancellation, no fallback buffer. Async via `make-process`. Marker pair planted on the hole's range when the request goes out (start: insertion-type nil, end: insertion-type t). On completion the sentinel verifies markers still live, the text between them is still `?` (catches edits inside the hole), and the fingerprint matches a fresh `deduce/holeContextAt` (catches theorem-statement edits); on success splices in, on mismatch errors with a clear message and leaves the buffer untouched. One in-flight session per buffer; different buffers can fill in parallel. Customization: `deduce-fill-hole-{python-program,deduce-root,max-attempts,model,api-key-env,prelude-disabled,timeout}`.
   - *Acceptance:* 16 ert tests in [editor/emacs/test/deduce-fill-hole-test.el](../editor/emacs/test/deduce-fill-hole-test.el) covering sidecar command construction, CLI flag assembly, deduce-root resolution priority, request payload (file path + content + LSP fields, error without `buffer-file-name`), response parsing (success / failure / empty / malformed), LSP position translation, keybinding registration. Manual end-to-end smoke confirmed: emacs's `deduce-fill-hole--build-request` produces a JSON payload the sidecar accepts; `python -m tools.claude_fill_hole --dry-run` against the buffer-derived payload drives `deduce.py` correctly and surfaces the structured `incomplete proof` error.

- [ ] **Step 8: Polish.** `deduce-fill-hole-cancel` interactive command. `*deduce-claude-results*` fallback buffer for stale-marker / fingerprint-mismatch cases. Mode-line indicator (`[fill-hole #N attempt M/5]`). Concurrent sessions keyed by request-id. Per-request progress buffer.
   - *Acceptance:* `ert` tests for cancellation (SIGINT exit code routes correctly), concurrent sessions (two requests don't trample each other's markers), fallback buffer is populated correctly when fingerprints diverge.

## Phase 4 — Docs

- [ ] **Step 9: Documentation.** Section in this file marking Phase 1–3 status. README under `tools/claude-fill-hole/` covering the stdin/stdout contract, retry budget, security notes, and how to run the sidecar standalone. Pointer in `lsp-plan.md`'s related-plans section. Brief mention in CLAUDE.md if appropriate.

## Validation backend: subprocess vs. LSP

The sidecar's validator interface is narrow on purpose: `validate(proof_text) -> {ok, error}`. Two backends:

| Backend | When | Cost (warm) | Notes |
|---|---|---|---|
| `SubprocessValidator` | No LSP endpoint provided; offline use | ~0.9–1.4s/attempt warm, ~14s cold (no `.thm` cache) | Forks `python deduce.py --quiet` on a tempfile in the user's directory. Subprocess isolation is the security boundary. |
| `LspValidator` | `lspEndpoint` in stdin payload | bounded by `validate_proof_at` cost | Default once Step 4 lands. Drops to near-zero validation time once incremental checking lands on the library side. |

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

1. **LSP request tests** (Steps 1–4): `test/lsp/test_hole_context.py`, `test/lsp/test_validate_proof.py`, additions to `test/lsp/test_lsp_server.py`.
2. **Sidecar isolation tests** (Steps 5–6): under `tools/claude-fill-hole/tests/`. Validator tests use real `deduce.py`; agent tests use a fake `anthropic` client. Live-API smoke gated by `RUN_LIVE_TESTS=1`.
3. **emacs `ert` tests** (Steps 7–8): in the separate `deduce-mode` repo. Mock `make-process`; cover marker behavior, fingerprint mismatch routing, cancellation, concurrent sessions.

## Cross-cutting notes

- The LSP daemon is now responsible for long-running tasks on behalf of clients (the `validateProof` path can take seconds while the model is between attempts). Step 4's handler should be careful not to block other LSP requests — pygls handles concurrency at the protocol level, but `validate_proof_at` itself must be safe to call while a `didChange` is in flight. Probably means a per-document mutex.
- The sidecar duplicates the LSP's prelude-loading cost when running via `SubprocessValidator`, since each `deduce.py --quiet` invocation pays the warm cost. With `LspValidator` this disappears. One more reason `LspValidator` is the default.
- Adding `tools/` is a small precedent. If a second tool ever shows up (a CLI front end, a different model integration), it goes alongside.
- Once the incremental proof-checking work is far enough along to expose "revalidate one theorem against the existing env" cleanly, Step 3 should switch from the fallback `check_file`-with-swapped-source implementation to the cheap path. That's a one-PR follow-up, not a redesign.
