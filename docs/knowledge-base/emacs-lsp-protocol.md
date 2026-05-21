# Emacs deduce-lsp ↔ LSP server wiring

*Implementor notes. End users should read [`editor/emacs/README.md`](../../editor/emacs/README.md) instead.*

This document records the protocol-level connection between the Emacs
client (`editor/emacs/deduce-lsp.el`) and the LSP server
(`lsp/lsp_server.py`). The user-facing README deliberately hides this
information; this is where it lives so that anyone touching either
side can reconcile them.

## Client / server topology

- `deduce-lsp.el` registers a major-mode hook on `deduce-mode` that
  calls `eglot-ensure`. The launch command is
  `python3 -m lsp.lsp_server` (override via
  `deduce-lsp-server-command`).
- The server is implemented with [pygls][pygls] (>= 2.1.0). Older
  pygls (2.0.x) had a different API and will not work.
- The Emacs side uses `eglot`, which ships in-tree from Emacs 29 and
  exposes a stable `jsonrpc` API.

[pygls]: https://github.com/openlawlibrary/pygls

## Standard LSP requests used

| Emacs entry point        | LSP method                       |
| ------------------------ | -------------------------------- |
| `M-.`                    | `textDocument/definition`        |
| `M-x imenu`              | `textDocument/documentSymbol`    |
| `C-c C-r` (refine hole)  | `textDocument/codeAction` (action title `Refine hole`) |
| `C-c C-i` (induction)    | `textDocument/codeAction` (action title `Induction`)   |
| Save                     | `textDocument/publishDiagnostics` (server-pushed) |

The two `codeAction`-driven commands apply the named action directly
(no picker). The action title is the contract — if the server renames
either, the client breaks.

## Custom (`deduce/*`) requests

These are server-specific JSON-RPC methods. They are not part of LSP
proper.

| Emacs command          | Custom request(s)                              | Purpose                                               |
| ---------------------- | ---------------------------------------------- | ----------------------------------------------------- |
| `C-c C-g`              | `deduce/goalAt`                                | Goal + givens at point, rendered into a popup buffer |
| `C-c C-c` (case split) | `deduce/splittableVarsAt`, `deduce/caseSplitAt` | Two-step: enumerate splittable vars, then split on chosen one |
| `C-c C-e` (eliminate)  | `deduce/eliminableVarsAt`, `deduce/eliminateAt` | Two-step: enumerate eliminable hypotheses, then apply chosen one |
| `C-c C-f` (fill-from-given) | `deduce/matchingGivensAt`, `deduce/fillFromGivenAt` | Two-step: enumerate givens whose formula matches the goal, then splice the chosen one |
| `C-c C-l` (search-lemma) | `deduce/availableLemmasAt`, `deduce/insertLemma` | Two-step: enumerate ranked in-scope lemmas with unify tier + module, then splice the chosen one with a tier-aware template |
| `C-c C-a` (LLM fill)   | `deduce/holeContextAt`                         | Captures goal, givens, lemmas in scope, and a stable fingerprint for the `tools/claude_fill_hole` sidecar |

The two-step pattern (`*VarsAt` + `*At`) exists so that Emacs can
present a `completing-read` picker without the server having to
generate every possible expansion eagerly. The `?` under the cursor
is the unambiguous replacement target — the client never has to guess
which hole the user meant.

## Hole replacement targeting

The cursor position pinpoints the `?` to be replaced. All hole-filling
commands (refine, case-split, induction, eliminate, fill-from-given,
search-lemma, LLM fill) use this convention. Tests that pin the request shape live
in `editor/emacs/test/deduce-lsp-test.el`.

## LLM hole-fill sidecar

`C-c C-a` is structurally different: rather than a server round-trip,
the Emacs client issues `deduce/holeContextAt` to gather context, then
spawns `tools/claude_fill_hole` as a subprocess. The sidecar runs
asynchronously, validating candidate proofs by re-invoking
`deduce.py` (or, when wired up, the in-process incremental checker).
On completion the client checks the stable fingerprint to confirm the
buffer hasn't drifted, then splices in the validated proof.

The sidecar entry point and validation contract are documented at
[`tools/claude_fill_hole/README.md`](../../tools/claude_fill_hole/README.md).

## What to keep in sync when changing the protocol

If you rename a custom method, change the schema of a request /
response, or rename a code-action title, all three of these need to
move together:

1. The server method registration in `lsp/lsp_server.py`.
2. The Emacs command definition in `editor/emacs/deduce-lsp.el`.
3. The corresponding pinning test in
   `editor/emacs/test/deduce-lsp-test.el` (and the server-side test).

Also update this document.
