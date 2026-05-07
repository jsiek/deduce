# Emacs mode implementation plan

A self-contained Emacs major mode for Deduce proof files (`.pf`) with eglot-based LSP integration. Lives in `editor/emacs/`. Pairs with the LSP server from [docs/lsp-plan.md](lsp-plan.md).

**Status:** Step 1 in progress.

## Goals

1. Replace the third-party `deduce-mode` (mateidragony/deduce-mode) with an in-repo, maintained alternative.
2. Provide a keybinding-driven Agda-shape UX:
   - `M-.` go-to-definition (eglot's standard binding)
   - `C-c C-g` show the proof goal at point
   - `C-c C-r` refine the hole at point (Phase 4 / LSP Step 15)
   - `C-c C-c` case-split the variable at point (Phase 4 / LSP Step 16)
   - `C-c C-i` generate the induction skeleton (Phase 4 / LSP Step 17)
3. Stay minimal: targets Emacs 29+ (eglot is built-in), no third-party Elisp dependencies.

## Non-goals

- VS Code support — separate effort, comes later.
- `lsp-mode` (the alternative LSP client) — easy to add as a sibling file when wanted; eglot is the default.
- Inline code-lens UI for refactor actions — keybindings are the contract.

## Architecture

```
editor/emacs/
  deduce-mode.el        ; major mode + font-lock + indentation
  deduce-lsp.el         ; eglot registration + custom commands
  README.md             ; install + keybinding reference
```

`deduce-mode.el` is usable on its own (no LSP). `deduce-lsp.el` builds on it and adds the eglot wiring. Two files so a user can adopt syntax highlighting without committing to running the language server.

## Phase A — Mode without LSP

- [ ] **Step 1: Bare-bones major mode.** `define-derived-mode deduce-mode prog-mode`, syntax table for comments (`//` line, `/* */` block), file association `\.pf\'` → `deduce-mode`, package metadata. No font-lock, no indentation logic — just enough that opening a `.pf` file shows "Deduce" in the mode line and `M-;` toggles a `//` comment.
  - *Acceptance:* byte-compile clean (`emacs --batch -f batch-byte-compile`), open a `.pf` fixture, mode line shows "Deduce", `M-;` on a non-comment line inserts `// `, `M-;` on `// foo` removes it.

- [ ] **Step 2: Font-lock.** All Deduce keywords highlighted.
  - Statement-level: `theorem`, `lemma`, `define`, `function`, `union`, `predicate`, `relation`, `import`, `postulate`, `auto`, `assert`, `module`, `private`, `public`, `opaque`.
  - Proof tactics: `proof`, `end`, `arbitrary`, `assume`, `suppose`, `cases`, `case`, `switch`, `induction`, `replace`, `expand`, `obtain`, `recall`, `equations`, `equation`, `suffices`, `have`, `enough`, `with`, `where`, `from`, `by`, `for`, `definition`, `evaluate`, `transitive`, `symmetric`, `injective`, `extensionality`, `choose`, `apply`, `to`, `show`, `simplify`, `stop`.
  - Logical: `if`, `then`, `else`, `all`, `some`, `let`, `in`, `fn`, `λ`, `not`, `and`, `or`, `iff`, `true`, `false`, `array`.
  - Special faces: `?` and `sorry` rendered as `font-lock-warning-face`; constructor names (capitalized identifiers in declaration / pattern position) as `font-lock-type-face`; numeric literals as `font-lock-constant-face`.
  - *Acceptance:* a representative fixture renders the right colors for each face; an Elisp regression test that ert-asserts `(face-at-point)` at marked positions.

- [ ] **Step 3: Indentation.** Either an SMIE grammar (proper structural indent) or a small `indent-line-function` that handles the common cases: `proof` opens a block (indent +2), `end` closes it (indent -2 to match), `{` and `case` similarly. Electric pairs for `()`, `{}`, `[]`. Newline-and-indent on RET.
  - *Acceptance:* hand-crafted fixture with known correct indentation; an ert test that re-indents the buffer and diffs against the expected text.

## Phase B — LSP integration

- [ ] **Step 4: Eglot registration.** `deduce-lsp.el` registers `deduce-mode` with eglot pointing at `python3 -m lsp.lsp_server`. Optional `deduce-lsp-mode` minor mode that calls `eglot-ensure` for users who want auto-start. Customization variable `deduce-lsp-server-command` so users can override the python interpreter / path.
  - *Acceptance:* manual smoke (per the README): `M-x eglot` in a `.pf` buffer connects, diagnostics appear after save, `M-.` jumps to definitions, `M-x imenu` lists top-level symbols.

- [ ] **Step 5: Goal-at-point command.** `deduce-show-goal-at-point` (`C-c C-g`). Issues `deduce/goalAt` via `jsonrpc-request`, formats the response (formula + givens), pops up a `*Deduce Goal*` buffer in `view-mode`. Subsequent calls reuse the buffer.
  - *Acceptance:* fixture with a known cursor position (e.g. between `arbitrary` and `reflexive` in a simple equality proof), command opens the buffer with the expected formula text. Tested manually; no automation past byte-compile.

- [ ] **Step 6: Phase-4 keybindings (LSP-driven structured editing).** When the LSP server's Phase 4 lands (Steps 15–17), bind:
  - `C-c C-r` → `eglot-code-actions` filtered by kind `refactor.rewrite.deduce.refine`
  - `C-c C-c` → ditto for `refactor.rewrite.deduce.caseSplit`
  - `C-c C-i` → ditto for `refactor.rewrite.deduce.induction`
  Each wrapper passes `t` for the "apply if exactly one match" parameter so the user gets Agda's "no menu, just do it" feel.
  - *Acceptance:* keybindings exist and call the right eglot function; a small ert test stubs out `eglot-code-actions` and asserts the right kind argument is passed. End-to-end is a manual smoke once the server features land.

## Phase C — Polish

- [ ] **Step 7: README + customization.** `editor/emacs/README.md` with:
  - Install snippet for `init.el` (with and without `use-package`).
  - Prerequisites: Emacs 29+, `pip install -r requirements-lsp.txt`.
  - Keybinding reference table.
  - Troubleshooting (server not starting, eglot not finding the command, prelude bootstrap timing).

  Customization variables:
  - `deduce-mode-indent-offset` (default 2).
  - `deduce-lsp-server-command` (default `("python3" "-m" "lsp.lsp_server")`).
  - `deduce-lsp-prelude-disabled` (sets `DEDUCE_NO_STDLIB=1` in the spawned env).

  - *Acceptance:* the install snippet works on a fresh Emacs config (manually verified by the user — I can byte-compile but can't drive the Emacs UI).

## Cross-cutting notes

- I (the agent) can byte-compile the `.el` files and lint them. I cannot drive the Emacs UI. Manual smoke tests for Steps 4–7 are the user's job; the README documents them step-by-step.
- The mode targets Emacs 29+ specifically because eglot is built-in there and the `jsonrpc` library has a stable API. Older Emacs would need `package-install eglot` and possibly `compat`; not worth supporting.
- Phase 4 keybindings are stubs until the server's Phase 4 lands; they'll be no-ops (eglot will report "no code actions") in the meantime. That's a known and acceptable interim state.
