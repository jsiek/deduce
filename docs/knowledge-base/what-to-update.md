# What to update

Deduce has a lot of internal working parts as well as external tools that rely on being up to date with the latest release of Deduce. This page is here to list what updates need to be made when a new change is added to a specific part of Deduce.

## Syntax changes

Any changes to the Deduce syntax should be reflected in the following places:


**Internal:**
- `Deduce.lark`: syntax rules for the lark parser
- `parser.py`: code for the lark parser
- `recursive-descent.py`: code for the recursive descent parser
- `abstract_syntax/`: code for AST nodes, proofs, declarations, environments,
  literals, rewriting, and cross-cutting AST operations. Keep the package
  facade compatible when adding public syntax classes or helpers.
- `gh_pages/scripts/keywords.py`: The list of known tokens mapping to token type should be updated.
- `gh_pages/js/codeUtils.js`: syntax highlighting for the site codeblocks.
- `gh_pages/js/sandbox.js`: syntax highlighting for live code monaco editor.

**Documentation (user-facing, under `gh_pages/doc/`):**
- `Reference.md`: add or update the alphabetical entry for the new construct, and cross-reference touches in any related entries.
- `SyntaxGrammar.md`: keep the `## Statements` list current when introducing a new top-level statement form.
- `CheatSheet.md`: add a row to the "Formula / Prove / Use" table when a new formula shape gains a canonical proof or elimination form.
- `TacticsCheatSheet.md`: add or update the corresponding row for any new or renamed tactic, and revise the "Common pitfalls" section if the change introduces a new gotcha.

When adding a new top-level documentation page under `gh_pages/doc/`, also add an entry for it to all four dictionaries in `gh_pages/scripts/convert.py` (`mdToHtmlName`, `mdToTitle`, `mdToDescription`, `mdToDeduceCode`), and link it from `Index.md`.

**In-tree editor integrations:**
- [`editor/vscode/`](../../editor/vscode/) — canonical VS Code extension.  Today: debugger contribution.  Roadmap: syntax highlighting, LSP client.
- [`editor/emacs/`](../../editor/emacs/) — Emacs major mode plus the LSP client (`deduce-lsp.el`), DAP client (`deduce-dap.el`), and LLM hole-fill front-end (`deduce-fill-hole.el`).

**External (legacy):**
- [HalflingHelper/deduce-mode](https://github.com/HalflingHelper/deduce-mode) — no longer maintained.  Replaced by in-tree `editor/vscode/`.
- [mateidragony/deduce-mode](https://github.com/mateidragony/deduce-mode) — early Emacs prototype, also superseded by the in-tree `editor/emacs/` package.

## Adding a new standard-library module

When a new top-level module is added under `lib/`, update:

- `gh_pages/doc/StandardLib.md`: add an entry for the new module (alphabetical order). Only list top-level module files — private helper files (e.g. `UIntAdd.pf`, `NatDiv.pf`) that are `public import`-ed from a main module should not be listed. If the module defines theorems, link both `<Name>.thm` and `<Name>.pf`; otherwise link only `<Name>.pf`.
- `lib/README.md`: keep the naming-convention notes accurate if the module introduces a new type prefix (e.g. `uint`, `nat`).
