# What to update

Deduce has a lot of internal working parts as well as external tools that rely on being up to date with the latest release of Deduce. This page is here to list what updates need to be made when a new change is added to a specific part of Deduce.

## Syntax changes

Any changes to the Deduce syntax should be reflected in the following places:


**Internal:**
- `Deduce.lark`: syntax rules for the lark parser
- `parser.py`: code for the lark parser
- `recursive-descent.py`: code for the recursive descent parser
- `abstract_syntax.py`: code for all of the AST nodes
- `gh_pages/scripts/keywords.py`: The list of known tokens mapping to token type should be updated.
- `gh_pages/js/codeUtils.js`: syntax highlighting for the site codeblocks.
- `gh_pages/js/sandbox.js`: syntax highlighting for live code monaco editor.

**Documentation (user-facing, under `gh_pages/doc/`):**
- `Reference.md`: add or update the alphabetical entry for the new construct, and cross-reference touches in any related entries.
- `SyntaxGrammar.md`: keep the `## Statements` list current when introducing a new top-level statement form.
- `CheatSheet.md`: add a row to the "Formula / Prove / Use" table when a new formula shape gains a canonical proof or elimination form.

**External:**
- [deduce-mode (vscode)](https://github.com/HalflingHelper/deduce-mode#): Deduce extension for vscode.
- [deduce-mode (emacs)](https://github.com/mateidragony/deduce-mode#): Deduce package for emacs.

## Adding a new standard-library module

When a new top-level module is added under `lib/`, update:

- `gh_pages/doc/StandardLib.md`: add an entry for the new module (alphabetical order). Only list top-level module files — private helper files (e.g. `UIntAdd.pf`, `NatDiv.pf`) that are `public import`-ed from a main module should not be listed. If the module defines theorems, link both `<Name>.thm` and `<Name>.pf`; otherwise link only `<Name>.pf`.
- `lib/README.md`: keep the naming-convention notes accurate if the module introduces a new type prefix (e.g. `uint`, `nat`).
