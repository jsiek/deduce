# What to update

Deduce has a lot of internal working parts as well as external tools that rely on being up to date with the latest release of Deduce. This page is here to list what updates need to be made when a new change is added to a specific part of Deduce.

## Syntax changes

Any changes to the Deduce syntax should be reflected in the following places:


**Internal:**
- `Deduce.lark`: syntax rules for the lark parser
- `parser.py`: code for the lark parser
- `recursive-descent.py`: code for the recursive descent parser
- `abstract_syntax.py`: code for all of the AST nodes
- `gh_pages/doc/lib_generate.py`: generates the html files for the stdlib. (The list of known tokens mapping to token type should be updated and the safeHTMLify for additional operator symbols.)
- `gh_pages/js/codeUtils.js`: syntax highlighting for the site codeblocks.
- `gh_pages/js/sandbox.js`: syntax highlighting for live code monaco editor.

**External:**
- [deduce-mode (vscode)](https://github.com/HalflingHelper/deduce-mode#): Deduce extension for vscode.
- [deduce-mode (emacs)](https://github.com/mateidragony/deduce-mode#): Deduce package for emacs.
