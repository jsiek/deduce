# deduce-mode for Emacs

A self-contained Emacs mode for the [Deduce][deduce] proof checker:
syntax highlighting + indentation in `deduce-mode.el`, plus optional
[eglot][eglot] integration in `deduce-lsp.el` that wires `.pf`
buffers to the LSP server in `lsp/lsp_server.py`.

[deduce]: https://github.com/jsiek/deduce
[eglot]: https://www.gnu.org/software/emacs/manual/html_mono/eglot.html

## Prerequisites

| Component                   | Required when                    | How to install                                  |
| --------------------------- | -------------------------------- | ----------------------------------------------- |
| Emacs **29.1** or newer     | always                           | `brew install emacs` / distro package           |
| Python 3.11+ with `lark`    | always (deduce.py itself)        | `pip install lark==1.2.2`                       |
| `pygls>=2.1.0`              | only if you load `deduce-lsp.el` | `pip install -r requirements-lsp.txt`           |

Emacs 29 is the minimum because `eglot` ships in-tree from 29 onward
and the `jsonrpc` library has a stable API there. Older Emacs would
need `package-install eglot` and `compat`; that path is not
supported.

## Quick start

### Without `use-package`

```elisp
;; ~/.emacs.d/init.el  (or ~/.emacs)
(add-to-list 'load-path "/path/to/deduce/editor/emacs")
(require 'deduce-mode)
(require 'deduce-lsp)         ; optional: omit for major mode only

;; If your .pf files live OUTSIDE the deduce repo, point the LSP
;; server at your checkout so `python3 -m lsp.lsp_server' resolves:
;; (setq deduce-lsp-deduce-root "~/src/deduce")
```

Opening any `.pf` file will then enter `deduce-mode` (registered via
`auto-mode-alist`) and, with `deduce-lsp` loaded, eglot will auto-
connect on first save.

### With `use-package`

```elisp
(use-package deduce-mode
  :load-path "/path/to/deduce/editor/emacs"
  :mode "\\.pf\\'")

(use-package deduce-lsp
  :load-path "/path/to/deduce/editor/emacs"
  :after (deduce-mode eglot)
  ;; :custom (deduce-lsp-deduce-root "~/src/deduce")
  )
```

### Major mode only (no LSP)

If you don't want eglot to auto-start, just skip
`(require 'deduce-lsp)`. You still get syntax highlighting and
indentation. You can also keep `deduce-lsp` loaded but disable the
auto-start hook:

```elisp
(setq deduce-lsp-auto-start nil)
;; ... and run M-x eglot manually when you want it.
```

## Features

`deduce-mode` (always on for `.pf` buffers):

- Syntax highlighting for keywords, types, theorem names, holes (`?`),
  string literals, and `--` / `/* */` comments.
- Indentation that matches `proof`/`end`, `case`/`{}`, and lines
  inside open brackets without trailing operators (TAB to indent).
- Sensible syntax-table entries (matched parentheses, comment
  syntax, word characters) for cursor motion and `C-M-f` /
  `C-M-b` over balanced expressions.

`deduce-lsp` (when loaded):

- Diagnostics on save (flymake-style underlines).
- `M-.` -- go to definition (`textDocument/definition`).
- `M-x imenu` -- outline of top-level declarations
  (`textDocument/documentSymbol`).
- `C-c C-g` -- show the proof goal at point in a popup buffer
  (custom `deduce/goalAt` request -- see below).
- `C-c C-r` -- refine the hole at point. Issues
  `textDocument/codeAction` filtered to `refactor.rewrite`, applies
  the first matching action's `WorkspaceEdit` directly (no picker).
  Templates by goal shape: `?, ?` for `P and Q`, `assume H: P\n?` for
  `if P then Q`, `arbitrary x:T\n?` for `all`, `choose ?\n?` for
  `some`, `reflexive` when both sides of an equation reduce to the
  same term.

## Keybindings

| Binding   | Command                          | Provided by    | Notes                                     |
| --------- | -------------------------------- | -------------- | ----------------------------------------- |
| `TAB`     | `deduce-mode-indent-line`        | `deduce-mode`  | Indent the current line                   |
| `M-.`     | `xref-find-definitions`          | eglot          | Jump to symbol's definition               |
| `M-,`     | `xref-go-back`                   | eglot          | Pop the xref stack                        |
| `M-x imenu` | `imenu`                        | eglot          | Outline of top-level declarations         |
| `C-c C-g` | `deduce-show-goal-at-point`      | `deduce-lsp`   | Goal + givens at cursor                   |
| `C-c C-r` | `deduce-lsp-refine-hole`         | `deduce-lsp`   | Apply LSP-suggested template at hole      |

Remaining Phase-4 keybindings (`C-c C-c` case split, `C-c C-i`
induction) will land when the server's Step 16 / Step 17 operations
do.

## Customization

All variables are `defcustom`s reachable via `M-x customize-group
RET deduce RET` or `M-x customize-group RET deduce-lsp RET`.

### `deduce-mode`

| Variable                    | Default | Effect                                         |
| --------------------------- | ------- | ---------------------------------------------- |
| `deduce-mode-indent-offset` | `2`     | Spaces per indentation step                    |

### `deduce-lsp`

| Variable                       | Default     | Effect                                                                 |
| ------------------------------ | ----------- | ---------------------------------------------------------------------- |
| `deduce-lsp-auto-start`        | `t`         | If non-nil, `eglot-ensure` runs on `deduce-mode` entry                 |
| `deduce-lsp-python-program`    | `"python3"` | Python interpreter used to launch `lsp.lsp_server`                     |
| `deduce-lsp-deduce-root`       | `nil`       | Path to a Deduce checkout; sets `PYTHONPATH` for the spawned server    |
| `deduce-lsp-prelude-disabled`  | `nil`       | If non-nil, sets `DEDUCE_NO_STDLIB=1` so the server skips the prelude  |

For full control over the launch command, `defun deduce-lsp-server-command`
in your `init.el` returning whatever list eglot should spawn.

## Troubleshooting

### "Server died" / `AttributeError` immediately after eglot starts

Check the Python side first:

```sh
python3 -m lsp.lsp_server </dev/null
```

The server should exit cleanly (it reads JSON-RPC from stdin; with
no input it terminates). If you get an `ImportError`, install the
LSP requirements: `pip install -r requirements-lsp.txt` from the
deduce repo root. Verify `pygls>=2.1.0` is what got installed --
2.0 had a different API and won't work.

### Server starts but `M-.` / `C-c C-g` always returns nothing

Most likely the server is launched outside the deduce repo and
can't import `lsp.lsp_server`. The fix is either:

1. Set `deduce-lsp-deduce-root` to your deduce checkout, or
2. Make sure `default-directory` is the repo root when you open
   the `.pf` file.

You can confirm by inspecting `M-x eglot-events-buffer` -- the
`initialize` reply should show the server's `serverInfo`. If the
buffer says "process exited abnormally," see the previous step.

### First `C-c C-g` is slow

Yes -- the first request bootstraps the prelude (~1s with the
`.thm` cache, ~13s without). Subsequent requests are warm. You can
disable the prelude entirely with `deduce-lsp-prelude-disabled = t`
if you don't need the standard library.

### Indentation is off

`deduce-mode-indent-line` uses a balanced-bracket / `proof`/`end`
matcher; it doesn't currently handle multi-line type signatures or
`case` placement perfectly. If `TAB` insists on a column you don't
want, just type the spaces yourself -- the indenter only fires when
you ask. SMIE-grade alignment is a future enhancement.

## Manual smoke test

After installing, verify the major mode:

1. Open `lib/Nat.pf`.
2. Confirm the mode line shows `Deduce` and the `theorem` / `proof`
   / `end` keywords are highlighted.
3. Press `TAB` on a few lines inside a `proof` block; the
   indentation should match the surrounding structure.

Then verify the LSP integration:

4. Wait for the eglot bootstrap to complete (watch the mode line
   for `[eglot:Deduce]`).
5. Place point on `equal` (any reference) and press `M-.` -- it
   should jump to the definition.
6. Press `M-x imenu RET` and confirm the top-level theorem names
   show up.
7. Place point inside a proof body (e.g. line 26 in `lib/Nat.pf`,
   the `IH` line of `equal_refl`) and press `C-c C-g`. A `*deduce
   goal*` popup should show the goal formula and any givens in
   scope.
8. In a scratch `.pf` buffer, type a theorem with a hole, e.g.

   ```
   theorem t: all P:bool. P = P
   proof
     ?
   end
   ```

   Place point on the `?` and press `C-c C-r`. The `?` should be
   replaced with `arbitrary P:bool\n?`. Press `C-c C-r` again on the
   inner `?`; it becomes `reflexive`.

## Development

Run the ert tests in batch mode (no GUI required):

```sh
emacs --batch -L editor/emacs -L editor/emacs/test \
      -l deduce-mode-test -f ert-run-tests-batch-and-exit
emacs --batch -L editor/emacs -L editor/emacs/test \
      -l deduce-lsp-test -f ert-run-tests-batch-and-exit
```

The end-to-end loop (subprocess server + real LSP traffic) is
impractical to drive from a batch process; the tests pin the
in-Emacs pieces (eglot registration, command construction,
keybindings, request shape) but the actual server interaction
relies on the manual smoke test above.

Byte-compile the sources to catch warnings:

```sh
emacs --batch -L editor/emacs \
      -f batch-byte-compile editor/emacs/deduce-mode.el editor/emacs/deduce-lsp.el
```

If a stale `.elc` file is loaded instead of the source, `M-x
load-file` on the `.el` will use the source directly. To remove
the byte-compiled artifacts entirely:

```sh
rm editor/emacs/*.elc editor/emacs/test/*.elc
```
