# deduce-mode for Emacs

A self-contained Emacs mode for the [Deduce][deduce] proof checker:
syntax highlighting + indentation in `deduce-mode.el`, plus optional
[eglot][eglot] integration in `deduce-lsp.el` that wires `.pf`
buffers to the LSP server in `lsp/lsp_server.py`. An optional
`deduce-fill-hole.el` adds Claude-powered hole filling on top.

[deduce]: https://github.com/jsiek/deduce
[eglot]: https://www.gnu.org/software/emacs/manual/html_mono/eglot.html

## Prerequisites

| Component                   | Required when                          | How to install                                  |
| --------------------------- | -------------------------------------- | ----------------------------------------------- |
| Emacs **29.1** or newer     | always                                 | `brew install emacs` / distro package           |
| Python 3.11+ with `lark`    | always (deduce.py itself)              | `pip install lark==1.2.2`                       |
| `pygls>=2.1.0`              | only if you load `deduce-lsp.el`       | `pip install -r requirements-lsp.txt`           |
| `anthropic>=0.40.0`         | only if you load `deduce-fill-hole.el` | `pip install -r requirements-fill-hole.txt`     |
| `openai>=1.50.0`            | only if you load `deduce-fill-hole.el` | `pip install -r requirements-fill-hole.txt`     |
| API key env var             | only if you load `deduce-fill-hole.el` | one of: `ANTHROPIC_API_KEY` (real Claude), `OPENAI_API_KEY` (real OpenAI), `REALLMS_API_KEY` (IU REALLMs) |

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
(require 'deduce-fill-hole)   ; optional: Claude hole filling, depends on deduce-lsp

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
  `textDocument/codeAction` and applies the action titled `Refine
  hole` directly (no picker). Templates by goal shape: `?, ?` for `P
  and Q`, `assume H: P\n?` for `if P then Q`, `arbitrary x:T\n?` for
  `all`, `choose ?\n?` for `some`, `reflexive` when both sides of an
  equation reduce to the same term.
- `C-c C-c` -- case split. Cursor must sit on a `?`. Issues
  `deduce/splittableVarsAt` to fetch the in-scope variables that
  case-split can target, prompts via `completing-read` (TAB
  completion) for which one to split on, then issues
  `deduce/caseSplitAt` with the chosen variable. Replaces the `?`
  with a `switch x { case Cons1(...) { ? } ... }` skeleton (for
  term variables of `Union` type) or `cases H\n  case h1: P { ? }
  ...` (for proof variables of `P or Q` shape). The `?` under the
  cursor is unambiguously the replacement target -- no surprise
  inserts at the wrong hole.
- `C-c C-i` -- induction skeleton. Cursor on a `?` whose goal is
  `all x:T. P(x)` (T a `Union` with at least two constructors).
  Issues `textDocument/codeAction` and applies the action titled
  `Induction` directly (no picker). Replaces the `?` with
  `induction T\n  case Cons1(...) { ? }\n  case Cons2(...) assume
  IH<N>: ... { ? }\n...` -- one case per constructor in declaration
  order; recursive parameters get `IH<N>` bindings whose formula is
  the body with the inducted variable substituted.
- `C-c C-e` -- eliminate / use-fact. Cursor on a `?`. Issues
  `deduce/eliminableVarsAt` to fetch the in-scope hypothesis labels
  whose formula has a supported template, prompts via
  `completing-read` (TAB completion) for which label to use, then
  issues `deduce/eliminateAt` with the chosen label. The template
  depends on the hypothesis's shape: destructure for `and`, `cases`
  for `or`, `apply ... to ?` for `if then`, `H[?]` for `all`,
  `obtain ... from H` for `some`, `replace H` for equality, the
  bare label for `false`. Dual to `C-c C-r` (refine): refine picks
  by goal shape, eliminate picks by named-hypothesis shape.
- `C-c C-f` -- fill hole with a given. Cursor on a `?`. Issues
  `deduce/matchingGivensAt` to fetch the in-scope hypothesis labels
  whose formula equals the goal, then issues
  `deduce/fillFromGivenAt` with a chosen label and replaces the `?`
  with `conclude <goal> by <label>`. With a single match, applies
  it directly (no prompt). With multiple matches, prompts via
  `completing-read` (TAB completion). A narrower sibling of `C-c
  C-e`: eliminate picks by hypothesis shape; fill-from-given picks
  by formula equality with the goal.

`deduce-fill-hole` (additional, requires an LLM API key — Anthropic,
OpenAI, or IU REALLMs depending on backend choice):

- `C-c C-a` -- ask an LLM to fill the `?` at point ("ask AI"). Issues
  `deduce/holeContextAt` to capture the goal, givens, lemmas in
  scope, and a stable fingerprint, then spawns the
  `tools/claude_fill_hole` sidecar asynchronously. Emacs stays
  interactive while the model iterates (up to
  `deduce-fill-hole-max-attempts` `validate_proof` calls; first valid
  proof wins). On completion, if the markers around the hole are
  still live and the fingerprint hasn't changed, the validated
  proof is spliced in; otherwise the command errors and leaves the
  buffer untouched. One fill-hole per buffer at a time; multiple
  buffers can fill in parallel.

## Keybindings

| Binding   | Command                          | Provided by    | Notes                                     |
| --------- | -------------------------------- | -------------- | ----------------------------------------- |
| `TAB`     | `deduce-mode-indent-line`        | `deduce-mode`  | Indent the current line                   |
| `M-.`     | `xref-find-definitions`          | eglot          | Jump to symbol's definition               |
| `M-,`     | `xref-go-back`                   | eglot          | Pop the xref stack                        |
| `M-x imenu` | `imenu`                        | eglot          | Outline of top-level declarations         |
| `C-c C-g` | `deduce-show-goal-at-point`      | `deduce-lsp`   | Goal + givens at cursor                   |
| `C-c C-r` | `deduce-lsp-refine-hole`         | `deduce-lsp`   | Apply LSP-suggested template at hole      |
| `C-c C-c` | `deduce-lsp-case-split`          | `deduce-lsp`   | Prompt for variable, replace `?` with case skeleton |
| `C-c C-i` | `deduce-lsp-induction`           | `deduce-lsp`   | Replace `?` with `induction T` skeleton at a forall goal |
| `C-c C-e` | `deduce-lsp-eliminate`           | `deduce-lsp`   | Prompt for hypothesis, replace `?` with use-fact tactic |
| `C-c C-f` | `deduce-lsp-fill-from-given`     | `deduce-lsp`   | Replace `?` with `conclude ... by H` for a given matching the goal |
| `C-c C-a` | `deduce-fill-hole`               | `deduce-fill-hole` | Ask an LLM to fill the `?` at point. Async, non-blocking. |

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

### `deduce-fill-hole`

| Variable                              | Default                       | Effect                                                      |
| ------------------------------------- | ----------------------------- | ----------------------------------------------------------- |
| `deduce-fill-hole-backend`            | `'anthropic`                  | `'anthropic` (Claude via Anthropic API) or `'openai-compat` (REALLMs / OpenAI / Ollama) |
| `deduce-fill-hole-base-url`           | `nil`                         | OpenAI-compat endpoint URL; e.g. `"https://reallms.rescloud.iu.edu/direct/v1"`. Ignored when backend is `'anthropic`. |
| `deduce-fill-hole-model`              | `nil` (backend default)       | Model id; backend default is `"claude-opus-4-7"` (anthropic) or `"Qwen3-Coder-Next"` (openai-compat) |
| `deduce-fill-hole-api-key-env`        | `nil` (backend default)       | Env var name; backend default is `"ANTHROPIC_API_KEY"` or `"OPENAI_API_KEY"`. IU REALLMs users override to `"REALLMS_API_KEY"`. |
| `deduce-fill-hole-python-program`     | `"python3"`                   | Python interpreter used to launch the sidecar               |
| `deduce-fill-hole-deduce-root`        | `nil`                         | Path to a Deduce checkout; falls back to `deduce-lsp-deduce-root`, then `project-root`, then cwd |
| `deduce-fill-hole-max-attempts`       | `5`                           | Maximum number of `validate_proof` calls per invocation     |
| `deduce-fill-hole-prelude-disabled`   | `nil`                         | If non-nil, sidecar invokes `deduce.py --no-stdlib`         |
| `deduce-fill-hole-timeout`            | `60`                          | Per-validate-proof timeout passed to the sidecar (seconds)  |

**IU REALLMs preset** — drop this in your `init.el` to point at REALLMs:

```elisp
(with-eval-after-load 'deduce-fill-hole
  (setq deduce-fill-hole-backend 'openai-compat
        deduce-fill-hole-base-url "https://reallms.rescloud.iu.edu/direct/v1"
        deduce-fill-hole-api-key-env "REALLMS_API_KEY"
        deduce-fill-hole-model "Qwen3-Coder-Next"))
```

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
9. In a scratch `.pf` buffer with a custom union, e.g.

   ```
   union N {
     z
     s(N)
   }

   theorem t: all x:N. x = x
   proof
     arbitrary x:N
     ?
   end
   ```

   Place point on the `?` and press `C-c C-c`. Emacs prompts `Case
   split on:` with TAB completion against the splittable variables
   in scope (`x` for this fixture). Type `x RET`. The `?` is
   replaced with `switch x { case z { ? } case s(n1) { ? } }`. Each
   branch is now its own hole that `C-c C-r` / `C-c C-c` can refine
   further.
10. In a scratch `.pf` buffer with the same `N` union, but with the
    `?` *before* `arbitrary`:

    ```
    union N {
      z
      s(N)
    }

    theorem t: all x:N. x = x
    proof
      ?
    end
    ```

    Place point on the `?` and press `C-c C-i`. The `?` should be
    replaced with `induction N\n  case z { ? }\n  case s(n1) assume
    IH1: n1 = n1 { ? }`. The recursive constructor `s` gets an `IH1`
    binding for the predecessor `n1`.
11. In a scratch `.pf` buffer with a hypothesis to eliminate:

    ```
    theorem t: all P:bool, Q:bool. if P or Q then Q or P
    proof
      arbitrary P:bool, Q:bool
      assume H: P or Q
      ?
    end
    ```

    Place point on the `?` and press `C-c C-e`. Emacs prompts
    `Eliminate on:` with TAB completion against the eliminable
    hypotheses in scope (`H` for this fixture). Type `H RET`. The
    `?` is replaced with `cases H\n  case h1: P { ? }\n  case h2: Q
    { ? }`. Try the same with an `assume H: P and Q` hypothesis to
    see the destructuring template, or `assume H: P = Q` to see
    `replace H`.
12. In a scratch `.pf` buffer with a given that already matches the
    goal:

    ```
    theorem t: all P:bool. if P then P
    proof
      arbitrary P:bool
      assume H: P
      ?
    end
    ```

    Place point on the `?` and press `C-c C-f`. There is exactly
    one matching given (`H: P` matches the goal `P`), so the `?` is
    replaced directly -- no prompt -- with `conclude P by H`. With
    two matching givens in scope (e.g. `assume H1: P` and `assume
    H2: P`), Emacs prompts `Fill from:` with TAB completion against
    the matching labels.

If you have `deduce-fill-hole` loaded and `ANTHROPIC_API_KEY`
exported, also verify the Claude path:

12. Smoke-test the sidecar standalone first (no API key needed):

    ```sh
    pip install -r requirements-fill-hole.txt
    cat > /tmp/req.json <<'EOF'
    {"file": "/tmp/smoke.pf",
     "holeRange": {"start": {"line": 3, "character": 2},
                   "end":   {"line": 3, "character": 3}},
     "goal": "P = P", "givens": [], "lemmasInScope": [],
     "fingerprint": "fp",
     "content": "theorem t: all P:bool. P = P\nproof\n  arbitrary P:bool\n  ?\nend\n"}
    EOF
    python3 -m tools.claude_fill_hole --dry-run --no-stdlib \
      --deduce-root . < /tmp/req.json
    ```

    The dry-run reports `ok: false` with a structured `incomplete
    proof` error (the stub it sends is `?`, which never validates).
    What you're checking is that the splice + subprocess pipeline
    works -- if you see the goal text in `errorTail`, the sidecar
    is wired correctly.

13. In a scratch `.pf` buffer with the same `theorem t: all P:bool.
    P = P` shape, place point on the `?` and press `C-c C-a`
    ("ask AI"). Emacs reports `deduce-fill-hole: asking...`. Within a
    few seconds (depending on `effort` and how many attempts it
    takes), the `?` is replaced with the validated proof and you
    get a `filled in N attempts` message. If the API key is
    missing, the sidecar surfaces a structured error and the buffer
    is untouched.

## Development

Run the ert tests in batch mode (no GUI required):

```sh
emacs --batch -L editor/emacs -L editor/emacs/test \
      -l deduce-mode-test -f ert-run-tests-batch-and-exit
emacs --batch -L editor/emacs -L editor/emacs/test \
      -l deduce-lsp-test -f ert-run-tests-batch-and-exit
emacs --batch -L editor/emacs -L editor/emacs/test \
      -l deduce-fill-hole-test -f ert-run-tests-batch-and-exit
```

The end-to-end loop (subprocess server + real LSP traffic) is
impractical to drive from a batch process; the tests pin the
in-Emacs pieces (eglot registration, command construction,
keybindings, request shape) but the actual server interaction
relies on the manual smoke test above.

Byte-compile the sources to catch warnings:

```sh
emacs --batch -L editor/emacs \
      -f batch-byte-compile editor/emacs/deduce-mode.el \
      editor/emacs/deduce-lsp.el editor/emacs/deduce-fill-hole.el
```

If a stale `.elc` file is loaded instead of the source, `M-x
load-file` on the `.el` will use the source directly. To remove
the byte-compiled artifacts entirely:

```sh
rm editor/emacs/*.elc editor/emacs/test/*.elc
```
