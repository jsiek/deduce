# deduce-mode for Emacs

A self-contained Emacs mode for the [Deduce][deduce] proof checker.
Three layers, each independently usable:

- **`deduce-mode`** — syntax highlighting and indentation for `.pf`
  files.
- **`deduce-lsp`** *(optional)* — structured editing backed by a
  language server: jump to definition, outline of top-level
  declarations, show the proof goal at point, and a family of
  hole-filling commands (refine, case split, induction skeleton,
  eliminate hypothesis, fill from a matching given). Diagnostics
  appear inline as you save.
- **`deduce-fill-hole`** *(optional)* — ask an LLM to fill the hole at
  point. Validated proofs only; the LLM's output is checked before
  it is spliced into your buffer.
- **`deduce-dap`** *(optional)* — drive the `python deduce.py --debug`
  command-line debugger through `dap-mode`, so gutter breakpoints,
  the call-stack pane, and the locals view all work directly from
  your `.pf` buffer.

[deduce]: https://github.com/jsiek/deduce

## Prerequisites

### Always

- **Emacs 29.1 or newer.** Install via `brew install emacs` or your
  distro package. Emacs 29 is the minimum because eglot ships in
  Emacs from version 29 onward; older Emacs is not supported.
- **Python 3.12+ with `lark`.** Required to run `deduce.py` itself:
  `pip install lark==1.2.2`.

### For LSP capabilities (`deduce-lsp`)

- **`pygls>=2.1.0`** — the language-server framework the Deduce LSP
  is built on. Install with `pip install -r requirements-lsp.txt`
  from the repo root. (pygls 2.0.x had a different API and will not
  work.)

### For the debugger (`deduce-dap`)

- **`dap-mode`** — the third-party package that drives the
  graphical debug UI.  Install from MELPA:
  `M-x package-install RET dap-mode RET`.  No specific minimum
  version; `dap-mode` 0.7 or later is widely tested.
- **The DAP adapter itself** is already part of the Deduce
  checkout (`lsp/dap_server.py`) and inherits the `python3 +
  lark` prerequisite listed above.  Make sure the Python you
  point `deduce-dap-python-program` at (default `"python3"`) is
  the one that has `lark` — see the troubleshooting entry below
  for the common pitfall.

### For LLM-powered hole filling (`deduce-fill-hole`)

- **`anthropic>=0.40.0`** and **`openai>=1.50.0`** — install both
  with `pip install -r requirements-fill-hole.txt` from the repo
  root. Which one is used at runtime depends on your backend choice
  (see `deduce-fill-hole-backend` under Customization).
- **An API key in your environment.** Pick one based on your
  provider:
  - `ANTHROPIC_API_KEY` — direct Anthropic API (Claude).
  - `OPENAI_API_KEY` — OpenAI or any OpenAI-compatible endpoint
    (e.g. a local Ollama server).
  - `REALLMS_API_KEY` — IU's REALLMs gateway.

  Add a line like the following to your shell initialization script
  (`~/.bashrc`, `~/.zshrc`, or `~/.config/fish/config.fish`) so the
  key is exported into every shell — Emacs picks it up from the
  environment of whichever shell launched it:

  ```sh
  export ANTHROPIC_API_KEY='sk-ant-...'
  ```

  Reload the shell (or open a new terminal) and confirm with
  `echo $ANTHROPIC_API_KEY`. On macOS, if you launch Emacs from the
  Dock rather than from a terminal, you will likely also want
  [exec-path-from-shell][epfs] so Emacs inherits the same
  environment as your interactive shell.

[epfs]: https://github.com/purcell/exec-path-from-shell

## Quick start

Pick one of the two install styles below: `use-package` is more
declarative and is the standard choice in modern Emacs configs, but
it adds a layer that not everyone wants. **If you don't have a
preference, use `use-package`** — it is built into Emacs 29 and
keeps the configuration tidy. Otherwise, use the plain `require`
form.

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

(use-package deduce-dap
  :load-path "/path/to/deduce/editor/emacs"
  :after (deduce-mode dap-mode)
  ;; :custom (deduce-dap-python-program "python3.13")
  )
```

### Without `use-package`

```elisp
;; ~/.emacs.d/init.el  (or ~/.emacs)
(add-to-list 'load-path "/path/to/deduce/editor/emacs")
(require 'deduce-mode)
(require 'deduce-lsp)         ; optional: omit for major mode only
(require 'deduce-fill-hole)   ; optional: LLM hole filling, depends on deduce-lsp
(require 'deduce-dap)         ; optional: debugger; requires dap-mode from MELPA

;; If your .pf files live OUTSIDE the deduce repo, point the LSP
;; server at your checkout so the language server can be found:
;; (setq deduce-lsp-deduce-root "~/src/deduce")
;; And/or pin the python interpreter for the debug adapter:
;; (setq deduce-dap-python-program "python3.13")
```

Opening any `.pf` file will then enter `deduce-mode` (registered via
`auto-mode-alist`) and, with `deduce-lsp` loaded, the language server
will auto-connect on first save.

### Major mode only (no LSP)

If you don't want the language server to auto-start, just skip
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

- **Diagnostics on save.** When you save a `.pf` buffer, the language
  server re-checks the file and reports any errors back to Emacs.
  Each error is marked with a colored
  squiggle drawn under the offending text directly in the buffer.
  Hover the cursor on an underlined region to see the
  error message in the echo area, or run `M-x flymake-show-buffer-diagnostics`
  for a list view of every error in the file.
- `M-.` — **go to definition.** Jump from a name to where it is
  declared. `M-,` pops back.
- `M-x imenu` — **outline of top-level declarations.** Browse the
  theorems, definitions, unions, etc. in the current file.
- `M-TAB` (or `C-M-i`) — **in-buffer completion.** Eglot registers
  itself as a CAPF when the server advertises completion
  capability (which the Deduce LSP server does as of Step 31), so
  the standard `completion-at-point` keybinding works without
  extra config.  The candidate set is Deduce keywords + every
  top-level name reachable from the file (own theorems / defines /
  unions / constructors / predicates / rules, plus the transitive
  walk through imports — so `import Nat` brings in `suc`, `zero`,
  `+`, `length`, ...) **plus the in-scope local bindings at the
  cursor** (proof labels from `assume`, term variables from
  `arbitrary` and pattern-bound names from `switch` / `case`).
  When the cursor sits on a `?` and a local label's formula
  matches the goal, that label is sorted first in the picker via
  the LSP `sortText` field — so completion on a hole shows the
  proof terms that can plausibly close it before the rest.  Set
  `(setq tab-always-indent 'complete)` in your config if you want
  plain `TAB` to fall through to completion when indentation
  would be a no-op.
- `C-c C-g` — **show the proof goal at point** in a popup buffer,
  along with the givens (named hypotheses) currently in scope.
- `C-c C-r` — **refine the hole at point.** Replaces a `?` with a
  template chosen by the goal's shape: `?, ?` for `P and Q`,
  `assume H: P\n?` for `if P then Q`, `arbitrary x:T\n?` for `all`,
  `choose ?\n?` for `some`, `reflexive` when both sides of an
  equation reduce to the same term.
- `C-c C-e` — **eliminate / use-fact.** Cursor on a `?`. Emacs prompts
  for a hypothesis label (TAB completion against the in-scope
  hypotheses whose shape matches a supported template). The
  template depends on the hypothesis's shape: destructure for `and`,
  `cases` for `or`, `apply ... to ?` for `if then`, `H[?]` for
  `all`, `obtain ... from H` for `some`, `replace H` for equality,
  the bare label for `false`. Dual to `C-c C-r` (refine): refine
  picks by goal shape, eliminate picks by named-hypothesis shape.
- `C-c C-c` — **case split.** Cursor must sit on a `?`. Emacs prompts
  (with TAB completion) for which in-scope variable to split on,
  then replaces the `?` with a `switch` skeleton (one branch per
  constructor) for term variables, or a `cases H` skeleton for proof
  variables of `P or Q` shape. The `?` under the cursor is the
  unambiguous replacement target — no surprise inserts at the wrong
  hole.
- `C-c C-i` — **induction skeleton.** Cursor on a `?` whose goal is
  `all x:T. P(x)` (T a `Union` with at least two constructors).
  Replaces the `?` with `induction T` followed by one case per
  constructor in declaration order; recursive parameters get `IH<N>`
  bindings whose formula is the body with the inducted variable
  substituted.
- `C-c C-f` — **fill hole with a matching given.** Cursor on a `?`.
  If exactly one in-scope given's formula equals the goal, the `?`
  is replaced directly with `conclude <goal> by <label>`. With
  multiple matches, Emacs prompts (TAB completion) for which one to
  use. A narrower sibling of `C-c C-e`: eliminate picks by
  hypothesis shape; fill-from-given picks by formula equality with
  the goal.
- `C-c C-l` — **lemma search at point.** Cursor on a `?`. Emacs
  fetches the ranked list of in-scope theorems, lemmas, and
  postulates from the server and prompts (TAB completion) for one
  via `completing-read`. Each row is annotated with the *unify
  tier* — `applies (by H, G)` when the lemma's conclusion matches
  the goal and every premise is discharged by a local given,
  `premises remain` when the conclusion matches but some premises
  stay open, `rewrite subterm` for an equation lemma whose LHS
  matches a goal subterm — plus the module of origin. The top
  candidate is the default; press RET on an empty filter to pick
  it. The `?` is then replaced with a tier-aware tactic skeleton:
  `conclude <goal> by apply <name> to <labels>` for the full tier,
  `apply <name> to ?` when premises remain, `replace <name>` for a
  rewrite, or the bare name otherwise. With a prefix arg
  (`C-u C-c C-l`), Emacs prompts for a query string — substring
  match against names/signatures or a goal-shape pattern with `_`
  placeholders — and forwards it to the server.
- `C-c C-x` — **show the full diagnostic at point** in a `*Deduce
  Diagnostic*` popup buffer. Deduce error messages are multi-line
  (headline + location + grammar / proof context); the echo area
  clips them to the first line. This command preserves the newlines
  and tab-indented continuations so the whole message is readable.
  When point sits between diagnostics, every diagnostic on the
  current line is shown.

`deduce-dap` (when loaded, also requires the third-party
`dap-mode` package from MELPA):

- `C-c C-d` — **launch a debug session on the current `.pf`
  file.**  Spawns `python3 -m lsp.dap_server` as the adapter and
  drives it via `dap-mode`'s standard UI: gutter breakpoints,
  call-stack pane (`*dap-ui-sessions*`), locals view
  (`*dap-ui-locals*`), program-output pane (`*Deduce :: launch
  current file out*` — `print` results land here), and the
  Debug Console.  The very first pause lands at your file's
  first user-level statement, mirroring `python deduce.py
  --debug`.
- **Stepping with F-keys.**  `F5` continues, `F10` steps over,
  `F11` steps in, `S-F11` steps out, `S-F5` disconnects.
  Bindings are gdb / VS Code conventions and only fire in
  `deduce-mode` buffers.
- **Breakpoints.**  `M-x dap-breakpoint-toggle` (or
  `dap-breakpoint-add`) on a line sets a line breakpoint;
  breakpoints set before `C-c C-d` are armed via
  `setBreakpoints` at launch.  Conditional breakpoints work via
  `M-x dap-breakpoint-condition`.  Function-name breakpoints are
  not exposed by stock dap-mode — set a line bp on the function
  definition instead, or use the CLI debugger's `b <name>`.
- **Evaluate expressions** at a pause: `M-x dap-eval RET <expr>
  RET` sends a DAP `evaluate` request that drives the same
  parser + reducer the CLI debugger's `print` command uses.
- **Pattern-bound locals are visible.**  When you step into a
  recursive function such as `count_down(suc(n'))`, the locals
  pane shows the pattern binding (e.g. `n' = suc(zero)`).  Each
  recursive descent updates it; each return restores the
  caller's binding.  The Locals tree starts collapsed — click
  the triangle (or `RET` on the line) to expand.
- **Return notifications** (`<- returned from count_down(...)`)
  appear in the per-session output pane as the recursion
  unwinds, one line per visible frame.
- Standard-library calls are stepped over automatically
  (matching the CLI's behavior); see
  [`gh_pages/doc/Debugger.md`](../../gh_pages/doc/Debugger.md#what-the-debugger-skips)
  for the full command surface and the skip rules.

Useful `dap-mode` commands you'll want to know about
(inherited as-is — `deduce-dap` is a thin contribution on top):

| Command                          | What it does                                                                        |
| -------------------------------- | ----------------------------------------------------------------------------------- |
| `dap-hydra` (bound to `C-c d h`) | Single-key transient menu: `n` next, `s` step-in, `o` step-out, `c` continue, `q` quit, `e` eval, etc.  The OS-independent way to drive the debugger; great on macOS where the F-keys get intercepted. |
| `dap-breakpoint-toggle`          | Toggle a line breakpoint at point.                                                  |
| `dap-breakpoint-add`             | Same as toggle when there's no bp; otherwise a no-op (idempotent set).              |
| `dap-breakpoint-delete-all`      | Clear every breakpoint in every file.                                               |
| `dap-breakpoint-condition`       | Cursor on an existing breakpoint; prompts for a Deduce expression.  The bp fires only when the expression reduces to `true`. |
| `dap-breakpoint-log-message`     | Turn a breakpoint into a *logpoint*: instead of pausing it logs a message to the output pane each time it would fire. |
| `dap-eval`                       | Prompts for an expression and evaluates it via the DAP `evaluate` request (same parser + reducer as the CLI's `print` command). |
| `dap-eval-region`                | Like `dap-eval` but uses the selected region as the expression.                     |
| `dap-eval-thing-at-point`        | Sends the identifier under cursor to `evaluate`.                                    |
| `dap-ui-locals`                  | Open / focus the locals pane (`*dap-ui-locals*`).  The tree starts collapsed — `RET` (or click the triangle) to expand. |
| `dap-ui-sessions`                | Open the active-sessions pane (`*dap-ui-sessions*`).                                |
| `dap-ui-breakpoints`             | Open the breakpoints pane (`*dap-ui-breakpoints*`).                                 |
| `dap-ui-many-windows`            | Open all the standard panes at once.  Handy at the start of a session.              |
| `dap-debug-restart`              | End the current session and re-launch the same configuration.                       |
| `dap-delete-session`             | Force-kill the currently-active session (use if it's stuck).                        |
| `dap-delete-all-sessions`        | Same as above for every session.                                                    |

For the full surface see [emacs-lsp.github.io/dap-mode][dapdoc].

[dapdoc]: https://emacs-lsp.github.io/dap-mode/

`deduce-fill-hole` (additional, requires an LLM API key — Anthropic,
OpenAI, or IU REALLMs depending on backend choice):

- `C-c C-a` — **ask an LLM to fill the `?` at point** ("ask AI"). The
  command captures the goal, in-scope givens, and lemmas, then runs
  the chosen model asynchronously. Emacs stays interactive while
  the model iterates (up to `deduce-fill-hole-max-attempts`
  validation attempts; first valid proof wins). On completion, if
  the buffer around the hole hasn't drifted in the meantime, the
  validated proof is spliced in; otherwise the command errors and
  leaves the buffer untouched. Multiple fill-hole requests can run in
  parallel, including in the same buffer; each still has to pass the
  marker and fingerprint checks before it edits.

## Keybindings

| Binding   | Notes                                                              | Command                          | Provided by    |
| --------- | ------------------------------------------------------------------ | -------------------------------- | -------------- |
| `TAB`     | Indent the current line                                            | `deduce-mode-indent-line`        | `deduce-mode`  |
| `M-TAB` / `C-M-i` | Complete the identifier at point                           | `completion-at-point`            | eglot          |
| `M-.`     | Jump to symbol's definition                                        | `xref-find-definitions`          | eglot          |
| `M-,`     | Pop the xref stack                                                 | `xref-go-back`                   | eglot          |
| `M-x imenu` | Outline of top-level declarations                                | `imenu`                          | eglot          |
| `C-c C-n` | Move to the next standalone `?` hole                               | `deduce-mode-next-hole`          | `deduce-mode`  |
| `C-c C-g` | Goal + givens at cursor                                            | `deduce-show-goal-at-point`      | `deduce-lsp`   |
| `C-c C-r` | Apply the suggested template at hole                               | `deduce-lsp-refine-hole`         | `deduce-lsp`   |
| `C-c C-c` | Prompt for variable, replace `?` with case skeleton                | `deduce-lsp-case-split`          | `deduce-lsp`   |
| `C-c C-i` | Replace `?` with `induction T` skeleton at a forall goal           | `deduce-lsp-induction`           | `deduce-lsp`   |
| `C-c C-e` | Prompt for hypothesis, replace `?` with use-fact tactic            | `deduce-lsp-eliminate`           | `deduce-lsp`   |
| `C-c C-f` | Replace `?` with `conclude ... by H` for a given matching the goal | `deduce-lsp-fill-from-given`     | `deduce-lsp`   |
| `C-c C-l` | Pick an in-scope lemma; splice a tier-aware reference at the hole  | `deduce-lsp-search-lemma`        | `deduce-lsp`   |
| `C-c C-x` | Show the full diagnostic at point in a popup buffer                | `deduce-show-diagnostic-at-point`| `deduce-lsp`   |
| `C-c C-a` | Ask an LLM to fill the `?` at point. Async, non-blocking.          | `deduce-fill-hole`               | `deduce-fill-hole` |
| `C-c C-d` | Launch a debug session on the current `.pf` file                   | `deduce-dap-debug-current-buffer`| `deduce-dap`   |
| `F5`      | Continue execution (inside an active debug session)                | `dap-continue`                   | `deduce-dap`   |
| `F10`     | Step over the current statement / call                             | `dap-next`                       | `deduce-dap`   |
| `F11`     | Step into the next function call                                   | `dap-step-in`                    | `deduce-dap`   |
| `S-F11`   | Step out of the current function                                   | `dap-step-out`                   | `deduce-dap`   |
| `S-F5`    | End the debug session                                              | `dap-disconnect`                 | `deduce-dap`   |
| `C-c d d` | Same as `C-c C-d` — launch a debug session                         | `deduce-dap-debug-current-buffer`| `deduce-dap`   |
| `C-c d c` | Continue (F-key-free fallback)                                     | `dap-continue`                   | `deduce-dap`   |
| `C-c d n` | Next / step-over (F-key-free fallback)                             | `dap-next`                       | `deduce-dap`   |
| `C-c d s` | Step in (F-key-free fallback)                                      | `dap-step-in`                    | `deduce-dap`   |
| `C-c d o` | Step out (F-key-free fallback)                                     | `dap-step-out`                   | `deduce-dap`   |
| `C-c d q` | Disconnect / end session (F-key-free fallback)                     | `dap-disconnect`                 | `deduce-dap`   |
| `C-c d h` | Open dap-mode's single-key transient menu                          | `dap-hydra`                      | `deduce-dap`   |
| `C-c d b` | Toggle a breakpoint at the current line                            | `dap-breakpoint-toggle`          | `deduce-dap`   |

> **macOS users:** F5 / F10 / F11 are intercepted *twice* —
> once by the hardware (brightness / mute / volume) and again
> by Mission Control (F11 = "Show Desktop").  Either fix both,
> or use the `C-c d <letter>` fallback bindings above (no
> F-keys involved).  `M-x dap-hydra` opens dap-mode's single-key
> transient menu (`n`/`s`/`o`/`c`/`q`) — another good escape
> hatch.  Troubleshooting section below has the exact menu paths.

## Customization

All variables are `defcustom`s reachable via `M-x customize-group
RET deduce RET` (root group), or any of the per-layer groups:
`deduce-lsp`, `deduce-fill-hole`, `deduce-dap`.

### `deduce-mode`

| Variable                    | Default | Effect                                         |
| --------------------------- | ------- | ---------------------------------------------- |
| `deduce-mode-indent-offset` | `2`     | Spaces per indentation step                    |

### `deduce-lsp`

| Variable                       | Default     | Effect                                                                 |
| ------------------------------ | ----------- | ---------------------------------------------------------------------- |
| `deduce-lsp-auto-start`        | `t`         | If non-nil, `eglot-ensure` runs on `deduce-mode` entry                 |
| `deduce-lsp-python-program`    | `"python3"` | Python interpreter used to launch the language server                  |
| `deduce-lsp-deduce-root`       | `nil`       | Path to a Deduce checkout; sets `PYTHONPATH` for the spawned server    |
| `deduce-lsp-prelude-disabled`  | `nil`       | If non-nil, sets `DEDUCE_NO_STDLIB=1` so the server skips the prelude  |
| `deduce-lsp-search-lemma-timeout` | `60`     | Per-request timeout (seconds) for the `C-c C-l` round trip. Bumps past the 10s jsonrpc default because ranking the stdlib's ~200 lemmas exceeds it on a cold-prelude first call. Set to nil to fall back to the default. |

For full control over the launch command, `defun deduce-lsp-server-command`
in your `init.el` returning whatever list eglot should spawn.

### `deduce-dap`

| Variable                       | Default     | Effect                                                                       |
| ------------------------------ | ----------- | ---------------------------------------------------------------------------- |
| `deduce-dap-python-program`    | `"python3"` | Python interpreter used to launch the DAP adapter (`lsp/dap_server.py`)      |
| `deduce-dap-deduce-root`       | `nil`       | Path to a Deduce checkout; sets `PYTHONPATH` so `python3 -m lsp.dap_server` resolves regardless of cwd. By default the adapter's cwd is the project root (via `project-current`), which is enough when your `.pf` lives inside the Deduce repo. |
| `deduce-dap-prelude-disabled`  | `nil`       | If non-nil, sets `DEDUCE_NO_STDLIB=1` so debug sessions skip the prelude     |
| `deduce-dap-auto-ui`           | `t`         | If non-nil, set up dap-mode's UI automatically before each launch: enables `dap-ui-mode` (one-time) and opens the standard side panes (locals / sessions / breakpoints / expressions) via `dap-ui-many-windows`. Set to nil to keep the launcher minimal and manage the UI yourself. |

The common gotcha: on systems with multiple Python installs the
`python3` first on `$PATH` may not be the one you `pip install
lark`ed into, leading to a `ModuleNotFoundError: No module named
'lark'` and the session exiting immediately.  Point
`deduce-dap-python-program` at the right interpreter — see the
matching troubleshooting entry below.

### `deduce-fill-hole`

| Variable                              | Default                       | Effect                                                      |
| ------------------------------------- | ----------------------------- | ----------------------------------------------------------- |
| `deduce-fill-hole-backend`            | `'anthropic`                  | `'anthropic` (Claude via Anthropic API) or `'openai-compat` (REALLMs / OpenAI / Ollama) |
| `deduce-fill-hole-base-url`           | `nil`                         | OpenAI-compat endpoint URL; e.g. `"https://reallms.rescloud.iu.edu/direct/v1"`. Ignored when backend is `'anthropic`. |
| `deduce-fill-hole-model`              | `nil` (backend default)       | Model id; backend default is `"claude-opus-4-7"` (anthropic) or `"gemma-4-31B-it"` (openai-compat) |
| `deduce-fill-hole-api-key-env`        | `nil` (backend default)       | Env var name; backend default is `"ANTHROPIC_API_KEY"` or `"OPENAI_API_KEY"`. IU REALLMs users override to `"REALLMS_API_KEY"`. |
| `deduce-fill-hole-python-program`     | `"python3"`                   | Python interpreter used to launch the sidecar               |
| `deduce-fill-hole-deduce-root`        | `nil`                         | Path to a Deduce checkout; falls back to `deduce-lsp-deduce-root`, then `project-root`, then cwd |
| `deduce-fill-hole-max-attempts`       | `5`                           | Maximum number of validation attempts per invocation        |
| `deduce-fill-hole-prelude-disabled`   | `nil`                         | If non-nil, sidecar invokes `deduce.py --no-stdlib`         |
| `deduce-fill-hole-timeout`            | `60`                          | Per-attempt timeout passed to the sidecar (seconds)         |

**IU REALLMs preset** — drop this in your `init.el` to point at REALLMs:

```elisp
(with-eval-after-load 'deduce-fill-hole
  (setq deduce-fill-hole-backend 'openai-compat
        deduce-fill-hole-base-url "https://reallms.rescloud.iu.edu/direct/v1"
        deduce-fill-hole-api-key-env "REALLMS_API_KEY"
        deduce-fill-hole-model "Qwen3-Coder-Next"))
```

## Troubleshooting

### "Server died" immediately after the language server starts

Check the Python side first:

```sh
python3 -m lsp.lsp_server </dev/null
```

The server should exit cleanly (it reads JSON-RPC from stdin; with
no input it terminates). If you get an `ImportError`, install the
LSP requirements: `pip install -r requirements-lsp.txt` from the
deduce repo root. Verify `pygls>=2.1.0` is what got installed —
2.0 had a different API and won't work.

### Server starts but `M-.` / `C-c C-g` always returns nothing

Most likely the server is launched outside the deduce repo and
can't find the deduce sources. The fix is either:

1. Set `deduce-lsp-deduce-root` to your deduce checkout, or
2. Make sure `default-directory` is the repo root when you open
   the `.pf` file.

You can confirm by inspecting `M-x eglot-events-buffer` — the
`initialize` reply should show the server's `serverInfo`. If the
buffer says "process exited abnormally," see the previous step.

### First `C-c C-g` is slow

Yes — the first request bootstraps the prelude (~1s with the
`.thm` cache, ~13s without). Subsequent requests are warm. You can
disable the prelude entirely with `deduce-lsp-prelude-disabled = t`
if you don't need the standard library.

### Indentation is off

`deduce-mode-indent-line` uses a balanced-bracket / `proof`/`end`
matcher; it doesn't currently handle multi-line type signatures or
`case` placement perfectly. If `TAB` insists on a column you don't
want, just type the spaces yourself — the indenter only fires when
you ask. SMIE-grade alignment is a future enhancement.

### F-keys do macOS / WM things instead of debugger actions

macOS intercepts the function-row keys at two layers before they
reach Emacs:

1. **Hardware row** — F5 = brightness, F10 = mute, F11 = volume
   down, etc.  Fix one of:
   - **One-shot**: hold `fn` while pressing the F-key.  `fn-F11`
     sends a real F11 to Emacs.
   - **Permanent (Sonoma / Sequoia)**: System Settings →
     Keyboard → *Keyboard Shortcuts…* (button) → sidebar:
     *Function Keys* → toggle on *Use F1, F2, etc. as standard
     function keys*.
   - **Permanent (Monterey and older)**: System Preferences →
     Keyboard → Keyboard tab → check *Use F1, F2, etc. keys as
     standard function keys*.

2. **Mission Control shortcuts** — even after step 1, macOS still
   binds F11 to *Show Desktop* and F12 to *Show Dashboard*.
   System Settings → Keyboard → *Keyboard Shortcuts…* → sidebar:
   *Mission Control* → uncheck (or rebind) anything you want
   freed up.  F11 is the usual culprit.

Linux users with `gnome-shell` or KDE sometimes hit the same
issue with WM-bound F-keys; check your window-manager shortcuts.

**Don't want to fight your OS?**  Two options that never touch
the function row:

- The `C-c d <letter>` bindings listed in the Keybindings table:
  `c`ontinue, `n`ext, `s`tep-in, step-`o`ut, `q`uit, `d`ebug
  (launch), `h`ydra.
- `C-c d h` (or `M-x dap-hydra`) — the transient menu — is the
  one to learn if you only learn one.  Single-key actions: `n`/
  `s`/`o`/`c`/`q`, plus `e` for eval, `b` for breakpoints, etc.
  Press `q` to dismiss the menu.

Linux users with `gnome-shell` or KDE sometimes hit the same
issue with WM-bound F-keys; check your window-manager shortcuts
if your distro intercepts them.

### Gutter-clicking doesn't set breakpoints

dap-mode doesn't bind mouse clicks in the fringe by default
(VS Code convention; emacs doesn't ship it out of the box) and
making it work cleanly fights the flymake / eglot fringe
indicators, which often grab `[left-fringe mouse-1]` to surface
their own actions.  **Strongly recommended:** use the keyboard
binding `C-c d b` (`dap-breakpoint-toggle`) instead.

If you really want a mouse click, **shift-click** in the fringe
avoids the conflict with flymake's plain-mouse-1 capture.  Paste
into your init after `(require 'deduce-dap)`:

```elisp
(defun my/dap-toggle-bp-at-mouse (event)
  "Toggle a dap-mode breakpoint at the clicked fringe line."
  (interactive "e")
  (let* ((posn   (event-start event))
         (window (posn-window posn))
         (pos    (posn-point posn)))
    (when (and window pos)
      (with-selected-window window
        (goto-char pos)
        (call-interactively #'dap-breakpoint-toggle)))))

(with-eval-after-load 'deduce-mode
  (define-key deduce-mode-map [left-fringe S-mouse-1]
              #'my/dap-toggle-bp-at-mouse))
```

We attach to `deduce-mode-map' rather than `dap-mode-map' so the
binding works in `.pf' buffers whether or not a debug session is
currently active.

### Function breakpoints from the keyboard

Stock dap-mode doesn't expose a command for function-name
breakpoints (the DAP protocol supports them — our adapter
implements ``setFunctionBreakpoints'' — but the dap-mode UI is
line-based).  Workaround: set a line breakpoint on the first
line of the function definition.  For a pattern-matched
``recursive'' function, set one breakpoint per arm so each case
traps.  The CLI debugger's ``b <name>'' command exposes the
function-bp surface directly if you need it.

### `C-c C-d` reports "Debug session process exited with status: exited abnormally with code 1"

Check the buffer named `*Deduce :: launch current file stderr*`
(or `M-x switch-to-buffer RET *De TAB`) for the actual error.
The two most common causes:

1. **`ModuleNotFoundError: No module named 'lark'`** — `lark` isn't
   installed on whichever `python3` is on your `$PATH`.  Macs and
   Linux distros routinely have multiple Python installs, and the
   one `dap-mode` finds first may not be the same one you used to
   `pip install lark`.  Tell `deduce-dap` which interpreter to use:

   ```elisp
   (setq deduce-dap-python-program "python3.13")  ;; or wherever lark lives
   ```

   Confirm from a shell first with `python3.13 -c 'import lark'` —
   exit code 0 means the variable above is the right setting.

2. **`No module named 'lsp'`** — the adapter's cwd isn't your
   Deduce checkout, so `python3 -m lsp.dap_server` can't find the
   `lsp/` directory.  `deduce-dap` defaults `:cwd` to
   `project-current`'s root; if Emacs can't determine the project
   root for your buffer, set `deduce-dap-deduce-root` to the
   absolute path of your checkout (this also feeds `PYTHONPATH`
   into the adapter's environment).

## Manual smoke test

After installing, verify the major mode:

1. Open `lib/Nat.pf`.
2. Confirm the mode line shows `Deduce` and the `theorem` / `proof`
   / `end` keywords are highlighted.
3. Press `TAB` on a few lines inside a `proof` block; the
   indentation should match the surrounding structure.

Then verify the LSP integration:

4. Wait for the language server to bootstrap (watch the mode line
   for `[eglot:Deduce]`).
5. Place point on `equal` (any reference) and press `M-.` — it
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
    replaced directly — no prompt — with `conclude P by H`. With
    two matching givens in scope (e.g. `assume H1: P` and `assume
    H2: P`), Emacs prompts `Fill from:` with TAB completion against
    the matching labels.
13. In a scratch `.pf` buffer with a non-trivial arithmetic goal:

    ```
    import UInt

    theorem t: all a:UInt, b:UInt. a + b = b + a
    proof
      arbitrary a:UInt, b:UInt
      ?
    end
    ```

    Place point on the `?` and press `C-c C-l`. Emacs prompts
    `Lemma:` with TAB completion against the ranked in-scope
    candidates; each row shows the lemma's signature, the unify
    tier (e.g. `applies`, `rewrite subterm`), and the module. The
    top candidate (`uint_add_commute` for this fixture) is the
    default — press `RET` on the empty filter to pick it. The `?`
    is replaced with a tier-aware skeleton (here:
    `conclude a + b = b + a by uint_add_commute`).

If you have `deduce-fill-hole` loaded and an API key exported, also
verify the LLM path:

14. In a scratch `.pf` buffer with a `theorem t: all P:bool. P = P`
    (or similar simple) shape, place point on the `?` and press
    `C-c C-a` ("ask AI"). Emacs reports `deduce-fill-hole: asking
    <model>...` (e.g. `asking claude-opus-4-7...`). Within a few
    seconds (depending on the model and how
    many attempts it takes), the `?` is replaced with the validated
    proof and you get a `filled in N attempts` message. If the API
    key is missing, the buffer is left untouched and an error
    message is reported.

If you have `deduce-dap` loaded and `dap-mode` installed
(`M-x package-install RET dap-mode RET` or via MELPA in your config),
also verify the debugger integration:

15. Open a `.pf` file that has at least one `print` statement —
    e.g. `tmp/debugger_smoke.pf` if you've worked through the
    Debugger.md walkthrough, or any prelude module like
    `lib/UInt.pf` that contains a top-level `print`. Press
    `C-c C-d`.  `deduce-dap` enables `dap-ui-mode` and opens the
    standard side panes (locals / sessions / breakpoints /
    expressions) for you automatically (see
    `deduce-dap-auto-ui`).  The source buffer should highlight
    a line at the first user-level statement (matching where
    `python deduce.py --debug` would initially trap).

16. The Locals tree starts collapsed — `RET` (or click the
    triangle next to `Locals`) to expand.  Inside a function
    call, the pattern-bound names appear there.

17. Set a breakpoint at a line of interest: `C-c d b` with
    cursor on the target line (or `M-x dap-breakpoint-toggle`).
    Resume with `F5` / `C-c d c`; step over with `F10` /
    `C-c d n`; step into with `F11` / `C-c d s`.  Or open
    `dap-hydra` with `C-c d h` for a single-key transient menu.
    (See the keybinding caveats above if F-keys don't work on
    your OS.)

18. While paused inside a function, the locals panel should show
    the pattern-bound names (e.g. `n' = suc(zero)` inside
    `count_down`'s `suc` case). The call-stack panel shows one
    entry per frame, gdb-style with the innermost at the top.

19. In the `*dap-ui-repl*` window (or via `dap-eval-region`), type
    an expression like `suc(zero)` to invoke the DAP `evaluate`
    request — the same reducer the CLI's `print` command uses.

20. Press `C-c d q` (or `M-x dap-disconnect`) to end the run.
    The DAP adapter exits cleanly when stdin is closed.

If `dap-mode` isn't installed, `C-c C-d` reports an error pointing
at the MELPA install command rather than crashing.

## Development

Run the ert tests in batch mode (no GUI required):

```sh
emacs --batch -L editor/emacs -L editor/emacs/test \
      -l deduce-mode-test -f ert-run-tests-batch-and-exit
emacs --batch -L editor/emacs -L editor/emacs/test \
      -l deduce-lsp-test -f ert-run-tests-batch-and-exit
emacs --batch -L editor/emacs -L editor/emacs/test \
      -l deduce-dap-test -f ert-run-tests-batch-and-exit
emacs --batch -L editor/emacs -L editor/emacs/test \
      -l deduce-fill-hole-test -f ert-run-tests-batch-and-exit
```

The end-to-end loop (subprocess server + real protocol traffic) is
impractical to drive from a batch process; the tests pin the
in-Emacs pieces (eglot registration, command construction,
keybindings, request shape) but the actual server interaction
relies on the manual smoke test above.

Byte-compile the sources to catch warnings:

```sh
emacs --batch -L editor/emacs \
      -f batch-byte-compile editor/emacs/deduce-mode.el \
      editor/emacs/deduce-lsp.el editor/emacs/deduce-fill-hole.el \
      editor/emacs/deduce-dap.el
```

If a stale `.elc` file is loaded instead of the source, `M-x
load-file` on the `.el` will use the source directly. To remove
the byte-compiled artifacts entirely:

```sh
rm editor/emacs/*.elc editor/emacs/test/*.elc
```

For the protocol-level wiring between the Emacs client and the
Python LSP server (request method names, server module path, what
to keep in sync when adding a new command), see
[`docs/knowledge-base/emacs-lsp-protocol.md`](../../docs/knowledge-base/emacs-lsp-protocol.md).
