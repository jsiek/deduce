# Emacs Mode

The [Getting Started guide](./GettingStarted.md#emacs) covers installing
Deduce's Emacs mode and trying the core keybindings. This page collects
the longer Emacs-specific setup notes.

For full editor details — including troubleshooting, customization, and
a manual smoke test — see
[`editor/emacs/README.md`](https://github.com/jsiek/deduce/blob/main/editor/emacs/README.md).

## AI-assisted proof completion in Emacs

`C-c C-a` asks a language model to fill the `?` at point. The Emacs
mode spawns the
[`tools/claude_fill_hole`](https://github.com/jsiek/deduce/tree/main/tools/claude_fill_hole)
sidecar, which requests a candidate proof, validates it against
`deduce.py`, and splices the first valid one back into your buffer.
Emacs stays interactive while the model iterates (up to five
attempts; the first valid proof wins).

The binding comes from `deduce-fill-hole` — make sure your init file
has `(require 'deduce-fill-hole)` from the
[Emacs setup](./GettingStarted.md#emacs). You'll also need an API key
for whichever model provider you point the sidecar at.

**1. Install the sidecar's Python dependencies:**

```sh
cd /path/to/deduce
python3 -m pip install -r requirements-fill-hole.txt
```

This pulls in `anthropic` and `openai`; the sidecar picks one at run
time based on your backend choice.

**2. Pick a backend and set its API key.** Three common setups:

*Anthropic / Claude (default; best quality, paid):*

```sh
export ANTHROPIC_API_KEY=sk-ant-...
```

*Indiana University REALLMs (free for IU researchers/faculty/staff,
hosted on-prem):*

```sh
export REALLMS_API_KEY=...
```

```elisp
;; In your init.el, after (require 'deduce-fill-hole):
(setq deduce-fill-hole-backend 'openai-compat
      deduce-fill-hole-base-url "https://reallms.rescloud.iu.edu/direct/v1"
      deduce-fill-hole-api-key-env "REALLMS_API_KEY"
      deduce-fill-hole-model "Qwen3-Coder-Next")
```

*OpenAI (paid):*

```sh
export OPENAI_API_KEY=sk-...
```

```elisp
(setq deduce-fill-hole-backend 'openai-compat
      deduce-fill-hole-model "gpt-4o")
```

Add the `export` line to your shell init file (`~/.zshrc`,
`~/.bashrc`, ...) so the variable is available in every Emacs session.
On macOS GUI Emacs, where shell variables sometimes fail to propagate
into the GUI environment, the
[`exec-path-from-shell`](https://github.com/purcell/exec-path-from-shell)
package is a reliable fix.

**3. (Optional) Pin the model and tune attempts.** By default the
sidecar uses `claude-opus-4-7` (Anthropic backend) or
`gemma-4-31B-it` (OpenAI-compat). To override:

```elisp
(setq deduce-fill-hole-model "claude-sonnet-4-6")  ; cheaper Claude
(setq deduce-fill-hole-max-attempts 3)             ; default is 5
(setq deduce-fill-hole-timeout 60)                 ; per validate_proof, seconds
```

The full set of `defcustom`s (with defaults) is reachable via `M-x
customize-group RET deduce-fill-hole RET`, and documented in the
[`editor/emacs/README.md`](https://github.com/jsiek/deduce/blob/main/editor/emacs/README.md#deduce-fill-hole)
customization table.

**4. Try it.** Open a `.pf` file with a `?` to fill, place point on
the `?`, and press `C-c C-a`. The mode line shows progress; when the
model returns a valid proof, it replaces the `?` automatically. If
every attempt fails validation, the sidecar surfaces its last error
in the echo area and leaves the buffer as it was.
