# Getting Started

Here are some resources to help you get started with Deduce.

* [Installing Deduce](#installation)
* [Running Programs](#running-deduce-programs)
* [Using Deduce with an AI Assistant](#using-deduce-with-an-ai-assistant)
* [Learning Deduce](#deduce-introduction)

## Installation

To get started with Deduce, follow these steps:

1. [Install Prerequisites](#install-prerequisites)
2. [Install Deduce](#install-deduce)
3. [Choose a Text Editor](#install-and-configure-a-text-editor)
4. [Set up an AI Assistant](#using-deduce-with-an-ai-assistant) (optional)

### Install Prerequisites

You will need [Python](https://www.python.org/) version 3.10 or later. Here are some [instructions](https://wiki.python.org/moin/BeginnersGuide/Download) and links to download Python for many computer systems.

You will also need the [Lark](https://github.com/lark-parser/lark) parsing library, which you can install by running the following command in the same directory as `deduce.py`

```
python -m pip install lark
```

### Install Deduce

You can find the stable releases of Deduce on
[github](https://github.com/jsiek/deduce/releases). Download the zip
file and unpack it. To check that Deduce is working, go into the top
`deduce` directory, and run `python` on the `deduce.py` script and the
provided example file.  (There is no executable for Deduce.)

```
python ./deduce.py ./example.pf
```

You should see the following response from Deduce.

```
example.pf is valid
```

This response means that all the proofs in `example.pf` are complete and flawless!
Most of the time you will be working on incomplete or flawed proofs and
Deduce will try to give you helpful feedback. For example, if you replace
the proof in `example.pf` with a `?` as follows

```
theorem one_x: 1 = x
proof
  ?
end
```

and run Deduce again, you will see the following response.

```
example.pf:8.3-8.4: incomplete proof
Goal:
	1 = x
Advice:
	To prove this equality, one of these statements might help:
		definition
		rewrite
		equations
```

The latest development branch of Deduce (not stable) is available
[here](https://github.com/jsiek/deduce) on github. It includes the
source code for Deduce and for the Deduce web site.


### Install and Configure a Text Editor

You can write Deduce in any text editor you want, and run Deduce through
the terminal. For the editors below, we ship extensions that add syntax
highlighting and (for Emacs) an interactive proof-editing experience
backed by Deduce's Language Server Protocol (LSP) implementation.

* [Emacs](#emacs) — bundled in the Deduce repo at
  [`editor/emacs/`](https://github.com/jsiek/deduce/tree/main/editor/emacs).
  Includes both a major mode (highlighting + indentation) and an LSP
  client with goal-at-cursor, refine-hole, case-split, induction
  skeleton, and more.
* [VS Code](#vs-code) — separate
  [`HalflingHelper/deduce-mode`](https://github.com/HalflingHelper/deduce-mode)
  repo. LSP integration is on the roadmap but not yet wired up.

#### Emacs

Requires **Emacs 29.1 or newer** (older Emacs would need a third-party
`eglot` package, which is unsupported).

**1. Install the Python LSP dependencies** (only required if you want
the interactive features beyond syntax highlighting):

```sh
cd /path/to/deduce
python3 -m pip install -r requirements-lsp.txt
```

This installs `pygls` (for the LSP server) and `mcp` (for the MCP
server documented in the next section). Skip this if you only want
syntax highlighting.

**2. Add to your Emacs init file.** Without `use-package`:

```elisp
;; ~/.emacs.d/init.el  (or ~/.emacs)
(add-to-list 'load-path "/path/to/deduce/editor/emacs")
(require 'deduce-mode)
(require 'deduce-lsp)         ; optional: omit for syntax highlighting only
(require 'deduce-fill-hole)   ; optional: enables `C-c C-a' (ask AI to fill a hole)

;; If your .pf files live OUTSIDE the deduce repo, point the LSP
;; server at your checkout so `python3 -m lsp.lsp_server' resolves:
;; (setq deduce-lsp-deduce-root "~/src/deduce")
```

With `use-package`:

```elisp
(use-package deduce-mode
  :load-path "/path/to/deduce/editor/emacs"
  :mode "\\.pf\\'")

(use-package deduce-lsp
  :load-path "/path/to/deduce/editor/emacs"
  :after (deduce-mode eglot))

(use-package deduce-fill-hole
  :load-path "/path/to/deduce/editor/emacs"
  :after deduce-lsp)
```

Opening any `.pf` file then enters `deduce-mode` automatically. With
`deduce-lsp` loaded, `eglot` connects on first save (the first
connection bootstraps the standard library; subsequent calls are warm).
`deduce-fill-hole` is independent — see
[Set up an AI Assistant](#using-deduce-with-an-ai-assistant) below
for its API-key / model configuration.

**3. Try the keybindings.** Inside a `.pf` buffer:

| Key       | Action                                                                |
| --------- | --------------------------------------------------------------------- |
| `M-.`     | Jump to a symbol's definition.                                        |
| `M-x imenu` | Outline of top-level theorems / definitions / unions.               |
| `C-c C-g` | Show the proof goal at point in a popup buffer.                       |
| `C-c C-r` | Refine the hole `?` at point. Picks a tactic template by goal shape (e.g. `arbitrary x:T` for `all x:T. ...`, `?, ?` for `P and Q`, `reflexive` for an obvious equality). |
| `C-c C-c` | Case split. Cursor on a `?`; prompts (with TAB completion) for an in-scope variable, then replaces the `?` with a `switch` skeleton (one branch per constructor) or `cases` (for `or`-shaped hypotheses). |
| `C-c C-i` | Induction skeleton. Cursor on a `?` whose goal is `all x:T. P(x)` with `T` a union; replaces the `?` with `induction T` and one case per constructor, including `IH<N>` bindings on recursive arguments. |
| `C-c C-e` | Eliminate / use-fact. Cursor on a `?`; prompts for a hypothesis label and replaces the `?` with a tactic chosen by the hypothesis's shape (destructure for `and`, `cases` for `or`, `apply ... to ?` for `if then`, `H[?]` for `all`, `obtain ... from H` for `some`, `replace H` for equality). |
| `C-c C-f` | Fill hole with a given. Cursor on a `?`; replaces it with `conclude <goal> by <label>` for an in-scope hypothesis whose formula equals the goal. Auto-applies on a single match; otherwise prompts. |
| `C-c C-a` | **Ask AI** to fill the `?` at point. Spawns an LLM-driven proof-completion sidecar; emacs stays interactive while the model iterates (up to 5 attempts, first valid proof wins). Requires API-key configuration — see [Set up an AI Assistant](#using-deduce-with-an-ai-assistant) below. |

For full details — including troubleshooting, customization, and a
manual smoke test — see
[`editor/emacs/README.md`](https://github.com/jsiek/deduce/blob/main/editor/emacs/README.md).

#### VS Code

The VS Code extension lives in a separate repo:
[HalflingHelper/deduce-mode](https://github.com/HalflingHelper/deduce-mode).
It currently provides syntax highlighting only; the interactive
LSP-backed features (goal-at-cursor, refine, case split, etc.) are not
yet wired up. If you want them today, use the Emacs mode above; if you
want to help build the VS Code client, the Deduce LSP server lives at
`lsp/lsp_server.py` and speaks standard LSP plus a few custom
`deduce/...` requests documented in
[`docs/lsp-plan.md`](https://github.com/jsiek/deduce/blob/main/docs/lsp-plan.md).


## Running Deduce Programs

As mentioned above, Deduce is run by providing the `deduce.py` script
with a `*.pf` file.

Suppose you have written thew following program in a file named `hello.pf`.

```{.deduce^#hello_starting_example}
// hello.pf
union Greeting {
  hello
}

define world : Greeting = hello

print world
```

This program defines a new union type called `Greeting`, defines a
variable `world`, and prints it out.

To run it, type the following command from within the `deduce`
directory, or use the run functionality provided by your deduce
editor.

```
python deduce.py hello.pf
```

You should see the output

```
hello
hello.pf is valid
```


## Using Deduce with an AI Assistant

Deduce ships two complementary AI integrations. They're independent —
pick whichever fits your workflow (or use both):

* [**In-editor proof completion (`C-c C-a`)**](#in-editor-proof-completion-c-c-c-a)
  — press a key, an LLM proposes a proof for the `?` at point and
  Deduce validates it before it lands in your buffer. Stays inside
  Emacs. Best when you want the AI as a focused tactic, not a
  conversational partner.
* [**MCP server for external assistants**](#mcp-server-for-external-ai-assistants)
  — exposes Deduce's checking and proof-editing helpers as MCP tools
  so a separate assistant (Claude Code, Claude Desktop, etc.) can
  inspect goals and edit proofs in conversation. Best when you want
  the AI to plan across multiple proofs, refactor, or explain.

### In-editor proof completion (`C-c C-a`)

The Emacs mode bundles `deduce-fill-hole` (loaded with `(require
'deduce-fill-hole)` per the install snippet above). When you press
`C-c C-a` on a `?`, it spawns the
[`tools/claude_fill_hole`](https://github.com/jsiek/deduce/tree/main/tools/claude_fill_hole)
sidecar, which talks to a model, validates each candidate proof
against `deduce.py`, and splices the first valid one back into your
buffer. Emacs stays interactive while the model iterates (up to five
attempts by default).

**1. Install the sidecar's Python dependencies:**

```sh
cd /path/to/deduce
python3 -m pip install -r requirements-fill-hole.txt
```

This pulls in `anthropic` and `openai` (the sidecar picks one at run
time depending on your backend choice).

**2. Pick a backend and set its API key.** Three common setups:

*Anthropic / Claude (default; best quality, paid):*

```sh
export ANTHROPIC_API_KEY=sk-ant-…
```

*Indiana University REALLMs (free for IU researchers/faculty/staff,
hosted on-prem):*

```sh
export REALLMS_API_KEY=…
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
export OPENAI_API_KEY=sk-…
```

```elisp
(setq deduce-fill-hole-backend 'openai-compat
      deduce-fill-hole-model "gpt-4o")
```

Add the `export` line to your shell init file (`~/.zshrc`,
`~/.bashrc`, …) so the variable is available in every Emacs session.
On macOS GUI Emacs, where shell variables don't always propagate, the
[`exec-path-from-shell`](https://github.com/purcell/exec-path-from-shell)
package is a reliable fix.

**3. (Optional) Pin the model and tune attempts.** When the model
variable is unset, the sidecar picks `claude-opus-4-7` for the
Anthropic backend and `gemma-4-31B-it` for OpenAI-compat. Override
either:

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
none of the attempts validate, the buffer is left untouched and the
sidecar's last error surfaces in the echo area.

### MCP server for external AI assistants

Deduce ships an [MCP](https://modelcontextprotocol.io) (Model Context
Protocol) server at `lsp/mcp_server.py`. It exposes Deduce's checking
and proof-editing helpers as *tools* a separate AI assistant can call,
so the assistant can inspect goals, navigate definitions, refine
holes, and case-split without you having to copy-paste source back
and forth.

Unlike the in-editor `C-c C-a` flow, **the MCP server itself doesn't
talk to any LLM and doesn't need credentials of its own.** It's a
bridge; the LLM credentials and model choice live in whatever MCP
client you point at it (Claude Code, Claude Desktop, Cursor, …). The
instructions below assume
[Claude Code](https://docs.anthropic.com/claude/docs/claude-code); the
shape is similar for other clients (consult their docs for the exact
config-file location).

**1. Install the MCP server's Python dependencies.** If you didn't
install the LSP requirements above, do it now:

```sh
cd /path/to/deduce
python3 -m pip install -r requirements-lsp.txt
```

This pulls in the `mcp` Python package.

**2. Install Claude Code.** See the [Claude Code installation
guide](https://docs.anthropic.com/claude/docs/claude-code/install) for
your platform; the TL;DR is `npm install -g
@anthropic-ai/claude-code`. After install, run `claude` once and
follow the login prompts.

**3. Configure API access.** Claude Code authenticates either via a
Claude.ai account (the default) or via an Anthropic API key:

```sh
export ANTHROPIC_API_KEY=sk-ant-…
```

Add the line to your shell init so it's available in every shell.

**4. Choose a model.** Claude Code defaults to a recent Claude Sonnet
model. To pin a specific one:

```sh
claude --model sonnet      # alias for the latest Sonnet
claude --model opus        # most capable, more expensive
claude --model haiku       # fastest, cheapest
# or a full model id, e.g.:
claude --model claude-sonnet-4-5-20250929
```

Equivalent persistent setting in `~/.claude/settings.json`:

```json
{ "model": "sonnet" }
```

**5. Register the Deduce MCP server with Claude Code.** Create (or
edit) `.mcp.json` in the directory where you'll run `claude` —
typically your Deduce checkout or the directory containing your `.pf`
files:

```json
{
  "mcpServers": {
    "deduce": {
      "command": "python3",
      "args": ["-m", "lsp.mcp_server"],
      "env": {
        "DEDUCE_ROOT": "/path/to/deduce"
      }
    }
  }
}
```

`DEDUCE_ROOT` tells the server where to find `lib/` (the standard
library prelude) and `Deduce.lark` (the parser grammar). If you launch
`claude` *from* the Deduce checkout, `DEDUCE_ROOT` is optional. To
skip the prelude entirely, add `"DEDUCE_NO_STDLIB": "1"`. Alternative
CLI registration:

```sh
claude mcp add deduce -- python3 -m lsp.mcp_server
```

**6. Try it out.** Start `claude` in the directory with your `.pf`
file and ask something concrete:

```
$ cd /path/to/your/proofs
$ claude
> Please check hello.pf and explain any errors.
```

Claude will call the Deduce MCP server's `check_file` tool, see the
diagnostics, and respond. The full tool list:

| Tool                       | What it does                                                  |
| -------------------------- | ------------------------------------------------------------- |
| `check_file`               | Type-check and proof-check a `.pf` file; returns diagnostics. |
| `goal_at`                  | Return the proof goal + givens at a cursor position.          |
| `definition_of`            | Jump from a symbol to its declaration.                        |
| `list_symbols`             | Outline of top-level theorems / definitions in a file.        |
| `refine_at`                | Refine a `?` based on the goal's shape.                       |
| `case_split_at`            | Replace a `?` with a `switch` / `cases` skeleton on a chosen variable. |
| `splittable_vars_at`       | List in-scope variables that `case_split_at` can target.      |
| `induction_skeleton_at`    | Replace a `?` with an `induction T` skeleton.                 |
| `eliminate_at`             | Replace a `?` with a tactic that uses a chosen hypothesis.    |
| `eliminable_vars_at`       | List in-scope hypotheses that `eliminate_at` can target.      |
| `fill_from_given_at`       | Replace a `?` with `conclude <goal> by <label>`.              |
| `matching_givens_at`       | List in-scope hypotheses whose formula equals the goal.       |

These are the same operations the Emacs mode binds to `C-c C-r`,
`C-c C-c`, `C-c C-i`, `C-c C-e`, and `C-c C-f` — Claude (or any other
MCP client) has the same proof-editing toolkit you do.


## Deduce Introduction

This introduction to Deduce has two parts. The first part gives a tutorial on how to write programs in Deduce. The second part shows how to write proofs in Deduce.

* [Programming in Deduce](./FunctionalProgramming.md)
* [Writing Proofs in Deduce](./ProofIntro.md)

I recommend that you work through the examples in this introduction. Create a file named `examples.pf` in the top `deduce` directory and add the examples one at a time. To check the file, run the `deduce.py` script on the file from the `deduce` directory.

The Deduce Reference manual is linked below. It provides an alphabetical list of all the features in Deduce. The Cheat Sheet gives some advice regarding proof strategy and which Deduce keyword to use next in a proof. The Syntax Overview page provides a brief overview of the syntax structure of deduce.

* [Reference Manual](./Reference.md)
* [Cheat Sheet](./CheatSheet.md)
* [Syntax Overview](./SyntaxGrammar.md)

### Command Line Arguments

The `deduce.py` script supports command line arguments which are
documented below. If an argument is not preceded by one of the
keywords listed below, then it is treated as the name of a file or
directory and will be processed by Deduce.

`--dir directory-name`

Tells Deduce to include the given `directory-name` in the list of
directories to search when importing a file. For example, if `test.pf`
imports `Curry`, and `Curry.pf` resides in a folder named `howard`,
then `--dir howard` will allow `test.pf` to import `Church`. Note that
`--dir` expects a directory name, not an individual file.

The rest of the command line arguments are useful primarily for the
authors of Deduce. Users of Deduce can ignore them.

`--no-stdlib`

Deduce, by default, will import the entire standard library
(in `/lib` of the Deduce repository). However if this argument is supplied, it
will not do so.

`--lalr`

Deduce normally uses a custom recursive descent parser to parse any
input files, however this argument will make Deduce instead use lark's
LALR parser. This argument exists solely for checking that
`Deduce.lark` maintains parity with the recursive descent parser.

`--recursive-descent`

Tells Deduce to use the recursive descent (default) parser. If
`--lalr` is also supplied, then only the recursive descent parser will
be used.

`--recursive-directories` or `-r`

Instead of only processing files in the specified directories, Deduce
will also descend into any subdirectories.

`--suppress-theorems`

When a file contains one or more proof declarations inside of it, Deduce will create a `.thm` file. However, this argument makes it such that Deduce never creates such files.

`--traceback`

Prints out the exception if processing a file triggers an error.

`--unique-names`

Prints out all variables and types with an unique name. For example,
if a program defines a variable `x` in several different scopes, `x`
would instead be printed out as `x.1` in one scope and printed as
`x.2` in a different scope.

`--verbose`

Makes Deduce print out the debug logs. It is generally recommended to
use `--traceback` instead, as this argument can make Deduce print out
thousands of lines.

By default, `--verbose` only prints debug logs for the current file.
If ran as `--verbose full` it also prints debug logs for all imported
files as well.

`--error`

Deduce will expect all files that it processes to contain an error. If
there is a file that does not contain an error, Deduce will exit with
a return code of 255.

`--no-check-imports`

Deduce will no longer check the proofs of imported files.

`--compile`

Translate the file to a self-contained C program instead of just
checking it. Pair with `-o <path>` to control the output filename.
See [Compiling Deduce Programs to C](./compiler.html) for the full
walkthrough.
