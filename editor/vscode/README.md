# Deduce for VS Code

The canonical VS Code extension for the [Deduce][deduce] proof
checker.  Lives in-tree alongside the language and is versioned in
lockstep with it.

[deduce]: https://github.com/jsiek/deduce

> **Status (May 2026):** the extension ships syntax highlighting
> (Phase 6 / Step 27 of `docs/lsp-plan.md`) and the debugger
> integration (Phase 5 / Step 26).  The LSP client wiring and
> goal-at-point command are the next chunks; until they land,
> diagnostics still require running `python deduce.py` from a
> terminal.

## What ships today

- **Syntax highlighting** for `.pf` files via the TextMate grammar
  at `syntaxes/deduce.tmLanguage.json`.  Keyword, type, constant,
  comment, numeric, and "warning" (standalone `?`, `sorry`)
  categories mirror the Emacs `deduce-mode` font-lock rules.
  Capitalized identifiers — user-defined Union types and
  constructors — are heuristically rendered with the type face.
- **Language configuration** (`language-configuration.json`) for
  `Cmd+/` line-comment toggling, `/* */` block-comment toggling,
  bracket matching and auto-closing for `{}` / `[]` / `()`, and
  a word pattern that treats `'`, `!`, `?` as identifier
  continuation characters so word motion (M-f / Ctrl-Right) stops
  at the right boundaries for names like `theorem1'?`.
- A `type: "deduce"` **debugger** contribution.  When you launch a
  debug session, the extension spawns
  `<deduce.pythonPath> <deduce.deduceRoot>/lsp/dap_server.py` as
  the DAP adapter and wires the standard VS Code debug UI
  (gutter breakpoints, the call-stack panel, the locals view, the
  Debug Console, the step/over/in/out toolbar) to it.

## Prerequisites

- VS Code 1.80 or newer.
- Python 3.11+ with `lark==1.2.2` installed (the same prerequisites
  as `deduce.py` itself).  See *Settings* below if your default
  `python3` doesn't have `lark`.
- A Deduce checkout (this repository).  By default the extension
  expects `.pf` files to live inside the checkout so the adapter
  can find `lsp/dap_server.py`; set `deduce.deduceRoot` otherwise.
- The `code` CLI helper if you want to launch from a terminal
  (used in the install snippets below).  Install via VS Code's
  Command Palette: `Cmd+Shift+P` → "Shell Command: Install 'code'
  command in PATH".

## Install

Two paths.  For day-to-day use, package and install; for trying it
out, run from source.

### Run from source (no install)

```sh
code --extensionDevelopmentPath="$(pwd)/editor/vscode" /path/to/your/proofs
```

VS Code opens a fresh window with the extension active for that
session only.  Useful while iterating on the extension itself.

The first time you open a directory, VS Code asks whether to
trust the authors — accept it ("Yes, I trust the authors") so
debug sessions are allowed.

### Install permanently

Package into a `.vsix` and install.  Requires [`vsce`][vsce]:

```sh
cd editor/vscode
npx vsce package           # produces deduce-0.1.0.vsix
code --install-extension deduce-0.1.0.vsix
```

[vsce]: https://github.com/microsoft/vscode-vsce

When the extension stabilises we'll publish to the Marketplace and
this section will gain a `Install Extension` link.

## Wire up your workspace

Drop a `launch.json` into your workspace's `.vscode/` (template in
[`launch.json.sample`](launch.json.sample)):

```json
{
  "version": "0.2.0",
  "configurations": [
    {
      "type": "deduce",
      "request": "launch",
      "name": "Debug current Deduce file",
      "program": "${file}",
      "cwd": "${workspaceFolder}"
    }
  ]
}
```

`${workspaceFolder}` should be (or contain) your Deduce checkout
so the adapter can find `lsp/dap_server.py`.  If your proofs live
elsewhere, set the `deduce.deduceRoot` setting (see *Settings*
below) to point at your Deduce repo root.

With no `launch.json` at all, F5 still works: VS Code's debug
picker offers the "Deduce" snippet from this extension's
`initialConfigurations`.

## Settings

The extension exposes two settings under the `Deduce` group
(`Cmd+,` → search for "deduce" or edit JSON):

| Setting              | Default     | Effect                                                                                |
| -------------------- | ----------- | ------------------------------------------------------------------------------------- |
| `deduce.pythonPath`  | `"python3"` | Path to the Python interpreter used to run the debug adapter (`lsp/dap_server.py`).  Must have `lark` installed.  Absolute paths are supported; otherwise looked up on `$PATH`. |
| `deduce.deduceRoot`  | `""`        | Absolute path to your Deduce **installation** — the directory containing `lsp/dap_server.py`.  **Not** your proofs directory.  Defaults to the workspace folder when empty.  Set this only when your workspace is your proofs directory and the Deduce checkout lives elsewhere. |

**Common pitfall on macOS:** the default `python3` on `$PATH` may
not be the interpreter you `pip install lark`ed into.  If F5
fails with "Debug Adapter process has terminated unexpectedly" or
a `ModuleNotFoundError`, point the extension at the right one:

```json
{
  "deduce.pythonPath": "/Library/Frameworks/Python.framework/Versions/3.13/bin/python3.13"
}
```

You can put this in either your workspace settings (`.vscode/settings.json`)
or User settings (Cmd+, → switch to JSON view).

Confirm the right interpreter from a shell first:

```sh
python3.13 -c 'import lark; print(lark.__version__)'
```

If that prints a version (e.g. `1.2.2`), `python3.13` is the
binary to put in `deduce.pythonPath`.

**Proofs outside the Deduce checkout.**  If your `.pf` files live
in (say) `~/courses/cs401/proofs/` and you've cloned Deduce to
`~/src/deduce/`, open the proofs directory as your VS Code
workspace and set `deduce.deduceRoot` to the Deduce installation:

```json
{
  "deduce.deduceRoot": "/Users/you/src/deduce"
}
```

The setting is the path to where `lsp/dap_server.py` is — i.e.
your Deduce *installation*.  It's not the path to your project
directory; VS Code already knows that as the workspace folder.

## Manual smoke test

After installing, wiring `launch.json`, and (if needed) setting
`deduce.pythonPath`:

1. **Open a `.pf` file** with a top-level `print` or `assert` —
   e.g. `tmp/debugger_smoke.pf` if you've worked through the
   [Debugger.md](../../gh_pages/doc/Debugger.md) walkthrough, or
   any prelude module under `lib/`.

2. **Press F5** (or *Run → Start Debugging*).  Within a couple of
   seconds the debug toolbar appears at the top of the window and
   the debugger pauses at the first user-level statement of the
   file — VS Code highlights the matching line with a yellow
   gutter arrow.  The left sidebar shows the **VARIABLES**,
   **WATCH**, **CALL STACK**, and **BREAKPOINTS** panels.

   If the toolbar appears then disappears immediately, see the
   *Troubleshooting* section below — most often it's the
   `python3` / `lark` mismatch.

3. **Step through.**  Use the toolbar buttons or the keyboard:
   - *Continue* (F5) — run until next breakpoint or end.
   - *Step Over* (F10) — advance one top-level statement,
     stepping *over* function calls.
   - *Step Into* (F11) — enter the next function call.
   - *Step Out* (Shift+F11) — run until the current function
     returns.

4. **Watch the locals.**  When you step into a recursive function
   such as `count_down(suc(n'))`, the **VARIABLES → Locals**
   panel should show the pattern-bound `n'` (click the chevron
   to expand if collapsed).  Each recursive descent updates it.

5. **Set a breakpoint.**  Click the gutter to the left of a line
   number — a red dot appears.  Press F5; execution resumes and
   pauses at the dot.  Breakpoints can be set before *or* during
   a session.

6. **Evaluate expressions.**  In the **DEBUG CONSOLE** panel at
   the bottom, type a Deduce expression — `suc(zero)`,
   `suc(zero) + suc(zero)`, `count_down(suc(zero))`, etc. — and
   press Enter.  VS Code sends a DAP `evaluate` request; the
   reduced value comes back inline.  Same reducer the CLI's
   `print <expr>` command uses (see
   [Debugger.md](../../gh_pages/doc/Debugger.md) for the full
   command surface).

7. **Stop the session.**  Click the red square in the toolbar, or
   press Shift+F5.  VS Code sends a DAP `disconnect`; the adapter
   exits cleanly and the toolbar disappears.

## Troubleshooting

### "Configured debug type 'deduce' is not supported"

The extension didn't load.  Either:
- You launched VS Code without `--extensionDevelopmentPath` and
  the extension isn't installed.  Re-launch with the flag or
  install via `vsce`.
- You installed the wrong version.  Check *Extensions* in the
  sidebar; `Deduce` should be enabled.

### Debug session exits immediately (toolbar appears then disappears)

By far the most common cause is `lark` not being installed on
whichever interpreter the extension is using.  Diagnose:

```sh
<your python> -m pip show lark
```

If that says "Package(s) not found", install:

```sh
<your python> -m pip install lark==1.2.2
```

Or point the extension at a different interpreter via
`deduce.pythonPath` — see the *Settings* section above for the
exact JSON snippet.

Less common but possible: the adapter can't find
`lsp/dap_server.py`.  This happens if your `.pf` workspace
doesn't contain a Deduce checkout.  Fix by setting
`deduce.deduceRoot` to the absolute path of your checkout.

To see the actual error message, temporarily redirect the
adapter's stderr to a file by editing `editor/vscode/extension.js`
(wrap the spawn in `/bin/sh -c "exec ... 2>>/tmp/dap_stderr.log"`),
then re-run.

### "Couldn't find a debug adapter descriptor for debug type 'deduce' (extension might have failed to activate)"

The extension's JavaScript failed to load.  Two common causes:

- **Syntax error in `extension.js`.**  Run `node --check
  editor/vscode/extension.js` from a shell; fix any error
  reported.  Then reload the window: `Cmd+Shift+P → Developer:
  Reload Window`.
- **Stale cache after editing the extension.**  With
  `--extensionDevelopmentPath`, a fresh `Cmd+Q` + relaunch
  *should* pick up changes, but occasionally a "Code Helper"
  subprocess keeps an older state alive.  Force-reload from the
  Command Palette: `Cmd+Shift+P → Developer: Reload Window`.  If
  that doesn't work, fully quit (`Cmd+Q`) and kill stragglers:
  `killall "Code Helper" "Code Helper (Plugin)" "Code Helper
  (Renderer)" 2>/dev/null`.

Open Developer Tools (*Help → Toggle Developer Tools* → Console)
to see the actual JavaScript error.

### Breakpoints are gray with "Verified: false"

Either the file path doesn't match what the adapter sees, or the
line number is past EOF.  Check that the file you set the
breakpoint on is the same one VS Code is debugging.

### Step Into ignores prelude functions

Expected.  The debugger automatically steps over standard-library
calls; this matches the CLI's behavior and is documented under
[*What the debugger skips* in Debugger.md](../../gh_pages/doc/Debugger.md#what-the-debugger-skips).
Set a function breakpoint on the name (e.g. `length`) to drill in
deliberately.

## Roadmap

Tracked in [`docs/lsp-plan.md`](../../docs/lsp-plan.md)'s Phase 6
section.  In rough landing order:

- **LSP client** (Step 28) wiring `python3 -m lsp.lsp_server` via
  `vscode-languageclient`.  Diagnostics, go-to-definition,
  document outline, and the no-prompt code actions ("Refine
  hole", "Induction") fall out for free — same surface
  [`deduce-lsp.el`](../emacs/deduce-lsp.el) exposes for Emacs.
- **Goal-at-point command** (Step 29) — `Ctrl+Alt+G` issues the
  custom `deduce/goalAt` request and renders the goal in a
  *Deduce Goal* output channel.  Emacs equivalent: `C-c C-g`.
- **Structured-editing commands** (Step 30) — refine, case split,
  induction, eliminate, fill-from-given.  Emacs equivalents:
  `C-c C-{r,c,i,e,f}`.
- **Tab completion** (Step 31).  Needs a new LSP-server feature
  (`textDocument/completion`) returning keywords + in-scope names
  + hole-aware label/variable candidates; once it lands, the LSP
  client picks it up automatically.  Same feature surfaces in
  Emacs as a CAPF.
- **LLM hole filling** (Step 32) — VS Code port of
  [`deduce-fill-hole.el`](../emacs/deduce-fill-hole.el).
- **Marketplace publication** (Step 33) once Steps 27-30 are in.

[kw]: ../../gh_pages/scripts/keywords.py

The replaced unmaintained extension was
[HalflingHelper/deduce-mode][external]; this in-tree directory
takes over and is the place for future contributions.

[external]: https://github.com/HalflingHelper/deduce-mode
