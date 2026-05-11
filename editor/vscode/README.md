# Deduce for VS Code

The canonical VS Code extension for the [Deduce][deduce] proof
checker.  Lives in-tree alongside the language and is versioned in
lockstep with it.

[deduce]: https://github.com/jsiek/deduce

> **Status (May 2026):** the extension currently ships the debugger
> integration (Phase 5 / Step 26 of `docs/lsp-plan.md`).  Syntax
> highlighting and the LSP client wiring will be added in follow-up
> work; today, language-mode features come from any companion
> TextMate / LSP setup you already have.  This directory is the
> place for those additions when they land.

## What ships today

- A `type: "deduce"` debugger contribution that launches
  `python3 -m lsp.dap_server` as the DAP adapter.  Enables the full
  VS Code debug UI for `.pf` files: gutter breakpoints, the
  call-stack panel, the locals view, the Debug Console, and the
  step/over/in/out toolbar.
- A minimal `deduce` language declaration so the debugger
  contribution can attach to `.pf` files.  (No syntax highlighting
  shipped here yet — that's a follow-up.)

## Prerequisites

- VS Code 1.80 or newer.
- Python 3.11+ with `lark` installed (the same prerequisites as
  `deduce.py` itself).
- A Deduce checkout — the same one that contains
  `lsp/dap_server.py`.

## Install

Two paths.  For day-to-day use, package and install; for trying it
out, run from source.

### Run from source (no install)

```sh
code --extensionDevelopmentPath="$(pwd)/editor/vscode" /path/to/your/proofs
```

VS Code opens a fresh window with the extension active for that
session only.  Useful while iterating on the extension itself.

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

`${workspaceFolder}` should be (or contain) your Deduce checkout so
the adapter's `python3 -m lsp.dap_server` resolves on the import
path.  If your proofs live elsewhere, set `cwd` to point at the
Deduce repo root explicitly.

With no `launch.json` at all, F5 still works: VS Code's debug
picker offers the "Deduce" snippet from this extension's
`initialConfigurations`.

## Manual smoke test

After installing and wiring `launch.json`:

1. **Open a `.pf` file** with a top-level `print` or `assert` —
   e.g. `tmp/debugger_smoke.pf` if you've worked through the
   [Debugger.md](../../gh_pages/doc/Debugger.md) walkthrough, or
   any prelude module under `lib/`.

2. **Set a breakpoint.**  Click the gutter to the left of a line
   number; a red dot appears.

3. **Press F5** (or *Run > Start Debugging*).  VS Code spawns the
   adapter, sends `initialize` / `launch` / `setBreakpoints` /
   `configurationDone`, and within a couple of seconds the debug
   toolbar appears at the top of the window.

4. **The debugger pauses** at the first user-level statement of
   the file — VS Code highlights the matching line and *Continue*
   becomes active.  The "Call Stack" view in the left sidebar
   shows the current frame; the "Variables" view shows `Locals`
   (empty at top level; populated once you step into a function).

5. **Step through.**  Use the toolbar:
   - *Continue* (F5) — run until next breakpoint or end.
   - *Step Over* (F10) — advance one top-level statement,
     stepping *over* function calls.
   - *Step Into* (F11) — enter the next function call.
   - *Step Out* (Shift+F11) — run until the current function
     returns.

6. **Watch the locals.**  When you step into a recursive function
   such as `count_down(suc(n'))`, the "Variables" panel should
   show the pattern-bound `n'`.  Each recursive descent updates
   it; each return (visible as the call-stack popping) takes you
   back to the caller's frame.

7. **Evaluate expressions.**  In the *Debug Console* at the bottom
   of the screen, type a Deduce expression — `suc(zero)`,
   `count_down(suc(zero))`, etc. — and press Enter.  VS Code sends
   a DAP `evaluate` request; the reduced value comes back inline.
   This uses the same reducer the CLI's `print <expr>` command
   uses (see [Debugger.md](../../gh_pages/doc/Debugger.md) for the
   full command surface).

8. **Stop the session.**  Click the red square (*Stop*) in the
   toolbar, press Shift+F5, or close the window.  VS Code sends a
   DAP `disconnect`; the adapter exits cleanly.

## Troubleshooting

### "Configured debug type 'deduce' is not supported"

The extension didn't load.  Either:
- You launched VS Code without `--extensionDevelopmentPath` and
  the extension isn't installed.  Re-launch with the flag or
  install via `vsce`.
- You installed the wrong version.  Check *Extensions* in the
  sidebar; `Deduce` should be enabled.

### "Couldn't import lsp.dap_server"

The adapter is launched with `python3 -m lsp.dap_server` from the
configured `cwd`.  Make sure `cwd` is your Deduce checkout
(containing the `lsp/` directory).  You can also set
`PYTHONPATH=/path/to/deduce` in `launch.json` under `env`.

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

- **Syntax highlighting** via a TextMate grammar (`syntaxes/`).
  The keyword list lives in `gh_pages/scripts/keywords.py`; a
  TextMate grammar generator there would keep VS Code and the web
  sandbox aligned.
- **LSP client** wiring `python3 -m lsp.lsp_server` via
  `vscode-languageclient`.  Diagnostics, hover, go-to-definition,
  the goal-at-point command — same surface
  [`deduce-lsp.el`](../emacs/deduce-lsp.el) exposes for Emacs.
- **Marketplace publication** once syntax + LSP are in.

The replaced unmaintained extension was
[HalflingHelper/deduce-mode][external]; this in-tree directory
takes over and is the place for future contributions.

[external]: https://github.com/HalflingHelper/deduce-mode
