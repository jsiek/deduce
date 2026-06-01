# Debugger

Deduce ships with a `gdb`-style debugger for stepping through the
functional parts of a program — top-level `print` and `assert`
statements and the user-defined functions they call.  Use it when a
`print` produces an unexpected value, an `assert` fails, or you want
to watch a recursive function unfold one call at a time.

The debugger does not step through *proofs* (those are static
derivations, not a stepwise execution).  It steps through *terms*.

## Starting a session

Pass `--debug` to the CLI:

```sh
python3 deduce.py --debug your_file.pf
```

The proof checker runs as usual.  When it reaches the first
statement of your file, the debugger pauses and prints a prompt:

```
-> statement at 12:1: count_down
(deduce-debug)
```

You're now at an interactive REPL.  Type `help` for the command
listing, or `quit` (or press `Ctrl-D`) to abort.

## What you see when the debugger pauses

Each pause prints a one-line description of where you are:

| Line                                         | What it means                                |
| -------------------------------------------- | -------------------------------------------- |
| `-> statement at 21:1: print ...`            | About to evaluate a top-level statement.     |
| `-> call double(suc(zero)) at 14:3`          | About to evaluate the body of a function call. |
| `<- returned from double(suc(zero))` <br> `     = suc(suc(zero))` | A call just returned the value shown.        |

After each pause, the debugger prompts for a command.

- Pressing Return with no text **replays the previous command**
  (handy for repeated `step`s).
- A mistyped command is rejected with a hint at the closest match —
  `unrecognized command: 'lis' (did you mean 'list'?)`.

At a terminal, the prompt has full line editing, **tab
completion**, and **persistent history**:

- Pressing Tab at the start of the line completes against the
  command verbs.
- Pressing Tab after `print` or `break` completes against
  identifiers visible in the current scope (top-level definitions
  and the focused frame's pattern bindings).
- Pressing Tab after `clear` completes against the active
  breakpoint specs (so you can finish what you typed to `break`)
  *and* against in-scope identifiers (useful for clearing a
  function-name breakpoint you haven't typed yet).
- Pressing Tab after `delete` completes against the active
  breakpoint ids.
- Up-arrow / down-arrow walk through previously entered commands.
  History is saved at `~/.config/deduce/debug_history` and persists
  across sessions.

## Stepping commands

| Command         | Short | Effect |
| --------------- | ----- | ------ |
| `continue`      | `c`   | Resume execution until the next breakpoint (or the end of the file). |
| `step`          | `s`   | Pause at the very next event — entry into a function, return from a function, or the next top-level statement. |
| `next`          | `n`   | Like `step`, but step *over* function calls instead of into them. Pauses at the next top-level statement. |
| `finish`        | `fin` | Run until the current function returns, then pause. |
| `quit`          | `q`   | Abort the session.  Use `Ctrl-D` for the same effect. |

`step` is the workhorse.  Inside a recursive function, repeated
`step`s walk down the recursion call by call, then back up frame by
frame as each call returns.

## Breakpoints

In the command table below, `<spec>` stands for one of three forms
that name a location:

| Form               | Example         | Meaning |
| ------------------ | --------------- | ------- |
| `<line>`           | `14`            | Line `<line>` of the *current* source file (the file the debugger is currently inside). |
| `<file>:<line>`    | `foo.pf:14`     | Line `<line>` of `<file>`. |
| `<name>`           | `double`        | Every call to the function `<name>`. |

| Command                                    | Short    | Effect |
| ------------------------------------------ | -------- | ------ |
| `break <spec>`                             | `b 14`   | Pause when execution reaches `<spec>`. |
| `break <spec> if <expr>`                   | `b 14 if x = zero` | Pause at `<spec>` only when `<expr>` reduces to `true` in the current scope. |
| `info breakpoints` <br> `info b`           |          | List active breakpoints, with their assigned ids. |
| `delete`                                   | `d`      | Remove all breakpoints. |
| `delete <id>...`                           | `d 1 3`  | Remove specific breakpoints by id (the number `info b` shows in the first column). |
| `clear <spec>`                             | `clear 14`, `clear double` | Remove the breakpoint(s) at `<spec>`. |

A breakpoint that names a function fires on **every** call to that
function — including recursive self-calls.

`delete` and `clear` are separate commands: `delete` takes ids
(from `info breakpoints`), `clear` takes locations (the same form
you wrote with `break`).  Use whichever is more convenient.

Each `break` reports the breakpoint's assigned id:

```
(deduce-debug) b 14
breakpoint 1 set: your_file.pf:14
```

## Inspection

| Command          | Short | Effect |
| ---------------- | ----- | ------ |
| `list`           | `l`   | Show source ±5 lines around the current location, marked with `->`. |
| `print <expr>`   | `p`   | Parse and evaluate `<expr>` in the current scope.  Reuses Deduce's reducer, so the result is what `print <expr>` would have produced. |
| `where` <br> `bt`|       | Show the call stack: frame 0 is the innermost call, increasing outward. |
| `up`             |       | Move the inspection cursor one frame outward (toward the caller). |
| `down`           |       | Move it one frame inward (toward the callee). |
| `locals`         |       | Show the bindings introduced by the current frame (function arguments and pattern-bound names). |
| `help`           | `h`   | Print the command listing. |

`print` is the most useful: at any pause you can ask the debugger
to evaluate an arbitrary Deduce expression in the current
environment.  Names already bound in the surrounding scope — both
top-level definitions and the current frame's pattern bindings —
are visible.

## What the debugger skips

Two policies keep the trace focused on your code:

1. **Standard-library calls are stepped over.**  When you type
   `step` and the next call would enter a function defined in
   Deduce's standard library, the debugger treats it as `next`
   instead — the function runs but no trap fires inside.  You can
   still set an explicit breakpoint on a standard-library function
   (e.g. `b length`) and drill in deliberately.
2. **A small number of internal helpers are hidden completely.**
   These functions exist for the proof checker's bookkeeping and
   would just clutter the trace.  You won't see them in `where`,
   they won't trap on `step`, and setting a breakpoint on them has
   no effect.

This is why a `step` through `print length([zero, suc(zero)])` does
not produce dozens of traps inside the prelude's arithmetic
machinery — it simply runs the call and lands on the next statement.

## Worked example

Given the file `count.pf`:

```deduce
import Nat

recursive count_down(Nat) -> Nat {
  count_down(zero) = zero
  count_down(suc(n')) = count_down(n')
}

print count_down(suc(suc(zero)))
```

Launch the debugger:

```sh
python3 deduce.py --debug count.pf
```

A typical session:

```
-> statement at 3:1: count_down
(deduce-debug) s
-> statement at 8:1: print count_down(suc(suc(zero)))
(deduce-debug) s
-> call count_down(suc(suc(zero))) at 5:3
(deduce-debug) locals
  n' = suc(zero)
(deduce-debug) s
-> call count_down(suc(zero)) at 5:3
(deduce-debug) s
-> call count_down(zero) at 4:3
(deduce-debug) list
    1  import Nat
    2
    3  recursive count_down(Nat) -> Nat {
->  4    count_down(zero) = zero
    5    count_down(suc(n')) = count_down(n')
    6  }
    7
    8  print count_down(suc(suc(zero)))
(deduce-debug) s
<- returned from count_down(zero)
     = zero
(deduce-debug) s
<- returned from count_down(suc(zero))
     = zero
(deduce-debug) s
<- returned from count_down(suc(suc(zero)))
     = zero
(deduce-debug) c
zero
count.pf is valid
```

Notice that each entry shows the argument value the call actually
received, and the matching return prints the same argument
signature alongside its result — so a recursive unwind reads top to
bottom in the order frames pop off the stack.

If you only care about the final value, type `c` from the first
prompt and the file runs to completion as if `--debug` weren't
there.

## Editor integration

Deduce exposes the same debugger over the
[Debug Adapter Protocol](https://microsoft.github.io/debug-adapter-protocol/),
so graphical IDEs can drive it.  Two editor packages ship in this
repository:

- **Emacs** — [`editor/emacs/deduce-dap.el`](../../editor/emacs/deduce-dap.el)
  registers a `dap-mode` debug template.  Install it alongside
  `deduce-mode` / `deduce-lsp` (see
  [`editor/emacs/README.md`](../../editor/emacs/README.md)), then
  press `C-c C-d` in any `.pf` buffer to launch.  Requires the
  `dap-mode` package from MELPA.
- **VS Code** — [`editor/vscode/`](../../editor/vscode/) contains a
  minimal extension that registers the `deduce` debugger type.  Run
  it standalone with
  `code --extensionDevelopmentPath=editor/vscode`, or package it
  into a `.vsix` and install permanently.  Drop the sample
  `launch.json` into your workspace and press F5.  See
  [`editor/vscode/README.md`](../../editor/vscode/README.md) for the
  full instructions.

Both packages launch `python -m lsp.dap_server` as the adapter and
expose the same UI surface as gdb-style debug clients: gutter
breakpoints, a call-stack panel, a locals view, an evaluate-in-REPL
console, and Step Over / Step Into / Step Out / Continue.  The
command-line debugger remains the recommended interface for
quickly iterating on a single proof — the editor packages add value
when you want to set many breakpoints visually or already have a
debug workflow muscle-memoried into your IDE.
