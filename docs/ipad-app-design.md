# Deduce for iPad: design

Status: design, nothing built yet. Tracking issue: #1213. The app will
live in `ipad/`.

## Use cases, in priority order

1. **Undergraduates** writing simple functional programs and proving
   them correct. This is the main use of Deduce today, and the first
   target.
2. **High-school geometry students** writing two-column proofs about
   diagrams. High priority, but it waits on the language and library
   work tracked in #1186.
3. **Researchers** proving programming-language metatheory with LLM
   help. Lowest priority.

## Principles

- **`.pf` is the model; the app is a view.** The app reads and writes
  ordinary `.pf` files, so they keep working with the CLI, the
  autograder, git and the website. Every gesture turns into a text edit
  on the source. What's on screen is a *projection* of the checked AST.
- **What you type and what you see are decoupled.** Input-only syntax
  is hidden, reasons can be folded away, and the screen can show
  formulas the source never states (the checker computed them).
- **Hybrid editing.** Structure for navigation, display and the common
  tactics. Any node can still be edited as text, re-parsed when the
  edit is committed, so experienced users are never slower than in a
  text editor.
- **Offline is a hard requirement** (classrooms, exams). The checker
  runs on the device.

## Architecture

```
SwiftUI views ── projections (textbook, two-column, source) ── gestures
      │                                                          │
      ▼                                                          ▼
Swift LSP client  ◀── JSON-RPC over an in-process pipe pair ──▶  edits
      │
      ▼
Embedded CPython 3.13 (dedicated thread with a large stack)
  └─ lsp/lsp_server.py → lsp/query.py → the Deduce checker → lib/*.pf
```

- **Embedded CPython.** iOS has been an official CPython platform
  since 3.13 (PEP 730). The app bundles the Python framework, the
  pure-Python dependencies (`lark`, `pygls`, `lsprotocol`, `cattrs`,
  `attrs`), the checker sources and `lib/`. No compiled extensions
  beyond the standard library. Porting the checker to Swift was
  rejected: two checkers would drift apart.
- **The existing LSP server, in-process.** iOS doesn't let an app
  spawn subprocesses, so the server runs on its own thread and talks
  over a pipe pair. Anything that shells out (for example
  `SubprocessValidator` in `tools/claude_fill_hole`) is unavailable;
  use the in-process `deduce/validateProof` instead.
- **Stack size.** `RECURSION_LIMIT` is 40000 (`flags.py`), but iOS
  gives secondary threads a 512 KB stack by default. C-level recursion
  (`repr`, dataclass `__eq__`, lark) would crash rather than raise
  `RecursionError`, so the interpreter thread needs a large stack set
  explicitly.
- **Swift client.** ChimeHQ's `LanguageServerProtocol` /
  `LanguageClient` packages, or hand-written JSON-RPC; the spike
  (#1220) decides.

## Protocol: the LSP, extended

The app uses the same LSP server as Emacs and VS Code. That server
already has most of what the app needs (`deduce/goalAt`,
`caseSplitAt`, `eliminateAt`, `fillFromGivenAt`, `availableLemmasAt`,
`insertLemma`, `holeContextAt`, `validateProof`), and its results are
text edits, which fits "`.pf` is the model". New capabilities go into
`lsp/query.py` and `lsp/lsp_server.py`, so every client gets them and
they're testable with pytest on a Mac:

| Gap | Issue |
|---|---|
| `goal_at` costs a re-check per position; a whole-proof view needs every step's goal and formula from one check | #1214 `deduce/proofOutline` |
| Formulas are strings; tapping a subterm needs a tree with paths | #1215 |
| Actions target holes only; textbook editing acts on a subterm of the goal ("rewrite *this*") | #1219 |
| `preview_*_at`, `apply_at`, `auto_rules_at` are reachable only through MCP | #1216 |

## Incremental checking

Current state: `checker_cache.py` caches each top-level statement's
verdict, keyed by the statement's hash and a fingerprint of its
dependencies, and `lsp/library.py` restores an in-memory snapshot taken
after the prelude was checked. Still missing:

- **Saving the prelude snapshot to disk** (#1217). Without it, every
  cold launch re-checks the whole stdlib. That is the biggest unknown
  in this plan, and the spike (#1220) measures it first.
- **Re-parsing only changed statements, and cancelling stale checks**
  (#1218). A UI that edits on every gesture triggers a check nearly
  every time.

## Textbook view

Take `length_append` from `lib/List.pf`:

```
theorem length_append: all U :type, xs :List<U>, ys :List<U>.
  length(xs ++ ys) = length(xs) + length(ys)
proof
  arbitrary U :type
  induction List<U>
  case [] {
    arbitrary ys:List<U>
    conclude length(@[]<U> ++ ys) = length(@[]<U>) + length(ys)  by {
      expand operator++ | length.
    }
  }
  case node(n, xs') suppose IH {
    arbitrary ys :List<U>
    equations
      length(node(n,xs') ++ ys)
          = 1 + length(xs' ++ ys)              by expand operator++ | length.
      ... = 1 + (length(xs') + length(ys))     by replace IH[ys].
      ... = #length(node(n,xs'))# + length(ys) by expand length.
  }
end
```

It renders roughly as:

> **Theorem.** length(xs ++ ys) = length(xs) + length(ys)
>
> *Proof.* By induction on xs.
>
> **Case [].** Immediate from the definitions. ⓘ
>
> **Case node(n, xs′).** Assume IH.
>
>     length(node(n,xs′) ++ ys)
>       = 1 + length(xs′ ++ ys)               def. of ++, length
>       = 1 + (length(xs′) + length(ys))      IH
>       = length(node(n,xs′)) + length(ys)    def. of length      ∎

Rules:

1. **Input-only syntax is hidden:** `#…#` marks, `arbitrary` for type
   parameters, `by { … }` braces.
2. **Each reason has three levels:** full source, a summary chip
   generated from the lemmas, definitions and givens the step uses, or
   hidden. Tap to cycle. A document-wide default lives in settings, and
   an assignment can force reasons to show (students should still learn
   them).
3. **Formulas the source doesn't state are shown.** After a bare
   `replace` or `expand`, the view shows the formula the checker
   computed. A "make explicit" action writes it into the source as an
   `equations` step or a `have`, so the proof is easier to read and
   less fragile.
4. **The goal is context, not proof text.** In edit mode, each step
   shows the goal and givens around it (like Lean's infoview). In
   reading mode they're hidden.
5. **Backward steps read as prose:** "By induction on xs", "Assume IH",
   "It suffices to show …".

The two-column geometry format (#1194) is the same projection with
reasons moved into a right-hand column.

## Editing interactions

The starting set ports the Emacs and VS Code actions (full table in
#1222):

- **Holes** are tappable chips. Tapping one offers refine (a
  goal-directed introduction), induction, case split, or eliminating a
  given.
- **Givens** that match the hole glow. Drag one onto the hole to use
  it.
- **Lemma side panel**, ranked by `availableLemmasAt`. Dropping a lemma
  inserts an `apply` with one `?` per premise, so the user doesn't have
  to remember how many premises it has.
- **Long-press previews** the goal that would result, before
  committing (#1216).
- **Tap a subterm** of the goal to rewrite or expand that occurrence
  (#1219).
- **Programs:** inline results of `print` / `assert`, a definition
  popover (useful right before "expand length"), and step-through
  evaluation via `lsp/dap_server.py`.
- **Text islands:** any step can be opened as text (`UITextView` /
  TextKit 2; SwiftUI's `TextEditor` is too limited). A math-symbol
  keyboard row and a hardware keyboard both work.

Formulas are drawn from the formula trees (#1215), not from strings,
so every subterm can be tapped.

## Geometry (later)

- **Constructions live in the `.pf`.** Per #1192, a figure is an
  ordinary Deduce function built from construction primitives, with
  sample parameter values as a consistency witness. Building a diagram
  in the UI (tap to place free points; pick "midpoint", "perpendicular
  through", "intersection", …) therefore turns into text edits on that
  function, like every other gesture.
- **The diagram canvas** evaluates the construction numerically, as the
  web sandbox's diagram pane does (#1195), and the two should share the
  evaluator's semantics. Dragging a free point re-runs the
  construction. Tapping an object inserts its name into the step being
  edited. Selecting a two-column row highlights the objects it
  mentions.
- **The sidecar diagram file** (`foo.pf.diagram.json`) holds only view
  state: viewport, label offsets, styling, hidden auxiliary objects,
  and the current dragged sample values if they differ from the
  witness. Nothing in it affects checking. Deleting it loses only
  layout.
- **Diagram facts are explicit.** Facts read off the figure
  (betweenness, same side) come in through #1192's selectors, never
  from the picture itself.

## LLM assistance (use case 3)

The tool-use loop runs in Swift (`URLSession`) against an
OpenAI-compatible endpoint, initially IU REALLMs (as the hole-fill
tool's `openai-compat` backend does), and calls `deduce/validateProof`
in-process. Doing it in Swift avoids bundling the OpenAI Python SDK,
whose `pydantic-core` dependency is a compiled Rust extension. LLM
features are online-only and disable themselves cleanly when offline.
Open question: REALLMs is available to IU researchers, faculty and
staff, so student access needs checking before LLM help reaches
undergraduates.

## Files

- **Opening files.** A `DocumentGroup` over the Files app and iCloud
  Drive. Researchers can work in a git checkout through Files
  providers such as Working Copy.
- **Bundled stdlib.** The app ships its own read-only `lib/` and a
  pre-built prelude snapshot (#1217). User libraries go in the
  equivalent of `~/.config/deduce/libraries`.

## Roadmap

1. **Spike** (#1220): embedded CPython, the in-process LSP,
   diagnostics for a file opened from Files, plus measurements.
2. **Backend:** #1214, then #1215, #1216 and #1217, built in parallel
   with the app.
3. **Slice 1** (#1221): the read-only textbook view.
4. **Slice 2** (#1222): editing gestures, then #1219 subterm actions
   and #1218 for responsiveness.
5. **Geometry**, once #1191–#1194 land: two-column view and diagram
   canvas.
6. **LLM assistance.**
