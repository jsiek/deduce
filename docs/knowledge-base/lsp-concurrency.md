# Concurrency in the LSP server

The LSP server (`lsp/lsp_server.py`) runs checks on one thread while
another reads new messages and may interrupt them. This page describes
how it is built and the rules that keep it correct. Read it before
changing `lsp/lsp_server.py`, `lsp/worker.py`, or anything that adds
module-level state to the pipeline.

The CLI (`deduce.py`) and the MCP server check on a single thread. The
DAP server (`lsp/dap_server.py`) runs the debugged program on its own
thread, but never interrupts it asynchronously; `check_file`'s lock
keeps it from overlapping another check.

## Architecture

```
 client ──stdio──▶ I/O loop thread (asyncio, pygls)
                     │  reads every message, owns the protocol
                     │  submit(job) ─────────────▶ worker thread (lsp/worker.py)
                     │                               runs one job at a time:
                     │  await future ◀─────────────  a document check or a request
                     ▼
 client ◀──stdio── results, diagnostics, log messages (sent from the I/O loop)
```

There are exactly two threads:

| Thread | What it does | What it owns |
|---|---|---|
| **I/O loop** (pygls's asyncio loop) | Reads messages, submits jobs, awaits their futures, sends responses and notifications. | The pygls protocol and transport, the workspace's documents, `lsp_server._checks`. |
| **Worker** (`Worker` in `lsp/worker.py`, 256 MB stack) | Runs jobs in submission order, one at a time. | Everything the Deduce pipeline touches: `flags` (including the import directories), the `abstract_syntax` globals, the caches in `lsp/library.py` and `lsp/query.py`, the statement cache, `lsp_server._workspace_dirs`. |

On the iPad, the app's own large-stack thread runs the I/O loop, and the
app's Stop button calls `lsp_server.interrupt()` from yet another thread.
That call only touches `Worker`'s lock.

### Jobs

- **Requests** are registered with `_feature`. pygls runs the `async`
  wrapper on the I/O loop, and the wrapper runs the plain handler on the
  worker. The handler functions themselves are ordinary functions, so
  the tests call them directly.
- **Document checks** (`didOpen`, `didChange`, `didSave`) are submitted
  with the document's URI as the job's key. A keyed job *supersedes*
  earlier jobs with that key: a queued one is dropped, and a running one
  is interrupted with `CheckSuperseded`. A burst of edits therefore ends
  in one completed check, of the final text.
- **`$/cancelRequest`** cancels the wrapper's asyncio task. The wrapper
  then drops the job if it's still queued, or interrupts it with
  `CheckCancelled`, and the client gets `RequestCancelled`.
- **`interrupt()`** (the iPad's Stop button) interrupts whichever job is
  running.

### Interrupting a job

`Worker` calls `PyThreadState_SetAsyncExc` on the worker thread, which
raises a `CheckCancelled` (or `CheckSuperseded`) at the worker's next
bytecode boundary, wherever it is: in the middle of a statement, inside
a `finally`, inside a context manager's cleanup. Both are
`BaseException`s, so the checker's `except Exception` handlers don't
turn a cancellation into a diagnostic.

An interrupt is only sent while the target job is the running one, and
`Worker._loop` treats an interrupt that arrives while it is clearing
`_running` as that job's outcome. So an interrupt never escapes into the
worker's own loop.

### Why nothing is left half done

An interrupt can skip any cleanup code, so correctness must not depend
on cleanup having run. Three things make sure it doesn't:

1. **Scoped state is reset before every job.** `Worker` runs
   `library.reset_scoped_state()` before each job. It puts every entry
   of `_SCOPED_STATE` back to its idle value: the flags and globals the
   checker sets for part of its work and restores afterwards, such as
   `flags.target_hole_location`, `reduce_all`, and the error sinks. If
   one of those leaked (say `_target_hole`'s `finally` was interrupted),
   the next check would treat every hole as proved.
2. **Post-prelude state is restored before every check.** `check_file`
   restores `_TRACKED_CONTAINERS` and `_TRACKED_SCALARS` from the
   post-prelude snapshot, so a half-imported module doesn't survive.
3. **Caches are written in one assignment, after the work.** The
   statement cache records a verdict only after a statement passes,
   `_hole_checks` stores a result only after `check_file` returns, and
   `_prelude_lemmas` is replaced as a whole tuple.

## Rules

1. **Only the worker runs the pipeline.** Every handler calls
   `check_file`, and the pipeline is built on module-level state, so two
   pipeline calls must never overlap. Don't run a "quick" query on the
   I/O loop or a thread pool: route it through `_feature` or
   `_worker.submit`. (`check_file`'s lock is a second line of defense,
   not the design.) The same goes for configuration the checker reads,
   such as `flags.import_directories`: `find_file` iterates it, so the
   workspace-folder handlers change it with a worker job
   (`_update_workspace_dirs`), never directly from the I/O loop.
2. **Only the I/O loop talks to the client.** Jobs return values; the
   I/O loop sends them. Never call `ls.text_document_publish_diagnostics`,
   `ls.protocol.notify` or `ls.window_log_message` from a job.
3. **The I/O loop never blocks on the worker.** It `await`s
   `asyncio.wrap_future(future)` and never calls `future.result()`.
   With the worker's lock as the only lock held across threads, and no
   thread holding two locks, there is no deadlock.
4. **Re-check after every `await`.** Another handler may have run in
   between. For example, `_publish_diagnostics` publishes only if its
   check is still the document's entry in `_checks`; otherwise a check
   that finished just before a `didClose` would publish stale
   diagnostics.
5. **Every future finishes.** A submitted job's future must end with a
   result, an exception, or a cancellation, or its request is never
   answered.
6. **New scoped state goes in `_SCOPED_STATE`.** If you add a
   module-level variable that the checker sets and later restores, add it
   to `_SCOPED_STATE` in `lsp/library.py`. If the checker accumulates it
   across a check (a cache, a registry), it belongs in
   `_TRACKED_CONTAINERS` / `_TRACKED_SCALARS` instead. Configuration
   (import directories, the parser) and fresh-name counters belong in
   neither.
7. **Write caches in one assignment, after the work is done.** Never
   leave a cache entry that a later job could read in a half-built
   state.
8. **Keep the I/O loop's state on the I/O loop.** `_checks` and pygls's
   workspace are read and written only by handlers running on the loop.

## Reviewing a change

- Does it run any pipeline code outside a worker job?
- Does it send anything to the client from a job?
- Does any code on the I/O loop wait for the worker?
- After each `await`, does the code still assume something it checked
  before it?
- Does it add module-level state? Which list does it belong in
  (`_SCOPED_STATE`, `_TRACKED_*`, or neither)?
- Is every new submitted future guaranteed to finish?
- Do the new tests force the interleaving they're about (blocking the
  loop, planting state) rather than relying on `sleep` and timing?

## Tests

- `test/lsp/test_lsp_worker.py`: `Worker` ordering, superseding,
  cancelling and interrupting, and the server over stdio (a burst of
  edits publishes once; `$/cancelRequest` interrupts a running request).
- `test/lsp/test_interrupt_fuzz.py`: planted leftover state is reset,
  and interrupting real checks at random points never changes the next
  job's result.
- `test/lsp/test_lsp_server.py::test_check_finished_before_close_is_not_published`:
  forces the `await` race behind rule 4.
