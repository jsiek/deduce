# claude_fill_hole — Claude proof-completion sidecar

A standalone Python program that fills a `?` hole in a Deduce proof
by asking Claude. Reads a JSON request on stdin, writes a JSON
response on stdout, streams progress events on stderr.

This is **Phase 2** of the [hole-fill plan](../../docs/hole-fill-plan.md).
Phase 1 (the LSP request handlers `deduce/holeContextAt` and
`deduce/validateProof`) lives in `lsp/`. Phase 3 (the emacs
binding) lives in the separate `deduce-mode` repo.

## Install

```sh
pip install -r ../../requirements-fill-hole.txt
export ANTHROPIC_API_KEY=...
```

## Usage

```sh
python3 -m tools.claude_fill_hole < request.json > response.json 2> progress.ndjson
```

Where `request.json` is the response shape from `deduce/holeContextAt`,
augmented with `file` (path to the source) and optionally `content`
(unsaved buffer text). See [Stdin contract](#stdin-contract) below.

### Smoke test (no API key required)

```sh
python3 -m tools.claude_fill_hole --dry-run < request.json
```

`--dry-run` skips the API entirely, splices a stub proof through the
subprocess validator, and reports whether the splice/validate
pipeline works. Useful for verifying a deployment before configuring
an API key.

### CLI flags

| Flag | Default | Purpose |
|---|---|---|
| `--max-attempts N` | 5 | Maximum number of `validate_proof` calls. |
| `--model MODEL` | `claude-opus-4-7` | Claude model to drive the loop. |
| `--deduce-cmd CMD` | `python3 deduce.py` | Command used to invoke the checker (space-separated). |
| `--deduce-root DIR` | dir of request file | Working directory for `deduce.py`. |
| `--no-stdlib` | off | Pass `--no-stdlib` to `deduce.py` on each call. |
| `--timeout SECS` | 60 | Per-validate timeout. |
| `--api-key-env NAME` | `ANTHROPIC_API_KEY` | Name of env var holding the API key. |
| `--dry-run` | off | Skip the API; smoke-test the validator only. |

## Stdin contract

The sidecar reads one JSON object on stdin. Field names are
LSP-shaped (camelCase) for the parts that mirror
`deduce/holeContextAt`'s response, snake_case otherwise — so emacs
can forward the LSP response directly with minimal munging.

```json
{
  "file": "/abs/path/to/proof.pf",
  "holeRange": {
    "start": {"line": 10, "character": 4},
    "end":   {"line": 10, "character": 5}
  },
  "goal": "P = P",
  "givens": [
    {"label": "H", "formula": "P or Q"}
  ],
  "lemmasInScope": [
    {"name": "list_length_zero", "kind": "lemma",
     "signature": "list_length_zero: ..."}
  ],
  "fingerprint": "sha256:...",
  "content": "<optional, the file's text if the buffer is unsaved>",
  "surroundingExcerpt": "<optional, ~30 lines around the hole>"
}
```

`content` and `surroundingExcerpt` are optional. When `content` is
absent, the sidecar reads `file` from disk. When `surroundingExcerpt`
is absent, the sidecar computes a 30-line slice itself from
`content`.

## Stdout contract

One JSON object on stdout when the loop finishes:

```json
{
  "ok": true,
  "proof": "reflexive",
  "fingerprint": "sha256:...",
  "attempts": 3,
  "elapsedMs": 12345,
  "model": "claude-opus-4-7",
  "validations": [
    {"attempt": 1, "ok": false,
     "proofPreview": "apply ...", "errorTail": "..."},
    {"attempt": 2, "ok": false,
     "proofPreview": "...",       "errorTail": "..."},
    {"attempt": 3, "ok": true,    "proofPreview": "reflexive",
     "errorTail": null}
  ]
}
```

On hard failure (budget exhausted, missing API key, malformed
input): `ok: false`, top-level `error` carrying a message,
non-zero exit code.

## Stderr progress channel

NDJSON — one event per line — so the emacs side can `forward-line`
and parse without a streaming JSON parser:

```
{"event": "start", "fingerprint": "...", "maxAttempts": 5}
{"event": "model_request", "attempt": 1}
{"event": "tool_call", "attempt": 1, "proofPreview": "..."}
{"event": "tool_result", "attempt": 1, "ok": false, "errorTail": "..."}
{"event": "finish", "ok": true, "attempts": 3}
```

Full proof candidates are deliberately *not* streamed on stderr —
only previews. The full `proof` text only appears on stdout at
the end.

## Architecture

```
__main__.py     — CLI entry; argparse, stdin reader, dry-run path
agent.py        — manual tool-use loop (anthropic SDK)
prompt.py       — system prompt assembly, cheatsheet embedding
validator.py    — Validator abstract + SubprocessValidator
schema.py       — request/response/event JSON shapes
```

The system prompt embeds [`TacticsCheatSheet.md`](../../gh_pages/doc/TacticsCheatSheet.md)
and [`CheatSheet.md`](../../gh_pages/doc/CheatSheet.md) verbatim with
prompt caching enabled (`cache_control: {type: "ephemeral"}`), so
the cheatsheet cost is paid once per 5-minute window rather than
once per attempt.

## Security

The sidecar's threat model is "the model writes Deduce text". Risk
surface:

- **Tempfile in the user's directory.** Required so relative `import`
  resolution matches `deduce.py file.pf`. Hidden filename, cleaned
  up after each call.
- **Arbitrary `.pf` text fed to `deduce.py`.** Capped at 32 kB per
  attempt to bound parser DOS. The checker doesn't `eval` Python or
  expand shell commands, so the surface here is no worse than what
  the user could write themselves.
- **Subprocess invocation.** Uses `subprocess.run` with a list (no
  `shell=True`).

Don't run the sidecar against files you wouldn't trust the user
to type into themselves.

## Pluggable validation backend

`validator.py` defines two backends:

| Backend | Status | Cost |
|---|---|---|
| `SubprocessValidator` | implemented | ~0.9–1.4s/attempt warm |
| `LspValidator` | placeholder | bounded by `validate_proof_at` |

`LspValidator` will be wired up once the in-flight
incremental-checking work lands, at which point validation drops
to near-free. Until then, the subprocess path is the one you get.
