#!/usr/bin/env python3
"""Run all hole-fill example fixtures against a list of models, print a table.

Usage::

    REALLMS_API_KEY=... \\
      python3 -m tools.claude_fill_hole.examples.run_benchmark [model ...]

Defaults to the four chat models REALLMs currently exposes
(``Qwen3-Coder-Next``, ``gpt-oss-120b``, ``llama-4-scout``,
``gemma-4-31B-it``).  Pass model names as positional args to
override.

For each (model, fixture) pair the script:

1. Asks ``lsp.query.hole_context_at`` for the fixture's goal /
   givens / lemmas in scope (so we don't need a running LSP daemon
   to drive this).
2. Builds the JSON request shape the sidecar expects on stdin.
3. Spawns ``python -m tools.claude_fill_hole`` with the openai-compat
   backend pointed at REALLMs.
4. Captures the JSON response and the elapsed wall time.

Output is a markdown table summarising success / attempts / elapsed
seconds per cell, plus a per-fixture detail block listing the
candidate proofs each model produced.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time
from pathlib import Path


THIS = Path(__file__).resolve()
EXAMPLES_DIR = THIS.parent
REPO_ROOT = THIS.parents[3]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

# Bootstrap the Deduce checker the same way `lsp.lsp_server' does at
# import.  Without this, the first `check_file' call inside
# `hole_context_at' runs against an unconfigured environment and
# silently produces unexpected results (e.g. None responses when a
# real HoleContext should come back).
sys.argv = [str(REPO_ROOT / "deduce.py")] + sys.argv[1:]
sys.setrecursionlimit(10000)
from abstract_syntax import (  # noqa: E402
    add_import_directory,
    init_import_directories,
)
from flags import set_quiet_mode  # noqa: E402

set_quiet_mode(True)
init_import_directories()
add_import_directory(str(REPO_ROOT / "lib"))

from lsp.query import Position, hole_context_at  # noqa: E402


DEFAULT_MODELS = (
    "Qwen3-Coder-Next",
    "gpt-oss-120b",
    "llama-4-scout",
    "gemma-4-31B-it",
)
BASE_URL = "https://reallms.rescloud.iu.edu/direct/v1"
API_KEY_ENV = "REALLMS_API_KEY"


def find_first_question_mark(content: str) -> tuple[int, int]:
    """Return 0-indexed (line, character) of the first ``?`` in CONTENT."""
    for line_no, line in enumerate(content.splitlines()):
        col = line.find("?")
        if col >= 0:
            return line_no, col
    raise ValueError("no `?` in fixture")


def build_request(fixture: Path) -> dict:
    content = fixture.read_text()
    line0, char0 = find_first_question_mark(content)
    pos = Position(line=line0 + 1, column=char0 + 1)  # query is 1-indexed
    ctx = hole_context_at(
        str(fixture),
        content,
        pos,
        prelude=(),
        include_lemmas=True,
    )
    if ctx is None:
        raise RuntimeError(
            f"hole_context_at returned None for {fixture.name} -- "
            "fixture may have changed, or the prelude needs adjusting."
        )
    return {
        "file": str(fixture),
        "holeRange": {
            "start": {"line": line0, "character": char0},
            "end": {"line": line0, "character": char0 + 1},
        },
        "goal": ctx.goal,
        "givens": [
            {"label": g.label, "formula": g.formula} for g in ctx.givens
        ],
        "lemmasInScope": [
            {"name": lemma.name, "kind": lemma.kind.value,
             "signature": lemma.signature}
            for lemma in ctx.lemmas_in_scope
        ],
        "fingerprint": ctx.fingerprint,
        "content": content,
    }


def run_one(fixture: Path, model: str, max_attempts: int, timeout: int) -> dict:
    request = build_request(fixture)
    cmd = [
        sys.executable, "-m", "tools.claude_fill_hole",
        "--backend", "openai-compat",
        "--base-url", BASE_URL,
        "--api-key-env", API_KEY_ENV,
        "--model", model,
        "--no-stdlib",
        "--deduce-root", str(REPO_ROOT),
        "--max-attempts", str(max_attempts),
        "--timeout", str(timeout),
    ]
    env = {**os.environ, "PYTHONPATH": str(REPO_ROOT)}
    started = time.monotonic()
    try:
        proc = subprocess.run(
            cmd,
            input=json.dumps(request),
            capture_output=True,
            text=True,
            cwd=str(REPO_ROOT),
            env=env,
            timeout=max_attempts * timeout + 60,
        )
    except subprocess.TimeoutExpired as e:
        return {
            "ok": False,
            "error": f"sidecar wall-clock timeout: {e}",
            "attempts": 0,
            "elapsed_s": round(time.monotonic() - started, 1),
            "validations": [],
        }
    elapsed = round(time.monotonic() - started, 1)
    if not proc.stdout.strip():
        return {
            "ok": False,
            "error": f"sidecar exit {proc.returncode}, no stdout",
            "attempts": 0,
            "elapsed_s": elapsed,
            "stderr_tail": proc.stderr[-500:],
            "validations": [],
        }
    try:
        result = json.loads(proc.stdout)
    except json.JSONDecodeError as e:
        return {
            "ok": False,
            "error": f"bad json from sidecar: {e}",
            "attempts": 0,
            "elapsed_s": elapsed,
            "validations": [],
        }
    result["elapsed_s"] = elapsed
    return result


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument(
        "models", nargs="*", default=list(DEFAULT_MODELS),
        help="Models to benchmark (defaults to the four REALLMs chat models)",
    )
    p.add_argument("--max-attempts", type=int, default=5)
    p.add_argument("--timeout", type=int, default=60)
    args = p.parse_args(argv)

    if not os.environ.get(API_KEY_ENV):
        print(f"error: {API_KEY_ENV} not set in environment", file=sys.stderr)
        return 2

    fixtures = sorted(EXAMPLES_DIR.glob("0*_*.pf"))
    if not fixtures:
        print("error: no fixtures found", file=sys.stderr)
        return 2

    results: dict[tuple[str, str], dict] = {}
    for model in args.models:
        for fixture in fixtures:
            print(f"[{model}] {fixture.name} ...",
                  file=sys.stderr, flush=True)
            r = run_one(fixture, model, args.max_attempts, args.timeout)
            results[(model, fixture.name)] = r
            status = "ok" if r.get("ok") else "fail"
            print(f"  -> {status} ({r.get('attempts', 0)} attempts, "
                  f"{r['elapsed_s']}s)", file=sys.stderr, flush=True)

    # Markdown summary table
    print("# Hole-fill benchmark\n")
    print("Each cell: ✓/✗ + attempts + elapsed seconds.\n")
    header = ["Fixture"] + list(args.models)
    print("| " + " | ".join(header) + " |")
    print("|" + "|".join(["---"] * len(header)) + "|")
    for fixture in fixtures:
        row = [fixture.name]
        for model in args.models:
            r = results[(model, fixture.name)]
            tick = "✓" if r.get("ok") else "✗"
            row.append(
                f"{tick} {r.get('attempts', 0)}/{args.max_attempts} "
                f"({r['elapsed_s']}s)"
            )
        print("| " + " | ".join(row) + " |")

    # Per-fixture detail
    print("\n# Per-fixture detail\n")
    for fixture in fixtures:
        print(f"## {fixture.name}\n")
        for model in args.models:
            r = results[(model, fixture.name)]
            print(f"### {model}\n")
            if r.get("ok"):
                print(f"  - **success** in {r['attempts']} attempt(s), "
                      f"{r['elapsed_s']}s")
                print(f"  - proof: `{r.get('proof', '?')}`")
            else:
                print(f"  - **failed** after {r.get('attempts', 0)} "
                      f"attempt(s), {r['elapsed_s']}s")
                if r.get("error"):
                    err = r["error"][:200]
                    print(f"  - error: `{err}`")
            for v in r.get("validations") or []:
                ok = "✓" if v.get("ok") else "✗"
                preview = (v.get("proofPreview") or "").strip()
                err_tail = (v.get("errorTail") or "").splitlines()
                err_first = err_tail[0] if err_tail else ""
                print(f"    - {ok} attempt {v.get('attempt')}: "
                      f"`{preview[:60]}`"
                      + (f" -- {err_first[:80]}" if err_first else ""))
            print()

    return 0


if __name__ == "__main__":
    sys.exit(main())
