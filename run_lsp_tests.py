#!/usr/bin/env python3
"""Parallel runner for the prelude-heavy ``test/lsp`` suite.

Every LSP test calls ``check_file``, which builds the Deduce prelude.
Run as one ``pytest test/lsp`` process the whole tree accumulates that
state across ~370 tests until peak memory is large enough to get the
process OOM-killed on a memory-constrained machine -- and even when it
fits, it runs serially in ~3+ minutes.

Running each test *file* in its own ``pytest`` subprocess frees that
memory between files (peak is one file's worth, not the whole tree's)
and lets us fan the files out across cores. The full suite then
finishes in well under three minutes with no loss of coverage.

Usage::

    python run_lsp_tests.py                 # default: test/lsp, capped workers
    python run_lsp_tests.py -j 8            # more workers
    python run_lsp_tests.py test/lsp test/unit
    python run_lsp_tests.py --deadline 180 # fail if wall time exceeds 180s

Exit status is non-zero if any test file fails or the deadline is
exceeded, so it is safe to use as a ``make`` target / CI step.
"""

from __future__ import annotations

import argparse
import concurrent.futures as cf
import os
import signal
import subprocess
import sys
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent

# Cap concurrency independently of core count: each worker holds a full
# prelude in memory, so peak memory is (workers x one file). Six keeps
# peak well under the single-process serial peak that OOMs, while still
# collapsing wall time on a typical multi-core machine.
DEFAULT_WORKER_CAP = 6
DEFAULT_DEADLINE_SECONDS = 180.0
# Per-file wall-time cap. The debugger / DAP-session tests drive a real
# debug subprocess and can wedge on a timeout if it can't start (e.g. in
# a constrained sandbox), taking many minutes. A per-file cap kills such
# a file and reports it instead of letting it sink the whole run; a
# healthy machine never reaches it, so coverage is unaffected.
DEFAULT_FILE_TIMEOUT_SECONDS = 120.0


def discover_test_files(paths: list[str]) -> list[Path]:
    """Expand ``paths`` (files or directories) into a list of test files,
    largest-first so the slowest files start while workers are free."""
    files: list[Path] = []
    for raw in paths:
        p = (REPO_ROOT / raw).resolve()
        if p.is_dir():
            files.extend(sorted(p.glob("test_*.py")))
        elif p.is_file():
            files.append(p)
        else:
            print(f"warning: no such test path: {raw}", file=sys.stderr)
    # Bigger files first: a crude proxy for runtime that improves packing.
    files.sort(key=lambda f: f.stat().st_size, reverse=True)
    return files


def run_one(path: Path, timeout: float) -> tuple[Path, int, float, str, bool]:
    """Run one test file in its own pytest process. Returns
    ``(path, returncode, seconds, combined_output, timed_out)``. On
    timeout the process group is killed and ``timed_out`` is True."""
    start = time.monotonic()
    proc = subprocess.Popen(
        [
            sys.executable,
            "-m",
            "pytest",
            str(path),
            "-q",
            "-p",
            "no:cacheprovider",
        ],
        cwd=str(REPO_ROOT),
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        # Own process group so a wedged debug subprocess is killed too.
        start_new_session=True,
    )
    try:
        out, _ = proc.communicate(timeout=timeout if timeout > 0 else None)
        return path, proc.returncode, time.monotonic() - start, out, False
    except subprocess.TimeoutExpired:
        try:
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            proc.kill()
        out, _ = proc.communicate()
        return path, 1, time.monotonic() - start, out or "", True


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "paths",
        nargs="*",
        default=["test/lsp"],
        help="test files or directories (default: test/lsp)",
    )
    parser.add_argument(
        "-j",
        "--workers",
        type=int,
        default=min(os.cpu_count() or 4, DEFAULT_WORKER_CAP),
        help=f"parallel workers (default: min(cores, {DEFAULT_WORKER_CAP}))",
    )
    parser.add_argument(
        "--deadline",
        type=float,
        default=DEFAULT_DEADLINE_SECONDS,
        help="fail if total wall time exceeds this many seconds "
        f"(default: {DEFAULT_DEADLINE_SECONDS:g}; 0 disables)",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=DEFAULT_FILE_TIMEOUT_SECONDS,
        help="kill and fail any single test file exceeding this many "
        f"seconds (default: {DEFAULT_FILE_TIMEOUT_SECONDS:g}; 0 disables)",
    )
    args = parser.parse_args(argv)

    files = discover_test_files(args.paths)
    if not files:
        print("no test files found", file=sys.stderr)
        return 1

    workers = max(1, min(args.workers, len(files)))
    print(
        f"running {len(files)} test file(s) across {workers} worker(s)...",
        flush=True,
    )

    start = time.monotonic()
    results: list[tuple[Path, int, float, str, bool]] = []
    with cf.ThreadPoolExecutor(max_workers=workers) as pool:
        for result in pool.map(lambda f: run_one(f, args.timeout), files):
            path, rc, secs, _, timed_out = result
            status = "TIMEOUT" if timed_out else ("PASS" if rc == 0 else "FAIL")
            rel = path.relative_to(REPO_ROOT)
            print(f"  [{status:7}] {secs:6.1f}s  {rel}", flush=True)
            results.append(result)
    total = time.monotonic() - start

    failures = [
        (p, out, timed_out)
        for (p, rc, _, out, timed_out) in results
        if rc != 0
    ]
    for path, out, timed_out in failures:
        why = "TIMED OUT" if timed_out else "FAILED"
        print(f"\n===== {why}: {path.relative_to(REPO_ROOT)} =====")
        print(out.rstrip())

    slowest = sorted(results, key=lambda r: r[2], reverse=True)[:5]
    print("\nslowest files:")
    for path, _rc, secs, _out, _to in slowest:
        print(f"  {secs:6.1f}s  {path.relative_to(REPO_ROOT)}")
    print(f"\ntotal wall time: {total:.1f}s ({len(files)} files, {workers} workers)")

    ok = not failures
    if not ok:
        n_timeout = sum(1 for _, _, to in failures if to)
        print(
            f"\n{len(failures)} file(s) FAILED ({n_timeout} timed out)",
            file=sys.stderr,
        )
    if args.deadline > 0 and total > args.deadline:
        print(
            f"\nDEADLINE EXCEEDED: {total:.1f}s > {args.deadline:g}s",
            file=sys.stderr,
        )
        ok = False
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
