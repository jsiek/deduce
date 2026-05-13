"""Latency benchmark for ``check_file`` (Phase 1 / Step 8).

Compares two ways of running the Deduce pipeline on a fixture:

* **Cold subprocess** -- ``python3 deduce.py file.pf``, which is what
  the CLI does and what the proof-writing inner loop pays today.
  Each invocation re-launches the interpreter, re-parses the
  standard library prelude, and runs the user file.

* **Warm in-process** -- ``lsp.query.check`` after the prelude has
  been loaded once (the snapshot/restore mechanism from Step 6).
  Each call only re-parses + re-checks the user file; the lib
  modules are reused.

The benchmark prints a side-by-side table and reports the speedup
factor for each fixture. The first MCP call per process is the
prelude bootstrap and is reported separately -- it's a one-time
cost a long-running daemon (the MCP server) only pays at startup.

Note about ``.thm`` caching
---------------------------

Both the cold and warm paths benefit from ``lib/*.thm`` files
generated during the first ``make tests-lib`` run -- they let the
proof checker skip re-proving the standard library. With the .thm
cache present (the typical developer state) cold latency is ~1s
per file. Without it (fresh checkout), cold latency is closer to
~13s, and the daemon bootstrap pays the same one-time cost. The
warm-path latency is ~0.2-0.7s in either case because the
in-memory snapshot doesn't depend on .thm files.

Run::

    python3 lsp/benchmark.py
    python3 lsp/benchmark.py path/to/file.pf path/to/another.pf
"""

from __future__ import annotations

import statistics
import subprocess
import sys
import time
from pathlib import Path
from typing import Callable


REPO_ROOT = Path(__file__).resolve().parent.parent

# Default fixtures: small/medium/large by line count, all inside
# test/should-validate so they're known to validate cleanly with the
# stdlib auto-prelude. (Files that redefine ``Nat`` etc. -- e.g.
# after.pf -- clash with the auto-prelude and are skipped.)
DEFAULT_FIXTURES: tuple[str, ...] = (
    "test/should-validate/IntTests.pf",
    "test/should-validate/NatTests.pf",
    "test/should-validate/ListTests.pf",
    "test/should-validate/LogTests.pf",
    "test/should-validate/UIntLogTests.pf",
)

# How many timing samples to take per phase. Median is reported so
# outliers (GC pauses, OS scheduling) don't skew the headline.
RUNS = 3


def _median(samples: list[float]) -> float:
    return statistics.median(samples)


def _measure(label: str, fn: Callable[[], None], runs: int = RUNS) -> float:
    """Time ``fn`` ``runs`` times, return the median seconds."""
    times: list[float] = []
    for _ in range(runs):
        t0 = time.perf_counter()
        fn()
        times.append(time.perf_counter() - t0)
    return _median(times)


def _cold_run(fixture: str) -> None:
    """Run ``deduce.py`` on ``fixture`` in a fresh subprocess."""
    cmd = [
        sys.executable,
        str(REPO_ROOT / "deduce.py"),
        "--quiet",
        "--suppress-theorems",
        fixture,
    ]
    result = subprocess.run(cmd, cwd=REPO_ROOT, capture_output=True)
    if result.returncode != 0:
        sys.stderr.write(
            f"\n[benchmark] WARNING: cold run for {fixture} exited with "
            f"{result.returncode}:\n{result.stderr.decode(errors='replace')}\n"
        )


def _set_up_query_environment() -> tuple[Callable[[str], None], tuple[str, ...]]:
    """Configure Deduce for in-process use and return ``(check, prelude)``.

    Mirrors what ``deduce.py``'s ``__main__`` and ``lsp.mcp_server``
    do at startup -- import directories, recursion limit, quiet mode
    -- so the warm-path measurement matches what the MCP server
    actually pays per call.
    """
    sys.path.insert(0, str(REPO_ROOT))
    sys.argv = [str(REPO_ROOT / "deduce.py")] + sys.argv[1:]
    sys.setrecursionlimit(10000)

    from abstract_syntax import (
        add_import_directory,
        init_import_directories,
    )
    from flags import set_quiet_mode

    set_quiet_mode(True)
    init_import_directories()
    add_import_directory(str(REPO_ROOT / "lib"))
    add_import_directory(str(REPO_ROOT / "test" / "test-imports"))

    from lsp.query import check as query_check

    lib_dir = REPO_ROOT / "lib"
    prelude = tuple(sorted(p.stem for p in lib_dir.glob("*.pf")))

    def runner(path: str) -> None:
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()
        diagnostics = query_check(path, content, prelude=prelude)
        # Sanity: the fixtures are in should-validate so they should
        # produce no diagnostics. Don't fail the benchmark if one
        # slips through, just flag it.
        if diagnostics:
            sys.stderr.write(
                f"\n[benchmark] WARNING: warm run for {path} returned "
                f"{len(diagnostics)} diagnostic(s)\n"
            )

    return runner, prelude


def _format_seconds(s: float) -> str:
    return f"{s:5.2f}s"


def main(argv: list[str]) -> int:
    fixtures = argv if argv else list(DEFAULT_FIXTURES)
    abs_fixtures: list[Path] = []
    for f in fixtures:
        p = Path(f)
        if not p.is_absolute():
            p = (REPO_ROOT / f).resolve()
        if not p.exists():
            sys.stderr.write(f"[benchmark] missing fixture: {f}\n")
            return 1
        abs_fixtures.append(p)

    print(f"Repo root:  {REPO_ROOT}")
    print(f"Python:     {sys.version.split()[0]}")
    print(f"Runs/phase: {RUNS} (median reported)\n")

    runner, prelude = _set_up_query_environment()
    print(f"Prelude size: {len(prelude)} modules from lib/\n")

    # The very first warm call bootstraps the prelude. Time it
    # separately so the per-fixture warm rows are post-bootstrap.
    print("Bootstrapping prelude (one-time per daemon)...")
    bootstrap = _measure("bootstrap", lambda: runner(str(abs_fixtures[0])), runs=1)
    print(f"  bootstrap+first check on {abs_fixtures[0].name}: {_format_seconds(bootstrap)}\n")

    header = f"{'File':<48}{'Cold':>10}{'Warm':>10}{'Speedup':>12}"
    sep = "-" * len(header)
    print(header)
    print(sep)

    for fixture in abs_fixtures:
        rel = fixture.relative_to(REPO_ROOT)
        cold = _measure(f"cold:{rel}", lambda: _cold_run(str(fixture)))
        warm = _measure(f"warm:{rel}", lambda: runner(str(fixture)))
        speedup = cold / warm if warm > 0 else float("inf")
        print(
            f"{str(rel):<48}{_format_seconds(cold):>10}"
            f"{_format_seconds(warm):>10}{speedup:>11.1f}x"
        )

    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
