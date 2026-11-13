"""An interrupted job leaves nothing behind (#1218).

The LSP worker (``lsp/worker.py``) interrupts a check wherever it is,
including inside a ``finally`` that restores pipeline state. These tests
check that the next job's result is the same as an uninterrupted one:
first with the leftover state planted directly, then by interrupting
real checks at random points."""

from __future__ import annotations

import os
import random
import time
from pathlib import Path
from typing import Callable

import pytest

pytest.importorskip("pygls")
os.environ["DEDUCE_NO_STDLIB"] = "1"

import error  # noqa: E402
import flags  # noqa: E402
from lsp import lsp_server, query  # noqa: E402
from lsp.worker import CheckCancelled  # noqa: E402

_SRC = """union N { z  s(N) }
recursive add(N, N) -> N {
  add(z, m) = m
  add(s(n), m) = s(add(n, m))
}
theorem add_zero: all n:N. add(n, z) = n
proof
  induction N
  case z { ? }
  case s(n') assume IH {
    expand add
    replace IH.
  }
end
theorem add_s: all n:N, m:N. add(n, s(m)) = s(add(n, m))
proof
  arbitrary n:N, m:N
  ?
end
assert add(s(s(z)), s(z)) = s(s(s(z)))
"""
_HOLES = [query.Position(9, 12), query.Position(18, 3)]


def _jobs(path: str) -> dict[str, Callable[[], object]]:
    def fresh(fn: Callable[[], object]) -> Callable[[], object]:
        def job() -> object:
            query._hole_checks.clear()  # make every job run the checker
            return fn()
        return job

    jobs = {
        "check": fresh(lambda: query.check(path, _SRC, prelude=())),
        "outline": fresh(lambda: query.proof_outline(path, _SRC, prelude=())),
    }
    for i, pos in enumerate(_HOLES):
        jobs[f"goal{i}"] = fresh(lambda pos=pos: query.goal_at(path, _SRC, pos, prelude=()))
    return jobs


def _run(job: Callable[[], object]) -> object:
    return lsp_server._worker.submit(job).result(timeout=60)


def test_state_left_by_a_skipped_restore_is_reset(tmp_path: Path) -> None:
    path = str(tmp_path / "fuzz.pf")
    jobs = _jobs(path)
    expected = _run(jobs["check"])
    assert expected  # the holes are reported

    def plant() -> None:
        # What an interrupt inside ``_target_hole``'s or
        # ``speculative_checking``'s ``finally`` would leave behind.
        flags.set_target_hole_location((1, 1))
        error._speculative_depth = 1

    _run(plant)
    assert _run(jobs["check"]) == expected


def test_interrupting_at_random_points_leaves_no_trace(tmp_path: Path) -> None:
    path = str(tmp_path / "fuzz.pf")
    jobs = _jobs(path)
    expected, duration = {}, {}
    for name, job in jobs.items():
        start = time.perf_counter()
        expected[name] = _run(job)
        duration[name] = time.perf_counter() - start

    rng = random.Random(1218)
    names = sorted(jobs)
    interrupted = 0
    for _ in range(150):
        name = rng.choice(names)
        future = lsp_server._worker.submit(jobs[name])
        time.sleep(rng.uniform(0, duration[name]))
        lsp_server.interrupt()
        try:
            assert future.result(timeout=60) == expected[name]
        except CheckCancelled:
            interrupted += 1
        check = rng.choice(names)
        assert _run(jobs[check]) == expected[check], (name, check)
    assert interrupted > 30  # most interrupts landed inside a job
