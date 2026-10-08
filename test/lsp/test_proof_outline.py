"""Tests for ``lsp.query.proof_outline`` (issue #1214): per-step proof
annotations computed from a single check."""

from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

import lsp.library  # noqa: E402
from lsp.query import ProofStep, StepUse, proof_outline  # noqa: E402

LIST_PF = REPO_ROOT / "lib" / "List.pf"


def _steps_in_lines(steps: tuple[ProofStep, ...], first: int, last: int):
    return [s for s in steps if first <= s.range.start.line <= last]


def _theorem_lines(source: str, name: str) -> tuple[int, int]:
    """1-indexed (theorem line, matching ``end`` line)."""
    lines = source.splitlines()
    start = next(
        i for i, line in enumerate(lines) if line.startswith(f"theorem {name}:")
    )
    end = next(i for i in range(start, len(lines)) if lines[i] == "end")
    return start + 1, end + 1


def test_length_append_induction_and_equations():
    source = LIST_PF.read_text()
    outline = proof_outline(str(LIST_PF), source)
    assert outline.diagnostics == ()
    first, last = _theorem_lines(source, "length_append")
    steps = _steps_in_lines(outline.steps, first, last)
    assert all(s.status == "ok" for s in steps)

    induction = next(s for s in steps if s.kind == "Induction")
    assert induction.goal == (
        "(all xs:List<U>, ys:List<U>. length(xs ++ ys) = length(xs) + length(ys))"
    )

    # The three links of the `equations` chain in the `node` case each
    # get their own range and the equation they establish.
    links = [s for s in steps if s.kind == "PAnnot" and s.range.start.line > first + 10]
    assert [s.formula for s in links] == [
        "length(node(n, xs') ++ ys) = 1 + length(xs' ++ ys)",
        "1 + length(xs' ++ ys) = 1 + (length(xs') + length(ys))",
        "1 + (length(xs') + length(ys)) = #length(node(n, xs'))# + length(ys)",
    ]
    assert len({s.range.start.line for s in links}) == 3
    assert links[1].uses == (StepUse("IH", "given"),)
    assert links[2].uses == (StepUse("length", "definition"),)
    assert all(
        [(g.label, g.formula) for g in s.givens]
        == [("IH", "(all ys:List<U>. length(xs' ++ ys) = length(xs') + length(ys))")]
        for s in links
    )

    # `replace` / `expand` record the goal they leave behind.
    replace = next(s for s in steps if s.kind == "RewriteGoal")
    assert replace.goal == "#1 + length(xs' ++ ys)# = 1 + (length(xs') + length(ys))"
    assert replace.formula == "true"


ERROR_PARTWAY = """\
theorem t: all P:bool, Q:bool. if P and Q then Q and P
proof
  arbitrary P:bool, Q:bool
  assume pq
  have p: P by conjunct 0 of pq
  have q: Q by conjunct 0 of pq
  conclude Q and P by ?
end
"""


def test_error_partway_keeps_earlier_and_later_steps(tmp_path):
    path = tmp_path / "partway.pf"
    outline = proof_outline(str(path), ERROR_PARTWAY)
    by_line: dict[int, list[ProofStep]] = {}
    for s in outline.steps:
        by_line.setdefault(s.range.start.line, []).append(s)

    have_p = by_line[5][0]
    assert (have_p.kind, have_p.status) == ("PLet", "ok")
    assert (have_p.goal, have_p.formula) == ("(Q and P)", "P")
    assert have_p.uses == (StepUse("pq", "given"),)
    assert [(g.label, g.formula) for g in have_p.givens] == [("pq", "(P and Q)")]

    # The bad `conjunct 0` owns the error; the `have` around it doesn't.
    have_q, bad = by_line[6][0], by_line[6][1]
    assert (have_q.kind, have_q.status) == ("PLet", "ok")
    assert (bad.kind, bad.status, bad.formula) == ("PAndElim", "error", "P")

    conclude, hole = by_line[7]
    assert (conclude.kind, conclude.status) == ("PAnnot", "ok")
    assert [g.label for g in conclude.givens] == ["pq", "p", "q"]
    assert (hole.kind, hole.status, hole.goal) == ("PHole", "incomplete", "(Q and P)")

    assert len(outline.diagnostics) == 2


def test_outline_runs_one_check(tmp_path, monkeypatch):
    calls = []
    real = lsp.library.check_file

    def counting(*args, **kwargs):
        calls.append(args)
        return real(*args, **kwargs)

    monkeypatch.setattr(lsp.library, "check_file", counting)
    # Check twice: the second run must still record every step even
    # though the per-statement proof cache now holds the theorem.
    path = str(tmp_path / "partway.pf")
    fixed = (ERROR_PARTWAY.replace("conjunct 0 of pq\n  conclude", "conjunct 1 of pq\n  conclude")
             .replace("by ?", "by q, p"))
    proof_outline(path, fixed)
    outline = proof_outline(path, fixed)
    assert len(calls) == 2
    assert len(outline.steps) == len({s.range for s in outline.steps}) > 8
