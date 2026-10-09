"""Tests for ``lsp.query.proof_outline`` (issue #1214): per-step proof
annotations computed from a single check."""

from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

import lsp.library  # noqa: E402
from lsp.query import ProofStep, StepUse, TermTree, proof_outline  # noqa: E402

LIST_PF = REPO_ROOT / "lib" / "List.pf"


def text(x):
    """``x`` with every :class:`TermTree` (also inside dicts and lists)
    rendered as its text."""
    if isinstance(x, TermTree):
        return str(x)
    if isinstance(x, dict):
        return {k: text(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return type(x)(text(v) for v in x)
    return x


def _at(pos) -> tuple[int, int]:
    return (pos.line, pos.column)


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
    assert text(induction.goal) == (
        "(all xs:List<U>, ys:List<U>. length(xs ++ ys) = length(xs) + length(ys))"
    )

    # The three links of the `equations` chain in the `node` case each
    # get their own range and the equation they establish.
    links = [s for s in steps if s.kind == "PAnnot" and s.range.start.line > first + 10]
    assert [text(s.formula) for s in links] == [
        "length(node(n, xs') ++ ys) = 1 + length(xs' ++ ys)",
        "1 + length(xs' ++ ys) = 1 + (length(xs') + length(ys))",
        "1 + (length(xs') + length(ys)) = #length(node(n, xs'))# + length(ys)",
    ]
    assert len({s.range.start.line for s in links}) == 3
    assert links[1].uses == (StepUse("IH", "given"),)
    assert links[2].uses == (StepUse("length", "definition"),)
    assert all(
        [(g.label, text(g.formula)) for g in s.givens]
        == [("IH", "(all ys:List<U>. length(xs' ++ ys) = length(xs') + length(ys))")]
        for s in links
    )

    # `replace` / `expand` record the goal they leave behind.
    replace = next(s for s in steps if s.kind == "RewriteGoal")
    assert text(replace.goal) == "#1 + length(xs' ++ ys)# = 1 + (length(xs') + length(ys))"
    assert text(replace.formula) == "true"

    # `detail` carries what a textbook rendering needs.
    assert text(steps[0].detail) == {"vars": [{"name": "U", "type": "type"}]}
    cases = text(induction.detail["cases"])
    assert induction.detail["variable"] == "xs"
    assert [(c["pattern"], c["hypotheses"]) for c in cases] == [
        ("[]", []), ("node(n, xs')", ["IH"]),
    ]
    # Each case's range covers all of its steps.
    in_node_case = [
        s for s in steps
        if _at(cases[1]["range"].start) <= _at(s.range.start)
        and _at(s.range.end) <= _at(cases[1]["range"].end)
    ]
    assert {s.range for s in links} <= {s.range for s in in_node_case}
    assert [text((s.detail["lhs"], s.detail["rhs"])) for s in links] == [
        ("length(node(n, xs') ++ ys)", "1 + length(xs' ++ ys)"),
        ("1 + length(xs' ++ ys)", "1 + (length(xs') + length(ys))"),
        ("1 + (length(xs') + length(ys))", "#length(node(n, xs'))# + length(ys)"),
    ]

    theorem = next(t for t in outline.theorems if t.name == "length_append")
    assert text(theorem.formula) == (
        "(all U:type, xs:List<U>, ys:List<U>. length(xs ++ ys) = length(xs) + length(ys))"
    )
    assert not theorem.lemma
    assert (theorem.range.start.line, theorem.range.end.line) == (first, last)


DETAIL_SRC = """\
theorem or_swap: all P:bool, Q:bool. if P or Q then Q or P
proof
  arbitrary P:bool, Q:bool
  assume pq: P or Q
  cases pq
  case p: P {
    have p2: P by p
    conclude Q or P by p2
  }
  case q: Q {
    conclude Q or P by q
  }
end

lemma bool_cases: all b:bool. b or not b
proof
  arbitrary b:bool
  switch b {
    case true {
      .
    }
    case false {
      .
    }
  }
end
"""


def test_step_detail_for_assume_have_cases_and_switch(tmp_path):
    outline = proof_outline(str(tmp_path / "detail.pf"), DETAIL_SRC)
    assert outline.diagnostics == ()
    by_kind: dict[str, list[ProofStep]] = {}
    for s in outline.steps:
        by_kind.setdefault(s.kind, []).append(s)

    # The whole `arbitrary` list, though it desugars to nested AllIntros.
    assert text(by_kind["AllIntro"][0].detail) == {
        "vars": [{"name": "P", "type": "bool"}, {"name": "Q", "type": "bool"}]
    }
    assert text(by_kind["ImpIntro"][0].detail) == {"label": "pq", "premise": "(P or Q)"}
    assert by_kind["PLet"][0].detail == {"label": "p2"}

    [cases] = by_kind["Cases"]
    arms = text(cases.detail["cases"])
    assert [(a["label"], a["formula"]) for a in arms] == [("p", "P"), ("q", "Q")]
    # Arms partition the steps: `have p2` is in the first, the last
    # `conclude` in the second.
    have = by_kind["PLet"][0]
    last = by_kind["PAnnot"][-1]
    assert (
        _at(arms[0]["range"].start) <= _at(have.range.start)
        < _at(arms[1]["range"].start)
    )
    assert _at(arms[1]["range"].start) <= _at(last.range.start)
    assert _at(last.range.end) <= _at(arms[1]["range"].end)

    [switch] = by_kind["SwitchProof"]
    assert text(switch.detail["subject"]) == "b"
    # A case with no `assume` gets an anonymous `_` assumption from the
    # parser; it isn't a hypothesis anyone can cite, so it's left out.
    assert [(c["pattern"], c["hypotheses"]) for c in text(switch.detail["cases"])] == [
        ("true", []), ("false", []),
    ]

    assert [(t.name, t.lemma) for t in outline.theorems] == [
        ("or_swap", False), ("bool_cases", True),
    ]


def test_step_detail_for_define_and_choose(tmp_path):
    source = (
        "theorem some_true: some b:bool. b\n"
        "proof\n"
        "  define t = true\n"
        "  choose t\n"
        "  expand t.\n"
        "end\n"
    )
    outline = proof_outline(str(tmp_path / "choose.pf"), source)
    assert outline.diagnostics == ()
    details = {s.kind: text(s.detail) for s in outline.steps}
    assert details["PTLetNew"] == {"name": "t", "term": "true"}
    assert details["SomeIntro"] == {"witnesses": ["t"]}


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
    assert text((have_p.goal, have_p.formula)) == ("(Q and P)", "P")
    assert have_p.uses == (StepUse("pq", "given"),)
    assert [(g.label, text(g.formula)) for g in have_p.givens] == [("pq", "(P and Q)")]

    # The bad `conjunct 0` owns the error; the `have` around it doesn't.
    have_q, bad = by_line[6][0], by_line[6][1]
    assert (have_q.kind, have_q.status) == ("PLet", "ok")
    assert text((bad.kind, bad.status, bad.formula)) == ("PAndElim", "error", "P")

    conclude, hole = by_line[7]
    assert (conclude.kind, conclude.status) == ("PAnnot", "ok")
    # Most recent first, as the checker lists givens.
    assert [g.label for g in conclude.givens] == ["q", "p", "pq"]
    assert text((hole.kind, hole.status, hole.goal)) == ("PHole", "incomplete", "(Q and P)")

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


def test_failing_synthesized_node_is_recorded(tmp_path):
    # The inner `conjunct 5 of pq` is only synthesized (no goal) and
    # fails inside its handler; it must still be a step, and own the error.
    source = ERROR_PARTWAY.replace("conjunct 0 of pq\n  conclude", "conjunct 0 of conjunct 5 of pq\n  conclude")
    outline = proof_outline(str(tmp_path / "nested.pf"), source)
    inner = [s for s in outline.steps if s.range.start.line == 6 and s.range.start.column == 30]
    assert [(s.kind, s.status, s.goal, s.formula) for s in inner] == [
        ("PAndElim", "error", None, None)
    ]
    outer = next(
        s for s in outline.steps
        if (s.range.start.line, s.range.start.column) == (6, 16)
    )
    assert outer.status == "ok"


def test_recorder_installed_only_under_check_lock(tmp_path):
    # While another caller holds the check lock, a pending
    # proof_outline must not have installed its recorder yet.
    import threading
    import time

    import flags

    result = []
    path = str(tmp_path / "partway.pf")
    worker = threading.Thread(
        target=lambda: result.append(proof_outline(path, ERROR_PARTWAY))
    )
    with lsp.library._check_file_lock:
        worker.start()
        time.sleep(0.2)
        assert flags.get_proof_outline() is None
    worker.join()
    assert flags.get_proof_outline() is None
    assert len(result[0].steps) > 8
