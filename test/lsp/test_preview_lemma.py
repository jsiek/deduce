"""Tests for ``lsp.query.preview_lemma_at``: the step
``insert_lemma_at`` would make at a hole, checked before it's made."""

from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from lsp import query  # noqa: E402

PRELUDE = ("Nat", "UInt", "List")

TRANS = """\
theorem t: all a:Nat, b:Nat, c:Nat. if a ≤ b and b ≤ c then a ≤ c
proof
  arbitrary a:Nat, b:Nat, c:Nat
  assume prem
  ?
end
"""

APPEND3 = """\
theorem t: all U:type, xs:List<U>, ys:List<U>, zs:List<U>.
  length(xs ++ ys ++ zs) = length(xs) + length(ys) + length(zs)
proof
  arbitrary U:type, xs:List<U>, ys:List<U>, zs:List<U>
  ?
end
"""


def _hole(content: str) -> query.Position:
    (pos,) = [
        query.Position(n, line.index("?") + 1)
        for n, line in enumerate(content.splitlines(), start=1)
        if "?" in line
    ]
    return pos


def _preview(tmp_path, content: str, name: str) -> query.LemmaPreview:
    preview = query.preview_lemma_at(
        str(tmp_path / "t.pf"), content, _hole(content), name, prelude=PRELUDE
    )
    assert preview is not None
    return preview


def test_apply_leaves_the_premise(tmp_path):
    p = _preview(tmp_path, TRANS, "less_implies_less_equal")
    assert p.outcome == "ok"
    assert p.edit.new_text == "apply less_implies_less_equal[a, c] to ?"
    assert [str(g) for g in p.goals] == ["a < c"]


def test_replace_leaves_a_hole_for_the_rest(tmp_path):
    p = _preview(tmp_path, APPEND3, "length_append")
    assert p.outcome == "ok"
    assert p.edit.new_text == "replace length_append\n  ?"
    assert [str(g) for g in p.goals] == [
        "length(xs) + length(ys ++ zs) = length(xs) + length(ys) + length(zs)"
    ]


def test_a_lemma_that_does_not_apply_is_an_error(tmp_path):
    p = _preview(tmp_path, TRANS, "length_append")
    assert p.outcome == "error" and p.message


def test_a_hole_the_check_never_reaches(tmp_path):
    broken = "theorem t: all n:Nat. n ≤ n + undefined_name\nproof\n  arbitrary n:Nat\n  ?\nend\n"
    p = _preview(tmp_path, broken, "less_equal_refl")
    assert p.outcome == "error"
    assert p.message is not None and p.message.startswith("the check stops before this hole")


def test_other_holes_are_not_the_steps(tmp_path):
    two = APPEND3.replace("  ?\n", "  have h: true by ?\n  ?\n")
    pos = query.Position(6, 3)
    p = query.preview_lemma_at(str(tmp_path / "t.pf"), two, pos, "length_append", prelude=PRELUDE)
    assert p is not None and p.outcome == "ok"
    assert len(p.goals) == 1


def test_off_a_hole_or_unknown_name(tmp_path):
    path = str(tmp_path / "t.pf")
    assert query.preview_lemma_at(path, TRANS, query.Position(1, 1), "x", prelude=PRELUDE) is None
    assert query.preview_lemma_at(path, TRANS, _hole(TRANS), "no_such_lemma", prelude=PRELUDE) is None


def test_a_transitivity_lemma_takes_its_middle_term_from_the_givens(tmp_path):
    # `less_trans`'s conclusion `x < z` leaves `y` open; the given
    # `a < b and b < c` supplies it.
    less = TRANS.replace("≤", "<")
    path = str(tmp_path / "t.pf")
    pos = _hole(less)
    tier = {m.name: m.unify_tier for m in query.available_lemmas_at(path, less, pos, prelude=PRELUDE)}
    assert tier["less_trans"] == "premises_remain"
    p = _preview(tmp_path, less, "less_trans")
    assert p.outcome == "ok"
    assert p.edit.new_text == "apply less_trans[a, b, c] to ?, ?"
    assert [str(g) for g in p.goals] == ["a < b", "b < c"]


def test_insert_lemma_matches_the_ranking_tier(tmp_path):
    # The ranking classifies with the type-checked formula; so must the step.
    path = str(tmp_path / "t.pf")
    pos = _hole(APPEND3)
    tier = {m.name: m.unify_tier for m in query.available_lemmas_at(path, APPEND3, pos, prelude=PRELUDE)}
    assert tier["length_append"] == "rewrite_subterm"
    edit = query.insert_lemma_at(path, APPEND3, pos, "length_append", prelude=PRELUDE)
    assert edit is not None and edit.new_text == "replace length_append"
