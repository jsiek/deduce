"""Tests for the subterm-addressed steps (issue #1219):
``preview_replace_at_subterm``, ``preview_expand_at_subterm`` and
``lemmas_for_subterm``."""

from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from lsp.library import check_file  # noqa: E402
from lsp.query import (  # noqa: E402
    Position, WorkspaceEdit, _line_col_to_offset, _subterm_at, _target_hole,
    _term_tree, lemmas_for_subterm, preview_expand_at_subterm,
    preview_replace_at_subterm,
)

PRELUDE = """\
union N { z  s(N) }
recursive dbl(N) -> N {
  dbl(z) = z
  dbl(s(n)) = s(s(dbl(n)))
}
postulate fun R : fn N, N -> bool
postulate dbl_s: all n:N. dbl(s(n)) = s(s(dbl(n)))
"""

# The goal `R(dbl(s(a)), dbl(s(a)))` has two occurrences of `dbl(s(a))`;
# the hypothesis matches only when just the second is rewritten.
TWO_OCCURRENCES = PRELUDE + """\
theorem t: all a:N. if R(dbl(s(a)), s(s(dbl(a)))) then R(dbl(s(a)), dbl(s(a)))
proof
  arbitrary a:N
  assume H
  ?
end
"""
HOLE = Position(12, 3)
SECOND = [2]  # R(dbl(s(a)), dbl(s(a))): [0] is `R`, [1] and [2] its arguments


def _apply(content: str, edit: WorkspaceEdit) -> str:
    start = _line_col_to_offset(content, edit.range.start)
    end = _line_col_to_offset(content, edit.range.end)
    return content[:start] + edit.new_text + content[end:]


def _finish(content: str, edit: WorkspaceEdit, last_step: str) -> bool:
    """Apply ``edit``, prove its new hole with ``last_step``, and check."""
    finished = _apply(content, edit).replace("  ?\n", f"  {last_step}\n")
    assert finished.count("?") == 0
    return check_file("finished.pf", content=finished, prelude=()).ok


def test_expand_targets_one_of_two_occurrences():
    preview = preview_expand_at_subterm("t.pf", TWO_OCCURRENCES, HOLE, SECOND, ["dbl"])
    assert preview is not None and preview.outcome == "ok"
    assert str(preview.goal) == "R(dbl(s(a)), s(s(dbl(a))))"
    # Plain `expand dbl` would also expand the first occurrence, so the
    # step marks the chosen one.
    assert preview.edit.new_text == (
        "show R(dbl(s(a)), #dbl(s(a))#)\n  expand dbl\n  ?"
    )
    assert _finish(TWO_OCCURRENCES, preview.edit, "H")
    plain = WorkspaceEdit("t.pf", preview.edit.range, "expand dbl\n  ?")
    assert not _finish(TWO_OCCURRENCES, plain, "H")


def test_replace_targets_one_of_two_occurrences():
    preview = preview_replace_at_subterm(
        "t.pf", TWO_OCCURRENCES, HOLE, SECOND, "dbl_s"
    )
    assert preview is not None and preview.outcome == "ok"
    assert str(preview.goal) == "R(dbl(s(a)), s(s(dbl(a))))"
    assert preview.edit.new_text.startswith("show R(dbl(s(a)), #dbl(s(a))#)\n")
    assert _finish(TWO_OCCURRENCES, preview.edit, "H")


def test_plain_step_when_it_changes_only_the_chosen_subterm():
    source = TWO_OCCURRENCES.replace(
        "then R(dbl(s(a)), dbl(s(a)))", "then R(dbl(s(a)), dbl(a))"
    )
    preview = preview_replace_at_subterm("t.pf", source, HOLE, [1], "dbl_s[a]")
    assert preview is not None and preview.outcome == "ok"
    assert preview.edit.new_text == "replace dbl_s[a]\n  ?"
    assert str(preview.goal) == "R(s(s(dbl(a))), dbl(a))"


def test_step_that_proves_the_goal_ends_with_a_period():
    source = PRELUDE + (
        "theorem t: all a:N. dbl(s(a)) = s(s(dbl(a)))\n"
        "proof\n"
        "  arbitrary a:N\n"
        "  ?\n"
        "end\n"
    )
    preview = preview_expand_at_subterm("t.pf", source, Position(11, 3), [0], ["dbl"])
    assert preview is not None and preview.outcome == "ok"
    assert str(preview.goal) == "true"
    assert preview.edit.new_text == "expand dbl."
    assert check_file("t.pf", content=_apply(source, preview.edit), prelude=()).ok


def test_invalid_paths_and_failing_steps():
    def outcome(path, equation="dbl_s"):
        p = preview_replace_at_subterm("t.pf", TWO_OCCURRENCES, HOLE, path, equation)
        return p.outcome, p.message

    assert outcome([7]) == ("invalid_path", "the goal has no term at path [7]")
    kind, message = outcome([0])
    assert kind == "invalid_path" and "`R` is the function of a call" in message
    kind, message = outcome(SECOND, "H")  # `H` is not an equation
    assert kind == "error" and message
    assert preview_replace_at_subterm(
        "t.pf", TWO_OCCURRENCES, Position(11, 3), SECOND, "dbl_s"
    ) is None  # not on a hole


def test_lemmas_ranked_against_the_subterm():
    lemmas = lemmas_for_subterm("t.pf", TWO_OCCURRENCES, HOLE, SECOND)
    assert lemmas and lemmas[0].name == "dbl_s"
    assert lemmas[0].unify_tier == "rewrite_subterm"
    assert lemmas_for_subterm("t.pf", TWO_OCCURRENCES, HOLE, [7]) == ()


REPEATED = PRELUDE + """\
postulate to_z: all n:N. n = z
theorem t: all a:N. R(a, a)
proof
  arbitrary a:N
  ?
end
"""


def test_mark_follows_the_path_not_the_node():
    """The path picks one occurrence by its place in the goal's text,
    even when the AST shares one node between several occurrences (as
    substitution can produce)."""
    preview = preview_replace_at_subterm("t.pf", REPEATED, Position(12, 3), [2], "to_z[a]")
    assert preview is not None and preview.outcome == "ok"
    assert preview.edit.new_text.startswith("show R(a, #a#)\n")
    assert str(preview.goal) == "R(a, z)"

    with _target_hole((12, 3)):
        goal = check_file("t.pf", content=REPEATED, prelude=()).exception.formula
    goal.args[1] = goal.args[0]  # share one node between both occurrences
    node, start = _subterm_at(_term_tree(goal), [2])
    assert (str(node), start) == ("a", len("R(a, "))


def test_callee_behind_an_inferred_instantiation_is_rejected():
    source = PRELUDE + (
        "union L<T> { nil  cons(T, L<T>) }\n"
        "recursive len<T>(L<T>) -> N {\n"
        "  len(nil) = z\n"
        "  len(cons(x, xs)) = s(len(xs))\n"
        "}\n"
        "theorem t: all xs:L<N>. R(len(xs), len(xs))\n"
        "proof\n"
        "  arbitrary xs:L<N>\n"
        "  ?\n"
        "end\n"
    )
    # [1, 0] is `len` in the first `len(xs)`, an instantiation `len<N>`
    # whose type argument is inferred.
    preview = preview_expand_at_subterm("t.pf", source, Position(16, 3), [1, 0], ["len"])
    assert preview is not None and preview.outcome == "invalid_path"
    assert "`len` is the function of a call" in preview.message
