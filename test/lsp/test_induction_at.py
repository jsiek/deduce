"""``lsp.query.goal_binders_at``, ``arbitrary_at`` and ``induction_at``:
make any variable the goal binds up front arbitrary, or induct on it,
after ``arbitrary`` for the ones before it."""

from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from lsp import query  # noqa: E402
from lsp.query import GoalBinder, Position, WorkspaceEdit  # noqa: E402

PRELUDE = ("Nat", "UInt", "List")

SOURCE = """\
theorem t: all U:type, xs:List<U>, ys:List<U>.
  length(xs ++ ys) = length(xs) + length(ys)
proof
  ?
end
"""
HOLE = Position(line=4, column=3)


def _write(tmp_path: Path) -> str:
    path = tmp_path / "t.pf"
    path.write_text(SOURCE)
    return str(path)


def _errors(path: str, edit: WorkspaceEdit) -> list[str]:
    lines = SOURCE.splitlines()
    lines[HOLE.line - 1] = "  " + edit.new_text
    text = "\n".join(lines) + "\n"
    Path(path).write_text(text)
    return [d.message for d in query.check(path, text, prelude=PRELUDE)
            if not d.message.startswith("incomplete proof")]


def test_the_binders_and_which_can_be_inducted_on(tmp_path: Path) -> None:
    # `U` is a type, so it can't be inducted on.
    path = _write(tmp_path)
    assert query.goal_binders_at(path, SOURCE, HOLE, prelude=PRELUDE) == (
        GoalBinder("U", "type", False),
        GoalBinder("xs", "List<U>", True),
        GoalBinder("ys", "List<U>", True),
    )


def test_arbitrary_up_to_a_variable(tmp_path: Path) -> None:
    path = _write(tmp_path)
    edit = query.arbitrary_at(path, SOURCE, HOLE, "U", prelude=PRELUDE)
    assert isinstance(edit, WorkspaceEdit) and edit.new_text == "arbitrary U:type\n  ?"
    edit = query.arbitrary_at(path, SOURCE, HOLE, "xs", prelude=PRELUDE)
    assert isinstance(edit, WorkspaceEdit) and edit.new_text == "arbitrary U:type, xs:List<U>\n  ?"
    assert _errors(path, edit) == []


def test_the_variables_before_it_are_made_arbitrary_first(tmp_path: Path) -> None:
    path = _write(tmp_path)
    edit = query.induction_at(path, SOURCE, HOLE, "xs", prelude=PRELUDE)
    assert isinstance(edit, WorkspaceEdit)
    assert edit.new_text.startswith("arbitrary U:type\n  induction List<U>\n")
    assert _errors(path, edit) == []


def test_inducting_on_a_later_variable(tmp_path: Path) -> None:
    path = _write(tmp_path)
    edit = query.induction_at(path, SOURCE, HOLE, "ys", prelude=PRELUDE)
    assert isinstance(edit, WorkspaceEdit)
    assert edit.new_text.startswith("arbitrary U:type, xs:List<U>\n  induction List<U>\n")
    assert _errors(path, edit) == []


def test_not_a_variable_to_induct_on(tmp_path: Path) -> None:
    path = _write(tmp_path)
    assert query.induction_at(path, SOURCE, HOLE, "U", prelude=PRELUDE) is None
    assert query.induction_at(path, SOURCE, HOLE, "zs", prelude=PRELUDE) is None
