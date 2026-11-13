"""``lsp.query.instantiation_vars_at`` and ``instantiate_at``: using an
``all`` given with values for its variables."""

from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from lsp import query  # noqa: E402
from lsp.query import InstantiationVar, Position, WorkspaceEdit  # noqa: E402

PRELUDE = ("Nat", "UInt", "List")

SOURCE = """\
theorem t: all U:type. all xs:List<U>, ys:List<U>. length(xs ++ ys) = length(xs) + length(ys)
proof
  arbitrary U:type
  induction List<U>
  case [] { expand operator++ | length. }
  case node(t1, l2) assume IH1 {
    arbitrary ys:List<U>
    expand operator++ | length
    ?
  }
end
"""
HOLE = Position(line=9, column=5)


def _write(tmp_path: Path) -> str:
    path = tmp_path / "t.pf"
    path.write_text(SOURCE)
    return str(path)


def test_vars_come_with_values_of_their_type_from_the_goal(tmp_path: Path) -> None:
    path = _write(tmp_path)
    assert query.instantiation_vars_at(path, SOURCE, HOLE, "IH1", prelude=PRELUDE) == (
        InstantiationVar("ys", "List<U>", ("l2", "ys", "l2 ++ ys")),
    )


def test_instantiating_states_the_formula_and_keeps_the_hole(tmp_path: Path) -> None:
    path = _write(tmp_path)
    edit = query.instantiate_at(path, SOURCE, HOLE, "IH1", ["ys"], prelude=PRELUDE)
    assert isinstance(edit, WorkspaceEdit)
    assert edit.new_text == (
        "have H1: length(l2 ++ ys) = length(l2) + length(ys) by IH1[ys]\n    ?"
    )


def test_replacing_with_the_instance_finishes_with_a_period(tmp_path: Path) -> None:
    # After `replace H1` the goal is `true`; a `?` there is never reached.
    path = _write(tmp_path)
    edit = query.instantiate_at(path, SOURCE, HOLE, "IH1", ["ys"], prelude=PRELUDE)
    assert isinstance(edit, WorkspaceEdit)
    lines = SOURCE.splitlines()
    lines[HOLE.line - 1] = "    " + edit.new_text
    text = "\n".join(lines) + "\n"
    (tmp_path / "t.pf").write_text(text)
    used = query.eliminate_at(path, text, Position(line=10, column=5), "H1", prelude=PRELUDE)
    assert used is not None and used.new_text == "replace H1."


def test_a_value_that_does_not_check_gives_the_message(tmp_path: Path) -> None:
    path = _write(tmp_path)
    message = query.instantiate_at(path, SOURCE, HOLE, "IH1", ["t1"], prelude=PRELUDE)
    assert isinstance(message, str) and "List<U>" in message


def test_not_a_local_given(tmp_path: Path) -> None:
    path = _write(tmp_path)
    assert query.instantiation_vars_at(path, SOURCE, HOLE, "nope", prelude=PRELUDE) == ()
    assert query.instantiate_at(path, SOURCE, HOLE, "nope", ["ys"], prelude=PRELUDE) is None
