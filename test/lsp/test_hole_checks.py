"""The step queries at a hole share one check of the document, which
:func:`lsp.query.proof_outline` fills in for every hole (see
``_check_at_target``)."""

from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

import lsp.library  # noqa: E402
from lsp import query  # noqa: E402

# Two holes with different givens: `p` at the first, `p`, `x` and `q`
# at the second.
TWO_HOLES = """\
theorem t: all P:bool, Q:bool. if P then (if Q then Q)
proof
  arbitrary P:bool, Q:bool
  assume p: P
  have x: P by ?
  assume q: Q
  ?
end
"""


def _holes(content: str) -> list[query.Position]:
    return [
        query.Position(n, line.index("?") + 1)
        for n, line in enumerate(content.splitlines(), start=1)
        if "?" in line
    ]


def test_queries_answer_for_the_hole_at_the_cursor(tmp_path):
    path = str(tmp_path / "holes.pf")
    first, second = _holes(TWO_HOLES)
    assert query.matching_givens_at(path, TWO_HOLES, first) == ("p",)
    assert query.matching_givens_at(path, TWO_HOLES, second) == ("q",)
    fill = query.fill_from_given_at(path, TWO_HOLES, second, "q")
    assert fill is not None and fill.new_text == "q"


def test_outline_answers_the_step_queries_without_a_check(tmp_path, monkeypatch):
    path = str(tmp_path / "holes.pf")
    query.proof_outline(path, TWO_HOLES)

    def no_check(*args, **kwargs):
        raise AssertionError("checked again")

    monkeypatch.setattr(lsp.library, "check_file", no_check)
    first, second = _holes(TWO_HOLES)
    assert query.goal_at(path, TWO_HOLES, second) is not None
    assert query.matching_givens_at(path, TWO_HOLES, first) == ("p",)
    assert query.matching_givens_at(path, TWO_HOLES, second) == ("q",)
    assert query.refine_at(path, TWO_HOLES, second) is not None
    query.splittable_vars_at(path, TWO_HOLES, second)
    query.eliminable_vars_at(path, TWO_HOLES, second)


def test_previews_keep_the_documents_checks(tmp_path, monkeypatch):
    path = str(tmp_path / "holes.pf")
    query.proof_outline(path, TWO_HOLES)
    _, second = _holes(TWO_HOLES)
    # Each preview checks a text of its own, with the step spliced in.
    for _ in range(query._HOLE_CHECK_DOCUMENTS + 1):
        query.preview_replace_at_subterm(path, TWO_HOLES, second, [], "q")

    def no_check(*args, **kwargs):
        raise AssertionError("checked again")

    monkeypatch.setattr(lsp.library, "check_file", no_check)
    assert query.matching_givens_at(path, TWO_HOLES, second) == ("q",)


def test_a_check_of_an_import_refreshes_its_importers(tmp_path, monkeypatch):
    # A document's text doesn't capture the modules it imports, so when
    # one changes the server's check of it (on save) starts afresh.
    import flags

    monkeypatch.setattr(
        flags, "import_directories", flags.import_directories | {str(tmp_path)}
    )
    dep = tmp_path / "HoleCheckDep.pf"
    dep.write_text("union Color {\n  red\n  green\n}\n")
    path = str(tmp_path / "importer.pf")
    importer = "import HoleCheckDep\n\ntheorem t: all c:Color. c = c\nproof\n  ?\nend\n"
    (hole,) = _holes(importer)

    def induction() -> str:
        edit = query.induction_skeleton_at(path, importer, hole)
        assert edit is not None
        return edit.new_text

    query.proof_outline(path, importer)
    assert "green" in induction()
    dep.write_text("union Color {\n  red\n  blue\n}\n")
    query.check(str(dep), dep.read_text())
    assert "blue" in induction() and "green" not in induction()
    # Likewise a new outline of the unchanged importer.
    dep.write_text("union Color {\n  red\n  teal\n}\n")
    query.proof_outline(path, importer)
    assert "teal" in induction()


def test_an_edit_is_checked_afresh(tmp_path):
    path = str(tmp_path / "holes.pf")
    first, _ = _holes(TWO_HOLES)
    assert query.matching_givens_at(path, TWO_HOLES, first) == ("p",)
    edited = TWO_HOLES.replace("assume p: P", "assume p2: P")
    assert query.matching_givens_at(path, edited, first) == ("p2",)
