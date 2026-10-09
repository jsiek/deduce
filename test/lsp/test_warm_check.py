"""Tests for warm checks (issue #1245): a check after the first reuses the
processed prelude imports instead of processing the prelude again, and
the AST sanity walks don't re-walk imported modules."""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

import checker_cache  # noqa: E402
import checker_pipeline  # noqa: E402
import flags  # noqa: E402
import lsp.library as library  # noqa: E402
from abstract_syntax import Import, Var  # noqa: E402
from abstract_syntax.ops import (  # noqa: E402
    check_post_typecheck_invariants, check_post_uniquify_invariants,
)
from lark.tree import Meta  # noqa: E402

MINI = """\
union Bit { o  i }

theorem bit_cases: all b:Bit. b = o or b = i
proof
  arbitrary b:Bit
  switch b {
    case o { . }
    case i { . }
  }
end
"""

USER = """\
theorem uses_mini: all b:Bit. b = o or b = i
proof
  bit_cases
end
"""


@pytest.fixture
def mini_prelude(tmp_path, monkeypatch):
    """The one-module prelude ``Mini`` on the import path, starting from
    a fresh prelude state."""
    (tmp_path / "Mini.pf").write_text(MINI)
    monkeypatch.setattr(
        flags, "import_directories", flags.import_directories | {str(tmp_path)}
    )
    library.reset_prelude_cache()
    yield
    library.reset_prelude_cache()


def _count_process_declaration(monkeypatch) -> list[object]:
    calls: list[object] = []
    real = checker_pipeline.process_declaration

    def counting(stmt, *args, **kwargs):
        calls.append(stmt)
        return real(stmt, *args, **kwargs)

    monkeypatch.setattr(checker_pipeline, "process_declaration", counting)
    return calls


def test_warm_check_does_not_process_the_prelude_again(mini_prelude, monkeypatch):
    calls = _count_process_declaration(monkeypatch)
    assert library.check_file("user.pf", content=USER, prelude=("Mini",)).ok
    first = len(calls)

    calls.clear()
    assert library.check_file("user.pf", content=USER, prelude=("Mini",)).ok
    # Only the user's theorem: the prelude import (and Mini's statements
    # inside it) came from the cache.
    assert len(calls) == 1 and first > 1


def test_warm_check_of_another_file_reuses_the_prelude(mini_prelude, monkeypatch):
    assert library.check_file("a.pf", content=USER, prelude=("Mini",)).ok
    calls = _count_process_declaration(monkeypatch)
    other = USER.replace("uses_mini", "also_uses_mini")
    result = library.check_file("b.pf", content=other, prelude=("Mini",))
    assert result.ok, result.error_message
    assert len(calls) == 1


def test_file_named_like_a_prelude_module_still_gets_the_recursion_error(mini_prelude):
    for _ in range(2):
        result = library.check_file("Mini.pf", content=USER, prelude=("Mini",))
        assert not result.ok and "recusive import" in result.error_message


def test_rebuilding_the_prelude_clears_the_cache(mini_prelude):
    assert library.check_file("user.pf", content=USER, prelude=("Mini",)).ok
    assert checker_cache._prelude_imports_cache
    library.reset_prelude_cache()
    assert not checker_cache._prelude_imports_cache


@pytest.mark.parametrize(
    "check", [check_post_uniquify_invariants, check_post_typecheck_invariants]
)
def test_sanity_walks_skip_imported_module_bodies(check):
    stray = Var(Meta(), None, "x")
    # Inside an imported module's body: not walked (the module was
    # checked when it was built).
    check([Import(Meta(), "M", [stray])])
    with pytest.raises(Exception, match="pre-uniquify `Var`"):
        check([stray])


MINI_IND = """\
union Bit { o  i }

postulate bit_induction: all P: fn Bit -> bool.
  if P(o) and P(i) then all b:Bit. P(b)

inductive Bit by bit_induction
"""


def test_user_inductive_does_not_leak_into_later_checks(tmp_path, monkeypatch):
    """The prelude declares an ``inductive``, so the cached env holds an
    inductives table. A user file's own ``inductive`` must not end up in
    it: checking the file again without that declaration must fail as it
    does in a fresh process (issue #1249 review)."""
    (tmp_path / "MiniInd.pf").write_text(MINI_IND)
    monkeypatch.setattr(
        flags, "import_directories", flags.import_directories | {str(tmp_path)}
    )
    full = (REPO_ROOT / "test" / "should-validate" / "custom_induction.pf").read_text()
    without = full.replace("inductive TwoList by tl_induction\n", "")
    assert without != full
    library.reset_prelude_cache()
    try:
        cold = library.check_file("u.pf", content=without, prelude=("MiniInd",))
        assert not cold.ok

        library.reset_prelude_cache()
        assert library.check_file("u.pf", content=full, prelude=("MiniInd",)).ok
        warm = library.check_file("u.pf", content=without, prelude=("MiniInd",))
        assert not warm.ok and warm.error_message == cold.error_message
    finally:
        library.reset_prelude_cache()
