"""Acceptance test for ``lsp.library.check_file`` (Phase 1 / Step 1).

For representative files in ``test/should-validate`` and
``test/should-error``, verifies that the library API returns the same
outcome (ok vs. error) that ``test-deduce.py`` produces in the full
corpus sweep.

The session/state fixtures live in ``conftest.py`` so the Step 3
acceptance test can share them.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from abstract_syntax import get_uniquified_modules  # noqa: E402
from lsp.library import CheckResult, check_file  # noqa: E402

PASS_DIR = REPO_ROOT / "test" / "should-validate"
ERROR_DIR = REPO_ROOT / "test" / "should-error"
LIB_DIR = REPO_ROOT / "lib"


_SAMPLE_VALID = [
    "empty_file.pf",
    "ImportTests.pf",
    "ListTests.pf",
    "uint_replicate.pf",
]

_SAMPLE_ERRORS = [
    "conclude.pf",
    "define_missing_semi.pf",
    "overload6.pf",
    "import_using_unknown.pf",
    "givens_conclude_hole.pf",
]

_SAMPLE_LIB_COLLECT_ERRORS = [
    "Base.pf",
    "Nat.pf",
    "List.pf",
    "IntMult.pf",
    "UIntDiv.pf",
]


def _paths(directory: Path, names: list[str]) -> list[Path]:
    return [directory / name for name in names]


@pytest.mark.parametrize(
    "path", _paths(PASS_DIR, _SAMPLE_VALID), ids=lambda p: p.name
)
def test_should_validate(path: Path) -> None:
    result = check_file(str(path), prelude=())
    assert isinstance(result, CheckResult)
    assert result.ok, (
        f"{path.name} should validate but check_file returned an error:\n"
        f"{result.error_message}"
    )
    assert result.error_message is None
    assert result.exception is None
    assert result.ast is not None
    assert result.module_name == path.stem


@pytest.mark.parametrize(
    "path", _paths(ERROR_DIR, _SAMPLE_ERRORS), ids=lambda p: p.name
)
def test_should_error(path: Path) -> None:
    result = check_file(str(path), prelude=())
    assert isinstance(result, CheckResult)
    assert not result.ok, (
        f"{path.name} should produce an error but check_file returned ok"
    )
    assert result.error_message is not None
    assert result.error_message != ""
    assert result.exception is not None
    assert result.module_name == path.stem


@pytest.mark.parametrize(
    "path", _paths(LIB_DIR, _SAMPLE_LIB_COLLECT_ERRORS),
    ids=lambda p: p.name,
)
def test_lib_collect_errors_no_false_positives(path: Path) -> None:
    """Regression test for issue #400: ``check_file(..., collect_errors=True)``
    on a stdlib file must agree with ``deduce.py`` -- speculative
    iff-application and PTuple goal-directed-then-synthesis attempts
    used to leak failed-probe errors into the sink even when the
    enclosing rule recovered."""
    result = check_file(str(path), collect_errors=True, prelude=())
    assert result.errors is not None
    assert result.ok, (
        f"{path.name} should validate but collect_errors mode reported "
        f"{len(result.errors)} error(s); first:\n{result.error_message}"
    )
    assert result.errors == []


def test_matching_disk_content_populates_module_cache(tmp_path: Path) -> None:
    """MCP tools pass disk-backed content into ``check_file``; that
    content should still use the on-disk module cache."""
    path = tmp_path / "Cacheable.pf"
    source = "theorem cached: true\nproof\n  .\nend\n"
    path.write_text(source, encoding="utf-8")

    result = check_file(str(path), content=source, prelude=())

    assert result.ok
    assert path.stem in get_uniquified_modules()


def test_unsaved_content_bypasses_module_cache(tmp_path: Path) -> None:
    """Content that differs from disk is an editor buffer snapshot and
    must not be cached as the file's module."""
    path = tmp_path / "Unsaved.pf"
    path.write_text("theorem disk: true\nproof\n  .\nend\n", encoding="utf-8")
    unsaved = "theorem buffer: true\nproof\n  .\nend\n"

    result = check_file(str(path), content=unsaved, prelude=())

    assert result.ok
    assert path.stem not in get_uniquified_modules()


@pytest.mark.parametrize("parser", ["recursive-descent", "lalr"])
def test_parser_argument_validates_with_each(parser: str) -> None:
    """``check_file(parser=...)`` runs the requested parser on the user
    file. Either parser should accept a simple valid file."""
    path = PASS_DIR / "empty_file.pf"
    result = check_file(str(path), prelude=(), parser=parser)
    assert result.ok, (
        f"{path.name} should validate under {parser} but check_file "
        f"reported: {result.error_message}"
    )


def test_parser_argument_rejects_unknown_value() -> None:
    """An unknown parser name is a programming error and must fail
    loudly rather than silently falling back to the default."""
    path = PASS_DIR / "empty_file.pf"
    with pytest.raises(ValueError, match="parser"):
        check_file(str(path), prelude=(), parser="bogus")


def test_collect_errors_includes_expand_residual_hint() -> None:
    """Regression test for issue #745: the ``expand_residual_hint``
    appended by ``_check_proof_of_apply_defs_goal`` must reach the
    diagnostic surfaced through ``collect_errors=True`` (MCP / LSP),
    not just the CLI. The fixture file at
    ``test/should-error/advice_expand_more.pf`` is the same one the
    CLI ``test/should-error`` sweep uses; here we additionally verify
    the hint round-trips through the sink path."""
    path = ERROR_DIR / "advice_expand_more.pf"
    result = check_file(str(path), collect_errors=True)
    assert result.errors is not None
    assert not result.ok
    assert len(result.errors) >= 1
    body = getattr(result.errors[0], "message_body", str(result.errors[0]))
    assert "goal still contains" in body and "sum_test" in body, (
        "expand-residual hint missing from collect_errors diagnostic:\n"
        + body
    )
