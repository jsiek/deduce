"""Resolving an overloaded `+` in a long sum takes work linear in the
sum's length, not exponential (#1343)."""
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]

TYPES = """\
union A { a }
union B { b }
union C { c }
union D { d }
fun operator +(x : A, y : A) { x }
fun operator +(x : B, y : B) { x }
fun operator +(x : C, y : C) { x }
fun operator +(x : D, y : D) { x }
"""


def test_long_sum_resolves_in_linear_work(
        tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    import checker_types
    from lsp.library import check_file

    calls = [0]
    orig = checker_types.type_check_call_funty

    def counted(*args, **kwargs):  # type: ignore[no-untyped-def]
        calls[0] += 1
        return orig(*args, **kwargs)

    monkeypatch.setattr(checker_types, 'type_check_call_funty', counted)
    s = ' + '.join(['a'] * 12)
    src = tmp_path / 'Sum.pf'
    src.write_text(TYPES + f'theorem t: {s} = {s}\nproof\n  .\nend\n')
    sys.argv = [str(ROOT / 'deduce.py')]
    result = check_file(str(src), prelude=[])
    assert result.ok, result.error_message
    # 244 with each call's result remembered; 43624 without.
    assert calls[0] < 1000
