"""Compiling a call that passes a where clause's operations is a
compile-time error until the back end passes them (#1292)."""
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]


@pytest.mark.parametrize("decl, call", [
    ("fun twice<T> where { Monoid<T> } (x:T) { x + x }", "twice(true)"),
    ("recfun count<T> where { Monoid<T> } (n:N, x:T) -> T\n"
     "  measure n of N\n"
     "{\n"
     "  switch n { case z { x } case s(m) { x + count(m, x) } }\n"
     "}\n"
     "terminates {\n"
     "  sorry\n"
     "}",
     "count(s(z), true)"),
])
def test_where_operations_are_a_compile_error(tmp_path: Path, decl: str,
                                              call: str) -> None:
    from compiler import lower
    from lsp.library import check_file

    src = tmp_path / "uses_where.pf"
    src.write_text(
        "union N { z  s(N) }\n"
        "fun operator < (a:N, b:N) { false }\n"
        "concept WellFounded<T> {\n"
        "  fun operator < : fn (T, T) -> bool\n"
        "  theorem strong_induction: all P: fn T -> bool, n:T.\n"
        "    if (all j:T. if (all i:T. if i < j then P(i)) then P(j))\n"
        "    then P(n)\n"
        "}\n"
        "postulate n_strong: all P: fn N -> bool, n:N.\n"
        "  if (all j:N. if (all i:N. if i < j then P(i)) then P(j))\n"
        "  then P(n)\n"
        "model WellFounded<N> {\n"
        "  fun operator < = operator <\n"
        "  theorem strong_induction = n_strong\n"
        "}\n"
        "concept Monoid<T> {\n"
        "  fun operator+ : fn (T, T) -> T\n"
        "  fun zero : T\n"
        "}\n"
        "fun bor(a:bool, b:bool) { a or b }\n"
        "model Monoid<bool> {\n"
        "  fun operator+ = bor\n"
        "  fun zero = false\n"
        "}\n"
        + decl + "\n"
        "print " + call + "\n")
    sys.argv = [str(ROOT / "deduce.py")]
    result = check_file(str(src), prelude=[])
    assert result.ok, result.error_message
    with pytest.raises(lower.CompileError, match="#1292"):
        lower.lower_program(result.ast, main_module=src.stem)
