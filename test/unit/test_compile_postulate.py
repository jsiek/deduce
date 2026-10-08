"""Compiling a use of a `postulate fun` is a compile-time error."""
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]


def test_use_of_postulate_fun_is_a_compile_error(tmp_path: Path) -> None:
    from compiler import lower
    from lsp.library import check_file

    src = tmp_path / "uses_postulate.pf"
    # A definition is lowered even if nothing prints it. (`print f(z)`
    # itself is rejected earlier, by the checker.)
    src.write_text("union N { z  s(N) }\n"
                   "postulate fun f : fn N -> N\n"
                   "fun g(x : N) { f(x) }\n")
    sys.argv = [str(ROOT / "deduce.py")]
    result = check_file(str(src), prelude=[])
    assert result.ok, result.error_message
    with pytest.raises(lower.CompileError, match="postulate fun"):
        lower.lower_program(result.ast, main_module=src.stem)
