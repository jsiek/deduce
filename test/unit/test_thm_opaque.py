"""A `.thm` file shows only the signature of an opaque declaration
(#1209)."""
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

SOURCE = """\
opaque union Box { box(bool) }

opaque fun unbox(b : Box) {
  switch b { case box(x) { x } }
}

union N { z  s(N) }

opaque recursive count(N) -> N {
  count(z) = z
  count(s(n)) = s(count(n))
}

fun visible(b : bool) { not b }
"""


def test_opaque_declarations_show_only_signatures(tmp_path: Path) -> None:
    from abstract_syntax import print_theorems
    from lsp.library import check_file

    src = tmp_path / "Opaques.pf"
    src.write_text(SOURCE)
    sys.argv = [str(ROOT / "deduce.py")]
    result = check_file(str(src), prelude=[])
    assert result.ok, result.error_message
    print_theorems(str(src), result.ast)
    thm = src.with_suffix(".thm").read_text()

    assert "opaque union Box\n" in thm
    assert "box(" not in thm                       # constructors hidden
    assert "opaque define unbox : (fn Box -> bool)\n" in thm
    assert "switch" not in thm                     # body hidden
    assert "opaque recursive count(N) -> N\n" in thm
    assert "count(z) = z" not in thm               # equations hidden
    assert "not b" in thm                          # non-opaque: definition shown
