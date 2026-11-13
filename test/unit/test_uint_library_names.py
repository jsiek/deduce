"""The UInt literal hooks use the stdlib's `Binary` even when another
module's same-named `Binary` was declared first (#1252).

Without the stdlib prelude, a file can import a module declaring its own
`Binary`, `bzero`, `dub_inc`, `inc_dub` and `dub` before `UInt`. Looking
those up by base name found the user's, so the native UInt arithmetic
fast path never applied and this assert exceeded the recursion limit."""
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def test_uint_fast_path_ignores_earlier_same_named_binary(
        tmp_path: Path) -> None:
    (tmp_path / "MyBin.pf").write_text(
        "module MyBin\n"
        "union Binary { bzero  dub_inc(Binary)  inc_dub(Binary) }\n"
        "recursive dub(Binary) -> Binary {\n"
        "  dub(bzero) = bzero\n"
        "  dub(dub_inc(x)) = dub(x)\n"
        "  dub(inc_dub(x)) = dub(x)\n"
        "}\n")
    main = tmp_path / "main.pf"
    main.write_text(
        "import MyBin\n"
        "import UInt\n"
        "assert (4000 * 4000 * 4000) / 3 / 4000 / 4000 = 1333\n")
    result = subprocess.run(
        [sys.executable, str(ROOT / "deduce.py"), "--no-stdlib",
         "--dir", str(ROOT / "lib"), "main.pf"],
        cwd=tmp_path, capture_output=True, text=True, timeout=300)
    assert result.returncode == 0, result.stdout + result.stderr
