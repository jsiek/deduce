"""Determinism check for the C emitter.

Step 25 of `docs/separate-compile-plan.md` requires that emit_c
output is a pure function of the input source. This script compiles
each lowering fixture in two fresh subprocess invocations and
byte-diffs the resulting `.c` files.

Run from the repo root:

    python3 test/compile/run_determinism.py
"""

from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
LOWER_DIR = ROOT / "test" / "compile" / "lower"
PRELUDE_DIR = ROOT / "test" / "compile" / "prelude"


def compile_to_c(pf: Path, c_out: Path) -> None:
    cmd = [
        sys.executable, str(ROOT / "deduce.py"),
        "--suppress-theorems", "--quiet", "--compile",
        "-o", str(c_out), str(pf),
    ]
    # Mirror run_e2e's heuristic for `--no-stdlib`.
    text = pf.read_text()
    needs_prelude = any(
        line.strip().startswith("import ") or line.strip().startswith("public import ")
        for line in text.splitlines()
        if not line.strip().startswith("//")
    )
    if not needs_prelude:
        cmd.insert(2, "--no-stdlib")
    subprocess.run(cmd, cwd=str(ROOT), check=True,
                   capture_output=True, text=True)


def main() -> int:
    fixtures: list[Path] = []
    for d in (LOWER_DIR, PRELUDE_DIR):
        if d.exists():
            fixtures.extend(sorted(d.glob("*.pf")))

    if not fixtures:
        print("no fixtures found", file=sys.stderr)
        return 1

    tmp = Path(tempfile.mkdtemp(prefix="deduce-det-"))
    failures: list[str] = []
    for pf in fixtures:
        a = tmp / f"{pf.stem}.a.c"
        b = tmp / f"{pf.stem}.b.c"
        try:
            compile_to_c(pf, a)
            compile_to_c(pf, b)
        except subprocess.CalledProcessError as e:
            failures.append(f"{pf.name}: compile failed: {e.stderr}")
            continue
        if a.read_bytes() != b.read_bytes():
            failures.append(
                f"{pf.name}: two compiles produced different .c "
                f"(see {a} and {b})"
            )
            continue
        print(f"ok {pf.relative_to(ROOT)}")

    # Cleanup unless we have failures (in which case keep the tmp for
    # human inspection).
    if not failures:
        for p in tmp.iterdir():
            p.unlink()
        tmp.rmdir()
    else:
        print(f"\nFAILURES (tmp kept at {tmp}):")
        for msg in failures:
            print(msg)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
