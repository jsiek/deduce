"""End-to-end test for the Deduce-to-C compiler.

For each `.pf` fixture in `test/compile/e2e/` (and the lowering
fixtures in `test/compile/lower/`):
1. Run it under the interpreter and capture stdout.
2. Compile it via `deduce.py --compile` to a `.c` file.
3. Compile that with the system `cc` and link against the runtime.
4. Run the binary and compare stdout to (1).

Skips the whole run with a clear message if `cc` is not available.

Run from the repo root:
    python3 test/compile/run_e2e.py
"""

from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
LOWER_DIR = ROOT / "test" / "compile" / "lower"
E2E_DIR = ROOT / "test" / "compile" / "e2e"
ALLOWLIST = ROOT / "test" / "compile-allowlist.txt"
RUNTIME_DIR = ROOT / "compiler" / "runtime"


def find_cc() -> str | None:
    return shutil.which("cc") or shutil.which("clang") or shutil.which("gcc")


def run_interpreter(pf: Path) -> str:
    """Returns the interpreter's stdout (excluding the trailing
    `... is valid` line)."""
    proc = subprocess.run(
        [sys.executable, str(ROOT / "deduce.py"), "--no-stdlib",
         "--suppress-theorems", "--quiet", str(pf)],
        cwd=str(ROOT),
        capture_output=True, text=True, check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(f"interpreter failed on {pf.name}:\n{proc.stdout}\n{proc.stderr}")
    lines = proc.stdout.splitlines()
    if lines and lines[-1].endswith("is valid"):
        lines = lines[:-1]
    return "\n".join(lines) + ("\n" if lines else "")


def run_compiled(pf: Path, cc: str, tmp: Path) -> str:
    c_path = tmp / (pf.stem + ".c")
    bin_path = tmp / pf.stem
    subprocess.run(
        [sys.executable, str(ROOT / "deduce.py"), "--no-stdlib",
         "--suppress-theorems", "--quiet", "--compile",
         "-o", str(c_path), str(pf)],
        cwd=str(ROOT), check=True,
        # Suppress the interpreter's own print/assert output during
        # compilation; we only want the compiled program's stdout.
        capture_output=True, text=True,
    )
    subprocess.run(
        [cc, "-Wall", "-Wextra", "-Werror",
         "-I", str(RUNTIME_DIR),
         "-o", str(bin_path),
         str(c_path), str(RUNTIME_DIR / "deduce.c")],
        check=True, capture_output=True, text=True,
    )
    proc = subprocess.run([str(bin_path)], capture_output=True, text=True, check=False)
    if proc.returncode != 0:
        raise RuntimeError(
            f"{pf.name}: compiled binary exit {proc.returncode}:\n"
            f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        )
    return proc.stdout


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--filter", default=None)
    ap.add_argument("--keep-tmp", action="store_true",
                    help="don't delete the working directory; print its path")
    args = ap.parse_args()

    cc = find_cc()
    if cc is None:
        print("SKIP: no C compiler (cc/clang/gcc) on PATH", file=sys.stderr)
        return 0

    fixtures: list[Path] = []
    for d in (E2E_DIR, LOWER_DIR):
        if d.exists():
            fixtures.extend(sorted(d.glob("*.pf")))
    if ALLOWLIST.exists():
        for raw in ALLOWLIST.read_text().splitlines():
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            p = (ROOT / line).resolve()
            if not p.exists():
                print(f"WARN: allowlist entry not found: {line}", file=sys.stderr)
                continue
            fixtures.append(p)
    if args.filter:
        fixtures = [f for f in fixtures if args.filter in f.name]
    if not fixtures:
        print("no fixtures found", file=sys.stderr)
        return 1

    tmp = Path(tempfile.mkdtemp(prefix="deduce-e2e-"))
    failures: list[str] = []
    for pf in fixtures:
        try:
            interp_out = run_interpreter(pf)
            compiled_out = run_compiled(pf, cc, tmp)
        except Exception as e:
            failures.append(f"{pf.name}: {e}")
            continue
        if interp_out != compiled_out:
            failures.append(
                f"{pf.name}: stdout mismatch\n"
                f"--- interpreter ({len(interp_out)} bytes)\n{interp_out}"
                f"--- compiled ({len(compiled_out)} bytes)\n{compiled_out}"
            )
            continue
        print(f"ok {pf.relative_to(ROOT)}")

    if args.keep_tmp:
        print(f"workdir: {tmp}")
    else:
        shutil.rmtree(tmp, ignore_errors=True)

    if failures:
        print("\nFAILURES:")
        for msg in failures:
            print(msg)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
