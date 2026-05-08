"""Acceptance test for `make compile-prelude` (prelude as static archive).

Step 29 of `docs/separate-compile-plan.md`. Builds the prelude
archive, then verifies a hand-rolled user program that imports
stdlib modules links against `-ldeduce_prelude` and produces the
same output as the interpreter. Also confirms the archive is
reproducible: a second build is byte-identical.

Run from the repo root:
    python3 test/compile/run_prelude_archive.py
"""

from __future__ import annotations

import filecmp
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
COMPILER = ROOT / "compiler"
RUNTIME = COMPILER / "runtime"
LIB = ROOT / "lib"
ARCHIVE = RUNTIME / "libdeduce_prelude.a"
INCLUDE_DIR = RUNTIME / "include"

# Small program exercising several stdlib modules. Output is what
# the interpreter would produce.
USER_PROGRAM = """\
import Nat
import UInt

print 0
print 1 + 2
print 3 * 4
"""
EXPECTED_OUTPUT = "0\n3\n12\n"


def find_cc() -> "str | None":
    return shutil.which("cc") or shutil.which("clang") or shutil.which("gcc")


def build_prelude() -> None:
    proc = subprocess.run(
        [sys.executable, str(COMPILER / "compile_prelude.py")],
        cwd=str(ROOT), capture_output=True, text=True, check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            "compile_prelude.py failed:\n"
            f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        )


def main() -> int:
    cc = find_cc()
    if cc is None:
        print("SKIP: no C compiler on PATH", file=sys.stderr)
        return 0

    # First build.
    build_prelude()
    if not ARCHIVE.exists():
        print(f"FAIL: archive not produced at {ARCHIVE}", file=sys.stderr)
        return 1

    # Snapshot for reproducibility check, then a clean second build.
    with tempfile.NamedTemporaryFile(delete=False, suffix=".a") as tmp:
        snapshot = Path(tmp.name)
    shutil.copy2(ARCHIVE, snapshot)
    try:
        subprocess.run(
            [sys.executable, str(COMPILER / "compile_prelude.py"), "--clean"],
            cwd=str(ROOT), capture_output=True, text=True, check=True,
        )
        if not filecmp.cmp(snapshot, ARCHIVE, shallow=False):
            print("FAIL: archive is not byte-identical between two builds",
                  file=sys.stderr)
            return 1
    finally:
        snapshot.unlink(missing_ok=True)

    # User-program acceptance.
    work = Path(tempfile.mkdtemp(prefix="deduce-prelude-"))
    try:
        app_pf = work / "app.pf"
        app_pf.write_text(USER_PROGRAM)
        # Compile with --compile-module against the prelude .pf
        # sources (deduce.py needs the full source for type-check;
        # the prebuilt archive only saves cc time + future Steps'
        # caching).
        subprocess.run([
            sys.executable, str(ROOT / "deduce.py"),
            "--compile-module", "--no-stdlib",
            "--dir", str(LIB),
            "--suppress-theorems", "--quiet",
            "-o", str(work / "app.c"),
            str(app_pf),
        ], cwd=str(ROOT), capture_output=True, text=True, check=True)
        # Link against the archive + runtime.
        bin_path = work / "app"
        subprocess.run([
            cc,
            "-I", str(INCLUDE_DIR), "-I", str(RUNTIME),
            "-L", str(RUNTIME),
            str(work / "app.c"), str(RUNTIME / "deduce.c"),
            "-ldeduce_prelude",
            "-o", str(bin_path),
        ], capture_output=True, text=True, check=True)
        proc = subprocess.run(
            [str(bin_path)], capture_output=True, text=True, check=False,
        )
        if proc.returncode != 0:
            print(f"FAIL: app exit {proc.returncode}\n"
                  f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}",
                  file=sys.stderr)
            return 1
        if proc.stdout != EXPECTED_OUTPUT:
            print(
                f"FAIL: stdout mismatch\n"
                f"--- expected\n{EXPECTED_OUTPUT}"
                f"--- actual\n{proc.stdout}",
                file=sys.stderr,
            )
            return 1
    finally:
        shutil.rmtree(work, ignore_errors=True)

    print("ok prelude archive (deterministic + linkable)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
