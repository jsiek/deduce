"""Build the deduce prelude as a static archive.

Step 29 of `docs/separate-compile-plan.md`. Runs `--compile-module`
on every `lib/*.pf` in topological order, compiles each generated
`.c` to a `.o`, and archives them into
`compiler/runtime/libdeduce_prelude.a`. Generated headers are
copied to `compiler/runtime/include/`.

User programs that import a stdlib module then link with:

    cc -I compiler/runtime/include
       -L compiler/runtime
       app.c compiler/runtime/deduce.c
       -ldeduce_prelude -Wl,--gc-sections
       -o app

so the stdlib stops being inlined into every user program.

The archive is built reproducibly: file order is deterministic
(topological), `ZERO_AR_DATE=1` zeroes the per-member timestamps in
the BSD `ar` on macOS, and the `D` modifier asks GNU `ar` for the
same on Linux. A second invocation produces a byte-identical `.a`.

Run from the repo root:
    python3 compiler/compile_prelude.py
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import sys
from graphlib import TopologicalSorter
from pathlib import Path
from typing import Dict, List

ROOT = Path(__file__).resolve().parent.parent
LIB = ROOT / "lib"
RUNTIME = ROOT / "compiler" / "runtime"
# Intermediate .c/.h/.o files live in the runtime build dir instead
# of cluttering lib/ next to the .pf source files. Headers are then
# also copied to RUNTIME/include/ for downstream `-I` consumers.
BUILD_DIR = RUNTIME / "_build"
INCLUDE_DIR = RUNTIME / "include"
ARCHIVE = RUNTIME / "libdeduce_prelude.a"

# Per Step 27/28: deduce.py infers each module's symbols from the
# file basename, not the in-file `module` declaration. So symbol
# stability and import resolution all key off the .pf basename.
IMPORT_RE = re.compile(r"^\s*import\s+(\S+)", re.MULTILINE)


def topo_order(pfs: List[Path]) -> List[Path]:
    """Topological sort of `pfs` by `import` directive."""
    by_name: Dict[str, Path] = {p.stem: p for p in pfs}
    deps: Dict[str, List[str]] = {}
    for p in pfs:
        text = p.read_text()
        # Only edges that point at other prelude files; user-side
        # imports (none here) would be ignored.
        deps[p.stem] = [
            imp for imp in IMPORT_RE.findall(text) if imp in by_name
        ]
    return [by_name[n] for n in TopologicalSorter(deps).static_order()]


def find_cc() -> str:
    cc = shutil.which("cc") or shutil.which("clang") or shutil.which("gcc")
    if cc is None:
        sys.exit("error: no C compiler (cc/clang/gcc) on PATH")
    return cc


def find_ar() -> str:
    ar = shutil.which("ar")
    if ar is None:
        sys.exit("error: no `ar` on PATH")
    return ar


def run(cmd: List[str], *, env: "dict[str, str] | None" = None) -> None:
    """Run `cmd` and propagate failures (with stderr) to the caller."""
    proc = subprocess.run(
        cmd, env=env, capture_output=True, text=True, check=False,
    )
    if proc.returncode != 0:
        sys.exit(
            f"command failed ({proc.returncode}): {' '.join(cmd)}\n"
            f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        )


def compile_pf_to_c(pf: Path) -> Path:
    """`deduce.py --compile-module --no-main` into the build dir.
    Returns the generated `.c` path."""
    out_c = BUILD_DIR / (pf.stem + ".c")
    run([
        sys.executable, str(ROOT / "deduce.py"),
        "--compile-module", "--no-main", "--no-stdlib",
        "--dir", str(LIB),
        "--suppress-theorems", "--quiet",
        "-o", str(out_c),
        str(pf),
    ])
    return out_c


def compile_c_to_o(cc: str, c: Path) -> Path:
    """Compile a generated `.c` to `.o` with section flags so the
    linker can later strip dead code via `-Wl,--gc-sections`. Both
    files live in the build dir."""
    o = c.with_suffix(".o")
    run([
        cc, "-c",
        "-Wall", "-Wextra", "-Werror",
        "-ffunction-sections", "-fdata-sections",
        "-I", str(BUILD_DIR), "-I", str(RUNTIME),
        "-o", str(o), str(c),
    ])
    return o


def make_archive(ar: str, objects: List[Path]) -> None:
    """`ar rcs` the objects into the prelude archive. The archive is
    rebuilt from scratch (deleted first) so removed prelude files
    don't leave stale entries behind. `ZERO_AR_DATE=1` makes BSD
    `ar` (macOS) zero the per-member timestamp; the `D` modifier
    does the same on GNU `ar` (Linux). Either flag is harmless on
    the platform that doesn't need it."""
    if ARCHIVE.exists():
        ARCHIVE.unlink()
    env = dict(os.environ)
    env["ZERO_AR_DATE"] = "1"
    # Try the `D` modifier first (GNU ar); fall back to plain `rcs`
    # for BSD ar (macOS), which doesn't accept `D` but is already
    # deterministic with ZERO_AR_DATE=1.
    cmd = [ar, "rcsD", str(ARCHIVE), *[str(o) for o in objects]]
    proc = subprocess.run(
        cmd, env=env, capture_output=True, text=True, check=False,
    )
    if proc.returncode != 0:
        cmd = [ar, "rcs", str(ARCHIVE), *[str(o) for o in objects]]
        proc = subprocess.run(
            cmd, env=env, capture_output=True, text=True, check=False,
        )
        if proc.returncode != 0:
            sys.exit(
                f"ar failed: {' '.join(cmd)}\n"
                f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
            )


def install_headers(hs: List[Path]) -> None:
    """Copy `.h` files into `compiler/runtime/include/`. The
    directory is rebuilt from scratch so a removed prelude file
    doesn't leave a stale header behind."""
    if INCLUDE_DIR.exists():
        shutil.rmtree(INCLUDE_DIR)
    INCLUDE_DIR.mkdir(parents=True)
    for h in hs:
        shutil.copy2(h, INCLUDE_DIR / h.name)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--clean", action="store_true",
        help="Remove the archive, include dir, and lib/*.{c,h,o} "
             "before building.",
    )
    parser.add_argument(
        "-v", "--verbose", action="store_true",
        help="Echo each step.",
    )
    args = parser.parse_args()

    pfs = sorted(LIB.glob("*.pf"))
    if not pfs:
        sys.exit(f"no .pf files in {LIB}")

    if args.clean:
        if BUILD_DIR.exists():
            shutil.rmtree(BUILD_DIR)
        if ARCHIVE.exists():
            ARCHIVE.unlink()
        if INCLUDE_DIR.exists():
            shutil.rmtree(INCLUDE_DIR)

    BUILD_DIR.mkdir(parents=True, exist_ok=True)

    order = topo_order(pfs)
    cc = find_cc()
    ar = find_ar()

    if args.verbose:
        print(f"prelude: {len(order)} files, topological order:")
        for p in order:
            print(f"  {p.name}")

    for pf in order:
        if args.verbose:
            print(f"deduce {pf.name}")
        compile_pf_to_c(pf)

    objects: List[Path] = []
    for pf in order:
        c = BUILD_DIR / (pf.stem + ".c")
        if args.verbose:
            print(f"cc {c.name}")
        objects.append(compile_c_to_o(cc, c))

    if args.verbose:
        print(f"ar -> {ARCHIVE.relative_to(ROOT)}")
    make_archive(ar, objects)

    headers = [BUILD_DIR / (pf.stem + ".h") for pf in order]
    if args.verbose:
        print(f"install headers -> {INCLUDE_DIR.relative_to(ROOT)}")
    install_headers(headers)

    print(
        f"built {ARCHIVE.relative_to(ROOT)} "
        f"({ARCHIVE.stat().st_size} bytes, "
        f"{len(order)} modules)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
