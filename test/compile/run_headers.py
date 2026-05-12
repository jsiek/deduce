"""Header-emission tests.

For each lowering fixture, compute its post-prune IR, walk every
module that contributed a kept top-level decl, and emit a `.h` for
each. Concatenate the per-module headers (in deterministic module
order) into a single string and compare it against the fixture's
sibling `.h` file.

Step 26 of `docs/separate-compile-plan.md` — the acceptance check
on header generation. Run from the repo root:

    python3 test/compile/run_headers.py
    python3 test/compile/run_headers.py --regenerate
"""

from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(ROOT))

from compiler import closure, emit_c, lower, prune  # noqa: E402
from abstract_syntax import (  # noqa: E402
    add_import_directory,
    init_import_directories,
)
from lsp.library import check_file  # noqa: E402

LOWER_DIR = ROOT / "test" / "compile" / "lower"
PRELUDE_DIR = ROOT / "test" / "compile" / "prelude"


def headers_for(path: Path) -> str:
    """Return the concatenated headers for every module that has at
    least one top-level decl in `path`'s post-prune IR. Modules are
    listed in alphabetical order so the output is reproducible."""
    sys.argv = [str(ROOT / "deduce.py")]
    init_import_directories()
    add_import_directory(str(ROOT / "lib"))

    needs_prelude = _needs_prelude(path)
    prelude: list[str] = []
    if needs_prelude:
        prelude = sorted(
            f.removesuffix(".pf")
            for f in os.listdir(ROOT / "lib")
            if f.endswith(".pf")
        )

    result = check_file(str(path), prelude=prelude)
    if not result.ok:
        raise RuntimeError(f"{path}: deduce check failed:\n{result.error_message}")
    program = lower.lower_program(result.ast, main_module=path.stem)
    program = closure.closure_convert(program)
    program = prune.prune(program)

    modules = emit_c.modules_in(program)
    parts: list[str] = []
    for m in modules:
        parts.append(f"// === module {m} ===")
        parts.append(emit_c.emit_header(program, m).rstrip("\n"))
        parts.append("")
    return "\n".join(parts) + ("\n" if parts else "")


def _needs_prelude(pf: Path) -> bool:
    for raw in pf.read_text().splitlines():
        s = raw.strip()
        if not s or s.startswith("//") or s.startswith("/*"):
            continue
        if s.startswith("import ") or s.startswith("public import "):
            return True
    return False


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--regenerate", action="store_true",
                    help="overwrite expected .h files with current output")
    ap.add_argument("--filter", default=None,
                    help="only run fixtures whose name contains this string")
    args = ap.parse_args()

    fixtures: list[Path] = []
    for d in (LOWER_DIR, PRELUDE_DIR):
        if d.exists():
            fixtures.extend(sorted(d.glob("*.pf")))
    if args.filter:
        fixtures = [f for f in fixtures if args.filter in f.name]

    failures: list[str] = []
    for pf in fixtures:
        try:
            actual = headers_for(pf)
        except Exception as e:
            failures.append(f"{pf.name}: header emission raised: {e}")
            continue

        expect_path = pf.with_suffix(".h")
        if args.regenerate:
            expect_path.write_text(actual)
            print(f"regenerated {expect_path.name}")
            continue
        if not expect_path.exists():
            failures.append(
                f"{pf.name}: missing expected file {expect_path.name}"
            )
            continue
        expected = expect_path.read_text()
        if actual != expected:
            failures.append(
                f"{pf.name}: header mismatch\n"
                f"--- expected\n{expected}--- actual\n{actual}"
            )
            continue
        print(f"ok {pf.name}")

    if failures:
        print("\nFAILURES:")
        for msg in failures:
            print(msg)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
