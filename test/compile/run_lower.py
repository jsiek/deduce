"""Standalone runner for lowering tests.

For each `*.pf` fixture in `test/compile/lower/`, run the Deduce
pipeline (parse + uniquify + type-check) without the prelude, then
hand the post-uniquify AST to `compiler.lower.lower_program` and
pretty-print the resulting IR. Compare against the sibling `*.ir`
file, regenerating with `--regenerate` if requested.

Run from the repo root:

    python3 test/compile/run_lower.py
    python3 test/compile/run_lower.py --regenerate
"""

from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path

# Make the repo root importable.
ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(ROOT))

from compiler import closure, ir, lower  # noqa: E402
from lsp.library import check_file  # noqa: E402


FIXTURE_DIR = ROOT / "test" / "compile" / "lower"


def lower_file(path: Path) -> tuple[str, str]:
    """Returns (post-lower IR, post-closure-conversion IR)."""
    sys.argv = [str(ROOT / "deduce.py")]  # check_file looks at sys.argv[0]
    result = check_file(str(path), prelude=[])
    if not result.ok:
        raise RuntimeError(f"{path}: deduce check failed:\n{result.error_message}")
    program = lower.lower_program(result.ast)
    lowered_str = ir.pp_program(program)
    converted = closure.closure_convert(program)
    converted_str = ir.pp_program(converted)
    return lowered_str, converted_str


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--regenerate", action="store_true",
                    help="overwrite expected .ir files with current output")
    ap.add_argument("--filter", default=None,
                    help="only run fixtures whose name contains this string")
    args = ap.parse_args()

    fixtures = sorted(FIXTURE_DIR.glob("*.pf"))
    if args.filter:
        fixtures = [f for f in fixtures if args.filter in f.name]

    failures: list[str] = []
    for pf in fixtures:
        try:
            lowered, converted = lower_file(pf)
        except Exception as e:
            failures.append(f"{pf.name}: lowering raised: {e}")
            continue

        for stage, actual in (("ir", lowered), ("cir", converted)):
            expect_path = pf.with_suffix("." + stage)
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
                    f"{pf.name} ({stage}): IR mismatch\n"
                    f"--- expected\n{expected}--- actual\n{actual}"
                )
                continue
            print(f"ok {pf.name} ({stage})")

    if failures:
        print("\nFAILURES:")
        for msg in failures:
            print(msg)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
