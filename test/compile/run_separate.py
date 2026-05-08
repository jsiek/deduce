"""End-to-end test for `--compile-module` (per-module compilation).

Step 27 of `docs/separate-compile-plan.md` — the integration check.
For each scenario in `test/compile/separate/`, compile every `.pf`
to its own `.c`+`.h`, link them all together with `cc`, run the
binary, and diff stdout against what the interpreter produces for
the program's entry-point file.

Each scenario lives in a directory with at least an `app.pf`
(the main module — has the `print` statements). Other `.pf`
files in the directory are compiled as library modules
(`--no-main`).

Run from the repo root:
    python3 test/compile/run_separate.py
"""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
SCENARIOS_DIR = ROOT / "test" / "compile" / "separate"
RUNTIME_DIR = ROOT / "compiler" / "runtime"


def find_cc() -> "str | None":
    return shutil.which("cc") or shutil.which("clang") or shutil.which("gcc")


def run_interpreter(scenario: Path, app_pf: Path) -> str:
    proc = subprocess.run(
        [sys.executable, str(ROOT / "deduce.py"),
         "--no-stdlib", "--dir", str(scenario),
         "--suppress-theorems", "--quiet", str(app_pf)],
        cwd=str(ROOT), capture_output=True, text=True, check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"interpreter failed on {app_pf.name}:\n"
            f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        )
    lines = proc.stdout.splitlines()
    if lines and lines[-1].endswith("is valid"):
        lines = lines[:-1]
    return "\n".join(lines) + ("\n" if lines else "")


def run_compiled(scenario: Path, cc: str, build_dir: Path) -> str:
    """Compile every .pf in the scenario directory separately, link
    the resulting .c files together, run, return stdout."""
    pfs = sorted(scenario.glob("*.pf"))
    app_pf = scenario / "app.pf"
    if not app_pf.exists():
        raise RuntimeError(f"{scenario}: no app.pf")

    # Stage .pf files into the build dir so the compiler's
    # `--dir <build_dir>` finds the imports next to the file
    # being compiled.
    for pf in pfs:
        shutil.copy(pf, build_dir / pf.name)

    for pf in pfs:
        is_app = pf.name == "app.pf"
        cmd = [
            sys.executable, str(ROOT / "deduce.py"),
            "--compile-module",
            "--no-stdlib",
            "--dir", str(build_dir),
            "--suppress-theorems", "--quiet",
            "-o", str(build_dir / (pf.stem + ".c")),
            str(build_dir / pf.name),
        ]
        if not is_app:
            cmd.insert(3, "--no-main")
        subprocess.run(cmd, cwd=str(ROOT), check=True,
                       capture_output=True, text=True)

    # Link
    bin_path = build_dir / "app"
    sources = [str(build_dir / (pf.stem + ".c")) for pf in pfs]
    cmd = [cc, "-Wall", "-Wextra", "-Werror",
           "-I", str(build_dir), "-I", str(RUNTIME_DIR),
           "-o", str(bin_path),
           *sources, str(RUNTIME_DIR / "deduce.c")]
    subprocess.run(cmd, check=True, capture_output=True, text=True)

    proc = subprocess.run(
        [str(bin_path)], capture_output=True, text=True, check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"{scenario.name}: compiled binary exit {proc.returncode}:\n"
            f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        )
    return proc.stdout


def check_diamond_init(build_dir: Path) -> "str | None":
    """For the diamond scenario, verify D's singletons are allocated
    exactly once. Concretely:
      - d.c contains an idempotent `_inited` guard inside `d_init`,
      - the line that assigns `C_d__zero_1` appears in exactly one
        .c file (d.c) — neither b.c, c.c, nor app.c re-runs it.
    Step 28 acceptance criterion."""
    d_c = (build_dir / "d.c").read_text()
    if "d_init__inited" not in d_c or "if (d_init__inited) return;" not in d_c:
        return "d.c missing idempotent d_init guard"
    assigns = []
    for c_path in sorted(build_dir.glob("*.c")):
        text = c_path.read_text()
        if "C_d__zero_1 =" in text:
            assigns.append(c_path.name)
    if assigns != ["d.c"]:
        return (f"C_d__zero_1 should only be assigned in d.c, "
                f"but found in: {assigns}")
    return None


def main() -> int:
    cc = find_cc()
    if cc is None:
        print("SKIP: no C compiler (cc/clang/gcc) on PATH", file=sys.stderr)
        return 0

    if not SCENARIOS_DIR.exists():
        print(f"no scenarios at {SCENARIOS_DIR}", file=sys.stderr)
        return 1

    scenarios = [d for d in sorted(SCENARIOS_DIR.iterdir()) if d.is_dir()]
    # If there's no subdir but there is an `app.pf` in the top dir,
    # treat it as a single inline scenario.
    if not scenarios and (SCENARIOS_DIR / "app.pf").exists():
        scenarios = [SCENARIOS_DIR]

    failures: list[str] = []
    tmp = Path(tempfile.mkdtemp(prefix="deduce-separate-"))
    for scenario in scenarios:
        build_dir = tmp / scenario.name
        build_dir.mkdir()
        try:
            interp_out = run_interpreter(scenario, scenario / "app.pf")
            compiled_out = run_compiled(scenario, cc, build_dir)
        except Exception as e:
            failures.append(f"{scenario.name}: {e}")
            continue
        if interp_out != compiled_out:
            failures.append(
                f"{scenario.name}: stdout mismatch\n"
                f"--- interpreter ({len(interp_out)} bytes)\n{interp_out}"
                f"--- compiled ({len(compiled_out)} bytes)\n{compiled_out}"
            )
            continue
        if scenario.name == "diamond":
            err = check_diamond_init(build_dir)
            if err is not None:
                failures.append(f"diamond: {err}")
                continue
        print(f"ok {scenario.name}")

    if failures:
        print(f"\nFAILURES (workdir kept at {tmp}):")
        for msg in failures:
            print(msg)
        return 1
    shutil.rmtree(tmp, ignore_errors=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
