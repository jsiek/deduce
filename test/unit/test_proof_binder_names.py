"""Proofs print the names they bind as the user wrote them, and with
their unique suffixes under `--unique-names` (#1311).

Runs on test/should-error/assume_body_binders_base_names_1311.pf, whose
error message prints an `assume` whose body binds names with
`arbitrary` and `obtain`. Its .err fixture covers the default output."""
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def test_unique_names_keeps_binder_suffixes() -> None:
    result = subprocess.run(
        [sys.executable, "deduce.py", "--no-stdlib", "--unique-names",
         "test/should-error/assume_body_binders_base_names_1311.pf"],
        cwd=ROOT, capture_output=True, text=True, timeout=300)
    assert ("assume q.1T_3{arbitrary x.1T_4 : bool "
            "obtain y.1T_5 where h.1T_6 : y.1T_5") in result.stdout, result.stdout
