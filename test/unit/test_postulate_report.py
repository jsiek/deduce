"""`deduce.py --postulates` lists exactly the postulates a file depends on.

Runs on test/should-validate/postulate_type_fun.pf, whose import
test/test-imports/PostulateSemigroup.pf declares postulates used
directly, through an auto rule, and through `associative`, plus one
(`s_unused`) that nothing uses."""
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def _report(path: str, *options: str) -> str:
    result = subprocess.run(
        [sys.executable, "deduce.py", *(options or ("--postulates",)),
         "--no-stdlib", "--suppress-theorems", "--dir", "test/test-imports",
         path],
        cwd=ROOT, capture_output=True, text=True, timeout=300)
    assert result.returncode == 0, result.stdout + result.stderr
    return result.stdout


def test_report_follows_direct_auto_and_associative_uses() -> None:
    out = _report("test/should-validate/postulate_type_fun.pf")
    for expected in [
        "postulate type S", "postulate fun e : S",
        "postulate fun operator * : (fn (S, S) -> S)",
        "postulate s_mult_e:",      # via the auto rule, through an imported theorem
        "postulate s_mult_assoc:",  # via `associative operator* in S`
        "postulate type T", "postulate fun one : T", "postulate t_one_mult:",
    ]:
        assert expected in out, out
    assert "s_unused" not in out, out
    assert "hidden" not in out, out


def test_report_without_postulates() -> None:
    out = _report("test/should-validate/all1.pf")
    assert "depends on no postulates" in out, out


def test_report_starts_from_unnamed_statements(tmp_path: Path) -> None:
    # `assert` and `print` define no name, but what they use still counts.
    src = tmp_path / "unnamed.pf"
    src.write_text("import PostulateSemigroup\nassert e = e\nprint e\n")
    out = _report(str(src))
    assert "postulate fun e : S" in out, out
    assert "postulate type S" in out, out
    assert "s_mult_e" not in out, out


def test_report_includes_uses_during_type_checking(tmp_path: Path) -> None:
    # `e * e * e` type-checks only because `*` is associative on S, which
    # the checker consults while declaring the definition, before any proofs.
    src = tmp_path / "typecheck.pf"
    src.write_text("import PostulateSemigroup\ndefine three : S = e * e * e\n")
    out = _report(str(src), "--postulates-of", "three")
    assert "postulate s_mult_assoc:" in out, out


def test_bare_import_depends_on_no_postulates(tmp_path: Path) -> None:
    src = tmp_path / "bare.pf"
    src.write_text("import PostulateSemigroup\n")
    assert "depends on no postulates" in _report(str(src))
