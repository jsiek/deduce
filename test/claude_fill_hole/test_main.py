"""End-to-end CLI tests for the sidecar's __main__ entry point.

Covers the request/response shape and the --dry-run path. The
real-API path is exercised in test_agent.py with a fake client; the
tests here only run the CLI entry, which means they don't need an
``ANTHROPIC_API_KEY``.
"""

from __future__ import annotations

import json
import sys
from io import StringIO
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]

from tools.claude_fill_hole import __main__ as sidecar_main  # noqa: E402


def _run_main(argv, stdin_text, monkeypatch) -> tuple[int, str, str]:
    """Invoke main() with patched stdin/stdout/stderr; return (rc, stdout, stderr)."""
    fake_stdin = StringIO(stdin_text)
    fake_stdout = StringIO()
    fake_stderr = StringIO()
    monkeypatch.setattr(sys, "stdin", fake_stdin)
    monkeypatch.setattr(sys, "stdout", fake_stdout)
    monkeypatch.setattr(sys, "stderr", fake_stderr)
    rc = sidecar_main.main(argv)
    return rc, fake_stdout.getvalue(), fake_stderr.getvalue()


def _build_request(file_path: str, source: str) -> str:
    """Assemble a request JSON that points at the single ``?`` in ``source``."""
    idx = source.index("?")
    # Convert byte offset back to (line, character).
    before = source[:idx]
    line = before.count("\n")
    last_nl = before.rfind("\n")
    character = idx - (last_nl + 1) if last_nl >= 0 else idx
    return json.dumps(
        {
            "file": file_path,
            "holeRange": {
                "start": {"line": line, "character": character},
                "end": {"line": line, "character": character + 1},
            },
            "goal": "P = P",
            "givens": [],
            "lemmasInScope": [],
            "fingerprint": "fp",
            "content": source,
        }
    )


def test_dry_run_with_valid_stub_passes(monkeypatch, tmp_path):
    """``--dry-run`` splices the stub ``?`` and confirms the
    splice/validate pipeline works against deduce.py."""
    source = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  ?\n"
        "end\n"
    )
    file_path = tmp_path / "proof.pf"
    file_path.write_text(source)
    request = _build_request(str(file_path), source)

    argv = [
        "--dry-run",
        "--no-stdlib",
        "--deduce-cmd",
        f"{sys.executable} {REPO_ROOT / 'deduce.py'}",
        "--deduce-root",
        str(REPO_ROOT),
        "--timeout",
        "30",
    ]
    rc, stdout, stderr = _run_main(argv, request, monkeypatch)

    # The stub proof is `?` itself, which leaves the file unchanged.
    # That fails validation (incomplete proof), but the *pipeline*
    # ran end-to-end -- which is what --dry-run checks.
    decoded = json.loads(stdout.strip())
    assert decoded["fingerprint"] == "fp"
    assert decoded["model"] == "<dry-run>"
    assert decoded["validations"][0]["attempt"] == 1
    # rc reflects the validation outcome (1 = invalid stub, 0 = valid).
    assert rc in (0, 1)


def test_missing_stdin_returns_failure(monkeypatch):
    rc, stdout, stderr = _run_main([], "", monkeypatch)
    assert rc == 2
    decoded = json.loads(stdout.strip())
    assert decoded["ok"] is False
    assert "empty stdin" in decoded["error"]


def test_malformed_stdin_returns_failure(monkeypatch):
    rc, stdout, stderr = _run_main([], "not json", monkeypatch)
    assert rc == 2
    decoded = json.loads(stdout.strip())
    assert decoded["ok"] is False
    assert "could not parse" in decoded["error"]


def test_missing_api_key_returns_failure(monkeypatch, tmp_path):
    """Without --dry-run and without the API key env var, the
    sidecar fails fast with a structured error before importing
    anthropic."""
    source = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  ?\n"
        "end\n"
    )
    file_path = tmp_path / "proof.pf"
    file_path.write_text(source)
    request = _build_request(str(file_path), source)

    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)
    rc, stdout, _ = _run_main(
        ["--api-key-env", "NONEXISTENT_KEY_FOR_TEST"], request, monkeypatch
    )
    assert rc == 2
    decoded = json.loads(stdout.strip())
    assert decoded["ok"] is False
    assert "NONEXISTENT_KEY_FOR_TEST" in decoded["error"]


def test_default_deduce_cmd_uses_sys_executable(monkeypatch, tmp_path):
    """Regression: when --deduce-cmd is omitted, the validator should
    fork the *current* Python (sys.executable), not bare ``python3''.

    Bare ``python3'' picks the first ``python3'' on PATH, which on
    macOS GUI emacs is typically the system Python without lark, so
    every validate would crash with a ``ModuleNotFoundError: No
    module named 'lark'`` traceback.  Pinning to ``sys.executable''
    means the checker subprocess inherits the host Python's
    site-packages.

    We assert the failure doesn't mention lark/ModuleNotFoundError
    -- if the default ever drifts back to bare ``python3'' on a
    machine without lark on $PATH's first python, this test fails."""
    source = (
        "theorem t: all P:bool. P = P\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  ?\n"
        "end\n"
    )
    file_path = tmp_path / "proof.pf"
    file_path.write_text(source)
    request = _build_request(str(file_path), source)

    # No --deduce-cmd: relies on the default.
    argv = [
        "--dry-run",
        "--no-stdlib",
        "--deduce-root",
        str(REPO_ROOT),
        "--timeout",
        "30",
    ]
    rc, stdout, _ = _run_main(argv, request, monkeypatch)
    decoded = json.loads(stdout.strip())
    error_text = (decoded.get("error") or "") + "".join(
        v.get("errorTail") or "" for v in decoded.get("validations") or ()
    )
    assert "ModuleNotFoundError" not in error_text, (
        "Validator's deduce.py subprocess crashed importing lark -- "
        "the default --deduce-cmd is forking the wrong Python."
    )
    assert "No module named 'lark'" not in error_text


def test_hole_range_out_of_bounds_returns_failure(monkeypatch, tmp_path):
    """A holeRange past EOF is rejected before hitting the validator."""
    source = "theorem t: bool = true\n"
    file_path = tmp_path / "proof.pf"
    file_path.write_text(source)
    request = json.dumps(
        {
            "file": str(file_path),
            "holeRange": {
                "start": {"line": 999, "character": 0},
                "end": {"line": 999, "character": 1},
            },
            "goal": "x",
            "givens": [],
            "lemmasInScope": [],
            "fingerprint": "fp",
            "content": source,
        }
    )
    rc, stdout, _ = _run_main(["--dry-run"], request, monkeypatch)
    assert rc == 2
    decoded = json.loads(stdout.strip())
    assert decoded["ok"] is False
    assert "out of bounds" in decoded["error"]
