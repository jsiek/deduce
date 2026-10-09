"""Tests for the post-prelude snapshot on disk (issue #1217).

Each test uses a one-module prelude in a temporary import directory and
simulates a new process by dropping the in-memory prelude state
(``reset_prelude_cache``), so only the disk snapshot can carry the
prelude over."""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

import flags  # noqa: E402
import lsp.library as library  # noqa: E402
from checker_cache import get_cache_stats  # noqa: E402

MINI = """\
union Bit { o  i }

theorem bit_cases: all b:Bit. b = o or b = i
proof
  arbitrary b:Bit
  switch b {
    case o { . }
    case i { . }
  }
end
"""

USER = """\
theorem uses_mini: all b:Bit. b = o or b = i
proof
  bit_cases
end
"""


@pytest.fixture
def prelude_dir(tmp_path, monkeypatch):
    """A directory holding the prelude module ``Mini``, on the import
    path, with snapshots saved under ``tmp_path / "snapshots"``."""
    lib = tmp_path / "lib"
    lib.mkdir()
    (lib / "Mini.pf").write_text(MINI)
    monkeypatch.setattr(flags, "import_directories", flags.import_directories | {str(lib)})
    library.set_snapshot_dir(str(tmp_path / "snapshots"))
    library.reset_prelude_cache()
    yield lib
    library.set_snapshot_dir(None)
    library.reset_prelude_cache()


def _new_process() -> None:
    """Forget the in-memory prelude, as a freshly started server would."""
    library.reset_prelude_cache()


def _bootstraps(monkeypatch) -> list[str]:
    """Record every prelude bootstrap (a check of ``__prelude__.pf``)."""
    calls: list[str] = []
    real = library._check_file_impl

    def recording(filename, *args, **kwargs):
        if filename == "__prelude__.pf":
            calls.append(filename)
        return real(filename, *args, **kwargs)

    monkeypatch.setattr(library, "_check_file_impl", recording)
    return calls


def test_second_start_loads_the_snapshot_instead_of_checking_the_prelude(
    prelude_dir, tmp_path, monkeypatch
):
    bootstraps = _bootstraps(monkeypatch)
    first = library.check_file("user.pf", content=USER, prelude=("Mini",))
    assert first.ok, first.error_message
    assert bootstraps == ["__prelude__.pf"]
    first_misses = get_cache_stats()["misses"]["check_proofs"]
    [snapshot] = (tmp_path / "snapshots").glob("prelude-*.pickle")

    _new_process()
    second = library.check_file("user.pf", content=USER, prelude=("Mini",))
    assert second.ok, second.error_message
    assert bootstraps == ["__prelude__.pf"]  # no second bootstrap
    # The statement cache saw only the user file's two statements (the
    # prelude's `import Mini` and the theorem): Mini's own statements,
    # checked in the first run, were never checked in this "process".
    assert get_cache_stats()["misses"] == {"check_proofs": 2}
    assert first_misses > 2
    assert list((tmp_path / "snapshots").glob("prelude-*.pickle")) == [snapshot]


def test_editing_a_prelude_file_invalidates_the_snapshot(prelude_dir, monkeypatch):
    bootstraps = _bootstraps(monkeypatch)
    assert library.check_file("user.pf", content=USER, prelude=("Mini",)).ok

    (prelude_dir / "Mini.pf").write_text(MINI.replace("bit_cases", "bit_split"))
    _new_process()
    result = library.check_file("user.pf", content=USER, prelude=("Mini",))
    # The renamed theorem shows the prelude was checked afresh.
    assert not result.ok and "bit_cases" in result.error_message
    assert len(bootstraps) == 2


def test_editing_a_dependency_in_another_directory_invalidates_the_snapshot(
    prelude_dir, tmp_path, monkeypatch
):
    """The prelude module imports a module from a different import
    directory; editing that dependency must still be noticed."""
    deps = tmp_path / "deps"
    deps.mkdir()
    (deps / "Dep.pf").write_text("union Bit { o  i }\n")
    (prelude_dir / "Mini.pf").write_text(
        "public import Dep\n" + MINI.replace("union Bit { o  i }\n", "")
    )
    monkeypatch.setattr(flags, "import_directories", flags.import_directories | {str(deps)})
    bootstraps = _bootstraps(monkeypatch)
    assert library.check_file("user.pf", content=USER, prelude=("Mini",)).ok

    _new_process()
    assert library.check_file("user.pf", content=USER, prelude=("Mini",)).ok
    assert len(bootstraps) == 1  # unchanged: the snapshot was used

    (deps / "Dep.pf").write_text("union Bit { o  i  x }\n")
    _new_process()
    uses_x = "theorem sees_x: x = x\nproof\n  .\nend\n"
    assert library.check_file("user.pf", content=uses_x, prelude=("Mini",)).ok
    assert len(bootstraps) == 2  # the edit to Dep forced a fresh check


def test_a_corrupt_snapshot_is_rebuilt(prelude_dir, tmp_path, capsys):
    assert library.check_file("user.pf", content=USER, prelude=("Mini",)).ok
    [snapshot] = (tmp_path / "snapshots").glob("prelude-*.pickle")
    snapshot.write_bytes(b"not a pickle")

    _new_process()
    assert library.check_file("user.pf", content=USER, prelude=("Mini",)).ok
    assert "ignoring prelude snapshot" in capsys.readouterr().err
    assert snapshot.read_bytes() != b"not a pickle"  # rewritten


def test_snapshots_are_off_unless_a_directory_is_set(tmp_path, monkeypatch):
    monkeypatch.setenv("DEDUCE_SNAPSHOT_DIR", "")
    assert library.default_snapshot_dir() is None
    monkeypatch.setenv("DEDUCE_SNAPSHOT_DIR", str(tmp_path))
    assert library.default_snapshot_dir() == str(tmp_path)
    monkeypatch.delenv("DEDUCE_SNAPSHOT_DIR")
    monkeypatch.setenv("XDG_CACHE_HOME", str(tmp_path / "xdg"))
    assert library.default_snapshot_dir() == str(tmp_path / "xdg" / "deduce")
