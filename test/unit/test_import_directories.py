"""Unit tests for the import-directory search path (issue #1246).

The same directory added under two spellings used to stay on the path
twice, in a ``set`` whose order changed between runs, so error messages
named library files sometimes by the relative and sometimes by the
absolute spelling.
"""

from __future__ import annotations

import os

import pytest

import flags


def test_same_directory_under_two_spellings_is_added_once(
        monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(flags, "import_directories", [])
    flags.add_import_directory("lib")
    flags.add_import_directory(os.path.abspath("lib"))
    flags.add_import_directory("./lib/")
    assert flags.get_import_directories() == ["lib"]


def test_directories_are_searched_in_the_order_added(
        monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(flags, "import_directories", [])
    for d in ["test/test-imports", ".", "lib"]:
        flags.add_import_directory(d)
    assert flags.get_import_directories() == ["test/test-imports", ".", "lib"]
