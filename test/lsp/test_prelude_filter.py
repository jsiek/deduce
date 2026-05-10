"""Issue #365: ``import M using ...`` / ``hiding ...`` must still
filter even when ``M`` is also in the auto-prelude.

Before the fix, the prelude entry for ``M`` ran first and populated
``env`` with all of ``M``'s exports, so the user's filter was silently
a no-op. The fix in ``lsp/library.py`` skips the prelude entry for any
module the user explicitly imports with a filter.
"""

from __future__ import annotations

import sys
import textwrap
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from lsp.library import check_file  # noqa: E402


# Full lib/ prelude, mirroring what ``deduce.py`` builds when run without
# ``--no-stdlib``. ``BigO`` is the leaf module the tests filter against —
# it has no other lib module that publicly re-imports it, so suppressing
# the prelude entry for ``BigO`` is enough to make the user's filter
# observable. Modules that ARE transitively re-imported (e.g. ``Nat``)
# would still leak through other prelude entries; that's a known
# limitation noted in #365.
LIB_DIR = REPO_ROOT / "lib"
PRELUDE = tuple(
    sorted(p.stem for p in LIB_DIR.glob("*.pf"))
)


def _check(tmp_path: Path, source: str):
    pf = tmp_path / "test_prelude_filter.pf"
    pf.write_text(textwrap.dedent(source))
    return check_file(str(pf), prelude=PRELUDE)


def test_using_admits_listed_name(tmp_path: Path) -> None:
    result = _check(
        tmp_path,
        """
        import BigO using bigo_refl | operator≲

        theorem t: all f : fn UInt -> UInt. f ≲ f
        proof
          bigo_refl
        end
        """,
    )
    assert result.ok, (
        "expected the file to validate; got: " + (result.error_message or "")
    )


def test_using_excludes_unlisted_name(tmp_path: Path) -> None:
    result = _check(
        tmp_path,
        """
        import BigO using bigo_refl | operator≲

        theorem t: all f : fn UInt -> UInt, g : fn UInt -> UInt, h : fn UInt -> UInt.
          if f ≲ g and g ≲ h then f ≲ h
        proof
          bigo_trans
        end
        """,
    )
    assert not result.ok, (
        "expected an error because bigo_trans is filtered out by `using`, "
        "but the file validated"
    )
    assert "bigo_trans" in (result.error_message or "")


def test_hiding_admits_unlisted_name(tmp_path: Path) -> None:
    result = _check(
        tmp_path,
        """
        import BigO hiding bigo_trans

        theorem t: all f : fn UInt -> UInt. f ≲ f
        proof
          bigo_refl
        end
        """,
    )
    assert result.ok, (
        "expected the file to validate; got: " + (result.error_message or "")
    )


def test_hiding_excludes_listed_name(tmp_path: Path) -> None:
    result = _check(
        tmp_path,
        """
        import BigO hiding bigo_trans

        theorem t: all f : fn UInt -> UInt, g : fn UInt -> UInt, h : fn UInt -> UInt.
          if f ≲ g and g ≲ h then f ≲ h
        proof
          bigo_trans
        end
        """,
    )
    assert not result.ok, (
        "expected an error because bigo_trans is hidden, "
        "but the file validated"
    )
    assert "bigo_trans" in (result.error_message or "")


def test_unfiltered_user_import_keeps_prelude_entry(tmp_path: Path) -> None:
    """An unfiltered user `import M` must NOT suppress the prelude entry.

    The prelude wins (and the user's import is dropped as a duplicate),
    matching the long-standing behaviour. Only ``using``/``hiding``
    triggers the suppression.
    """
    result = _check(
        tmp_path,
        """
        import BigO

        theorem t: all f : fn UInt -> UInt, g : fn UInt -> UInt, h : fn UInt -> UInt.
          if f ≲ g and g ≲ h then f ≲ h
        proof
          bigo_trans
        end
        """,
    )
    assert result.ok, (
        "expected the file to validate (full BigO is in scope via prelude); got: "
        + (result.error_message or "")
    )
