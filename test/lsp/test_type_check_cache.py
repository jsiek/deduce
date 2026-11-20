"""The per-statement type-check cache (#1301).

``check_deduce`` caches each statement's type check, keyed by its
structural hash and a fingerprint of the statements it depends on (see
``checker_cache.type_check_fingerprints``). A statement that only moved
reuses its cached check with the locations shifted.

What this file pins:

- a re-check of unchanged content type-checks nothing,
- editing one statement re-checks only it and what depends on it,
  including through a type alias and through every overload of a name,
- a barrier (here an ``auto``) invalidates everything,
- diagnostics of statements that moved are where a cold check puts them.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

import proof_checker  # noqa: E402
from lsp.query import Position, check, goal_at  # noqa: E402


@pytest.fixture(autouse=True)
def _fresh_cache():
    proof_checker.reset_stmt_cache()
    yield
    proof_checker.reset_stmt_cache()


def _recheck(content: str) -> tuple[int, int]:
    """Check ``content`` and return the type-check (hits, misses)."""
    proof_checker._cache_stats["hits"].clear()
    proof_checker._cache_stats["misses"].clear()
    assert check("test.pf", content) == []
    stats = proof_checker.get_cache_stats()
    return stats["hits"].get("type_check", 0), stats["misses"].get("type_check", 0)


_FILE = """\
union N { z  s(N) }
union K { z }

type M = N

fun f(x : M) { x }

fun g(x : N) { x }

theorem uses_f: f(z) = z
proof
  expand f.
end

theorem uses_g: g(z) = z
proof
  expand g.
end

assert g(s(z)) = s(z)

auto uses_g
"""
# The statements whose type check is cached: f, g, uses_f, uses_g, and
# the assert. (Edits below keep the number of statements: inserting one
# renames every statement after it, #1303.)


def test_unchanged_recheck_type_checks_nothing() -> None:
    assert _recheck(_FILE) == (0, 5)
    assert _recheck(_FILE) == (5, 0)


def test_moving_statements_type_checks_nothing() -> None:
    _recheck(_FILE)
    assert _recheck("\n\n" + _FILE) == (5, 0)


def test_moving_statements_apart_rechecks_one_carrying_anothers_location() -> None:
    _recheck(_FILE)
    # `f`'s type carries the location of the alias `M`, which now moved
    # by a different amount than `f`, so `f` is checked again.
    assert _recheck("\n\n" + _FILE.replace("\n\n", "\n\n\n")) == (4, 1)


def test_editing_one_theorem_rechecks_only_it() -> None:
    _recheck(_FILE)
    edited = _FILE.replace("theorem uses_f: f(z) = z", "theorem uses_f: z = f(z)")
    assert _recheck(edited) == (4, 1)


def test_editing_a_function_rechecks_its_users() -> None:
    _recheck(_FILE)
    # `g`, and `uses_g` and the assert that mention it.
    edited = _FILE.replace("fun g(x : N) { x }", "fun g(x : N) { s(x) }") \
        .replace("theorem uses_g: g(z) = z", "theorem uses_g: g(z) = s(z)") \
        .replace("assert g(s(z)) = s(z)", "assert g(z) = s(z)")
    assert _recheck(edited) == (2, 3)


def test_editing_a_type_alias_rechecks_users_of_functions_that_mention_it() -> None:
    _recheck(_FILE)
    # `uses_f` mentions only `f`, but `f`'s type comes from `M`, so
    # whether its `z` is N's or K's does too.
    assert _recheck(_FILE.replace("type M = N", "type M = K")) == (3, 2)


def test_every_overload_is_a_dependency() -> None:
    content = """\
union N { z  s(N) }
union B { t  ff }

fun h(x : N) { x }
fun h(x : B) { x }

theorem uses_h: h(z) = z
proof
  expand h.
end
"""
    assert _recheck(content) == (0, 3)
    # `uses_h` calls the first `h`, but editing the second one can
    # change which one it resolves to.
    edited = content.replace("fun h(x : B) { x }", "fun h(x : B) { t }")
    assert _recheck(edited) == (1, 2)


def test_a_barrier_rechecks_everything() -> None:
    _recheck(_FILE)
    assert _recheck(_FILE.replace("auto uses_g", "auto uses_f")) == (0, 5)


_SHIFTED = """\
union N { z  s(N) }

fun f(x : N) { s(x) }

assert f(z) = z

theorem holey: f(z) = s(z)
proof
  ?
end

theorem wrong: f(z) = z
proof
  expand f.
end
"""


def _diagnostics(content: str) -> list[tuple[object, str]]:
    return [(d.range, d.message) for d in check("test.pf", content)]


@pytest.mark.parametrize("prefix", ["\n\n\n", "// a comment\n", "  "])
def test_moved_statements_report_where_a_cold_check_does(prefix: str) -> None:
    _diagnostics(_SHIFTED)
    moved = prefix + _SHIFTED
    warm = _diagnostics(moved)
    proof_checker.reset_stmt_cache()
    cold = _diagnostics(moved)
    assert warm == cold
    assert len(cold) == 3


def test_goal_at_in_a_moved_theorem() -> None:
    # Without the failing statements, which stop `goal_at`'s check.
    content = _SHIFTED.split("assert")[0] + "theorem holey" \
        + _SHIFTED.split("theorem holey")[1].split("theorem wrong")[0]
    check("test.pf", content)
    moved = "\n\n" + content
    line = moved.split("\n").index("  ?") + 1
    goal = goal_at("test.pf", moved, Position(line, 3))
    assert goal is not None
    assert goal.range.start.line == line
