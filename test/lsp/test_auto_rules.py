"""Acceptance tests for ``lsp.query.auto_rules_at`` (issue #404).

The fixtures stay self-contained -- the prelude is intentionally
empty so test ordering doesn't affect the rule list returned. The
prelude path is exercised separately via the cached
``get_uniquified_modules()`` map.
"""

from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from lsp.query import (  # noqa: E402
    AutoRule,
    Position,
    auto_rules_at,
)


# Self-contained mini-arithmetic: a unary-Nat-shaped union with a
# recursive ``add`` whose two equations make non-trivial auto rules
# (lhs differs from rhs, so the rewriter terminates).
SRC = (
    "union Foo {\n"                                                   # 1
    "  fzero\n"                                                       # 2
    "  fsucc(Foo)\n"                                                  # 3
    "}\n"                                                             # 4
    "\n"                                                              # 5
    "recursive fadd(Foo, Foo) -> Foo {\n"                             # 6
    "  fadd(fzero, y) = y\n"                                          # 7
    "  fadd(fsucc(x), y) = fsucc(fadd(x, y))\n"                       # 8
    "}\n"                                                             # 9
    "\n"                                                              # 10
    "theorem fadd_zero_left: all y:Foo. fadd(fzero, y) = y\n"         # 11
    "proof\n"                                                         # 12
    "  arbitrary y:Foo\n"                                             # 13
    "  conclude fadd(fzero, y) = y by expand fadd.\n"                 # 14
    "end\n"                                                           # 15
    "auto fadd_zero_left\n"                                           # 16
    "\n"                                                              # 17
    "theorem fadd_succ:\n"                                            # 18
    "  all x:Foo, y:Foo. fadd(fsucc(x), y) = fsucc(fadd(x, y))\n"     # 19
    "proof\n"                                                         # 20
    "  arbitrary x:Foo, y:Foo\n"                                      # 21
    "  conclude fadd(fsucc(x), y) = fsucc(fadd(x, y))\n"              # 22
    "    by expand fadd.\n"                                           # 23
    "end\n"                                                           # 24
    "auto fadd_succ\n"                                                # 25
    "\n"                                                              # 26
    "theorem use_them: all z:Foo. z = z\n"                            # 27
    "proof\n"                                                         # 28
    "  arbitrary z:Foo\n"                                             # 29
    "  ?\n"                                                           # 30
    "end\n"                                                           # 31
)


def test_auto_rules_at_lists_both_in_declaration_order() -> None:
    rules = auto_rules_at("auto_test.pf", SRC, Position(line=30, column=3))
    assert [r.name for r in rules] == ["fadd_zero_left", "fadd_succ"]
    # Equation text echoes the theorem's body (parentheses around the
    # quantifier are how the printer renders ``all``).
    assert "fadd(fzero, y) = y" in rules[0].equation
    assert "fadd(fsucc(x), y) = fsucc(fadd(x, y))" in rules[1].equation


def test_auto_rules_at_attributes_module_to_user_file_stem() -> None:
    rules = auto_rules_at("my_module.pf", SRC, Position(line=30, column=3))
    assert all(r.module == "my_module" for r in rules)


def test_auto_rules_at_filters_to_those_declared_before_cursor() -> None:
    # Cursor on line 17 -- only the first auto declaration (line 16)
    # is in scope; the second (line 25) is later in the file.
    rules = auto_rules_at("test.pf", SRC, Position(line=17, column=1))
    assert [r.name for r in rules] == ["fadd_zero_left"]


def test_auto_rules_at_includes_rule_on_cursor_line() -> None:
    # Cursor at the start of the line where ``auto fadd_zero_left`` is
    # declared: still in scope (location.column <= cursor.column).
    rules = auto_rules_at("test.pf", SRC, Position(line=16, column=20))
    assert [r.name for r in rules] == ["fadd_zero_left"]


def test_auto_rules_at_returns_empty_when_no_rules_yet() -> None:
    rules = auto_rules_at("test.pf", SRC, Position(line=1, column=1))
    assert rules == ()


def test_auto_rules_at_returns_AutoRule_dataclass() -> None:
    rules = auto_rules_at("test.pf", SRC, Position(line=30, column=3))
    assert all(isinstance(r, AutoRule) for r in rules)
    assert all(isinstance(r.name, str) for r in rules)
    assert all(isinstance(r.equation, str) for r in rules)
    assert all(isinstance(r.module, str) for r in rules)


def test_auto_rules_at_handles_file_with_no_auto_decls() -> None:
    src = (
        "theorem t: true\n"
        "proof\n"
        "  .\n"
        "end\n"
    )
    rules = auto_rules_at("test.pf", src, Position(line=4, column=1))
    assert rules == ()
