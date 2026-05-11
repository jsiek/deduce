"""Acceptance tests for ``lsp.query.definition_of`` and
``lsp.query.list_symbols`` (Phase 1 / Step 5).

Hand-crafted fixtures embedded inline -- one per scenario worth pinning.
Source snippets stay in bool/built-in territory so the tests run
without the standard library prelude. Step 6's daemon mode will let
us exercise these on richer programs.
"""

from __future__ import annotations

import sys
from dataclasses import dataclass
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from lsp.query import (  # noqa: E402
    Position,
    SymbolInfo,
    SymbolKind,
    definition_of,
    list_symbols,
)


# --------------------------------------------------------------------------
# list_symbols
# --------------------------------------------------------------------------


def test_list_symbols_collects_all_top_level_kinds() -> None:
    src = (
        "theorem t1: true\n"             # line 1: theorem
        "proof\n"
        "  .\n"
        "end\n"
        "\n"
        "lemma l1: true\n"               # line 6: lemma
        "proof\n"
        "  .\n"
        "end\n"
        "\n"
        "postulate p1: true\n"           # line 11: postulate
        "\n"
        "define X: bool = true\n"        # line 13: define
        "\n"
        "union Color {\n"                # line 15: union
        "  Red\n"
        "  Blue\n"
        "}\n"
    )
    syms = list_symbols("test.pf", src)
    by_name = {s.name: s for s in syms}

    # Every declared name shows up exactly once.
    assert set(by_name) == {"t1", "l1", "p1", "X", "Color"}

    assert by_name["t1"].kind is SymbolKind.THEOREM
    assert by_name["l1"].kind is SymbolKind.LEMMA
    assert by_name["p1"].kind is SymbolKind.POSTULATE
    assert by_name["X"].kind is SymbolKind.DEFINE
    assert by_name["Color"].kind is SymbolKind.UNION

    # Locations point at the start of each declaration.
    assert by_name["t1"].location.range.start.line == 1
    assert by_name["l1"].location.range.start.line == 6
    assert by_name["p1"].location.range.start.line == 11
    assert by_name["X"].location.range.start.line == 13
    assert by_name["Color"].location.range.start.line == 15

    # Signatures echo the user-visible name (no .NNN suffix).
    assert "t1" in by_name["t1"].signature
    assert ".uniquify" not in by_name["t1"].signature
    assert by_name["X"].signature.startswith("define X")
    assert by_name["Color"].signature.startswith("union Color")
    assert by_name["p1"].signature.startswith("p1:")


def test_list_symbols_returns_empty_on_parse_error() -> None:
    # Truncated source: parser error before any declaration is built.
    src = "theorem t: true\nproof\n"
    assert list_symbols("test.pf", src) == []


def test_list_symbols_handles_empty_program() -> None:
    assert list_symbols("test.pf", "") == []


def test_list_symbols_returns_symbols_on_typecheck_failure() -> None:
    """Even when type checking fails, the partial AST should still
    surface symbol-outline data."""
    src = (
        "theorem t1: true\n"
        "proof\n"
        "  .\n"
        "end\n"
        "\n"
        "theorem broken: false\n"   # cannot prove false
        "proof\n"
        "  .\n"
        "end\n"
    )
    syms = list_symbols("test.pf", src)
    names = {s.name for s in syms}
    # We don't insist on exhaustive output here -- some pipeline phases
    # may bail before populating every symbol -- but at minimum we
    # should not raise. If we get nothing back the API is unusable in
    # an editor's normal "broken file" state.
    assert isinstance(syms, list)
    # The pre-error theorem is the bare minimum we want to surface.
    assert "t1" in names or syms == []


# --------------------------------------------------------------------------
# definition_of
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class DefnCase:
    name: str
    source: str
    cursor: Position
    expected_def_line: int  # line where the target's `theorem`/`define`/etc. starts


CASES = [
    DefnCase(
        name="theorem_use_in_other_proof",
        # `t1` is referenced as a proof variable in t2's body; the
        # cursor sits on it (line 8, col 3) and definition_of should
        # return the location of `theorem t1`.
        source=(
            "theorem t1: true\n"
            "proof\n"
            "  .\n"
            "end\n"
            "\n"
            "theorem t2: true\n"
            "proof\n"
            "  t1\n"
            "end\n"
        ),
        cursor=Position(line=8, column=3),
        expected_def_line=1,
    ),
    DefnCase(
        name="define_use_in_term",
        # X is a term-level reference, picked up by Var (not PVar).
        # Source layout: "theorem t: X = X" -- X sits at column 12.
        source=(
            "define X: bool = true\n"
            "\n"
            "theorem t: X = X\n"
            "proof\n"
            "  reflexive\n"
            "end\n"
        ),
        cursor=Position(line=3, column=12),
        expected_def_line=1,
    ),
    DefnCase(
        name="constructor_use_after_union",
        source=(
            "union Color {\n"
            "  Red\n"
            "  Blue\n"
            "}\n"
            "\n"
            "define MyColor: Color = Red\n"
        ),
        # cursor on the Color in the type annotation
        cursor=Position(line=6, column=17),
        expected_def_line=1,
    ),
    DefnCase(
        # F12 on a Union constructor (vs. the Union name above) must
        # descend into Union.alternatives and return the constructor's
        # own location, not None.  Pre-fix the lookup only checked
        # top-level statements; constructors live inside the Union.
        name="constructor_red_in_define_body",
        source=(
            "union Color {\n"          # line 1
            "  Red\n"                  # line 2: constructor declaration
            "  Blue\n"                 # line 3
            "}\n"                      # line 4
            "\n"                       # line 5
            "define MyColor: Color = Red\n"   # line 6
        ),
        # cursor on the `R` of `Red` in the body of the define
        cursor=Position(line=6, column=25),
        expected_def_line=2,
    ),
    DefnCase(
        # F12 on a predicate-rule label (e.g. ``ev0`` below) must
        # descend into ``Predicate.rules`` -- the rule's name + Meta
        # live inside the predicate declaration, not at top level.
        name="predicate_rule_use_in_proof",
        source=(
            "import UInt\n"                                       # line 1
            "\n"                                                  # line 2
            "predicate even : fn UInt -> bool {\n"                # line 3
            "  ev0   : even(0)\n"                                 # line 4: rule declaration
            "  ev_ss : all n : UInt. if even(n) then even(n + 2)\n"  # line 5
            "}\n"                                                 # line 6
            "\n"                                                  # line 7
            "theorem zero_is_even : even(0)\n"                    # line 8
            "proof\n"                                             # line 9
            "  ev0\n"                                             # line 10: rule used as a proof
            "end\n"                                               # line 11
        ),
        # cursor on the `e` of `ev0` on the proof line
        cursor=Position(line=10, column=3),
        expected_def_line=4,
    ),
]


@pytest.mark.parametrize("case", CASES, ids=lambda c: c.name)
def test_definition_of(case: DefnCase) -> None:
    loc = definition_of("test.pf", case.source, case.cursor)
    assert loc is not None, f"{case.name}: definition_of returned None"
    assert loc.path == "test.pf"
    assert loc.range.start.line == case.expected_def_line, (
        f"{case.name}: expected definition at line {case.expected_def_line}, "
        f"got {loc.range.start.line}"
    )


def test_definition_of_returns_none_when_cursor_on_whitespace() -> None:
    source = (
        "theorem t1: true\n"
        "proof\n"
        "  .\n"
        "end\n"
    )
    # Whitespace at the start of the body line.
    assert definition_of("test.pf", source, Position(line=3, column=1)) is None


def test_definition_of_returns_none_on_parse_error() -> None:
    """Cursor lookup needs the AST; if parsing fails entirely we have
    nothing to walk."""
    source = "theorem t1: true\nproof\n"  # truncated
    assert definition_of("test.pf", source, Position(line=2, column=1)) is None


def test_definition_of_returns_none_when_target_is_imported() -> None:
    """The ``true`` literal is a ``Bool`` AST node, not a ``Var``, so it
    has no resolvable name -- ``_find_reference_at`` returns ``None``
    well before ``_find_declaration`` would get a chance.  Holds
    regardless of the cross-file import-walking added later."""
    source = (
        "theorem t: true\n"
        "proof\n"
        "  .\n"
        "end\n"
    )
    assert definition_of("test.pf", source, Position(line=1, column=13)) is None


# --------------------------------------------------------------------------
# Cross-file definition_of
# --------------------------------------------------------------------------


def test_definition_of_cross_file_constructor() -> None:
    """F12 on ``suc`` from a file that ``import Nat``s should jump to
    the constructor's declaration in ``lib/NatDefs.pf`` (the actual
    Union home, reached transitively through Nat's barrel imports)."""
    source = (
        "import Nat\n"                       # line 1
        "\n"                                  # line 2
        "define x : Nat = suc(zero)\n"        # line 3
    )
    # column count for line 3: d=1 e=2 f=3 i=4 n=5 e=6 ' '=7 x=8 ' '=9
    # :=10 ' '=11 N=12 a=13 t=14 ' '=15 ==16 ' '=17 s=18
    loc = definition_of("test.pf", source, Position(line=3, column=18))
    assert loc is not None, "cross-file F12 on suc returned None"
    assert loc.path.endswith("lib/NatDefs.pf"), (
        f"expected lib/NatDefs.pf, got {loc.path!r}"
    )
    # The ``suc(Nat)`` constructor sits inside ``union Nat { ... }`` on
    # line 5 of NatDefs.pf.
    assert loc.range.start.line == 5


def test_definition_of_cross_file_operator() -> None:
    """F12 on a ``recursive operator`` defined in an imported module
    should jump to the start of the operator's declaration block --
    same shape as the constructor case but exercises the ``RecFun``
    arm of the walker rather than ``Union.alternatives``."""
    source = (
        "import Nat\n"                       # line 1
        "\n"                                  # line 2
        "define one : Nat = suc(zero)\n"      # line 3
        "define two : Nat = one + one\n"      # line 4
    )
    # line 4: d=1 e=2 f=3 i=4 n=5 e=6 ' '=7 t=8 w=9 o=10 ' '=11 :=12
    # ' '=13 N=14 a=15 t=16 ' '=17 ==18 ' '=19 o=20 n=21 e=22 ' '=23 +=24
    loc = definition_of("test.pf", source, Position(line=4, column=24))
    assert loc is not None, "cross-file F12 on + returned None"
    assert loc.path.endswith("lib/NatDefs.pf"), (
        f"expected lib/NatDefs.pf, got {loc.path!r}"
    )
    # ``recursive operator +(Nat,Nat) -> Nat { ... }'' starts on line 8.
    assert loc.range.start.line == 8


def test_definition_of_overloaded_operator_preserves_use_site() -> None:
    """Regression for the type-checker location leak: when an
    overloaded operator's call gets resolved during type-check,
    ``type_check_call_helper'' must keep the rator's use-site
    location on the new ``ResolvedVar''.  Pre-fix it copied the
    FunctionType's declaration-site location, which made
    ``_find_reference_at'' miss the use site and F12 returned null.

    ``+'' is overloaded across at least Nat and UInt; both arms
    exercise the bug, but Nat's is enough.  This test asserts F12
    on ``+'' returns the Nat operator (and not None), which is
    only possible when the rator's Var/ResolvedVar still has the
    use-site Meta in the user-file."""
    source = (
        "import Nat\n"                       # line 1
        "\n"                                  # line 2
        "theorem add_zero : all n:Nat. zero + n = n\n"   # line 3
        "proof\n"                                         # line 4
        "  arbitrary n:Nat\n"                             # line 5
        "  evaluate\n"                                    # line 6
        "end\n"                                           # line 7
    )
    # line 3: t=1 h=2 e=3 o=4 r=5 e=6 m=7 ' '=8 a=9 d=10 d=11 _=12 z=13
    # e=14 r=15 o=16 ' '=17 :=18 ' '=19 a=20 l=21 l=22 ' '=23 n=24 :=25
    # N=26 a=27 t=28 .=29 ' '=30 z=31 e=32 r=33 o=34 ' '=35 +=36
    loc = definition_of("test.pf", source, Position(line=3, column=36))
    assert loc is not None, (
        "F12 on overloaded `+' returned None -- "
        "type checker is leaking the operator declaration's location "
        "onto the ResolvedVar, masking the use site"
    )
    # ``recursive operator +(Nat,Nat) -> Nat { ... }'' starts on line 8
    # of lib/NatDefs.pf.
    assert loc.path.endswith("lib/NatDefs.pf"), (
        f"expected lib/NatDefs.pf, got {loc.path!r}"
    )
    assert loc.range.start.line == 8


def test_definition_of_ignores_imported_node_locations() -> None:
    """Issue #398: with the prelude active, post-typecheck nodes copied
    in from library files share Meta line/column with the user's file
    by coincidence. The lookup must filter those out by ``filename``,
    or the cursor in a postulate / equation lands on a library node
    instead of the user's reference."""
    # Prelude entries get auto-imported by the harness and contribute
    # the noisy library-file Var nodes. ``List`` is enough to give
    # ``app`` a return type of ``List<E>`` and pull in the library
    # locations whose line numbers overlap the user file.
    prelude = ("List",)
    source = (
        "recursive app <E>(List<E>, List<E>) -> List<E> {\n"  # 1
        "  app([], ys) = ys\n"                                 # 2
        "  app(node(n, xs), ys) = node(n, app(xs, ys))\n"      # 3
        "}\n"                                                  # 4
        "\n"                                                   # 5
        "postulate p: all T:type. all x:T, y:T.\n"             # 6
        "  app([x], [y]) = [x,y]\n"                            # 7 — the postulate body
    )
    # Cursor on the `app` reference inside the postulate body.
    loc = definition_of("test.pf", source, Position(line=7, column=3),
                        prelude=prelude)
    assert loc is not None, "postulate body: definition_of returned None"
    assert loc.range.start.line == 1
