"""Tests for formula trees (issue #1215): ``lsp.query.TermTree`` and how
it is built from the checked AST."""

from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from abstract_syntax import (  # noqa: E402
    AST, Call, Theorem, VarRef, is_infix_operator, is_prefix_operator,
    operator_display_name,
)
from abstract_syntax.ops import _walk_ast_descendants  # noqa: E402
from lsp.library import check_file  # noqa: E402
from lsp.query import TermTree, _term_tree, goal_at, Position  # noqa: E402


def _nodes(tree: TermTree, path: tuple[int, ...] = ()):
    """Every node of ``tree`` with its path."""
    yield path, tree
    children = [p for p in tree.parts if isinstance(p, TermTree)]
    for i, child in enumerate(children):
        yield from _nodes(child, path + (i,))


def _at(tree: TermTree, path: list[int]) -> TermTree:
    for i in path:
        tree = [p for p in tree.parts if isinstance(p, TermTree)][i]
    return tree


def _kind(node: AST) -> str:
    return "Var" if isinstance(node, VarRef) else type(node).__name__


def test_every_node_is_a_subterm_with_its_printed_text():
    """Round trip over lib goals: each node's text is what ``str()``
    prints for a subterm of that kind (or, for an operator, its displayed
    name), and the root's text is the whole statement."""
    checked = 0
    for name in ("List", "Nat", "Set"):
        path = REPO_ROOT / "lib" / f"{name}.pf"
        result = check_file(str(path), prelude=())
        assert result.ok, result.error_message
        for stmt in result.ast:
            if not (isinstance(stmt, Theorem) and stmt.location.filename == str(path)):
                continue
            tree = _term_tree(stmt.what)
            assert str(tree) == str(stmt.what)
            subterms = [
                d for d in _walk_ast_descendants(stmt.what) if isinstance(d, AST)
            ]
            printed = {(_kind(d), str(d)) for d in subterms} | {
                ("Var", operator_display_name(d.rator))
                for d in subterms
                if isinstance(d, Call)
                and (is_infix_operator(d.rator) or is_prefix_operator(d.rator))
            }
            for node_path, node in _nodes(tree):
                assert (node.kind, str(node)) in printed, (stmt.name, node_path)
            checked += 1
    assert checked > 100


def test_paths_address_subterms():
    source = (
        "union N { z  s(N) }\n"
        "recursive add(N, N) -> N {\n"
        "  add(z, y) = y\n"
        "  add(s(x), y) = s(add(x, y))\n"
        "}\n"
        "theorem t: all a:N, b:N. add(a, s(b)) = s(add(a, b))\n"
        "proof\n"
        "  arbitrary a:N, b:N\n"
        "  ?\n"
        "end\n"
    )
    goal = goal_at("paths.pf", source, Position(9, 3))
    assert goal is not None
    tree = goal.formula
    assert str(tree) == "add(a, s(b)) = s(add(a, b))"
    # Children in printed order: an infix operator sits between its
    # arguments, a callee before them.
    assert [p if isinstance(p, str) else p.kind for p in tree.parts] == [
        "Call", " ", "Var", " ", "Call",
    ]
    # Paths count only the tree-valued parts.
    assert str(_at(tree, [0])) == "add(a, s(b))"
    assert _at(tree, [1]) == TermTree("Var", ("=",))
    assert _at(tree, [0, 0]) == TermTree("Var", ("add",))
    assert str(_at(tree, [0, 2])) == "s(b)"
    assert _at(tree, [0, 2, 1]) == TermTree("Var", ("b",))
    assert str(_at(tree, [2, 1, 1])) == "a"


def test_sugar_stays_text():
    """A child the printer does not show verbatim (here `false` in
    `not P`, which is `if P then false`) stays in its parent's text."""
    source = (
        "theorem t: all P:bool. not (P and not P)\n"
        "proof\n"
        "  arbitrary P:bool\n"
        "  ?\n"
        "end\n"
    )
    goal = goal_at("sugar.pf", source, Position(4, 3))
    assert goal is not None
    assert str(goal.formula) == "not (P and not P)"
    assert goal.formula.kind == "IfThen"
    [conj] = [p for p in goal.formula.parts if isinstance(p, TermTree)]
    assert (conj.kind, str(conj)) == ("And", "(P and not P)")


def _text_outside(tree: TermTree, kind: str):
    """The text parts of ``tree`` not inside a node of ``kind``."""
    if tree.kind == kind:
        return
    for p in tree.parts:
        if isinstance(p, str):
            yield p
        else:
            yield from _text_outside(p, kind)


def test_explicit_type_arguments_are_nodes():
    """`@m_empty<T>()` calls a `TermInst`: it must be a node, not text, so
    clients can drop the type arguments and address the callee."""
    path = REPO_ROOT / "lib" / "MultiSet.pf"
    result = check_file(str(path), prelude=())
    assert result.ok, result.error_message
    stmts = [
        s for s in result.ast
        if isinstance(s, Theorem) and s.location.filename == str(path)
    ]
    assert any("@" in str(s.what) for s in stmts)
    # A callee with inferred type arguments (`length(xs)`) is still text,
    # so arguments keep the same paths as in a non-generic call.
    assert not any(
        n.kind == "TermInst"
        for s in check_file(str(REPO_ROOT / "lib" / "List.pf"), prelude=()).ast
        if isinstance(s, Theorem) and s.name.startswith("length_append")
        for _, n in _nodes(_term_tree(s.what))
    )
    for stmt in stmts:
        assert not any(
            "@" in t for t in _text_outside(_term_tree(stmt.what), "TermInst")
        ), stmt.name
