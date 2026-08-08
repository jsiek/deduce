"""Coverage for AST-wide walkers used by proof-checking phases."""

from __future__ import annotations

import copy
from dataclasses import fields as dc_fields
from dataclasses import is_dataclass
from typing import Any, Iterable

import pytest

import abstract_syntax as ast
import proof_checker
from abstract_syntax.rewrite import (
    MarkException,
    count_marks,
    find_mark,
    remove_mark,
    replace_mark,
)
from test_ast_invariants import _SPECIMEN_FACTORIES, _make, _meta


def _contains_ast(value: Any) -> bool:
    if isinstance(value, ast.AST):
        return True
    if isinstance(value, (list, tuple)):
        return any(_contains_ast(item) for item in value)
    if isinstance(value, dict):
        return any(_contains_ast(item) for item in value.values())
    return False


def _reference_ast_descendants(root: Any) -> Iterable[ast.AST]:
    """Independent traversal for checking production AST walkers."""
    seen: set[int] = set()
    stack = [root]
    while stack:
        value = stack.pop()
        if isinstance(value, (str, int, bool, float)) or value is None:
            continue
        if isinstance(value, (list, tuple)):
            stack.extend(value)
            continue
        if isinstance(value, dict):
            stack.extend(value.values())
            continue
        if not isinstance(value, ast.AST):
            continue

        value_id = id(value)
        if value_id in seen:
            continue
        seen.add(value_id)
        yield value

        if is_dataclass(value):
            for field in dc_fields(value):
                if field.name == "location":
                    continue
                stack.append(getattr(value, field.name, None))


def _hash_sentinel() -> ast.Var:
    return ast.Var(_meta(), None, "__hash_sentinel__")


def _changed_child_value(value: Any) -> Any:
    sentinel = _hash_sentinel()
    if isinstance(value, ast.AST):
        return sentinel
    if isinstance(value, list):
        return value + [sentinel]
    if isinstance(value, tuple):
        return value + (sentinel,)
    if isinstance(value, dict):
        changed = dict(value)
        changed["__hash_sentinel__"] = sentinel
        return changed
    return sentinel


def test_post_phase_ast_descendant_walker_reaches_every_ast_child() -> None:
    """The invariant walker should reach AST children on every specimen."""
    roots = [_make(cls) for cls in _SPECIMEN_FACTORIES]
    expected = {id(node) for node in _reference_ast_descendants(roots)}
    actual = {
        id(node)
        for node in ast._walk_ast_descendants(roots)
        if isinstance(node, ast.AST)
    }

    assert actual == expected


def test_check_proofs_hash_walker_includes_ast_child_fields() -> None:
    """Changing any direct AST-valued child field should affect cache keys."""
    missed_fields: list[str] = []

    for cls in sorted(_SPECIMEN_FACTORIES, key=lambda c: c.__name__):
        node = _make(cls)
        if not is_dataclass(node):
            continue

        for field in dc_fields(node):
            if field.name == "location":
                continue

            value = getattr(node, field.name, None)
            if not _contains_ast(value):
                continue

            original = copy.deepcopy(node)
            changed = copy.deepcopy(node)
            setattr(
                changed,
                field.name,
                _changed_child_value(getattr(changed, field.name, None)),
            )

            if proof_checker._hash_ast(original) == proof_checker._hash_ast(changed):
                missed_fields.append(f"{cls.__name__}.{field.name}")

    assert missed_fields == []


# ---------------------------------------------------------------------------
# Mark-walker agreement (issue #1169)
# ---------------------------------------------------------------------------
#
# ``count_marks``/``find_mark``/``replace_mark`` in ``abstract_syntax.rewrite``
# must traverse the same set of node types. ``GenRecFun`` and ``Omitted`` were
# handled only by ``count_marks``, so the other two walkers fell through to
# their ``_`` arm and raised ``internal_error`` on those subterms. These build
# a formula that embeds each opaque node and assert all three walkers agree.

# GenRecFun and Omitted are the two node types the sibling walkers used to miss;
# RecFun and Hole are their already-handled siblings, included as controls.
_OPAQUE_SUBTERM_SPECIMENS = ["GenRecFun", "Omitted", "RecFun", "Hole"]


@pytest.mark.parametrize("spec_name", _OPAQUE_SUBTERM_SPECIMENS)
def test_mark_walkers_agree_on_opaque_subterms(spec_name: str) -> None:
    """find_mark/replace_mark traverse the nodes count_marks already handles."""
    factory = next(
        f for cls, f in _SPECIMEN_FACTORIES.items() if cls.__name__ == spec_name
    )
    opaque = factory()

    # No mark present: every walker must complete without an internal_error.
    no_mark = ast.And(_meta(), None, [opaque])
    assert count_marks(no_mark) == 0
    assert find_mark(no_mark) is None
    assert replace_mark(no_mark, ast.Var(_meta(), None, "r")) == no_mark

    # Mark placed after the opaque subterm forces the walkers to traverse the
    # opaque node before reaching the mark.
    subject = ast.Var(_meta(), None, "s")
    marked = ast.And(_meta(), None, [opaque, ast.Mark(_meta(), None, subject)])
    assert count_marks(marked) == 1
    with pytest.raises(MarkException) as exc:
        find_mark(marked)
    assert exc.value.subject == subject
    assert remove_mark(marked) == ast.And(_meta(), None, [opaque, subject])
