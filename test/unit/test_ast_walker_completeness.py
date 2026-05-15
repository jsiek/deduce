"""Coverage for AST-wide walkers used by proof-checking phases."""

from __future__ import annotations

import copy
from dataclasses import fields as dc_fields
from dataclasses import is_dataclass
from typing import Any, Iterable

import abstract_syntax as ast
import proof_checker
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
