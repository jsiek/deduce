"""Unit tests for the ghost-variable dependency predicate (issue #1114).

`imp_ghost_dependencies(term, ghost_names)` is the core of ghost-variable
noninterference: it returns the ghost names a term references. A runtime
context (runtime local initializer, runtime assignment, branch condition,
return value) whose result is nonempty would let proof-only data influence
runtime behavior and is rejected by the checker. These tests exercise the
predicate directly, in isolation from the pipeline.
"""

import pytest
from lark.tree import Meta

from abstract_syntax import And, Bool, BoolType, Or, Var
from checker_pipeline import imp_ghost_dependencies


def _meta() -> Meta:
  m = Meta()
  m.empty = False
  m.filename = 'test.pf'
  m.line = 1
  m.column = 1
  m.start_pos = 0
  m.end_line = 1
  m.end_column = 2
  m.end_pos = 1
  return m


def _var(name: str) -> Var:
  return Var(_meta(), None, name)


def _bool(value: bool) -> Bool:
  return Bool(_meta(), BoolType(_meta()), value)


def _and(*args: object) -> And:
  return And(_meta(), None, list(args))


def _or(*args: object) -> Or:
  return Or(_meta(), None, list(args))


GHOST = {'g', 'h'}

# (description, term, expected ghost dependencies)
_CASES = [
  ('bare ghost var', _var('g'), {'g'}),
  ('bare runtime var', _var('x'), set()),
  ('constant', _bool(True), set()),
  ('nested ghost under conjunction', _and(_var('x'), _var('g')), {'g'}),
  ('two ghosts referenced', _and(_var('g'), _var('h')), {'g', 'h'}),
  ('deeply nested ghost', _or(_var('x'), _and(_var('y'), _var('h'))), {'h'}),
  ('only runtime data', _and(_var('x'), _var('y')), set()),
  ('ghost mentioned twice', _or(_var('g'), _var('g')), {'g'}),
]


@pytest.mark.parametrize('desc,term,expected',
                         _CASES, ids=[c[0] for c in _CASES])
def test_ghost_dependency_predicate(desc: str, term: object,
                                    expected: set[str]) -> None:
  assert imp_ghost_dependencies(term, GHOST) == expected


def test_empty_ghost_set_never_depends() -> None:
  # With no ghost bindings in scope, nothing can depend on ghost data.
  assert imp_ghost_dependencies(_and(_var('g'), _var('h')), set()) == set()
