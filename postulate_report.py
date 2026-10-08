"""Which postulates a file depends on (`deduce.py --postulates`).

Like Lean's `#print axioms`: while every module is checked, each
top-level statement records the names it depends on -- the names it
mentions (`checker_cache._collect_referenced_names`) plus the theorems
it uses implicitly, in any checking phase, through auto rules,
`associative`, and `inductive` (`flags.implicit_uses`). The report
starts from every statement of the checked file, named or not (`print`,
`assert`), follows those dependencies through imports, and lists every
`postulate` it reaches, plus the file's own postulates.

The postulates that `predicate` declarations generate internally for
their rules are not reported: like the rest of the checker, they are
part of the trusted base.
"""
from typing import Sequence

from abstract_syntax import (
    Import, Postulate, PostulateFun, PostulateType, Statement, base_name,
)
from checker_cache import _collect_defined_names, _collect_referenced_names

# Uniquified defined name -> uniquified names the defining statement uses.
statement_deps: dict[str, set[str]] = {}
# Source location of a top-level statement -> the names it uses. Covers
# statements that define no name, such as `print` and `assert`.
located_deps: dict[tuple[str, int, int], set[str]] = {}
# Implicit uses recorded while a statement was declared and type-checked,
# waiting for `record_statement` once its proofs are checked.
pending_uses: dict[tuple[str, int, int], set[str]] = {}
# Uniquified name -> the postulate statement that introduced it.
postulates: dict[str, Statement] = {}


def _key(stmt: Statement) -> tuple[str, int, int]:
  loc = stmt.location
  return (getattr(loc, 'filename', ''), loc.line, loc.column)


def record_pending(stmt: Statement, implicit: set[str]) -> None:
  """Implicit uses from declaring or type-checking `stmt`."""
  if not isinstance(stmt, Import):
    pending_uses.setdefault(_key(stmt), set()).update(implicit)


def record_statement(stmt: Statement, implicit: set[str]) -> None:
  """Record what `stmt` uses, after its proofs have been checked."""
  if isinstance(stmt, Import):
    return
  if isinstance(stmt, (Postulate, PostulateType, PostulateFun)):
    postulates[stmt.name] = stmt
  deps = _collect_referenced_names(stmt) | implicit \
      | pending_uses.pop(_key(stmt), set())
  located_deps[_key(stmt)] = deps
  for name in _collect_defined_names(stmt):
    statement_deps[name] = deps


def postulates_used(ast: Sequence[Statement],
                    theorem: str | None = None) -> list[Statement]:
  """The postulates the statements of `ast` declare or use, or only
  those of the statement named `theorem` when it is given."""
  todo: list[str] = []
  used: dict[str, Statement] = {}
  for stmt in ast:
    if isinstance(stmt, Import):
      continue
    if theorem is not None and base_name(getattr(stmt, 'name', '')) != theorem:
      continue
    if isinstance(stmt, (Postulate, PostulateType, PostulateFun)):
      used[stmt.name] = stmt
    todo.extend(located_deps.get(_key(stmt), ()))
  seen: set[str] = set()
  while todo:
    name = todo.pop()
    if name in seen:
      continue
    seen.add(name)
    if name in postulates:
      used[name] = postulates[name]
    todo.extend(statement_deps.get(name, ()))
  return sorted(used.values(), key=_where)


def _where(stmt: Statement) -> tuple[str, int]:
  return (getattr(stmt.location, 'filename', ''), stmt.location.line)


def has_statement(ast: Sequence[Statement], name: str) -> bool:
  return any(base_name(getattr(s, 'name', '')) == name for s in ast)


def format_report(filename: str, ast: Sequence[Statement],
                  theorem: str | None = None) -> str:
  subject = filename if theorem is None else theorem + ' (' + filename + ')'
  used = postulates_used(ast, theorem)
  if not used:
    return subject + ' depends on no postulates'
  lines = [subject + ' depends on ' + str(len(used)) + ' postulate'
           + ('s' if len(used) != 1 else '') + ':']
  for stmt in used:
    file, line = _where(stmt)
    lines.append('  ' + _describe(stmt) + '  [' + file + ':' + str(line) + ']')
  return '\n'.join(lines)


def _describe(stmt: Statement) -> str:
  match stmt:
    case PostulateType():
      return f'postulate type {base_name(stmt.name)}'
    case PostulateFun():
      return f'{stmt.pretty_print(0).strip()}'
    case Postulate():
      return f'postulate {base_name(stmt.name)}: {stmt.what}'
  return str(stmt)
