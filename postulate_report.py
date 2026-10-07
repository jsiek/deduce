"""Which postulates a file depends on (`deduce.py --postulates`).

Like Lean's `#print axioms`: while every module is checked, each
top-level statement records the names it depends on -- the names it
mentions (`checker_cache._collect_referenced_names`) plus the theorems
it uses implicitly through auto rules, `associative`, and `inductive`
(`flags.implicit_uses`). The report follows those dependencies from the
statements of the checked file and lists every `postulate` it reaches.

The postulates that `predicate` declarations generate internally for
their rules are not reported: like the rest of the checker, they are
part of the trusted base.
"""
from typing import Sequence

from abstract_syntax import (
    Postulate, PostulateFun, PostulateType, Statement, base_name,
)
from checker_cache import _collect_defined_names, _collect_referenced_names

# Uniquified defined name -> uniquified names the defining statement uses.
statement_deps: dict[str, set[str]] = {}
# Uniquified name -> the postulate statement that introduced it.
postulates: dict[str, Statement] = {}


def record_statement(stmt: Statement, implicit: set[str]) -> None:
  if isinstance(stmt, (Postulate, PostulateType, PostulateFun)):
    postulates[stmt.name] = stmt
  deps = _collect_referenced_names(stmt) | implicit
  for name in _collect_defined_names(stmt):
    statement_deps[name] = deps


def postulates_used(ast: Sequence[Statement]) -> list[Statement]:
  todo: list[str] = []
  for stmt in ast:
    for name in _collect_defined_names(stmt):
      todo.extend(statement_deps.get(name, ()))
  seen: set[str] = set()
  used: dict[str, Statement] = {}
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


def format_report(filename: str, ast: Sequence[Statement]) -> str:
  used = postulates_used(ast)
  if not used:
    return filename + ' depends on no postulates'
  lines = [filename + ' depends on ' + str(len(used)) + ' postulate'
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
