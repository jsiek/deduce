from enum import Enum
import os
from pathlib import Path
from typing import TYPE_CHECKING, Callable, Optional

if TYPE_CHECKING:
  from lsp.debugger import Debugger

class VerboseLevel(Enum):
  NONE = 0
  CURR_ONLY = 1
  FULL = 2

# flag for displaying uniquified names

unique_names: bool = False

def set_unique_names(b: bool) -> None:
  global unique_names
  unique_names = b

def get_unique_names() -> bool:
  global unique_names
  return unique_names

# flag for verbose trace
#
# `verbose` carries two value shapes: the literal `False` sentinel
# (used as the off-state and as the falsy value returned by
# `get_verbose` when the level is `NONE`) and a `VerboseLevel`. Callers
# rely on both: `if get_verbose():` for truthiness, and
# `if get_verbose() == VerboseLevel.CURR_ONLY:` for level checks.

verbose: bool | VerboseLevel = False

def set_verbose(b: bool | VerboseLevel) -> None:
  global verbose
  verbose = b

def get_verbose() -> bool | VerboseLevel:
  global verbose
  if verbose == VerboseLevel.NONE:
    return False
  return verbose

def print_verbose(msg_thunk: Callable[[], str]) -> None:
  if get_verbose():
    print(msg_thunk())

# flag for expect fail

expect_fail_flag: bool = False

def expect_fail() -> bool:
  return expect_fail_flag

def set_expect_fail(b: bool) -> None:
  global expect_fail_flag
  expect_fail_flag = b

# flag for expect static_fail

expect_static_fail_flag: bool = False

def expect_static_fail() -> bool:
  return expect_static_fail_flag

def set_expect_static_fail(b: bool) -> None:
  global expect_static_fail_flag
  expect_static_fail_flag = b

# flag for import directories

import_directories: set[str] = set()

def init_import_directories() -> None:
  import_directories.add(".")
  lib_config_path = Path(os.path.expanduser("~/.config/deduce/libraries"))
  if lib_config_path.exists() and lib_config_path.is_file():
    with open(lib_config_path, 'r') as lib_config_file:
      for line in lib_config_file:
        import_directories.add(line.strip())


def get_import_directories() -> set[str]:
  global import_directories
  if (get_verbose()):
    print("import directories: ", import_directories)
  return import_directories


def add_import_directory(dir: str) -> None:
  global import_directories
  import_directories.add(dir)

# flag for recursive descent parser

recursive_descent: bool = True

def get_recursive_descent() -> bool:
  global recursive_descent
  return recursive_descent


def set_recursive_descent(b: bool) -> None:
  global recursive_descent
  recursive_descent = b

# flag for quiet mode (primarily for testing errors)

quiet_mode: bool = False

def get_quiet_mode() -> bool:
  global quiet_mode
  return quiet_mode

def set_quiet_mode(b: bool) -> None:
  global quiet_mode
  quiet_mode = b

# flag for checking to see if we need to re-deduce imported files

check_imports: bool = True

def get_check_imports() -> bool:
  global check_imports
  return check_imports

def set_check_imports(b: bool) -> None:
  global check_imports
  check_imports = b

# flag for LSP-targeted hole queries: when set to (line, column), the
# proof checker treats every `?` hole at a different location as a
# successful proof of its goal, and only raises IncompleteProof at the
# hole matching this location. None (the default) preserves the
# raise-on-first-hole behavior used by the CLI.

target_hole_location: Optional[tuple[int, int]] = None

def get_target_hole_location() -> Optional[tuple[int, int]]:
  global target_hole_location
  return target_hole_location

def set_target_hole_location(loc: Optional[tuple[int, int]]) -> None:
  global target_hole_location
  target_hole_location = loc

# active debugger session (Phase 5 / Step 21).  ``None`` in non-debug
# runs; the hook callbacks in ``proof_checker.check_proofs`` and
# ``abstract_syntax.do_function_call`` / ``Call.reduce`` short-circuit
# on ``None`` so debugger-disabled runs pay only one attribute load
# per hook site.  Set by ``lsp.library.check_file`` for the duration
# of one call (paired ``set_debugger(d)`` / ``set_debugger(None)`` in
# a try/finally).
#
# The Debugger import is type-only to avoid an import cycle: flags.py
# sits at the bottom of the import stack and lsp.debugger imports from it.

debugger: Optional["Debugger"] = None

def get_debugger() -> Optional["Debugger"]:
  global debugger
  return debugger

def set_debugger(d: Optional["Debugger"]) -> None:
  global debugger
  debugger = d

# Display-only aliases mapping a view's source-type name to the view's
# public name. Populated when a `view` declaration is processed
# (`Env.declare_view`). Consulted by `name2str` so a private source
# type like `Binary` is shown as `UInt` in printed types and goals.

view_source_aliases: dict[str, str] = {}

def register_view_source_alias(source_name: str, view_name: str) -> None:
  global view_source_aliases
  view_source_aliases[source_name] = view_name

def lookup_view_source_alias(name: str) -> Optional[str]:
  global view_source_aliases
  return view_source_aliases.get(name)

# Nested counter that suppresses view-source aliasing in `name2str`.
# Bumped by `ViewDecl.pretty_print` so the view's own declaration
# still names its underlying source type instead of self-referentially
# rendering as the view name.

_suppress_view_alias_depth: int = 0

def push_suppress_view_alias() -> None:
  global _suppress_view_alias_depth
  _suppress_view_alias_depth += 1

def pop_suppress_view_alias() -> None:
  global _suppress_view_alias_depth
  _suppress_view_alias_depth -= 1

def view_aliasing_suppressed() -> bool:
  return _suppress_view_alias_depth > 0
