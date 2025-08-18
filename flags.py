from enum import Enum
import os
from pathlib import Path

class VerboseLevel(Enum):
  NONE = 0
  CURR_ONLY = 1
  FULL = 2

# flag for displaying uniquified names

unique_names = False

def set_unique_names(b):
  global unique_names
  unique_names = b

def get_unique_names():
  global unique_names
  return unique_names

# flag for verbose trace

verbose = False

def set_verbose(b):
  global verbose
  verbose = b

def get_verbose():
  global verbose
  if verbose == VerboseLevel.NONE:
    return False
  return verbose

def print_verbose(msg_thunk):
  if get_verbose():
    print(msg_thunk())

# flag for expect fail

expect_fail_flag = False

def expect_fail():
  return expect_fail_flag

def set_expect_fail(b):
  global expect_fail_flag
  expect_fail_flag = b

# flag for expect static_fail

expect_static_fail_flag = False

def expect_static_fail():
  return expect_static_fail_flag

def set_expect_static_fail(b):
  global expect_static_fail_flag
  expect_static_fail_flag = b

# flag for import directories

import_directories = set()

def init_import_directories():
  import_directories.add(".")
  lib_config_path = Path(os.path.expanduser("~/.config/deduce/libraries"))
  if lib_config_path.exists() and lib_config_path.is_file():
    with open(lib_config_path, 'r') as lib_config_file:
      for line in lib_config_file:
        import_directories.add(line.strip())


def get_import_directories():
  global import_directories
  if (get_verbose()):
    print("import directories: ", import_directories)
  return import_directories


def add_import_directory(dir):
  global import_directories
  import_directories.add(dir)

# flag for recursive descent parser

recursive_descent = True

def get_recursive_descent():
  global recursive_descent
  return recursive_descent


def set_recursive_descent(b):
  global recursive_descent
  recursive_descent = b

# flag for quiet mode (primarily for testing errors)

quiet_mode = False

def get_quiet_mode():
  global quiet_mode
  return quiet_mode

def set_quiet_mode(b):
  global quiet_mode
  quiet_mode = b

# flag for checking to see if we need to re-deduce imported files

check_imports = True

def get_check_imports():
  global check_imports
  return check_imports

def set_check_imports(b):
  global check_imports
  check_imports = b
  
