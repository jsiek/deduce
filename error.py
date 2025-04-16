from enum import Enum

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
  
def error_header(location):
  if not location.empty:
    return '{file}:{line1}.{column1}-{line2}.{column2}: ' \
        .format(file=location.filename,
                line1=location.line, column1=location.column,
                line2=location.end_line, column2=location.end_column)
  else:
    return '' # Don't want to risk returning None ever leading to issues
            
def error(location, msg):
  exc = Exception(error_header(location) + msg)
  exc.depth = 0
  raise exc

class IncompleteProof(Exception):
  pass

def incomplete_error(location, msg):
  exc = IncompleteProof(error_header(location) + msg)
  exc.depth = 0
  raise exc

def warning(location, msg):
  print(error_header(location) + msg)

class StaticError(Exception):
  pass

def static_error(location, msg):
  raise StaticError(error_header(location) + msg)

MAX_ERR_DEPTH = 2

# Parse Errors need to carry around some extra data
class ParseError(Exception):
  def __init__(self, loc, msg, depth=0, missing=False, last=False):
    super().__init__(msg)
    self.loc = loc
    self.depth = depth
    self.missing = missing
    self.last = last
    self.trace = []

  def extend(self, loc, msg):
    self.trace.append(ParseError(loc, msg))
    return self

  def base_message(self):
    return super().__str__()

  def __str__(self):
    base =  error_header(self.loc) + super().__str__()
    if self.trace:
      base = "\n" + base

    return  "\n".join([str(x) for x in reversed(self.trace[:MAX_ERR_DEPTH])]) + base
