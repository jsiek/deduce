import flags

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

class MatchFailed(Exception):
  pass

def match_failed(location, msg):
  raise MatchFailed(error_header(location) + msg)

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
