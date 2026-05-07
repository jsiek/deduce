import flags

def get_location_text_lines(location):
  if not location.empty:
    try:
      with open(location.filename, 'r') as f:
        lines = list(f.readlines())
        return lines[location.line-1:location.end_line]
    except OSError:
      # Library/LSP/MCP callers pass in-memory content with a path
      # that may not exist on disk. Returning an empty source excerpt
      # keeps str(ParseError) from crashing -- the location header
      # still carries the file:line:col coordinates.
      return ''
  else:
    return ''

def error_header(location):
  if not location.empty:
    return '{file}:{line1}.{column1}-{line2}.{column2}: ' \
        .format(file=location.filename,
                line1=location.line, column1=location.column,
                line2=location.end_line, column2=location.end_column)
  else:
    return '' # Don't want to risk returning None ever leading to issues

def error_program_text(location):
  if not location.empty:
    lines = get_location_text_lines(location)
    if not lines:
      # Source file isn't on disk (in-memory content from library/LSP
      # callers); skip the source excerpt and carrot rendering.
      return ''
    # last line decides where we draw the carrots (^)
    error = lines[-1]

    start_column = location.column - 1 if location.line == location.end_line else 0
    num_space = start_column
    num_carrot = location.end_column - start_column - 1

    # replace tabs with an exact number of spaces
    tab_width = 4
    for i in range(len(error)):
      if error[i] == '\t':
        if i < start_column:
          num_space += tab_width - 1
        else:
          num_carrot += tab_width - 1
          # num_space += tab_width
          # num_carrot -= 1
          
    error = error.replace('\t', ' ' * tab_width)
    lines = list(map(lambda s: s.replace('\t', ' ' * tab_width), lines))

    if error[-1] != '\n': error += '\n'
    error += (' ' * num_space) + ('^' * num_carrot)
    return ''.join(lines[:-1]) + error
  else:
    return ''

def error(location, msg):
  exc = Exception(error_header(location) + msg)
  # exc = Exception(error_header(location) + '\n\n' + error_program_text(location) + '\n\n' + msg)
  exc.depth = 0
  # Attach structured fields so library/LSP/MCP callers can build
  # Diagnostic objects without regex-parsing str(exc). The CLI ignores
  # these attributes; existing print(str(exc)) output is unchanged.
  exc.location = location
  exc.message_body = msg
  raise exc

class IncompleteProof(Exception):
  pass

def incomplete_error(location, msg, *, formula=None, env=None):
  exc = IncompleteProof(error_header(location) + msg)
  exc.depth = 0
  exc.location = location
  exc.message_body = msg
  # Optional structured fields for the LSP/MCP refine pipeline:
  # the goal AST and the type-checking env at the hole. The CLI
  # ignores these; print(str(exc)) output is unchanged.
  exc.formula = formula
  exc.env = env
  raise exc

def warning(location, msg):
  print(error_header(location) + msg)

def wrap_error(inner, context):
  """Return a new Exception that re-raises ``inner`` with ``context``
  appended to the message, preserving the structured ``location`` and
  ``message_body`` attributes set by error()/incomplete_error()/
  static_error()/match_failed().

  Callers that catch a structured exception and want to add trailing
  context should use this helper instead of ``raise Exception(str(e)
  + context)`` -- the bare-Exception form drops the location, which
  the LSP/MCP query API needs for Diagnostic.range.

  ``str()`` of the returned exception equals ``str(inner) + context``,
  so user-visible error text (and the should-error/*.pf.err fixtures)
  is unchanged.
  """
  new_exc = Exception(str(inner) + context)
  inner_loc = getattr(inner, 'location', None)
  if inner_loc is not None:
    new_exc.location = inner_loc
  inner_body = getattr(inner, 'message_body', None)
  if inner_body is None:
    inner_body = str(inner)
  new_exc.message_body = inner_body + context
  return new_exc

class StaticError(Exception):
  pass

def static_error(location, msg):
  exc = StaticError(error_header(location) + msg)
  # raise StaticError(error_header(location) + '\n\n' + error_program_text(location) + '\n\n' + msg)
  exc.location = location
  exc.message_body = msg
  raise exc

class MatchFailed(Exception):
  pass

def match_failed(location, msg):
  exc = MatchFailed(error_header(location) + msg)
  # raise MatchFailed(error_header(location) + '\n\n' + error_program_text(location) + '\n\n' + msg)
  exc.location = location
  exc.message_body = msg
  raise exc

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
    # Aliases that match the attribute names attached to Exception by
    # error()/incomplete_error()/static_error()/match_failed(), so the
    # query API can read e.location / e.message_body uniformly across
    # exception types.
    self.location = loc
    self.message_body = msg

  def extend(self, loc, msg):
    self.trace.append(ParseError(loc, msg))
    return self

  def base_message(self):
    return super().__str__()

  def error_base(self):
    base =  error_header(self.loc) + super().__str__()
    if self.trace:
      base = "\n" + base
    return base
  # return "\n".join([x.error_str() for x in reversed(self.trace[:MAX_ERR_DEPTH])]) + base

  def __str__(self):
    # base =  error_header(self.loc) + super().__str__()
    # if self.trace:
    #   base = "\n" + base

    return  "\n".join([x.error_base() for x in reversed(self.trace[:MAX_ERR_DEPTH])]) + \
      '\n\n' + error_program_text(self.loc) + '\n' + \
      self.error_base()

    # return  self.error_str() #+ '\n\n' + error_program_text(self.loc)

