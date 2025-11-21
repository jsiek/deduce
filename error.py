import flags

def error_header(location):
  if not location.empty:
    return '{file}:{line1}.{column1}-{line2}.{column2}: ' \
        .format(file=location.filename,
                line1=location.line, column1=location.column,
                line2=location.end_line, column2=location.end_column)
  else:
    return '' # Don't want to risk returning None ever leading to issues

def get_location_text_lines(location):
  if not location.empty:
    with open(location.filename, 'r') as f:
      lines = list(f.readlines())
      return lines[location.line-1:location.end_line]
  else:
    return ''

def error_program_text(location):
  if not location.empty:
    lines = get_location_text_lines(location)
    # last line decides where we draw the carrots (^)
    error = lines[-1]

    start_column = location.column - 1 if location.line == location.end_line else 0
    num_space = start_column
    num_carrot = location.end_column - start_column - 1

    # replace tabs with an exact number of spaces
    tab_width = 4
    for i in range(len(error)):
      if error[i] == '\t':
        if i < start_column: num_space += tab_width - 1
        else: num_carrot += tab_width - 1
        error.replace('\t', ' ' * tab_width)

    error += (' ' * num_space) + ('^' * num_carrot)
    return ''.join(lines[:-1]) + error
  else:
    return ''

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

