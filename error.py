import contextlib

import flags

class Diagnostic(Exception):
  """Base class for exceptions that represent user-facing diagnostics.
  ``ErrorSink`` and the per-statement / sibling-recovery sites catch
  ``Diagnostic`` so every subclass is collected uniformly. Internal
  errors and control-flow signals (``InternalError``, ``MatchFailed``)
  intentionally do not inherit from this -- they should not be caught
  by the sink machinery."""
  pass

class UserError(Diagnostic):
  pass

class InternalError(Exception):
  pass

class IncompleteProof(Diagnostic):
  pass

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

class ErrorSink:
  """Collects :class:`Diagnostic` exceptions during a checker run
  instead of letting them propagate. When ``proof_checker.check_deduce``
  is given a sink, each top-level statement runs in a try/except per
  phase; ``Diagnostic`` subclasses (``UserError``, ``IncompleteProof``,
  ``StaticError``) are appended to ``errors`` and the next statement
  runs. ``InternalError``, ``MatchFailed``, and unexpected exceptions
  intentionally bypass the sink so bugs and control-flow signals are
  not silently swallowed. Without a sink (the default), ``check_deduce``
  keeps its raise-on-first-error behavior — preserving CLI semantics
  and the ``goal_at`` / MCP query paths that depend on it.
  """
  def __init__(self):
    self.errors: list[Diagnostic] = []

  def add(self, exc: 'Diagnostic'):
    self.errors.append(exc)

  def __bool__(self):
    return bool(self.errors)

  def __len__(self):
    return len(self.errors)

def user_error(location, msg):
  exc = UserError(error_header(location) + msg)
  exc.depth = 0
  # Attach structured fields so library/LSP/MCP callers can build
  # Diagnostic objects without regex-parsing str(exc). The CLI ignores
  # these attributes; existing print(str(exc)) output is unchanged.
  exc.location = location
  exc.message_body = msg
  raise exc

def internal_error(location, msg):
  raise InternalError(error_header(location) + msg)

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

def wrap_user_error(inner, context):
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
  new_exc = UserError(str(inner) + context)
  inner_loc = getattr(inner, 'location', None)
  if inner_loc is not None:
    new_exc.location = inner_loc
  inner_body = getattr(inner, 'message_body', None)
  if inner_body is None:
    inner_body = str(inner)
  new_exc.message_body = inner_body + context
  return new_exc

# ---------------------------------------------------------------------------
# Active sink (Step 11, depth-2)
# ---------------------------------------------------------------------------
#
# ``check_deduce`` installs an :class:`ErrorSink` here for the
# duration of one run when its caller asked for multi-error
# collection. ``add_diagnostic`` / ``add_incomplete``
# consult this slot and, when set, append the just-built exception to
# the sink before raising — so every diagnostic is captured at its
# own raise site rather than waiting for a top-level catch. None
# outside of an opted-in run, so CLI / goal_at / MCP behaviour is
# untouched.
_active_sink = None


def set_active_sink(sink):
  """Install ``sink`` as the active error sink and return the
  previously installed sink (so callers can restore it on exit
  exactly the way ``check_deduce`` does in its try/finally)."""
  global _active_sink
  prev = _active_sink
  _active_sink = sink
  return prev

def get_active_sink():
  return _active_sink

# Depth counter for nested speculative_probe blocks. While > 0,
# ``add_diagnostic`` raises instead of silently recording — so the
# surrounding ``except UserError`` at a backtracking site actually
# fires. ``add_incomplete`` is intentionally unaffected so holes
# from sibling subproofs (e.g. ``?, ?`` in a PTuple) still each
# become their own diagnostic.
_speculative_depth = 0


@contextlib.contextmanager
def speculative_probe():
  """Make a speculative proof-checker probe well-behaved when an
  error sink is active.

  Use at sites that try one interpretation and have a recovery path
  on failure (iff-application picking a direction, PTuple's
  goal-directed-then-synthesis fallback, etc.). Inside the block:

  * ``add_diagnostic`` raises (instead of silently recording into the
    sink), so the surrounding ``except UserError`` fires and the
    parent rule's recovery path runs.
  * ``add_incomplete`` continues to record holes — multiple ``?``
    siblings still each become their own diagnostic.

  On exit, if a ``UserError`` escaped the block, any sink entries
  that were added inside are discarded (apart from
  ``IncompleteProof`` holes, which represent real user-visible
  ``?``s that the recovery path can't conjure away). Without this,
  failed probes used to surface as false-positive errors in
  ``check_file(..., collect_errors=True)`` while ``deduce.py``
  validated the same file cleanly (issue #400)."""
  global _speculative_depth
  sink = _active_sink
  saved_len = len(sink.errors) if sink is not None else 0
  _speculative_depth += 1
  try:
    yield
  except UserError:
    if sink is not None:
      kept = [e for e in sink.errors[saved_len:]
              if isinstance(e, IncompleteProof)]
      del sink.errors[saved_len:]
      sink.errors.extend(kept)
    raise
  finally:
    _speculative_depth -= 1

def add_diagnostic(location, msg):
  """Record a user-visible diagnostic in the active sink and *return
  normally*, unlike :func:`user_error` which raises. Use at sites whose
  enclosing function can tolerate falling through.

  Without an active sink and outside any probing region, falls
  back to :func:`error` -- so a CLI run still raises and the
  existing ``goal_at`` / MCP paths see the same shape they always
  have.

  Inside a :func:`speculative_probe` block (depth > 0), this also
  raises -- the parent rule has a recovery path waiting on the
  exception, and silently recording would leak the failed probe's
  error into the user-visible list (issue #400).
  """
  global _active_sink
  if _active_sink is None or _speculative_depth > 0:
    user_error(location, msg)
  exc = UserError(error_header(location) + msg)
  exc.depth = 0
  exc.location = location
  exc.message_body = msg
  _active_sink.add(exc)

def add_incomplete(location, msg, formula=None, env=None):
  """Record a user-visible diagnostic in the active sink and *return
  normally*, unlike :func:`user_error` which raises. Use at sites whose
  enclosing function can tolerate falling through.

  Without an active sink and outside any probing region, falls
  back to :func:`incompleteerror` -- so a CLI run still raises and the
  existing ``goal_at`` / MCP paths see the same shape they always
  have.
  """
  global _active_sink
  if _active_sink is None:
    incomplete_error(location, msg, formula=formula, env=env)
  exc = IncompleteProof(error_header(location) + msg)
  exc.depth = 0
  exc.location = location
  exc.message_body = msg
  # Optional structured fields for the LSP/MCP refine pipeline:
  # the goal AST and the type-checking env at the hole. The CLI
  # ignores these; print(str(exc)) output is unchanged.
  exc.formula = formula
  exc.env = env
  _active_sink.add(exc)

  
class StaticError(Diagnostic):
  pass

def static_error(location, msg):
  exc = StaticError(error_header(location) + msg)
  exc.location = location
  exc.message_body = msg
  raise exc

class MatchFailed(Exception):
  pass

def match_failed(location, msg):
  exc = MatchFailed(error_header(location) + msg)
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

