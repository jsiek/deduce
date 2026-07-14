import contextlib
from dataclasses import dataclass
from typing import Iterator, List, NoReturn, Optional, TYPE_CHECKING

from lark.tree import Meta

import style

# Type-only imports to avoid an import cycle: abstract_syntax.core
# imports `internal_error` from this module, so error.py sits below
# abstract_syntax in the import stack. The IncompleteProof refine
# pipeline still wants the structured `formula` / `env` payloads
# typed precisely, so we forward-reference them under TYPE_CHECKING.
if TYPE_CHECKING:
  from abstract_syntax import Env, Term

class Diagnostic(Exception):
  """Base class for exceptions that represent user-facing diagnostics.
  ``ErrorSink`` and the per-statement / sibling-recovery sites catch
  ``Diagnostic`` so every subclass is collected uniformly. Internal
  errors and control-flow signals (``InternalError``, ``MatchFailed``)
  intentionally do not inherit from this -- they should not be caught
  by the sink machinery."""

  # Post-construction-stashed structured fields: every helper that
  # raises a ``Diagnostic`` (``user_error``, ``incomplete_error``,
  # ``static_error``, ``match_failed``, ``add_diagnostic``,
  # ``add_incomplete``) attaches ``location`` and ``message_body`` so
  # library/LSP/MCP callers can reconstruct ``Diagnostic`` objects
  # without regex-parsing ``str(exc)``. Declared at the base so every
  # subclass shares the same shape — mypy then accepts the post-hoc
  # ``exc.location = ...`` / ``exc.message_body = ...`` assignments
  # without ``attr-defined`` errors.
  location: Meta
  message_body: str

class UserError(Diagnostic):
  # Set by ``user_error`` / ``add_diagnostic`` to 0; currently no
  # caller reads it, but keeping the slot reserves the field so an
  # incidental ``exc.depth`` access keeps type-checking. Dead-code
  # removal is its own cleanup.
  depth: int

class InternalError(Exception):
  pass

class IncompleteProof(Diagnostic):
  depth: int
  # Set by ``incomplete_error`` / ``add_incomplete``: optional
  # structured fields for the LSP/MCP refine pipeline (the goal AST
  # and the type-checking env at the hole). ``None`` outside of
  # opted-in flows.
  formula: Optional['Term']
  env: Optional['Env']

def get_location_text_lines(location: Meta) -> List[str]:
  if not location.empty:
    try:
      with open(getattr(location, 'filename'), 'r') as f:
        lines = list(f.readlines())
        return lines[location.line-1:location.end_line]
    except OSError:
      # Library/LSP/MCP callers pass in-memory content with a path
      # that may not exist on disk. Returning an empty source excerpt
      # keeps str(ParseError) from crashing -- the location header
      # still carries the file:line:col coordinates.
      return []
  else:
    return []

def error_header(location: Meta) -> str:
  if not location.empty:
    header = '{file}:{line1}.{column1}-{line2}.{column2}:' \
        .format(file=getattr(location, 'filename'),
                line1=location.line, column1=location.column,
                line2=location.end_line, column2=location.end_column)
    return style.blue(header) + ' '
  else:
    return '' # Don't want to risk returning None ever leading to issues

def error_program_text(location: Meta) -> str:
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
    error += (' ' * num_space) + style.bold_red('^' * num_carrot)
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
  def __init__(self) -> None:
    self.errors: list[Diagnostic] = []

  def add(self, exc: 'Diagnostic') -> None:
    self.errors.append(exc)

  def __bool__(self) -> bool:
    return bool(self.errors)

  def __len__(self) -> int:
    return len(self.errors)

def user_error(location: Meta, msg: str) -> NoReturn:
  exc = UserError(error_header(location) + msg)
  exc.depth = 0
  # Attach structured fields so library/LSP/MCP callers can build
  # Diagnostic objects without regex-parsing str(exc). The CLI ignores
  # these attributes; existing print(str(exc)) output is unchanged.
  exc.location = location
  exc.message_body = msg
  raise exc

def internal_error(location: Meta, msg: str) -> NoReturn:
  raise InternalError(error_header(location) + msg)

def incomplete_error(location: Meta, msg: str, *,
                     formula: Optional['Term'] = None,
                     env: Optional['Env'] = None) -> NoReturn:
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

@dataclass
class WarningRecord:
  """A single ``warning()`` emission captured by an active warning sink.

  Mirrors the ``(location, message_body)`` shape ``Diagnostic`` sub-
  classes attach post-construction, so ``lsp.query.check`` can render
  a warning entry with the same helpers it uses for errors.
  """

  location: Meta
  message_body: str


# When set, ``warning()`` records into this list *instead of* printing.
# ``lsp.library.check_file(collect_errors=True)`` installs a sink for
# the duration of one run so ``lsp.query.check`` can surface warnings
# as ``Severity.WARNING`` diagnostics (issue #991). The CLI leaves this
# ``None``, so ``deduce.py`` keeps printing warnings verbatim.
_active_warning_sink: Optional[List[WarningRecord]] = None


def set_active_warning_sink(
    sink: Optional[List[WarningRecord]],
) -> Optional[List[WarningRecord]]:
  """Install ``sink`` as the active warning sink and return the
  previously installed sink (so callers can restore it on exit
  the way ``check_file`` does in its try/finally)."""
  global _active_warning_sink
  prev = _active_warning_sink
  _active_warning_sink = sink
  return prev


def get_active_warning_sink() -> Optional[List[WarningRecord]]:
  return _active_warning_sink


def warning(location: Meta, msg: str) -> None:
  sink = _active_warning_sink
  if sink is not None:
    # A caller (``lsp.library.check_file(collect_errors=True)``)
    # asked to capture warnings instead of printing them. Skipping
    # the print also keeps stdout clean for the stdio-based LSP
    # server, where any extra bytes on stdout corrupt the JSON-RPC
    # framing.
    sink.append(WarningRecord(location=location, message_body=msg))
    return
  print(error_header(location) + msg)

def wrap_user_error(inner: BaseException, context: str) -> UserError:
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
_active_sink: Optional[ErrorSink] = None


def set_active_sink(sink: Optional[ErrorSink]) -> Optional[ErrorSink]:
  """Install ``sink`` as the active error sink and return the
  previously installed sink (so callers can restore it on exit
  exactly the way ``check_deduce`` does in its try/finally)."""
  global _active_sink
  prev = _active_sink
  _active_sink = sink
  return prev

def get_active_sink() -> Optional[ErrorSink]:
  return _active_sink

# Depth counter for nested speculative_probe blocks. While > 0,
# ``add_diagnostic`` raises instead of silently recording — so the
# surrounding ``except UserError`` at a backtracking site actually
# fires. ``add_incomplete`` is intentionally unaffected so holes
# from sibling subproofs (e.g. ``?, ?`` in a PTuple) still each
# become their own diagnostic.
_speculative_depth = 0


@contextlib.contextmanager
def speculative_probe() -> Iterator[None]:
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

def add_diagnostic(location: Meta, msg: str) -> None:
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

def add_incomplete(location: Meta, msg: str,
                   formula: Optional['Term'] = None,
                   env: Optional['Env'] = None) -> None:
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

def static_error(location: Meta, msg: str) -> NoReturn:
  exc = StaticError(error_header(location) + msg)
  exc.location = location
  exc.message_body = msg
  raise exc

class MatchFailed(Exception):
  # Stashed the same way as ``Diagnostic`` subclasses (see base-class
  # comment) so the LSP/MCP query API can read e.location /
  # e.message_body uniformly across exception types.
  location: Meta
  message_body: str

def match_failed(location: Meta, msg: str) -> NoReturn:
  exc = MatchFailed(error_header(location) + msg)
  exc.location = location
  exc.message_body = msg
  raise exc

MAX_ERR_DEPTH = 2

# Parse Errors need to carry around some extra data
class ParseError(Exception):
  def __init__(self, loc: Meta, msg: str, depth: int = 0,
               missing: bool = False, last: bool = False) -> None:
    super().__init__(msg)
    self.loc = loc
    self.depth = depth
    self.missing = missing
    self.last = last
    self.trace: List['ParseError'] = []
    # Aliases that match the attribute names attached to Exception by
    # error()/incomplete_error()/static_error()/match_failed(), so the
    # query API can read e.location / e.message_body uniformly across
    # exception types.
    self.location = loc
    self.message_body = msg

  def extend(self, loc: Meta, msg: str) -> 'ParseError':
    self.trace.append(ParseError(loc, msg))
    return self

  def base_message(self) -> str:
    return super().__str__()

  def error_base(self) -> str:
    base =  error_header(self.loc) + super().__str__()
    if self.trace:
      base = "\n" + base
    return base
  # return "\n".join([x.error_str() for x in reversed(self.trace[:MAX_ERR_DEPTH])]) + base

  def __str__(self) -> str:
    # base =  error_header(self.loc) + super().__str__()
    # if self.trace:
    #   base = "\n" + base

    return  "\n".join([x.error_base() for x in reversed(self.trace[:MAX_ERR_DEPTH])]) + \
      '\n\n' + error_program_text(self.loc) + '\n' + \
      self.error_base()

    # return  self.error_str() #+ '\n\n' + error_program_text(self.loc)


def lark_unexpected_chars_to_parse_error(exc: object, filename: str) -> 'ParseError':
  """Turn a lark ``UnexpectedCharacters`` into a Deduce ``ParseError``.

  The default lark message ("No terminal matches '\\' in the current
  parser context...") drops the reader into the lark internals and
  lists raw terminal names. For characters Deduce wants to call out
  specifically -- ``\\`` is the obvious one, since Haskell-style
  lambdas are reflex for incoming FP students -- we replace the
  message with a hint that points at the supported syntax.
  """
  char = getattr(exc, 'char', '?')
  line = getattr(exc, 'line', 1)
  column = getattr(exc, 'column', 1)
  pos_in_stream = getattr(exc, 'pos_in_stream', 0)
  meta = Meta()  # type: ignore[no-untyped-call,unused-ignore]
  meta.empty = False
  setattr(meta, 'filename', filename)
  meta.line = line
  meta.column = column
  meta.start_pos = pos_in_stream
  meta.end_line = line
  meta.end_column = column + 1
  meta.end_pos = pos_in_stream + 1
  if char == '\\':
    msg = ("'\\' is not a valid character in Deduce. "
           "Anonymous functions are written\n"
           "\tfun x { ... }\n"
           "or, equivalently,\n"
           "\tλx{ ... }\n"
           "e.g. `filter(xs, fun x { x % 2 = 0 })`.")
  else:
    msg = (f"unexpected character {char!r} in input "
           "(no terminal matches it in the current parser context)")
  return ParseError(meta, msg)
