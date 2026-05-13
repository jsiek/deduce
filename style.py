"""ANSI color helpers for diagnostic output (issue #136).

Colors are off by default. ``deduce.py`` enables them at startup if
``sys.stdout`` is a TTY and neither the ``NO_COLOR`` env var nor the
``--no-color`` flag is set. Library and test callers
(``lsp.library.check_file``, ``test-deduce.py``) never enable colors,
so captured stdout stays plain and the
``test/should-error/*.pf.err`` and ``test/parse/*.err`` fixtures keep
matching their textual expectations.
"""

import os
import sys

enabled: bool = False

_RESET        = '\033[0m'
_BOLD         = '\033[1m'
_RED          = '\033[31m'
_GREEN        = '\033[32m'
_YELLOW       = '\033[33m'
_BLUE         = '\033[34m'
_CYAN         = '\033[36m'
_BOLD_RED     = '\033[1;31m'
_BOLD_GREEN   = '\033[1;32m'
_BOLD_YELLOW  = '\033[1;33m'
_BOLD_BLUE    = '\033[1;34m'
_BOLD_CYAN    = '\033[1;36m'
# 256-color extensions: standard 8-color doesn't include orange, and
# "dark green" needs to be distinguishable from plain green 32.
_ORANGE       = '\033[38;5;208m'
_DARK_GREEN   = '\033[38;5;28m'

def enable() -> None:
    global enabled
    enabled = True

def disable() -> None:
    global enabled
    enabled = False

def maybe_enable_for_tty() -> None:
    """Enable colors iff stdout is a TTY and NO_COLOR is unset."""
    if os.environ.get('NO_COLOR'):
        return
    if not sys.stdout.isatty():
        return
    enable()

def _wrap(code: str, s: str) -> str:
    if not enabled:
        return s
    return code + s + _RESET

def bold(s: str) -> str:         return _wrap(_BOLD, s)
def red(s: str) -> str:          return _wrap(_RED, s)
def green(s: str) -> str:        return _wrap(_GREEN, s)
def yellow(s: str) -> str:       return _wrap(_YELLOW, s)
def blue(s: str) -> str:         return _wrap(_BLUE, s)
def cyan(s: str) -> str:         return _wrap(_CYAN, s)
def orange(s: str) -> str:       return _wrap(_ORANGE, s)
def dark_green(s: str) -> str:   return _wrap(_DARK_GREEN, s)
def bold_red(s: str) -> str:     return _wrap(_BOLD_RED, s)
def bold_green(s: str) -> str:   return _wrap(_BOLD_GREEN, s)
def bold_yellow(s: str) -> str:  return _wrap(_BOLD_YELLOW, s)
def bold_blue(s: str) -> str:    return _wrap(_BOLD_BLUE, s)
def bold_cyan(s: str) -> str:    return _wrap(_BOLD_CYAN, s)
