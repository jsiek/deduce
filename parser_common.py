# Parser state and helpers shared by both front ends: the LALR parser
# (``parser.py``) and the recursive-descent parser
# (``rec_desc_parser.py``). Both track the current source filename and
# the Deduce install directory the same way, build their lark grammar
# object from the same ``Deduce.lark`` file, and gate the experimental
# imperative syntax behind the same flag. This module is the single
# home for that shared state so the two parsers cannot drift apart.

from lark import Lark
from lark.tree import Meta

from error import ParseError

filename: str = '???'

def set_filename(fname: str) -> None:
    global filename
    filename = fname

def get_filename() -> str:
    return filename


deduce_directory: str = '???'

def set_deduce_directory(dir: str) -> None:
    global deduce_directory
    deduce_directory = dir

def get_deduce_directory() -> str:
    return deduce_directory


def make_lark_parser(lalr: bool) -> Lark:
    """Build the lark grammar object from ``Deduce.lark``.

    ``parser.py`` parses with the LALR algorithm; ``rec_desc_parser.py``
    only uses the resulting object for its non-contextual ``.lex()``, so
    it keeps lark's default parser.
    """
    lark_file = get_deduce_directory() + "/Deduce.lark"
    grammar = open(lark_file, encoding="utf-8").read()
    if lalr:
        return Lark(grammar, start='program', parser='lalr',
                    debug=True, propagate_positions=True)
    return Lark(grammar, start='program',
                debug=True, propagate_positions=True)


experimental_imperative_enabled = False

def set_experimental_imperative(enabled: bool) -> None:
    global experimental_imperative_enabled
    experimental_imperative_enabled = enabled

def get_experimental_imperative_enabled() -> bool:
    return experimental_imperative_enabled

def require_experimental_imperative(loc: Meta) -> None:
    if not experimental_imperative_enabled:
        raise ParseError(
            loc,
            'experimental imperative syntax requires --experimental-imperative',
        )


# Keyword tokens that belong exclusively to the experimental imperative
# layer (#854): every recursive-descent parse path that consumes one is
# gated behind ``require_experimental_imperative``. Because RD tokenizes
# with lark's *non-contextual* ``.lex()`` (unlike the LALR parser's
# contextual lexer), these words would otherwise be reserved globally and
# rejected as ordinary identifiers even when ``--experimental-imperative``
# is off -- a divergence from the LALR parser, which accepts them as
# identifiers in that mode (issue #473). When the flag is off, RD demotes
# these tokens to ``IDENT`` and the LALR parser skips them in
# ``reject_reserved_identifiers`` so both parsers agree.
#
# Excluded on purpose: ``VAR``/``GHOST`` (also used by the stable ``object``
# field syntax) and ``VIEW``/``SOURCE``/``TARGET``/``INTO``/``OUT``/
# ``ROUNDTRIP``/``INVERSE`` (the ``view`` declaration is not gated in RD),
# since those are reachable with the flag off and must stay reserved.
experimental_imperative_keywords = frozenset({
    'EMP', 'NEW', 'PROC', 'OBSERVER', 'RESOURCE', 'REQUIRES', 'ENSURES',
    'READS', 'MODIFIES', 'DECREASES', 'INVARIANT', 'ESTABLISHED',
    'PRESERVED', 'CALL', 'WHILE', 'RETURN', 'AS', 'FOOTPRINT',
})
