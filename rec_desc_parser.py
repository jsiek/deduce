# The motivation for this recursive-descent version of the parser
# is to provide better error messages. -Jeremy

from typing import Optional, cast

from abstract_syntax import (
    All, AllElim, AllElimTypes, AllIntro, And, ApplyDefsFact,
    ApplyDefsGoal, ArrayGet, ArrayType, Assert, Associative, Auto,
    Bool, BoolType, Call, Cases, Conditional, Constructor,
    Define, Emp, EvaluateFact, EvaluateGoal, Export, FieldAccess, FrameEmpty,
    FrameFootprint, FrameTerm, FunCase, FunctionType,
    GenRecFun, Generic, Hole, IfThen, ImpIntro, Import,
    ImpAssert, ImpAssign, ImpAssume, ImpCall, ImpCallExpr, ImpIf, ImpReturn,
    ImpStmt, ImpVar, ImpWhile, LValueField, LValueIndex, LValueVar,
    IndCase, Induction, Inductive, Lambda, MakeArray, Mark,
    Module, ModusPonens, MutableArrayType, ObjectDecl, ObjectField,
    ObserverDecl, Omitted,
    Or, PAndElim, PAnnot, PExtensionality, PHelpUse, PHole, PInjective, PLet,
    PRecall, PReflexive, PSorry, PSymmetric, PTLetNew, PTransitive, PTrue,
    PointsTo, PTuple, PVar, Pattern, PatternBool, PatternCons, PatternTerm,
    Postulate,
    PostconditionRef, Predicate, Print, ProcDecl, ProcParam, ProcProofEntry,
    ProcSpec, Proof, RecFun, ResourceDecl,
    RewriteFact, RewriteGoal, Rule, RuleInduction, RuleInductionCase,
    RuleInversion, SepConj, SimplifyFact, SimplifyGoal, Some, SomeElim, SomeIntro,
    Statement, Suffices, Switch, SwitchCase, SwitchProof, SwitchProofCase,
    TAnnote, TLet, Term, TermInst,
    Theorem, Trace, Type, TypeAlias, TypeInst, TypeType, Union, Var, ViewDecl,
    build_equations_proof, extract_and, extract_or, extract_tuple,
    listToNodeList, mkIntLit, mkLitNat, mkUIntLit, remove_mark,
)
from lark import Lark, Token, exceptions
from lark.tree import Meta
from error import ParseError, error_header, lark_unexpected_chars_to_parse_error
from flags import VerboseLevel, get_experimental_imperative
from edit_distance import closest_keyword, edit_distance
from parser_common import (
    get_experimental_imperative_enabled, make_lark_parser,
    require_experimental_imperative, set_experimental_imperative,
)
# Re-exported so ``rec_desc_parser.<name>`` stays a valid module attribute
# for the callers (LSP, declarations, tests) that reach through the active
# parser.
from parser_common import get_deduce_directory as get_deduce_directory
from parser_common import get_filename as get_filename
from parser_common import set_deduce_directory as set_deduce_directory
from parser_common import set_filename as set_filename

expt_operators = { '^' }
mult_operators = {'*', '/', '%', '∘', '.o.'}
add_operators = {'+', '-', '∸', '.-.', '∪', '|', '∩', '&', '⨄', '.+.', '++', '⊝' }
compare_operators = {'<', '>', '≤', '<=', '≥', '>=', '⊆', '(=', '∈', 'in', '≲', '<~'}
equal_operators = {'=', '≠', '/=', '≈', '~~'}
iff_operators = {'iff', "<=>", "⇔"}

to_unicode = {'.o.': '∘', '|': '∪', '&': '∩', '.+.': '⨄', '.-.': '∸',
              '<=': '≤', '>=': '≥',
              '~~': '≈', '<~': '≲',
              '(=': '⊆', 'in': '∈', '.0.': '∅', '<=>': '⇔', 'iff': '⇔'}


accessiblity_keywords = {'OPAQUE', 'PRIVATE', 'PUBLIC'}

# Keyword tokens that belong exclusively to the experimental imperative
# layer (#854): every recursive-descent parse path that consumes one is
# gated behind ``require_experimental_imperative``. Because RD tokenizes
# with lark's *non-contextual* ``.lex()`` (unlike the LALR parser's
# contextual lexer), these words would otherwise be reserved globally and
# rejected as ordinary identifiers even when ``--experimental-imperative``
# is off -- a divergence from the LALR parser, which accepts them as
# identifiers in that mode (issue #473). When the flag is off we demote
# these tokens to ``IDENT`` so both parsers agree.
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

lark_parser: Optional[Lark] = None

def init_parser() -> None:
  global lark_parser
  lark_parser = make_lark_parser(lalr=False)

# The current_position needs to be a global so that the changes to the
# current_position don't get discarded when an exception is
# thrown. -Jeremy

current_position = 0
token_list: list[Token] = []

def current_token() -> Token:
  if end_of_file():
    raise ParseError(meta_from_tokens(token_list[-1], token_list[-1]),
          'Expected a token, got end of file')
  return token_list[current_position]

def next_token() -> Token:
  if current_position + 1 >= len(token_list):
    raise ParseError(meta_from_tokens(token_list[-1], token_list[-1]),
          'Expected a token, got end of file')
  return token_list[current_position + 1]

def previous_token() -> Token:
    return token_list[current_position - 1]

def advance() -> None:
    global current_position
    current_position = current_position + 1

def end_of_file() -> bool:
    return current_position >= len(token_list)

def consume_token(expected: str, display: str, context: str = "", advice: str = "") -> None:
  if current_token().type != expected:
    expect_msg = display
    if advice:
      advice = "\n" + advice
    raise ParseError(meta_from_tokens(current_token(), current_token()),
                     f'expected {expect_msg} {context}, not\n\t{current_token().value}{advice}')
  else:
    advance()

check_closest_kwd = False

def parse(program_text: str,
          trace: "bool | VerboseLevel" = False,
          error_expected: bool = False,
          experimental_imperative: bool | None = None) -> "list[Statement]":
  global token_list, current_position, check_closest_kwd
  previous_experimental_imperative = get_experimental_imperative_enabled()
  if experimental_imperative is None:
    experimental_imperative = get_experimental_imperative()
  set_experimental_imperative(experimental_imperative)
  try:
    assert lark_parser is not None, "init_parser() must be called before parse()"
    lexed = lark_parser.lex(program_text)
    token_list = []
    current_position = 0
    # ``lark_parser.lex`` is a generator -- ``UnexpectedCharacters``
    # only surfaces once the bad char is reached during iteration. Wrap
    # the consume loop (not the construction) so the default
    # parser-internal message gets replaced with a Deduce hint (notably
    # for ``\``, which Haskell-trained users reach for first).
    try:
      for token in lexed:
        if trace:
          print(repr(token))
        if not get_experimental_imperative_enabled() \
           and token.type in experimental_imperative_keywords:
          # See ``experimental_imperative_keywords``: with the flag off,
          # this word is an ordinary identifier, matching the LALR parser.
          token = Token.new_borrow_pos('IDENT', token.value, token)
        token_list.append(token)
    except exceptions.UnexpectedCharacters as e:
      raise lark_unexpected_chars_to_parse_error(e, get_filename())

    stmts: list[Statement] = []
    while not end_of_file():
      try:
        stmt = parse_statement()
      except ParseError as e:
        if not check_closest_kwd:
          check_closest_kwd = True
          parse(program_text, trace, error_expected,
                experimental_imperative=experimental_imperative)
        else:
          raise e
      except Exception as e:
        raise e


      stmts.append(stmt)
    return stmts
  finally:
    # check_closest_kwd is set to True when a first-pass parse error
    # triggers a "did you mean" retry. Without this reset, the True
    # value leaks into subsequent parses (e.g. of imported library
    # files in library mode) and produces spurious keyword-closeness
    # suggestions. The CLI never noticed because each invocation is
    # a fresh process.
    check_closest_kwd = False
    set_experimental_imperative(previous_experimental_imperative)


def parse_identifier() -> str:
  if end_of_file():
    raise ParseError(meta_from_tokens(previous_token(), previous_token()),
          'expected an identifier, not end of file')
  token = current_token()
  if token.type == 'IDENT':
    advance()
    return cast(str, token.value)
  elif token.value == '__':
    advance()
    return '__'
  elif current_token().value == 'operator':
    advance()
    rator = cast(str, current_token().value)
    advance()
    return to_unicode.get(rator, rator)
  else:
    raise ParseError(meta_from_tokens(token, token),
          'expected an identifier, not\n\t' + quote(token.value))

def require_token_position(value: int | None, name: str) -> int:
    assert value is not None, f"missing token {name}"
    return value

def meta_from_tokens(start_token: Token, end_token: Token) -> Meta:
    meta = Meta()  # type: ignore[no-untyped-call,unused-ignore]
    meta.empty = False
    setattr(meta, "filename", get_filename())
    meta.line = require_token_position(start_token.line, "line")
    meta.column = require_token_position(start_token.column, "column")
    meta.start_pos = require_token_position(start_token.start_pos, "start_pos")
    meta.end_line = require_token_position(end_token.end_line, "end_line")
    meta.end_column = require_token_position(end_token.end_column, "end_column")
    meta.end_pos = require_token_position(end_token.end_pos, "end_pos")
    return meta

def parse_term_hi() -> Term:
  token = current_token()

  if token.type == 'ALL':
    advance()
    vars = parse_type_annot_list()
    try:
      consume_token('DOT', '"."', context='after parameters of "all"')
    except ParseError as e:
      raise e.extend(meta_from_tokens(token, current_token()), '\nwhile parsing\n\tterm ::= "all" var_list "." term')
    body = parse_term()
    meta = meta_from_tokens(token, previous_token())
    result = body
    for j, var in enumerate(reversed(vars)):
      result = All(meta, None, var, (j, len(vars)), result)
    return result
  elif token.type == 'AT':
    start_token = current_token()
    advance()
    subject = parse_term_hi()
    try:
      consume_token('LESSTHAN', '"<"', context='after subject of instantiation ("@")')
      type_args = parse_type_list()
      consume_token('MORETHAN', '">"', context='after type arguments of instantiation ("@")')
      meta = meta_from_tokens(token, previous_token())
      return TermInst(meta, None, subject, type_args, False)
    except ParseError as e:
      raise e.extend(meta_from_tokens(start_token, current_token()), '\nwhile parsing\n' \
            + '\tterm ::= "@" term "<" type_list ">"')
  elif token.type == 'FALSE':
    advance()
    return Bool(meta_from_tokens(token,token), None, False)

  elif token.type == 'INT' or token.value == '0':
    advance()
    return mkUIntLit(meta_from_tokens(token,token), int(token.value))

  elif token.type == 'NAT' or token.value == '0':
    advance()
    meta = meta_from_tokens(token,token)
    return mkLitNat(meta, int(token.value[1:]))

  elif token.type == 'PLUS':
    advance()
    intToken = current_token()
    if intToken.type == 'INT' or intToken.value == '0':
      advance()
      return mkIntLit(meta_from_tokens(intToken,intToken),
                      int(intToken.value), token.type)
    else:
      raise ParseError(meta_from_tokens(current_token(),current_token()),
            'expected an integer not\n\t' + current_token().value)

  elif token.type == 'IF':
    start_token = current_token()
    advance()
    prem = parse_term()
    try:
      consume_token('THEN', 'keyword "then"', context='after premise of "if" formula')
    except ParseError as e:
      raise e.extend(meta_from_tokens(start_token, current_token()), '\nwhile parsing\n' \
            + '\tformula ::= "if" formula "then" formula')
    conc = parse_term()

    if current_token().type == 'ELSE':
      advance()
      els = parse_term()
      return Conditional(meta_from_tokens(token, previous_token()), None,
                         prem, conc, els)
    else:
      return IfThen(meta_from_tokens(token, previous_token()),
                    None, prem, conc)

  elif token.value == '∅' or token.value == '.0.':
    advance()
    meta = meta_from_tokens(token, token)
    return Call(meta, None, Var(meta, None, 'empty_set'), [])

  elif token.type == 'EMP':
    require_experimental_imperative(meta_from_tokens(token, token))
    advance()
    return Emp(meta_from_tokens(token, token), None)

  elif token.type == 'FUN' or token.type == 'Λ':
    advance()
    type_params = parse_type_parameters()
    params = parse_var_list()
    consume_token('LBRACE', '"{"', context='after parameters of fun')
    body = parse_term()
    consume_token('RBRACE', '"}"', context='after body of fun')
    meta = meta_from_tokens(token, previous_token())
    if len(type_params) > 0:
      return Generic(meta, None, type_params, Lambda(meta, None, params, body))
    else:
      return Lambda(meta, None, params, body)

  elif token.type == 'GENERIC':
    advance()
    type_params = parse_ident_list()
    consume_token('LBRACE', '"{"', context='after parameters of "generic"')
    body = parse_term()
    consume_token('RBRACE', '"}"', context='after body of "generic"')
    meta = meta_from_tokens(token, previous_token())
    return Generic(meta, None, type_params, body)

  elif token.type == 'LESSTHAN':
    advance()
    type_params = parse_ident_list()
    consume_token('MORETHAN', 'closing ">"', context='after type parameters')
    body = parse_term()
    meta = meta_from_tokens(token, previous_token())
    result = body
    for j, ty in enumerate(reversed(type_params)):
      result = All(meta, None, (ty, TypeType(meta)), (j, len(type_params)), result)
    return result

  elif token.type == 'LPAR':
    start_token = current_token()
    advance()
    while_parsing = 'while parsing parenthesized term\n' \
        + '\tterm ::= "(" term ")"\n'

    try:
      term = parse_term()
      consume_token('RPAR', 'closing parenthesis ")"')
    except ParseError as e:
      raise e.extend(meta_from_tokens(start_token, current_token()), while_parsing)

    return term

  elif token.type == 'HASH':
    advance()
    term = parse_term()
    consume_token('HASH', 'closing hash "#"') # Closing token
    meta = meta_from_tokens(token, previous_token())
    return Mark(meta, None, term)

  elif token.value == '─' or token.value == '__':
    advance()
    meta = meta_from_tokens(token,token)
    return Omitted(meta, None)

  elif token.type == 'MINUS':
    advance()
    subject = parse_call()
    meta = meta_from_tokens(token, previous_token())
    return Call(meta, None, Var(meta, None, '-'), [subject])

  elif token.value == '∸':
    advance()
    subject = parse_call()
    meta = meta_from_tokens(token, previous_token())
    return Call(meta, None, Var(meta, None, '∸'), [subject])

  elif token.type == 'NOT':
    advance()
    subject = parse_term_equal()
    meta = meta_from_tokens(token, previous_token())
    return IfThen(meta, None, subject, Bool(meta, None, False))

  elif token.type == 'NEW':
    raise ParseError(
      meta_from_tokens(token, token),
      "`new` allocation syntax is only available in imperative "
      "statement right-hand sides",
    )

  elif token.type == 'QMARK':
    advance()
    meta = meta_from_tokens(token,token)
    return Hole(meta, None)

  elif token.type == 'NAMED_HOLE':
    advance()
    meta = meta_from_tokens(token,token)
    return Hole(meta, None)

  elif token.type == 'SOME':
    advance()
    vars = parse_type_annot_list()
    consume_token('DOT', '"."', context='after parameters of "some"')
    body = parse_term()
    return Some(meta_from_tokens(token, previous_token()),
                None, vars, body)

  elif token.type == 'SWITCH':
    advance()
    subject = parse_term()
    consume_token('LBRACE', '"{"', context='after subject of "switch"')
    cases = []
    while current_token().type == 'CASE':
      switch_case = parse_switch_case()
      cases.append(switch_case)
    consume_token('RBRACE', '"}"', context='after last case of "switch"')
    return Switch(meta_from_tokens(token, previous_token()), None,
                   subject, cases)

  elif token.type == 'TRUE':
    advance()
    return Bool(meta_from_tokens(token,token), None, True)

  elif token.type == 'LSQB':
    advance()
    if current_token().type == 'RSQB':
        advance()
        return listToNodeList(meta_from_tokens(token,token), [])
    lst_terms = []
    term = parse_term()
    lst_terms.append(term)
    token = current_token()
    while token.type == 'COMMA':
      advance()
      term = parse_term()
      lst_terms.append(term)
      token = current_token()
    consume_token('RSQB', 'closing bracket "]"', context='at end of list literal')
    return listToNodeList(meta_from_tokens(token,token), lst_terms)

  elif token.type == 'DEFINE':
    return parse_define_term()

  else:
    try:
      name = parse_identifier()
      meta = meta_from_tokens(token, token)
      var = Var(meta, None, name)
      return var
    except ParseError:
      raise ParseError(meta_from_tokens(token, current_token()),
            'expected a term, not\n\t' + quote(current_token().value))
    except Exception as e:
      raise ParseError(meta_from_tokens(token, previous_token()), "Unexpected error while parsing:\n\t" \
        + str(e))

def parse_postfix_chain(term: Term, start_token: Token) -> Term:
  # Chain postfix calls `(...)` and array accesses `[...]` in any
  # order. LALR's `?atomic_term` rule already interleaves both via
  # left recursion: `atomic_term "(" term_list ")"` and
  # `atomic_term "[" term "]"`. Mirror that here so `f(a)[0]` and
  # `array(l)[0]` parse identically under both parsers.
  while not end_of_file():
    tt = current_token().type
    if tt == 'LPAR':
      while_parsing = 'while parsing function call\n' \
          + '\tterm ::= term "(" term_list ")"\n'
      try:
        advance()
        args = parse_term_list('RPAR')
        consume_token('RPAR', 'closing parenthesis ")"',
                      advice='Perhaps you forgot a comma?')
        term = Call(meta_from_tokens(start_token, previous_token()), None,
                    term, args)
      except ParseError as e:
        raise e.extend(meta_from_tokens(start_token, previous_token()),
                       while_parsing)
      except Exception as e:
        raise ParseError(meta_from_tokens(start_token, previous_token()),
                         "Unexpected error while parsing:\n\t" + str(e))
    elif tt == 'LSQB':
      while_parsing = 'while parsing array access\n' \
          + '\tterm ::= term "[" term "]"\n'
      # Use the `[` as the diagnostic anchor so the "while parsing
      # array access" context points at the bracket, matching the
      # original parse_array_get behavior captured by the parse/
      # error fixtures.
      bracket_token = current_token()
      try:
        advance()
        index = parse_term()
        consume_token('RSQB', 'closing bracket "]"')
        term = ArrayGet(meta_from_tokens(bracket_token, previous_token()),
                        None, term, index)
      except ParseError as e:
        raise e.extend(meta_from_tokens(bracket_token, previous_token()),
                       while_parsing)
      except Exception as e:
        raise ParseError(meta_from_tokens(bracket_token, previous_token()),
                         "Unexpected error while parsing:\n\t" + str(e))
    elif tt == 'FIELDACCESS':
      # Field access `subject.field` (#854 Phase 1h). The FIELDACCESS token
      # carries its leading `.`; the field name drops it.
      require_experimental_imperative(meta_from_tokens(current_token(),
                                                       current_token()))
      field = current_token().value[1:]
      advance()
      term = FieldAccess(meta_from_tokens(start_token, previous_token()),
                         None, term, field)
    else:
      break
  return term

def parse_call() -> Term:
  start_token = current_token()
  term = parse_term_hi()
  return parse_postfix_chain(term, start_token)

def parse_make_array() -> Term:
  if current_token().value == 'array':
    while_parsing = 'while parsing array creation\n' \
        + '\tterm ::= "array" "(" term ")"\n'
    start_token = current_token()
    advance()
    try:
      consume_token('LPAR', 'open parenthesis "("')
      arg = parse_term()
      consume_token('RPAR', 'closing parenthesis ")"')
      term = MakeArray(meta_from_tokens(start_token, previous_token()),None,arg)
    except ParseError as e:
      raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
    except Exception as e:
      raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
        + str(e))
    return parse_postfix_chain(term, start_token)
  else:
    return parse_call()


def parse_term_expt() -> Term:
  term = parse_make_array()

  while (not end_of_file()) and current_token().value in expt_operators:
    start_token = current_token()
    rator = Var(meta_from_tokens(current_token(), current_token()),
                None, to_unicode.get(current_token().value,
                                     current_token().value))
    advance()
    right = parse_make_array()
    term = Call(meta_from_tokens(start_token, previous_token()), None,
                rator, [term,right])

  return term

def parse_term_mult() -> Term:
  term = parse_term_expt()

  while (not end_of_file()) and current_token().value in mult_operators:
    start_token = current_token()
    rator = Var(meta_from_tokens(current_token(), current_token()),
                None, to_unicode.get(current_token().value,
                                     current_token().value))
    advance()
    right = parse_term_expt()
    term = Call(meta_from_tokens(start_token, previous_token()), None,
                rator, [term,right])

  return term

def parse_term_add() -> Term:
  token = current_token()
  term = parse_term_mult()

  while (not end_of_file()) and current_token().value in add_operators:
    rator = Var(meta_from_tokens(current_token(), current_token()),
                None, to_unicode.get(current_token().value, current_token().value))
    advance()
    right = parse_term_mult()
    term = Call(meta_from_tokens(token, previous_token()), None,
                rator, [term,right])

  return term

def parse_term_compare() -> Term:
  token = current_token()
  term = parse_term_add()

  while (not end_of_file()) and current_token().value in compare_operators:
    rator = Var(meta_from_tokens(current_token(), current_token()),
                None, to_unicode.get(current_token().value, current_token().value))
    advance()
    right = parse_term_compare()
    term = Call(meta_from_tokens(token, previous_token()), None,
                rator, [term,right])

  return term

def parse_term_equal() -> Term:
  token = current_token()
  term = parse_term_compare()
  while (not end_of_file()) and current_token().value in equal_operators:
    meta = meta_from_tokens(current_token(), current_token())
    opr = current_token().value
    advance()
    right = parse_term_equal()
    call_meta = meta_from_tokens(token, previous_token())
    if opr == '≠' or opr == '/=':
      term = IfThen(call_meta, None,
                    Call(call_meta, None, Var(meta, None, '='), [term,right]),
                    Bool(call_meta, None, False))
    else:
      term = Call(call_meta, None,
                  Var(meta, None, opr), [term,right])
  return term

def parse_term_pointsto() -> Term:
  # `lhs |-> rhs` (experimental imperative layer, #854 Phase 1h).
  # Non-associative: the operands are equality-level terms, matching the LALR
  # grammar. A field-access address like `p.f` is an ordinary atomic term
  # parsed by `parse_postfix_chain`, so no special handling is needed here.
  token = current_token()
  term = parse_term_equal()
  if (not end_of_file()) and current_token().value == '|->':
    require_experimental_imperative(meta_from_tokens(current_token(),
                                                     current_token()))
    advance()
    right = parse_term_equal()
    return PointsTo(meta_from_tokens(token, previous_token()), None,
                    term, right)
  return term

def parse_term_sep() -> Term:
  # Separating conjunction `**`, left-associative (#854 Phase 1h).
  token = current_token()
  term = parse_term_pointsto()
  while (not end_of_file()) and current_token().value == '**':
    require_experimental_imperative(meta_from_tokens(current_token(),
                                                     current_token()))
    advance()
    right = parse_term_pointsto()
    term = SepConj(meta_from_tokens(token, previous_token()), None,
                   term, right)
  return term

def parse_term_logic() -> Term:
  token = current_token()
  term = parse_term_sep()
  while (not end_of_file()) and (current_token().type == 'AND'
                                 or current_token().type == 'OR'):
    opr = current_token().type
    advance()
    right = parse_term_logic()
    if opr == 'AND':
      term = And(meta_from_tokens(token, previous_token()), None,
                 extract_and(term) + extract_and(right))
    elif opr == 'OR':
      term = Or(meta_from_tokens(token, previous_token()), None,
                 extract_or(term) + extract_or(right))

  if (not end_of_file()) and current_token().type == 'COLON':
    advance()
    typ = parse_type()
    term = TAnnote(meta_from_tokens(token, previous_token()), None,
                   term, typ)

  return term

def parse_term_iff() -> Term:
  token = current_token()
  term = parse_term_logic()
  while (not end_of_file()) and (current_token().value in iff_operators):
    advance()
    right = parse_term_logic()
    loc = meta_from_tokens(token, previous_token())
    left_right = IfThen(loc, None, term.copy(), right.copy())
    right_left = IfThen(loc, None, right.copy(), term.copy())
    term = And(loc, None, [left_right, right_left])

  if (not end_of_file()) and current_token().type == 'COLON':
    advance()
    typ = parse_type()
    term = TAnnote(meta_from_tokens(token, previous_token()), None,
                   term, typ)

  return term

def parse_term() -> Term:
  if end_of_file():
      raise ParseError(meta_from_tokens(previous_token(),previous_token()),
            'expected a term, not end of file')

  token = current_token()
  term = parse_term_iff()

  if not end_of_file() and current_token().type == 'COLON':
    advance()
    typ = parse_type()
    term = TAnnote(meta_from_tokens(token, previous_token()), None,
                   term, typ)
  return term

def parse_define_term() -> Term:
  while_parsing = 'while parsing\n' \
      + '\tterm ::= "define" identifier "=" term ";" term\n'
  try:
    start_token = current_token()
    advance()
    name = parse_identifier()
    consume_token('EQUAL', '"="', context='after name in "define"')
    rhs = parse_term_logic()
    consume_token('SEMICOLON', '";"', context='after right-hand side of "define"')
    meta = meta_from_tokens(start_token, previous_token())
    body = parse_term()
    return TLet(meta, None, name, rhs, body)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
      + str(e))

def parse_assumption() -> tuple[str, Term | None]:
  if current_token().type == 'COLON':
    label = '_'
  else:
    label = parse_identifier()
  if current_token().type == 'COLON':
    advance()
    premise = parse_term()
    return label,premise
  else:
    return label,None

proof_keywords = {'apply', 'arbitrary', 'assume',
                  'cases', 'case', 'choose', 'conclude', 'conjunct',
                  'expand',
                  'equations', 'evaluate', 'extensionality',
                  'have', 'induction', 'injective', 'obtain',
                  'recall', 'reflexive', 'replace',
                  'suffices', 'suppose', 'switch', 'symmetric',
                  'transitive'}

def parse_recall() -> Proof:
  start_token = current_token()
  advance()
  facts = parse_nonempty_term_list()
  meta = meta_from_tokens(start_token, previous_token())
  return PRecall(meta, facts)

def parse_reason() -> Proof:
    if end_of_file():
      raise ParseError(meta_from_tokens(current_token(), current_token()),
            'expected a reason, not end of file')
    if current_token().type == 'BY':
      advance()
      proof = parse_proof()
    elif current_token().type == 'PROOF':
      advance()
      proof = parse_proof()
      consume_token('END', 'keyword "end"', context='after proof of theorem')
    else:
      raise ParseError(meta_from_tokens(current_token(), current_token()),
            'expected the keyword "by" or "proof" at beginning of a reason, not\n\t' \
            + current_token().value)
    return proof

def parse_proof_hi() -> Proof:
  token = current_token()
  if token.type == 'APPLY':
    while_parsing = 'while parsing apply-to (use a logical implication)\n' \
        + '\tconclusion ::= "apply" proof "to" proof\n'
    advance()
    try:
      imp = parse_proof()
      consume_token('TO', '"to"', context='after implication part of "apply"')
      arg = parse_proof()
      return ModusPonens(meta_from_tokens(token, previous_token()), imp, arg)
    except ParseError as e:
      raise e.extend(meta_from_tokens(token, previous_token()), while_parsing)
    except Exception as e:
      raise ParseError(meta_from_tokens(token, previous_token()), "Unexpected error while parsing:\n\t" \
        + str(e))

  elif token.type == 'CONTRADICT':
    while_parsing = 'while parsing contracit (use a logical negation)\n' \
        + '\tconclusion ::= "contradict" proof "," proof\n'
    advance()
    try:
      child1 = parse_proof()
      child2 = child1.copy()
      return ModusPonens(meta_from_tokens(token, previous_token()), child1, child2)
    except ParseError as e:
      raise e.extend(meta_from_tokens(token, previous_token()), while_parsing)
    except Exception as e:
      raise ParseError(meta_from_tokens(token, previous_token()), "Unexpected error while parsing:\n\t" \
        + str(e))

  elif token.type == 'CASES':
    while_parsing = 'while parsing cases (use a logical or)\n' \
        + '\tconclusion ::= "cases" proof case_clause*\n' \
        + '\tcase_clause ::= "case" identifier ":" term "{" proof "}"\n'
    advance()
    try:
      subject = parse_proof(allow_missing=False)
      cases = []
      while (not end_of_file()) and current_token().type == 'CASE':
          c = parse_case()
          cases.append(c)
      meta = meta_from_tokens(token, previous_token())
      return Cases(meta, subject, cases)
    except ParseError as e:
      raise e.extend(meta_from_tokens(token, previous_token()), while_parsing)
    except Exception as e:
      raise ParseError(meta_from_tokens(token, previous_token()), "Unexpected error while parsing:\n\t" \
        + str(e))

  elif token.type == 'CONCLUDE':
    while_parsing = 'while parsing\n' \
        + '\tconclusion ::= "conclude" formula "by" proof\n'
    advance()
    try:
      claim = parse_term()
      reason = parse_reason()
      return PAnnot(meta_from_tokens(token, previous_token()), claim, reason)
    except ParseError as e:
      raise e.extend(meta_from_tokens(token, previous_token()), while_parsing)
    except Exception as e:
      raise ParseError(meta_from_tokens(token, previous_token()), "Unexpected error while parsing:\n\t" \
        + str(e))

  elif token.type == 'CONJUNCT':
    advance()
    meta = meta_from_tokens(current_token(),current_token())

    if current_token().type != 'INT' and current_token().value != '0':
      raise ParseError(meta, 'expected an int literal after "conjunct", not\n\t' \
            + current_token().value)

    index = int(current_token().value)
    advance()
    consume_token('OF', 'keyword "of"', context='after index of "conjunct"')

    subject = parse_proof()
    meta = meta_from_tokens(token,previous_token())
    return PAndElim(meta, index, subject)

  elif token.type == 'DOT':
    advance()
    return PTrue(meta_from_tokens(token, token))

  elif token.type == 'EQUATIONS':
    advance()
    first = parse_equation()
    rest = parse_equation_list()
    eqs: list[tuple[Term, Term, Proof]] = [first]
    for (lhs, rhs, reason) in rest:
        if lhs == None:
            # `... = rhs` chains: inherit the previous step's RHS,
            # stripping any mark the user wrote on it (each step gets
            # its own mark) via `remove_mark`. Previously this used
            # `.copy()` and relied on a `Mark.copy` bug that dropped
            # the mark.
            lhs = remove_mark(eqs[-1][1])
        eqs.append((lhs, rhs, reason))
    return build_equations_proof(meta_from_tokens(token, token), eqs)

  elif token.type == 'RECALL':
    return parse_recall()

  elif token.type == 'INDUCTION':
    return parse_induction()

  elif token.type == 'RULE':
    return parse_rule_induction()

  elif token.type == 'LPAR':
    advance()
    proof = parse_proof()
    consume_token('RPAR', 'closing parenthesis ")"', context='around proof')
    return proof

  elif token.type == 'LBRACE':
    advance()
    proof = parse_proof()
    consume_token('RBRACE', 'closing "}"', context='around proof')
    return proof

  elif token.type == 'QMARK':
    advance()
    meta = meta_from_tokens(token, token)
    return PHole(meta)

  elif token.type == 'NAMED_HOLE':
    advance()
    meta = meta_from_tokens(token, token)
    return PHole(meta)

  elif token.type == 'SORRY':
    advance()
    meta = meta_from_tokens(token,token)
    return PSorry(meta)

  elif token.type == 'HELP':
    advance()
    subject = parse_proof()
    meta = meta_from_tokens(token,previous_token())
    return PHelpUse(meta, subject)

  elif token.type == 'REFLEXIVE':
    advance()
    meta = meta_from_tokens(token, token)
    return PReflexive(meta)

  elif token.type == 'SWITCH':
    advance()
    subject = parse_term()
    if current_token().type == 'FOR':
        advance()
        defs = parse_ident_list()
    else:
        defs = []
    consume_token('LBRACE', '"{"', context='after subject of "switch"')
    cases = []
    while current_token().type == 'CASE':
        c = parse_proof_switch_case()
        cases.append(c)
    consume_token('RBRACE', '"}"', context='after last case of "switch"')
    meta = meta_from_tokens(token, previous_token())
    if len(defs) == 0:
        return SwitchProof(meta, subject, cases)
    else:
        return ApplyDefsGoal(meta, [Var(meta, None, t) for t in defs],
                              SwitchProof(meta, subject, cases))

  elif token.type == 'SYMMETRIC':
    advance()
    eq = parse_proof()
    meta = meta_from_tokens(token, token)
    return PSymmetric(meta, eq)

  elif token.type == 'TRANSITIVE':
    advance()
    eq1 = parse_proof()
    eq2 = parse_proof()
    meta = meta_from_tokens(token, token)
    return PTransitive(meta, eq1, eq2)

  elif token.type == 'EVALUATE':
    advance()
    if current_token().type == 'IN':
        advance()
        subject = parse_proof()
        return EvaluateFact(meta_from_tokens(token, previous_token()),
                             subject)
    else:
        return EvaluateGoal(meta_from_tokens(token, previous_token()))

  else:
    if check_closest_kwd:
      close_keyword = closest_keyword(token.value, proof_keywords)
      if close_keyword and close_keyword != token.value:
        raise ParseError(meta_from_tokens(token, token),
                         'expected a proof.\nDid you mean "' + close_keyword \
                         + '" instead of "' + token.value + '"?')

    try:
      name = parse_identifier()
    except ParseError:
      raise ParseError(meta_from_tokens(token, current_token()),
                       'expected a proof, not\n\t' + quote(current_token().value),
                       missing=True)
    except Exception as e:
      raise ParseError(meta_from_tokens(token, previous_token()), "Unexpected error while parsing:\n\t" \
        + str(e))

    return PVar(meta_from_tokens(token, token), name)

def parse_proof_list() -> list[Proof]:
  proof_list = []
  proof = parse_proof()
  proof_list.append(proof)
  while (not end_of_file()) and current_token().value == '|':
    advance()
    proof = parse_proof()
    proof_list.append(proof)
  return proof_list

def parse_case() -> tuple[str, Term | None, Proof]:
  try:
    start_token = current_token()
    advance()
    label,premise = parse_assumption()
    consume_token('LBRACE', '"{"', context='after assumption of "case"')
    body = parse_proof()
    consume_token('RBRACE', '"}"', context='after body of "case"')
    return (label,premise,body)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, current_token()),
                   'while parsing:\n\t"case" label ":" formula "{" proof "}"')

def parse_proof_switch_case() -> SwitchProofCase:
  while_parsing='while parsing one of the following\n' \
            + '\tswitch_proof_case ::= "case" pattern "{" proof "}"\n' \
            + '\tswitch_proof_case ::= "case" pattern "assume" assumption_list "{" proof "}"'
  try:
    start_token = current_token()
    advance()
    pat = parse_pattern()
    if current_token().type == 'SUPPOSE' or current_token().type == 'ASSUME':
        advance()
        assumptions = []
        label,asm = parse_assumption()
        assumptions.append((label,asm))
        while current_token().type == 'COMMA':
            advance()
            label,asm = parse_assumption()
            assumptions.append((label,asm))
    else:
        assumptions = []
    consume_token('LBRACE', '"{"', context='after assumption of "case"')
    body = parse_proof()
    consume_token('RBRACE', '"}"', context='after body of "case"')
    meta = meta_from_tokens(start_token,previous_token())
    return SwitchProofCase(meta, pat, assumptions, body)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, current_token()), while_parsing)

def parse_proof_med() -> Proof:
    start_token = current_token()
    proof = parse_proof_hi()

    while (not end_of_file()) and current_token().type == 'LESSTHAN':
      while_parsing= 'while trying to parse type arguments for instantiation of an "all" formula:\n\t'\
              + 'proof ::= proof "<" type_list ">"'
      advance()
      try:
        type_list = parse_type_list()
        consume_token('MORETHAN', 'a closing ">"')
        meta = meta_from_tokens(start_token, previous_token())
        for j, ty in enumerate(type_list):
          proof = AllElimTypes(meta, proof, ty, (j, len(type_list)))
      except ParseError as e:
        raise e.extend(meta_from_tokens(start_token, current_token()), while_parsing)

    while (not end_of_file()) and current_token().type == 'LSQB':
      advance()
      term_list = parse_nonempty_term_list()
      consume_token('RSQB', 'a closing "]"', advice="Perhaps you forgot a comma?")
      meta = meta_from_tokens(start_token, previous_token())
      for j, term in enumerate(term_list):
        proof = AllElim(meta, proof, term, (j, len(term_list)))

    return proof

def parse_proof_statement() -> tuple[Proof | None, bool]:
  if end_of_file():
    raise ParseError(meta_from_tokens(previous_token(),previous_token()),
          'expected a proof, not end of file')

  token = current_token()

  if token.type == 'SUFFICES':
    advance()
    formula = parse_term()
    proof = parse_reason()
    meta = meta_from_tokens(token, previous_token())
    return Suffices(meta, formula, proof, None), False

  elif token.type == 'EXPAND':
    token = current_token()
    advance()
    defs = parse_ident_list_bar()
    if current_token().type == 'IN':
        advance()
        subject = parse_proof()
        meta = meta_from_tokens(token, previous_token())
        return ApplyDefsFact(meta, [Var(meta, None, t) for t in defs],
                              subject), True
    else:
      meta = meta_from_tokens(token, previous_token())
      return ApplyDefsGoal(meta,
                           [Var(meta, None, t) for t in defs],
                           None), False

  elif token.type == 'REPLACE':
    token = current_token()
    advance()
    eqns = parse_proof_list()
    if current_token().type == 'IN':
      advance()
      subject = parse_proof()
      meta = meta_from_tokens(token, previous_token())
      return RewriteFact(meta, subject, eqns), True
    else:
      meta = meta_from_tokens(token, previous_token())
      return RewriteGoal(meta, eqns, None), False

  elif token.type == 'SIMPLIFY':
    token = current_token()
    advance()
    if current_token().type == 'WITH':
      advance()
      givens = parse_proof_list()
    else:
      givens = []
    if current_token().type == 'IN':
      advance()
      subject = parse_proof()
      meta = meta_from_tokens(token, previous_token())
      return SimplifyFact(meta, subject, givens), True
    else:
      meta = meta_from_tokens(token, previous_token())
      return SimplifyGoal(meta, None, givens), False

  elif token.type == 'SUPPOSE' or token.type == 'ASSUME':
    start_token = current_token()
    advance()
    try:
      label,premise = parse_assumption()
    except ParseError as e:
      raise ParseError(meta_from_tokens(token, current_token()),
            'expected an assumption:\n\t"assume" label ":" formula\n' \
            + str(e))
    except Exception as e:
      raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
        + str(e))

    meta = meta_from_tokens(token,previous_token())
    return ImpIntro(meta, label, premise, None), False

  elif token.type == 'ARBITRARY':
    advance()
    vars = parse_type_annot_list()
    meta = meta_from_tokens(token, previous_token())
    result: Proof | None = None
    for j, var in enumerate(reversed(vars)):
        result = AllIntro(meta, var, (j, len(vars)), result)
    return result, False

  elif token.type == 'CHOOSE':
    advance()
    witnesses = parse_nonempty_term_list()
    meta = meta_from_tokens(token, previous_token())
    return SomeIntro(meta, witnesses, None), False

  elif token.type == 'OBTAIN':
    advance()
    witnesses = parse_ident_list()
    consume_token('WHERE', '"where"', context='after variables of "obtain"')
    label, premise = parse_assumption()
    consume_token('FROM', '"from"', context='after "where" part of "obtain"')
    some = parse_proof()
    meta = meta_from_tokens(token, previous_token())
    return SomeElim(meta, witnesses, label, premise, some, None), False

  elif token.type == 'HAVE':
    return parse_have(), False

  elif token.type == 'DEFINE':
    return parse_define_proof_stmt(), False

  elif token.type == 'INJECTIVE':
    advance()
    constr = parse_term()
    meta = meta_from_tokens(token, previous_token())
    return PInjective(meta, constr, None), False

  elif token.type == 'EXTENSIONALITY':
    advance()
    meta = meta_from_tokens(token, previous_token())
    return PExtensionality(meta, None), False

  elif token.type == 'SHOW':
    advance()
    claim = parse_term()
    return PAnnot(meta_from_tokens(token, previous_token()),
                  claim, None), False

  else:
    return None, False

def parse_define_proof_stmt() -> Proof:
  while_parsing = 'while parsing\n' \
      + '\tproof_stmt ::= "define" identifier "=" term\n'
  try:
    start_token = current_token()
    token = current_token()
    advance()
    name = parse_identifier()
    consume_token('EQUAL', '"="', context='after name in "define"')
    rhs = parse_term()
    meta = meta_from_tokens(token, previous_token())
    return PTLetNew(meta, name, rhs, None)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
      + str(e))


def parse_have() -> Proof:
  while_parsing = 'while parsing\n' \
      + '\tproof_stmt ::= "have" identifier ":" formula "by" proof\n' \
      + '\tproof_stmt ::= "have" ":" formula "by" proof\n'
  try:
    start_token = current_token()
    token = start_token
    advance()

    if end_of_file():
      raise ParseError(meta_from_tokens(start_token, start_token),
            'expected an identifier or colon after "have", not end of file')

    if current_token().type != 'COLON':
      try:
        label = parse_identifier()
      except ParseError:
        raise ParseError(meta_from_tokens(current_token(), current_token()),
            'expected an identifier or colon after "have", not\n\t' \
            + current_token().value)
      except Exception as e:
        raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
          + str(e))
    else:
      label = '_'

    if end_of_file():
      raise ParseError(meta_from_tokens(start_token, start_token),
            'expected a colon after label of "have", not end of file')
    elif current_token().type != 'COLON':
      raise ParseError(meta_from_tokens(current_token(), current_token()),
            'expected a colon after label of "have", not\n\t' \
            + current_token().value)
    advance()
    proved = parse_term()
    because = parse_reason()
    return PLet(meta_from_tokens(token, previous_token()), label, proved, because, None)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
      + str(e))

def parse_proof(allow_missing: bool = True) -> Proof:
    proof_stmt, concluded = parse_proof_statement()
    if concluded:
        return proof_stmt
    if proof_stmt:
        try:
          body = parse_proof()
        except ParseError as ex:
          if not ex.missing:
              raise ex
          else:
              body = PHole(meta_from_tokens(current_token(), current_token()))
        except Exception as e:
            raise ParseError(meta_from_tokens(current_token(), previous_token()),
                             "Unexpected error while parsing:\n\t" \
              + str(e))

        if isinstance(proof_stmt, AllIntro):
            proof_stmt.set_body(body)
        else:
            proof_stmt.body = body
        return proof_stmt
    else:
        ret = None
        try:
          ret = parse_finishing_proof()
        except ParseError as ex:
          if not ex.missing or not allow_missing:
              raise ex
          else:
              ret = PHole(meta_from_tokens(current_token(), current_token()))
        except Exception as e:
            raise ParseError(meta_from_tokens(current_token(), previous_token()), "Unexpected error while parsing:\n\t" \
              + str(e))
        return ret

def parse_finishing_proof() -> Proof:
    start_token = current_token()
    proof = parse_proof_med()
    while not end_of_file() and current_token().type == 'COMMA':
      advance()
      right = parse_proof()
      proof = PTuple(meta_from_tokens(start_token, previous_token()),
                     extract_tuple(proof) + extract_tuple(right))
    return proof

def parse_induction() -> Proof:
  while_parsing = 'while parsing\n' \
      + '\tconclusion ::= "induction" type ind_case*\n'
  try:
    start_token = current_token()
    token = start_token
    advance()
    typ = parse_type()
    cases = []
    while current_token().type == 'CASE':
      c = parse_induction_case()
      cases.append(c)
    return Induction(meta_from_tokens(token, previous_token()), typ, cases)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
      + str(e))

def parse_induction_case() -> IndCase:
  while_parsing = 'while parsing\n' \
      + '\tind_case ::= "case" pattern "{" proof "}"\n'
  try:
    start_token = current_token()
    advance()
    pat = parse_pattern()
    ind_hyps = []
    if current_token().type == 'SUPPOSE' or current_token().type == 'ASSUME':
      advance()
      label,ih = parse_assumption()
      ind_hyps.append((label,ih))
      while current_token().type == 'COMMA':
          advance()
          label,ih = parse_assumption()
          ind_hyps.append((label,ih))
    consume_token('LBRACE', '"{"', context='after pattern of "case"')
    body = parse_proof()
    consume_token('RBRACE', '"}"', context='after body of induction case')
    return IndCase(meta_from_tokens(start_token, previous_token()),
                    pat, ind_hyps, body)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
      + str(e))

def parse_rule_induction() -> Proof:
  # Dispatch on the second token: "induction" -> RuleInduction,
  # "inversion" -> RuleInversion. Both have the same case-branch shape.
  start_token = current_token()
  advance()  # consume 'rule'
  next_tok = current_token()
  if next_tok.type == 'INDUCTION':
    is_inv = False
    keyword_msg = 'induction'
    advance()
  elif next_tok.type == 'INVERSION':
    is_inv = True
    keyword_msg = 'inversion'
    advance()
  else:
    raise ParseError(
      meta_from_tokens(start_token, next_tok),
      'expected "induction" or "inversion" after "rule", not "'
      + next_tok.value + '"')
  while_parsing = 'while parsing\n' \
      + '\tconclusion ::= "rule" "' + keyword_msg \
      + '" identifier rule_ind_case*\n'
  try:
    hyp_name = parse_identifier()
    cases = []
    while current_token().type == 'CASE':
      c = parse_rule_induction_case()
      cases.append(c)
    # An empty case list is accepted at parse time (matching the LALR
    # grammar's `rule_ind_case*`); `_check_rule_induction_or_inversion`
    # reports the missing rule cases with a semantic diagnostic. See the
    # `induction_case_list` comment in Deduce.lark.
    meta = meta_from_tokens(start_token, previous_token())
    if is_inv:
      return RuleInversion(meta, hyp_name, cases)
    return RuleInduction(meta, hyp_name, cases)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()),
                   while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()),
                     "Unexpected error while parsing:\n\t" + str(e))

def parse_rule_induction_case() -> RuleInductionCase:
  while_parsing = 'while parsing\n' \
      + '\trule_ind_case ::= "case" identifier "{" proof "}"\n'
  try:
    start_token = current_token()
    advance()  # consume 'case'
    rule_name = parse_identifier()
    consume_token('LBRACE', '"{"',
                  context='after rule name "' + rule_name
                  + '" in rule induction case')
    body = parse_proof()
    consume_token('RBRACE', '"}"',
                  context='after body of rule induction case')
    return RuleInductionCase(meta_from_tokens(start_token, previous_token()),
                             rule_name, body)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()),
                   while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()),
                     "Unexpected error while parsing:\n\t" + str(e))

def parse_equation_side_logic() -> Term:
  # `and`/`or` directly on top of comparison terms (left-associative, to
  # match the LALR `eqs_logical_term` rule). The equality level is skipped so
  # the step-separator `=` is not consumed here.
  token = current_token()
  term = parse_term_compare()
  while (not end_of_file()) and (current_token().type == 'AND'
                                 or current_token().type == 'OR'):
    opr = current_token().type
    advance()
    right = parse_term_compare()
    loc = meta_from_tokens(token, previous_token())
    if opr == 'AND':
      term = And(loc, None, extract_and(term) + extract_and(right))
    else:
      term = Or(loc, None, extract_or(term) + extract_or(right))
  return term

def parse_equation_side() -> Term:
  # One side of an `equations` step. Allows the logical connectives
  # `iff`/`and`/`or` (which sit below `=` in the normal precedence ladder) by
  # parsing them on top of comparison terms, leaving the top-level `=` to
  # separate the two sides of the step. See Deduce.lark `equation_side`.
  token = current_token()
  term = parse_equation_side_logic()
  while (not end_of_file()) and (current_token().value in iff_operators):
    advance()
    right = parse_equation_side_logic()
    loc = meta_from_tokens(token, previous_token())
    left_right = IfThen(loc, None, term.copy(), right.copy())
    right_left = IfThen(loc, None, right.copy(), term.copy())
    term = And(loc, None, [left_right, right_left])
  return term

def parse_equation() -> tuple[Term, Term, Proof]:
  lhs = parse_equation_side()
  consume_token('EQUAL', '"="', context='after left-hand side of equation')
  rhs = parse_equation_side()
  reason = parse_reason()
  return (lhs, rhs, reason)

def parse_half_equation() -> tuple[Term | None, Term, Proof]:
  if current_token().value == '...':
    advance()
    consume_token('EQUAL', '"="', context='after "..."')
    rhs = parse_equation_side()
    reason = parse_reason()
    return (None, rhs, reason)
  elif current_token().value == '$':
    advance()
    return parse_equation()
  else:
    raise ParseError(meta_from_tokens(current_token(), current_token()),
          'expected "... = rhs" or "$ lhs = rhs" in "equations", not\n\t' \
          + current_token().value)

def parse_equation_list() -> list[tuple[Term | None, Term, Proof]]:
  eqn_list = []
  while current_token().value == '$' or current_token().value == '...':
    eqn = parse_half_equation()
    eqn_list.append(eqn)
  return eqn_list

def parse_theorem(visibility: str) -> Statement:
  while_parsing = 'while parsing\n' \
      + '\tproof_stmt ::= "theorem" identifier ":" formula "proof" proof "end"'
  try:
    start_token = current_token()
    is_lemma = start_token.type == 'LEMMA'
    is_postulate = start_token.type == 'POSTULATE'
    advance()

    try:
      name = parse_identifier()
    except ParseError:
      if end_of_file():

        raise ParseError(meta_from_tokens(start_token, start_token),
          'expected name of theorem, not end of file')
      else:
        raise ParseError(meta_from_tokens(current_token(), current_token()),
          'expected name of theorem, not:\n\t' + current_token().value)
    except Exception as e:
        raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
          + str(e))

    consume_token('COLON', 'a colon', context='after theorem name')

    what = parse_term()

    if is_postulate:
        return Postulate(meta_from_tokens(start_token, previous_token()),
                         name, what, visibility=visibility)

    proof = parse_reason()
    return Theorem(meta_from_tokens(start_token, previous_token()),
                   name, what, proof, is_lemma, visibility=visibility)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()),
                   while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
      + str(e))


def parse_union(visibility: str) -> Statement:
  while_parsing = 'while parsing\n' \
      + '\tstatement ::= "union" identifier type_params_opt "{" constructor* "}"\n'
  try:
    start_token = current_token()
    advance()
    name = parse_identifier()
    type_params = parse_type_parameters()

    consume_token('LBRACE', '"{"', context='after name of union')
    constr_list = []
    while current_token().type != 'RBRACE':
      constr = parse_constructor()
      constr_list.append(constr)
    meta = meta_from_tokens(start_token, current_token())
    advance()
    return Union(meta, name, type_params, constr_list, visibility=visibility)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
      + str(e))

def parse_type_alias(visibility: str) -> Statement:
  while_parsing = 'while parsing\n' \
      + '\tstatement ::= "type" identifier type_params_opt "=" type\n'
  try:
    start_token = current_token()
    advance()
    name = parse_identifier()
    type_params = parse_type_parameters()
    consume_token('EQUAL', '"="', context='after type alias name')
    body = parse_type()
    return TypeAlias(meta_from_tokens(start_token, previous_token()),
                     name, type_params, body, visibility=visibility)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
      + str(e))

def parse_object_field() -> ObjectField:
  while_parsing = 'while parsing\n' \
      + '\tobject_field ::= ["ghost"] "var" identifier ":" type\n'
  try:
    start_token = current_token()
    ghost = False
    if current_token().type == 'GHOST':
      ghost = True
      advance()
    consume_token('VAR', '"var"', context='at start of object field')
    name = parse_identifier()
    consume_token('COLON', '":"',
                  context='after object field name "' + name + '"')
    typ = parse_type()
    return ObjectField(meta_from_tokens(start_token, previous_token()),
                       name, typ, ghost)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()),
                     "Unexpected error while parsing:\n\t" + str(e))

def parse_object(visibility: str) -> Statement:
  while_parsing = 'while parsing\n' \
      + '\tstatement ::= "object" identifier type_params_opt ["{" object_field* "}"]\n'
  try:
    start_token = current_token()
    advance()
    name = parse_identifier()
    type_params = parse_type_parameters()
    fields = None
    if not end_of_file() and current_token().type == 'LBRACE':
      advance()
      fields = []
      while current_token().type != 'RBRACE':
        fields.append(parse_object_field())
      consume_token('RBRACE', '"}"', context='after object fields')
    return ObjectDecl(meta_from_tokens(start_token, previous_token()),
                      name, type_params, fields, visibility=visibility)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()),
                     "Unexpected error while parsing:\n\t" + str(e))

def parse_predicate(visibility: str, keyword: str) -> Statement:
  # Parses both `predicate` and `relation`. They produce the same AST;
  # `keyword` ('predicate' | 'relation') is preserved on the AST node so
  # later error messages can echo the form the user wrote.
  while_parsing = 'while parsing\n' \
      + '\tstatement ::= "' + keyword + '" identifier type_params_opt' \
      + ' ":" type "{" rule* "}"\n'
  try:
    start_token = current_token()
    advance()  # consume the keyword
    name = parse_identifier()
    type_params = parse_type_parameters()
    consume_token('COLON', '":"',
                  context='after name of ' + keyword + ' "' + name + '"')
    signature = parse_type()
    consume_token('LBRACE', '"{"',
                  context='after signature of ' + keyword + ' "' + name + '"')
    rules = []
    while current_token().type != 'RBRACE':
      rules.append(parse_predicate_rule())
    meta = meta_from_tokens(start_token, current_token())
    advance()  # consume }
    return Predicate(meta, name, type_params, signature, rules, keyword,
                     visibility=visibility)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()),
                     "Unexpected error while parsing:\n\t" + str(e))

def parse_predicate_rule() -> Rule:
  while_parsing = 'while parsing\n' \
      + '\trule ::= identifier ":" formula\n'
  try:
    start_token = current_token()
    name = parse_identifier()
    consume_token('COLON', '":"',
                  context='after rule name "' + name + '"')
    formula = parse_term()
    return Rule(meta_from_tokens(start_token, previous_token()), name, formula)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()),
                     "Unexpected error while parsing:\n\t" + str(e))

def parse_function(visibility: str) -> Statement:
  while_parsing = 'while parsing\n' \
      + '\tstatement ::= "fun" identifier type_params_opt "(" variable_list ")" "{" term "}"\n'
  try:
    start_token = current_token()
    advance()
    name = parse_identifier()
    typarams = parse_type_parameters()

    if current_token().type == 'LPAR':
      advance()
      params = parse_var_list()
      consume_token('RPAR', '")"')

    consume_token('LBRACE', '"{"', context='after parameters of function')
    body = parse_term()
    consume_token('RBRACE', '"}"', context='after body of function')
    meta = meta_from_tokens(start_token, previous_token())
    lam = Lambda(meta, None, params, body)
    if len(typarams) > 0:
      fun = Generic(meta, None, typarams, lam)
    else:
      fun = lam
    return Define(meta, name, None, fun, visibility=visibility)

  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
      + str(e))

def parse_gen_rec_function(visibility: str) -> Statement:
  while_parsing = 'while parsing\n' \
      + '\tstatement ::= "recfun" identifier type_params_opt "(" variable_list ")" "->" type "measure" term ":" type "{" term "}" "terminates" proof\n'
  try:
    start_token = current_token()
    advance()
    name = parse_identifier()
    typarams = parse_type_parameters()

    if current_token().type == 'LPAR':
      advance()
      params = parse_var_list()
      consume_token('RPAR', 'a closing parenthesis ")"')

    consume_token('ARROW', '"->"', context='between parameter types and return type')
    return_type = parse_type()
    consume_token('MEASURE', '"measure"', context='after return type of recfun')
    measure = parse_term()
    consume_token('OF', '"of"', context='after measure of function')
    measure_ty = parse_type()
    consume_token('LBRACE', '"{"', context='after parameters of function')
    body = parse_term()
    consume_token('RBRACE', '"}"', context='after body of function')

    consume_token('TERMINATES', '"terminates"', context='after "}" in "recfun"')
    terminates = parse_proof()

    meta = meta_from_tokens(start_token, previous_token())
    return GenRecFun(meta, name,
                     typarams, params, return_type,
                     measure, measure_ty, body, terminates, visibility=visibility)

  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()),
                   while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()),
                     "Unexpected error while parsing:\n\t" + str(e))

def parse_view_decl(visibility: str) -> Statement:
  while_parsing = 'while parsing\n' \
      + '\tstatement ::= "view" identifier type_params_opt "{" "source" type "target" type "into" identifier "out" identifier "roundtrip" identifier [ "inverse" identifier ] "}"\n'
  try:
    start_token = current_token()
    advance()
    name = parse_identifier()
    typarams = parse_type_parameters()

    consume_token('LBRACE', '"{"', context='after view name')
    consume_token('SOURCE', '"source"', context='inside view declaration')
    source = parse_type()
    consume_token('TARGET', '"target"', context='inside view declaration')
    target = parse_type()
    consume_token('INTO', '"into"', context='inside view declaration')
    into = parse_identifier()
    consume_token('OUT', '"out"', context='inside view declaration')
    out = parse_identifier()
    consume_token('ROUNDTRIP', '"roundtrip"', context='inside view declaration')
    roundtrip = parse_identifier()
    inverse = None
    if current_token().type == 'INVERSE':
      advance()
      inverse = parse_identifier()
    consume_token('RBRACE', '"}"', context='after view declaration')

    meta = meta_from_tokens(start_token, previous_token())
    return ViewDecl(meta, name, typarams, source, target, into, out,
                    roundtrip, inverse, visibility=visibility)

  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()),
                   while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()),
                     "Unexpected error while parsing:\n\t" + str(e))

def parse_recursive_function(visibility: str) -> Statement:
  while_parsing = 'while parsing\n' \
      + '\tstatement ::= "recursive" identifier type_params_opt' \
      + ' "(" type_list ")"\n\t\t\t "->" type "{" fun_case* "}"\n'
  try:
    start_token = current_token()
    advance()
    name = parse_identifier()
    type_params = parse_type_parameters()

    if current_token().type == 'LPAR':
      advance()
      param_types = parse_type_list()
      consume_token('RPAR', 'a closing parenthesis ")"')

    consume_token('ARROW', '"->"', context='between parameter types and return type')
    return_type = parse_type()
    consume_token('LBRACE', '"{"', context='after the return type of the function')

    cases = []
    while current_token().type != 'RBRACE':
      fun_case = parse_fun_case()
      cases.append(fun_case)
    advance()
    return RecFun(meta_from_tokens(start_token, previous_token()),
                  name, type_params, param_types, return_type, cases,
                  visibility=visibility)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
      + str(e))

def parse_define(visibility: str) -> Statement:
  while_parsing = 'while parsing\n' \
      + '\tproof_stmt ::= "define" identifier "=" term\n'
  try:
    start_token = current_token()
    advance()
    name = parse_identifier()
    if current_token().type == 'LESSTHAN':
      raise ParseError(meta_from_tokens(current_token(), current_token()),
            '`define` does not take type parameters.\n'
            'For a generic value, put the type parameters on the right:\n'
            '\tdefine ' + name + ' : fn <T> ... -> ... = generic T { ... }\n'
            'or use `fun`/`recursive`:\n'
            '\tfun ' + name + '<T>(...) { ... }\n'
            '\trecursive ' + name + '<T>(...) -> ... { ... }')
    if current_token().type == 'COLON':
      advance()
      while_parsing = 'while parsing\n' \
          + '\tproof_stmt ::= "define" identifier ":" type "=" term\n'
      typ = parse_type()
    else:
      typ = None
    consume_token('EQUAL', '"="', context='after name in "define"')
    body = parse_term()
    return Define(meta_from_tokens(start_token, previous_token()),
                  name, typ, body,
                  visibility=visibility)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
      + str(e))

def parse_frame_expr() -> FrameTerm | FrameFootprint | FrameEmpty:
  require_experimental_imperative(meta_from_tokens(current_token(), current_token()))
  start = current_token()
  if current_token().type == 'LBRACE':
    advance()
    consume_token('RBRACE', 'closing "}"', context='after empty frame')
    return FrameEmpty(meta_from_tokens(start, previous_token()))
  if current_token().value == 'footprint' and current_position + 1 < len(token_list) \
     and next_token().type == 'LPAR':
    advance()
    consume_token('LPAR', '"("', context='after "footprint"')
    subject = parse_term()
    consume_token('RPAR', 'closing ")"', context='after footprint subject')
    return FrameFootprint(meta_from_tokens(start, previous_token()), subject)

  # A field-access subject like `a.f` is an ordinary term (FieldAccess), so
  # `parse_term` already consumes it; there is no separate frame-field node.
  subject = parse_term()
  return FrameTerm(meta_from_tokens(start, previous_token()), subject)

def parse_frame_list() -> list[FrameTerm | FrameFootprint | FrameEmpty]:
  frames = [parse_frame_expr()]
  while not end_of_file() and current_token().type == 'COMMA':
    advance()
    frames.append(parse_frame_expr())
  return frames

def parse_proc_param() -> ProcParam:
  require_experimental_imperative(meta_from_tokens(current_token(), current_token()))
  start = current_token()
  ghost = False
  if current_token().value == 'ghost':
    ghost = True
    advance()
  name = parse_identifier()
  consume_token('COLON', '":"', context='after proc parameter name')
  typ = parse_type()
  return ProcParam(meta_from_tokens(start, previous_token()), name, typ, ghost)

def parse_proc_param_list() -> list[ProcParam]:
  if current_token().type == 'RPAR':
    return []
  params = [parse_proc_param()]
  while not end_of_file() and current_token().type == 'COMMA':
    advance()
    params.append(parse_proc_param())
  return params

def parse_proc_spec_label() -> str | None:
  if current_token().type == 'IDENT' and next_token().type == 'COLON':
    label = parse_identifier()
    consume_token('COLON', '":"', context='after proc spec label')
    return label
  return None

def parse_proc_spec() -> ProcSpec:
  require_experimental_imperative(meta_from_tokens(current_token(), current_token()))
  start = current_token()
  if current_token().value == 'requires':
    advance()
    value = parse_term()
    return ProcSpec(meta_from_tokens(start, previous_token()), 'requires',
                    value)
  if current_token().value == 'ensures':
    advance()
    label = parse_proc_spec_label()
    value = parse_term()
    return ProcSpec(meta_from_tokens(start, previous_token()), 'ensures',
                    value, label)
  if current_token().value == 'decreases':
    advance()
    value = parse_term()
    return ProcSpec(meta_from_tokens(start, previous_token()), 'decreases',
                    value)
  if current_token().value not in ('reads', 'modifies'):
    raise ParseError(meta_from_tokens(current_token(), current_token()),
                     'expected proc spec, not\n\t' + quote(current_token().value))
  keyword = cast(str, current_token().value)
  advance()
  frames = parse_frame_list()
  return ProcSpec(meta_from_tokens(start, previous_token()), keyword, frames)

def parse_proc_specs() -> list[ProcSpec]:
  specs: list[ProcSpec] = []
  while not end_of_file() and current_token().value in (
      'requires', 'ensures', 'reads', 'modifies', 'decreases'):
    specs.append(parse_proc_spec())
  return specs

def parse_proc_decl(visibility: str) -> Statement:
  require_experimental_imperative(meta_from_tokens(current_token(), current_token()))
  start = current_token()
  advance()
  name = parse_identifier()
  typarams = parse_type_parameters()
  consume_token('LPAR', '"("', context='after proc name')
  params = parse_proc_param_list()
  consume_token('RPAR', '")"', context='after proc parameters')
  return_type = None
  if not end_of_file() and current_token().type == 'ARROW':
    advance()
    return_type = parse_type()
  specs = parse_proc_specs()
  body = parse_imp_block(context='after proc header and specs')
  proof_block = parse_proc_proof_block()
  return ProcDecl(meta_from_tokens(start, previous_token()), name, typarams,
                  params, return_type, specs, body, proof_block,
                  visibility=visibility)

def parse_proc_proof_entry() -> ProcProofEntry:
  start = current_token()
  label = parse_identifier()
  consume_token('LBRACE', '"{"', context='after proof-slot label')
  proof = parse_proof()
  consume_token('RBRACE', '"}"', context='at end of proof-slot body')
  return ProcProofEntry(meta_from_tokens(start, previous_token()), label, proof)

def parse_proc_proof_block() -> list[ProcProofEntry]:
  # Optional out-of-line `proof <entry>* end` block after a proc body. Each
  # entry is `label { proof }`.
  if end_of_file() or current_token().type != 'PROOF':
    return []
  advance()  # consume "proof"
  entries: list[ProcProofEntry] = []
  while not end_of_file() and current_token().type != 'END':
    entries.append(parse_proc_proof_entry())
  consume_token('END', '"end"', context='at end of proc proof block')
  return entries

def parse_imp_block(context: str) -> list[ImpStmt]:
  consume_token('LBRACE', '"{"', context=context)
  stmts: list[ImpStmt] = []
  while not end_of_file() and current_token().type != 'RBRACE':
    stmts.append(parse_imp_stmt())
  consume_token('RBRACE', '"}"', context='at end of imperative block')
  return stmts

def parse_imp_lvalue() -> LValueVar | LValueIndex | LValueField:
  start = current_token()
  name = parse_identifier()
  if not end_of_file() and current_token().type == 'LSQB':
    advance()
    index = parse_term()
    consume_token('RSQB', 'closing "]"', context='after array index of assignment')
    return LValueIndex(meta_from_tokens(start, previous_token()), name, index)
  if not end_of_file() and current_token().type == 'FIELDACCESS':
    field = current_token().value[1:]
    advance()
    return LValueField(meta_from_tokens(start, previous_token()), name, field)
  return LValueVar(meta_from_tokens(start, previous_token()), name)

def parse_imp_rhs() -> Term | ImpCallExpr:
  # A `var`/assignment right-hand side is either a `call f(..)` expression
  # (optionally labelled with `as h`) or an ordinary term.
  if current_token().value == 'call':
    start = current_token()
    advance()
    call = parse_term()
    label = None
    if not end_of_file() and current_token().type == 'AS':
      advance()
      label = parse_identifier()
    return ImpCallExpr(meta_from_tokens(start, previous_token()), call, label)
  return parse_term()

def parse_imp_var(ghost: bool) -> ImpVar:
  start = current_token()
  advance()  # consume "var"
  name = parse_identifier()
  type_annot = None
  if not end_of_file() and current_token().type == 'COLON':
    advance()
    type_annot = parse_type()
  consume_token('ASSIGN', '":="', context='after variable name of "var"')
  rhs = parse_imp_rhs()
  return ImpVar(meta_from_tokens(start, previous_token()), name, type_annot,
                rhs, ghost)

def parse_imp_proof() -> Proof:
  # Parse the proof supplied after `by` in an imperative proof clause. A
  # qualified call-postcondition reference (`h.valid_post`) is signalled by an
  # identifier immediately glued to a field access (`.valid_post`, one
  # FIELDACCESS token); anything else is an ordinary proof expression (which
  # also covers a bare proof-slot label, parsed as a `PVar`).
  if current_token().type == 'IDENT' and not end_of_file() \
     and current_position + 1 < len(token_list) \
     and next_token().type == 'FIELDACCESS':
    start = current_token()
    subject = parse_identifier()
    field = current_token().value[1:]
    advance()  # consume FIELDACCESS
    return PostconditionRef(meta_from_tokens(start, previous_token()),
                            subject, field)
  return parse_proof(allow_missing=False)

def parse_loop_specs() -> tuple[list[Term], list[FrameTerm
                                                  | FrameFootprint | FrameEmpty],
                                Optional[Term], Optional[Proof],
                                Optional[Proof], Optional[Proof]]:
  invariants: list[Term] = []
  modifies: list[FrameTerm | FrameFootprint | FrameEmpty] = []
  decreases: Optional[Term] = None
  decreases_proof: Optional[Proof] = None
  established: Optional[Proof] = None
  preserved: Optional[Proof] = None
  while not end_of_file() and current_token().value in (
      'invariant', 'modifies', 'decreases', 'established', 'preserved'):
    keyword = current_token().value
    advance()
    if keyword == 'invariant':
      invariants.append(parse_term())
    elif keyword == 'modifies':
      modifies.extend(parse_frame_list())
    elif keyword == 'established':
      consume_token('BY', '"by"', context='after "established"')
      established = parse_imp_proof()
    elif keyword == 'preserved':
      consume_token('BY', '"by"', context='after "preserved"')
      preserved = parse_imp_proof()
    else:
      decreases = parse_term()
      if not end_of_file() and current_token().type == 'BY':
        advance()
        decreases_proof = parse_imp_proof()
  return invariants, modifies, decreases, established, preserved, \
      decreases_proof

def parse_imp_stmt() -> ImpStmt:
  require_experimental_imperative(
      meta_from_tokens(current_token(), current_token()))
  start = current_token()
  tok = current_token()
  if tok.value == 'var':
    return parse_imp_var(False)
  if tok.value == 'ghost':
    advance()  # consume "ghost"
    if current_token().value != 'var':
      raise ParseError(meta_from_tokens(current_token(), current_token()),
                       'expected "var" after "ghost", not\n\t'
                       + quote(current_token().value))
    result = parse_imp_var(True)
    return ImpVar(meta_from_tokens(start, previous_token()), result.name,
                  result.type_annot, result.rhs, True)
  if tok.value == 'if':
    advance()
    cond = parse_term()
    then_body = parse_imp_block(context='after condition of "if"')
    else_body = None
    if not end_of_file() and current_token().value == 'else':
      advance()
      else_body = parse_imp_block(context='after "else"')
    return ImpIf(meta_from_tokens(start, previous_token()), cond,
                 then_body, else_body)
  if tok.value == 'while':
    advance()
    cond = parse_term()
    invariants, modifies, decreases, established, preserved, decreases_proof \
        = parse_loop_specs()
    body = parse_imp_block(context='after "while" loop header')
    return ImpWhile(meta_from_tokens(start, previous_token()), cond,
                    invariants, modifies, decreases, body, established,
                    preserved, decreases_proof)
  if tok.value == 'assert':
    advance()
    formula = parse_term()
    proof = None
    if not end_of_file() and current_token().type == 'BY':
      advance()
      proof = parse_imp_proof()
    return ImpAssert(meta_from_tokens(start, previous_token()), formula, proof)
  if tok.value == 'assume':
    advance()
    return ImpAssume(meta_from_tokens(start, previous_token()), parse_term())
  if tok.value == 'call':
    advance()
    call = parse_term()
    label = None
    if not end_of_file() and current_token().type == 'AS':
      advance()
      label = parse_identifier()
    proof = None
    if not end_of_file() and current_token().type == 'BY':
      advance()
      proof = parse_imp_proof()
    return ImpCall(meta_from_tokens(start, previous_token()), call, label,
                   proof)
  if tok.value == 'return':
    advance()
    return ImpReturn(meta_from_tokens(start, previous_token()), parse_term())
  lhs = parse_imp_lvalue()
  consume_token('ASSIGN', '":="', context='after assignment target')
  rhs = parse_imp_rhs()
  return ImpAssign(meta_from_tokens(start, previous_token()), lhs, rhs)

def parse_observer_reads_list() -> list[list[FrameTerm | FrameFootprint | FrameEmpty]]:
  clauses: list[list[FrameTerm | FrameFootprint | FrameEmpty]] = []
  while not end_of_file() and current_token().value == 'reads':
    require_experimental_imperative(
        meta_from_tokens(current_token(), current_token()))
    advance()
    clauses.append(parse_frame_list())
  return clauses

def parse_observer_decl(visibility: str) -> Statement:
  require_experimental_imperative(meta_from_tokens(current_token(), current_token()))
  start = current_token()
  advance()
  name = parse_identifier()
  typarams = parse_type_parameters()
  consume_token('LPAR', '"("', context='after observer name')
  params = parse_proc_param_list()
  consume_token('RPAR', '")"', context='after observer parameters')
  consume_token('ARROW', '"->"', context='after observer parameters')
  return_type = parse_type()
  reads = parse_observer_reads_list()
  body = None
  if not end_of_file() and current_token().type == 'LBRACE':
    advance()
    body = parse_term()
    consume_token('RBRACE', '"}"', context='after observer body')
  return ObserverDecl(meta_from_tokens(start, previous_token()), name,
                      typarams, params, return_type, reads, body,
                      visibility=visibility)

def parse_resource_decl(visibility: str) -> Statement:
  require_experimental_imperative(meta_from_tokens(current_token(), current_token()))
  start = current_token()
  advance()
  name = parse_identifier()
  typarams = parse_type_parameters()
  consume_token('LPAR', '"("', context='after resource name')
  params = parse_proc_param_list()
  consume_token('RPAR', '")"', context='after resource parameters')
  body = None
  if not end_of_file() and current_token().type == 'LBRACE':
    advance()
    body = parse_term()
    consume_token('RBRACE', '"}"', context='after resource body')
  return ResourceDecl(meta_from_tokens(start, previous_token()), name,
                      typarams, params, body, visibility=visibility)

statement_keywords = {'assert', 'define', 'import', 'inductive', 'object',
                      'observer',
                      'print',
                      'theorem', 'lemma', 'postulate', 'predicate', 'recursive',
                      'relation', 'fun', 'trace', 'type', 'union', 'view',
                      'proc', 'resource'}

def parse_statement() -> Statement:
  if end_of_file():
      raise ParseError(meta_from_tokens(previous_token(),previous_token()),
            'expected a statement, not end of file')
  token = current_token()

  if token.type in accessiblity_keywords:
    visibility = token.value
    advance()
  else:
    visibility = 'default'

  token = current_token()

  if token.type == 'DEFINE':
    return parse_define(visibility)

  elif token.type == 'FUN':
    return parse_function(visibility)

  elif token.type == 'RECURSIVE':
    return parse_recursive_function(visibility)

  elif token.value == 'proc':
    return parse_proc_decl(visibility)

  elif token.type == 'UNION':
    return parse_union(visibility)

  elif token.type == 'TYPE':
    return parse_type_alias(visibility)

  elif token.type == 'OBJECT':
    return parse_object(visibility)

  elif token.type == 'OBSERVER':
    return parse_observer_decl(visibility)

  elif token.type == 'RESOURCE':
    return parse_resource_decl(visibility)

  elif token.type == 'PREDICATE':
    return parse_predicate(visibility, 'predicate')

  elif token.type == 'RELATION':
    return parse_predicate(visibility, 'relation')

  elif token.type == 'RECFUN':
    return parse_gen_rec_function(visibility)

  elif token.type == 'VIEW':
    return parse_view_decl(visibility)

  elif token.type == 'PROC':
    return parse_proc_decl(visibility)

  elif token.type == 'ASSERT':
    while_parsing = 'while parsing assert\n' \
        + '\tstatement ::= "assert" formula\n'
    advance()
    try:
        body = parse_term()
        return Assert(meta_from_tokens(token, previous_token()), body)
    except ParseError as e:
      raise e.extend(meta_from_tokens(token, previous_token()), while_parsing)
    except Exception as e:
      raise ParseError(meta_from_tokens(token, previous_token()), "Unexpected error while parsing:\n\t" \
        + str(e))
  elif token.type == 'THEOREM' or token.type == 'LEMMA' or token.type == 'POSTULATE':
    return parse_theorem(visibility)

  elif token.type == 'EXPORT':
    while_parsing = 'while parsing import\n' \
        + '\tstatement ::= "export" identifier\n'
    advance()
    try:
        name = parse_identifier()
        return Export(meta_from_tokens(token, previous_token()), name)
    except ParseError as e:
      raise e.extend(meta_from_tokens(token, previous_token()), while_parsing)
    except Exception as e:
      raise ParseError(meta_from_tokens(token, previous_token()), "Unexpected error while parsing:\n\t" \
        + str(e))

  elif token.type == 'IMPORT':
    while_parsing = 'while parsing import\n' \
        + '\tstatement ::= "import" identifier ["using" | "hiding" name ("|" name)*]\n'
    advance()
    try:
        name = parse_identifier()
        using = None
        hiding = None
        if not end_of_file() and current_token().type in ('USING', 'HIDING'):
          clause = current_token().type
          advance()
          names = [parse_identifier()]
          while not end_of_file() and current_token().type == 'VBAR':
            advance()
            names.append(parse_identifier())
          if clause == 'USING':
            using = names
          else:
            hiding = names
        return Import(meta_from_tokens(token, previous_token()),
                      name, using=using, hiding=hiding,
                      visibility=visibility)
    except ParseError as e:
      raise e.extend(meta_from_tokens(token, previous_token()), while_parsing)
    except Exception as e:
      raise ParseError(meta_from_tokens(token, previous_token()), "Unexpected error while parsing:\n\t" \
        + str(e))

  elif token.type == 'PRINT':
    while_parsing = 'while parsing\n' \
        + '\tstatement ::= "print" term\n'
    advance()
    try:
        subject = parse_term()
        meta = meta_from_tokens(token, previous_token())
        return Print(meta, subject)
    except ParseError as e:
        raise e.extend(meta_from_tokens(token, previous_token()), while_parsing)
    except Exception as e:
        raise ParseError(meta_from_tokens(token, previous_token()), "Unexpected error while parsing:\n\t" \
          + str(e))

  elif token.type == 'AUTO':
    advance()
    pvar = parse_proof_hi()
    meta = meta_from_tokens(token, previous_token())
    return Auto(meta, pvar)

  elif token.type == 'ASSOCIATIVE':
    advance()
    name = parse_identifier()
    typarams = parse_type_parameters()
    advance()

    typ = parse_type()
    meta = meta_from_tokens(token, previous_token())
    return Associative(meta, typarams, Var(meta, None, name), typ)

  elif token.type == 'INDUCTIVE':
    start = current_token()
    advance()
    ty = parse_type()
    consume_token('BY', '"by"', context='after type part of "inductive"')
    pf = parse_proof_hi()
    meta = meta_from_tokens(start, previous_token())
    return Inductive(meta, ty, pf)


  elif token.type == 'MODULE':
    advance()
    name = parse_identifier()
    meta = meta_from_tokens(token, previous_token())
    return Module(meta, name)

  elif token.type == 'TRACE':
    advance()
    fun = parse_identifier()
    my_meta = meta_from_tokens(token, previous_token())
    var_meta = meta_from_tokens(previous_token(), previous_token())
    return Trace(my_meta, Var(var_meta, None, fun))

  else:
    for kw in statement_keywords:
        if edit_distance(token.value, kw) <= 2:
            raise ParseError(meta_from_tokens(token, token),
                  'did you mean "' + kw \
                  + '" instead of "' + token.value + '"?')

    if token.value == '/' and current_position + 1 < len(token_list) and next_token().value == '*':
      raise ParseError(meta_from_tokens(token, token),
        "expected a statement, not '/*', did you forget to close a comment?")
    raise ParseError(meta_from_tokens(token, token),
          'expected a statement, not\n\t' + token.value)

def parse_type_parameters() -> list[str]:
  if not end_of_file() and current_token().type == 'LESSTHAN':
      advance()
      ident_list = parse_ident_list()
      consume_token('MORETHAN', '>', context='after type parameters of "fn"')
      return ident_list
  else:
      return []

def parse_type() -> Type:
  if end_of_file():
      raise ParseError(meta_from_tokens(previous_token(),previous_token()),
            'expected a type, not end of file')

  token = current_token()
  if token.type == 'BOOL':
    advance()
    return BoolType(meta_from_tokens(token,token))
  if token.type == 'TYPE':
    advance()
    return TypeType(meta_from_tokens(token,token))
  elif token.type == 'FN':
    return parse_function_type()
  elif token.type == 'LSQB':
    advance()
    elt_type = parse_type()
    consume_token('RSQB', 'closing "]"')
    if not end_of_file() and current_token().value == '!':
      require_experimental_imperative(meta_from_tokens(current_token(), current_token()))
      advance()
      return MutableArrayType(meta_from_tokens(token, previous_token()),
                              elt_type)
    return ArrayType(meta_from_tokens(token, previous_token()), elt_type)
  elif token.type == 'LPAR':
    start_token = current_token()
    advance()
    typ = parse_type()
    consume_token('RPAR', 'closing ")"')
    return typ
  else:
    try:
      name = parse_identifier()
    except ParseError:
      raise ParseError(meta_from_tokens(token, current_token()),
            'expected a type, not\n\t' + quote(current_token().value))
    except Exception as e:
      raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
        + str(e))

    var = Var(meta_from_tokens(token,token), None, name)
    inst = False

    if not end_of_file() and current_token().type == 'LESSTHAN':
      inst = True
      start_token = current_token()
      advance()
      arg_types = parse_type_list()
      consume_token('MORETHAN', 'a closing ">"')
    if inst:
        return TypeInst(meta_from_tokens(token, previous_token()),
                        var, arg_types)
    else:
        return var

def parse_function_type() -> Type:
  while_parsing = 'while parsing\n' \
      + '\ttype ::= "fn" type_params_opt type_list "->" type\n' \
      + '\t       | "fn" type_params_opt "(" type "," type_list ")" "->" type\n'
  try:
    start_token = current_token()
    advance()
    type_params = parse_type_parameters()
    if current_token().type == 'LPAR':
      advance()
      first_type = parse_type()
      if current_token().type == 'COMMA':
        advance()
        rest_types = parse_type_list()
        param_types = [first_type] + rest_types
        consume_token('RPAR', 'closing ")"',
                      context='after parenthesized parameter types')
      else:
        consume_token('RPAR', 'closing ")"')
        param_types = [first_type]
    else:
      param_types = parse_type_list()
    consume_token('ARROW', '"->"', context='after parameter types')
    return_type = parse_type()
    return FunctionType(meta_from_tokens(start_token, previous_token()),
                        type_params, param_types, return_type)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
      + str(e))


def parse_type_list() -> list[Type]:
  typ = parse_type()
  type_list = [typ]
  while current_token().type == 'COMMA':
    advance()
    typ = parse_type()
    type_list.append(typ)
  return type_list

def parse_term_list(end: str) -> list[Term]:
  if current_token().type == end:
      return []
  else:
      trm = parse_term()
      trm_list = [trm]
  while current_token().type == 'COMMA':
    advance()
    trm = parse_term()
    trm_list.append(trm)
  return trm_list

def parse_nonempty_term_list() -> list[Term]:
  trm = parse_term()
  trm_list = [trm]
  while current_token().type == 'COMMA':
    advance()
    trm = parse_term()
    trm_list.append(trm)
  return trm_list

def parse_constructor() -> Constructor:
  while_parsing = 'while parsing\n' \
      + '\tconstructor ::= identifier | identifier "(" type_list ")"'
  try:
    start_token = current_token()
    name = parse_identifier()

    if current_token().type == 'LPAR':
      advance()
      param_types = parse_type_list()
      consume_token('RPAR', 'closing parenthesis ")"')
    else:
      param_types = []
    meta = meta_from_tokens(start_token, previous_token())
    return Constructor(meta, name, param_types)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
      + str(e))


def parse_constructor_pattern() -> Pattern:
  start_token = current_token()
  constr_name = parse_identifier()
  ident_list = []
  if current_token().type == 'LPAR':
    advance()
    ident_list = parse_ident_list()
    consume_token('RPAR', 'closing parenthesis ")"')
  return PatternCons(meta_from_tokens(start_token, previous_token()),
                     Var(meta_from_tokens(start_token,
                                          start_token),
                         None, constr_name),
                     ident_list)


def parse_pattern() -> Pattern:
  if current_token().value == '0':
    advance()
    meta = meta_from_tokens(current_token(), current_token())
    return PatternCons(meta, Var(meta, None, 'zero'), [])
  if current_token().type == 'LSQB' and next_token().type == 'RSQB':
    advance()
    advance()
    meta = meta_from_tokens(current_token(), current_token())
    return PatternCons(meta, Var(meta, None, 'empty'), [])
  elif current_token().type == 'TRUE':
    advance()
    meta = meta_from_tokens(current_token(), current_token())
    return PatternBool(meta, True)
  elif current_token().type == 'FALSE':
    advance()
    meta = meta_from_tokens(current_token(), current_token())
    return PatternBool(meta, False)
  elif current_token().type == 'WITH':
    start_token = current_token()
    advance()
    idents = parse_ident_list()
    consume_token('DOT', '"."', context='after parameters in induction case')
    term = parse_term()
    return PatternTerm(meta_from_tokens(start_token, current_token()), term, idents)
  else:
    start_token = current_token()
    try:
      return parse_constructor_pattern()
    except ParseError:
      raise ParseError(meta_from_tokens(start_token, current_token()),
            'expected a pattern, not\n\t' + quote(current_token().value))
    except Exception as e:
      raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
        + str(e))

def parse_pattern_list() -> list[Pattern | str]:
  pat = parse_pattern()
  if current_token().type == 'COMMA':
    advance()
    ident_list = parse_ident_list()
    return [pat] + ident_list
  else:
    return [pat]

def parse_ident_list() -> list[str]:
  ident = parse_identifier()
  ident_list = [ident]
  while current_token().type == 'COMMA':
    advance()
    ident = parse_identifier()
    ident_list.append(ident)
  return ident_list

def parse_single_or_repeat() -> list[str]:
  if current_token().type == 'INT':
      num = int(current_token().value)
      advance()
      advance()
      ident = parse_identifier()
      ident_list = num * [ident]
  else:
      ident = parse_identifier()
      ident_list = [ident]
  return ident_list

def parse_ident_list_bar() -> list[str]:
  ident_list = parse_single_or_repeat()
  while current_token().value == '|':
    advance()
    ident_list += parse_single_or_repeat()
  return ident_list

def parse_type_annot_list() -> list[tuple[str, Type]]:
  start_tok = current_token()
  ident = parse_identifier()
  if current_token().type == 'COLON':
    advance()
    ty = parse_type()
  else:
    raise ParseError(meta_from_tokens(current_token(), current_token()), "Missing type annotation. Expected ':' followed by a type.\n" \
          + error_header(meta_from_tokens(start_tok, current_token())) \
          + 'while parsing\n\ttype_annot_list ::= identifier ":" type' \
          + '\n\ttype_annot_list ::= identifier ":" type "," type_annot_list')
  type_annot_list = [(ident,ty)]

  while current_token().type == 'COMMA':
    advance()
    ident = parse_identifier()
    if current_token().type == 'COLON':
      advance()
      ty = parse_type()
    else:
      raise ParseError(meta_from_tokens(current_token(), current_token()), "Missing type annotation. Expected ':' followed by a type.\n" \
          + error_header(meta_from_tokens(start_tok, current_token())) \
          + 'while parsing\n\ttype_annot_list ::= identifier ":" type' \
          + '\n\ttype_annot_list ::= identifier ":" type "," type_annot_list')
    type_annot_list.append((ident, ty))
  return type_annot_list

def parse_var_list() -> list[tuple[str, Type | None]]:
  if current_token().type == 'RPAR':
      return []

  ident = parse_identifier()
  if current_token().type == 'COLON':
    advance()
    ty = parse_type()
  else:
    ty = None
  var_list = [(ident,ty)]

  while current_token().type == 'COMMA':
    advance()
    ident = parse_identifier()
    if current_token().type == 'COLON':
      advance()
      ty = parse_type()
    else:
      ty = None
    var_list.append((ident, ty))
  return var_list

def parse_fun_case() -> FunCase:
  while_parsing = 'while parsing\n' \
      + '\tfun_case ::= identifier "(" param_list ")" "=" term\n'
  try:
    start_token = current_token()
    rator = parse_identifier()
    rator_meta = meta_from_tokens(start_token, previous_token())

    if current_token().type == 'LPAR':
      advance()
      pat_list = parse_pattern_list()
      consume_token('RPAR', 'closing parenthesis ")"')
    consume_token('EQUAL', '"=" and then a term',)
    body = parse_term()
    meta = meta_from_tokens(start_token, previous_token())
    return FunCase(meta, Var(rator_meta, None, rator),
                   pat_list[0], pat_list[1:], body)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
      + str(e))

def quote(text: str) -> str:
    return '"' + text + '"'

def parse_switch_case() -> SwitchCase:
    while_parsing = 'while parsing\n' \
        + '\tswitch_case ::= "case" pattern "{" term "}"'
    start_token = current_token()
    advance()
    try:
        pattern = parse_pattern()
        consume_token('LBRACE', '"{"', context='after pattern of case')
        body = parse_term()
        consume_token('RBRACE', '"}"', context='after body of case')
    except ParseError as e:
        raise e.extend(meta_from_tokens(start_token, current_token()), while_parsing)
    except Exception as e:
        raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
          + str(e))

    return SwitchCase(meta_from_tokens(start_token, previous_token()),
                      pattern, body)
