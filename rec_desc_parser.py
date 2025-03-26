# The motivation for this recursive-descent version of the parser
# is to provide better error messages. -Jeremy

from abstract_syntax import *
from lark import Lark, Token, logger, exceptions, tree
from error import *
from edit_distance import closest_keyword, edit_distance

filename = '???'

def set_filename(fname):
    global filename
    filename = fname

def get_filename():
    global filename
    return filename


deduce_directory = '???'

def set_deduce_directory(dir):
    global deduce_directory
    deduce_directory = dir

def get_deduce_directory():
    global deduce_directory
    return deduce_directory

expt_operators = { '^' }
mult_operators = {'*', '/', '%', '∘', '.o.'}
add_operators = {'+', '-', '∪', '|', '∩', '&', '⨄', '.+.', '++', '⊝' }
compare_operators = {'<', '>', '≤', '<=', '≥', '>=', '⊆', '(=', '∈', 'in'}
equal_operators = {'=', '≠', '/='}
iff_operators = {'iff', "<=>", "⇔"}

to_unicode = {'.o.': '∘', '|': '∪', '&': '∩', '.+.': '⨄', '<=': '≤', '>=': '≥',
              '(=': '⊆', 'in': '∈', '.0.': '∅', '<=>': '⇔', 'iff': '⇔'}

lark_parser = None

def init_parser():
  global lark_parser
  lark_file = get_deduce_directory() + "/Deduce.lark"
  lark_parser = Lark(open(lark_file, encoding="utf-8").read(),
                     start='program',
                     debug=True, propagate_positions=True)

# The current_position needs to be a global so that the changes to the
# current_position don't get discarded when an exception is
# thrown. -Jeremy

current_position = 0
token_list = []

def current_token():
  if end_of_file():
    raise ParseError(meta_from_tokens(token_list[-1], token_list[-1]),
          'Expected a token, got end of file')
  return token_list[current_position]

def next_token():
  if current_position + 1 >= len(token_list):
    raise ParseError(meta_from_tokens(token_list[-1], token_list[-1]),
          'Expected a token, got end of file')
  return token_list[current_position + 1]

def previous_token():
    return token_list[current_position - 1]

def advance():
    global current_position
    current_position = current_position + 1
    
def end_of_file():
    return current_position >= len(token_list)


def parse(program_text, trace = False, error_expected = False):
  global token_list, current_position
  lexed = lark_parser.lex(program_text)
  token_list = []
  current_position = 0
  for token in lexed:
    if trace:
      print(repr(token))
    token_list.append(token)

  stmts = []
  while not end_of_file():
    stmt = parse_statement()
    stmts.append(stmt)
  return stmts


def parse_identifier():
  if end_of_file():
    raise ParseError(meta_from_tokens(previous_token(), previous_token()),
          'expected an identifier, not end of file')
  token = current_token()      
  if token.type == 'IDENT':
    advance()
    return token.value
  elif current_token().value == 'operator':
    advance()
    rator = current_token().value
    advance()
    return to_unicode.get(rator, rator)
  else:
    raise ParseError(meta_from_tokens(token, token),
          'expected an identifier, not\n\t' + quote(token.value))

def meta_from_tokens(start_token, end_token):
    meta = Meta()
    meta.empty = False
    meta.filename = get_filename()
    meta.line = start_token.line
    meta.column = start_token.column
    meta.start_pos = start_token.start_pos
    meta.end_line = end_token.end_line
    meta.end_column = end_token.end_column
    meta.end_pos = end_token.end_pos
    return meta
      
def parse_term_hi():
  token = current_token()
  
  if token.type == 'ALL':
    advance()
    vars = parse_type_annot_list()
    if current_token().type != 'DOT':
      raise ParseError(meta_from_tokens(current_token(), current_token()),
            'expected "." after parameters of "all", not\n\t' \
            + current_token().value \
            + '\nwhile parsing\n' \
            + '\tterm ::= "all" var_list "." term')
    advance()
    body = parse_term()
    meta = meta_from_tokens(token, previous_token())
    result = body
    for j, var in enumerate(reversed(vars)):
      result = All(meta, None, var, (j, len(vars)), result)
    return result
  elif token.type == 'AT':
    advance()
    subject = parse_term_hi()
    if current_token().type != 'LESSTHAN':
      raise ParseError(meta_from_tokens(current_token(),current_token()),
            'expected "<" after subject of instantiation ("@"), not\n\t' \
            + current_token().value \
            + '\nwhile parsing\n' \
            + '\tterm ::= "@" term "<" type_list ">"')
    advance()
    type_args = parse_type_list()
    if current_token().type != 'MORETHAN':
      raise ParseError(meta_from_tokens(current_token(),current_token()),
            'expected closing ">" after type arguments of instantiation ("@")' \
            + ' , not\n\t' + current_token().value \
            + '\nwhile parsing\n' \
            + '\tterm ::= "@" term "<" type_list ">"')
    advance()
    meta = meta_from_tokens(token, previous_token())
    return TermInst(meta, None, subject, type_args, False)

  elif token.type == 'FALSE':
    advance()
    return Bool(meta_from_tokens(token,token), None, False)

  elif token.type == 'INT' or token.value == '0':
    advance()
    return intToNat(meta_from_tokens(token,token), int(token.value))

  elif token.type == 'PLUS':
    advance()
    intToken = current_token()
    if intToken.type == 'INT' or intToken.value == '0':
      advance()
      return intToDeduceInt(meta_from_tokens(intToken,intToken),
                             int(intToken.value), token.type)
    else: 
      raise ParseError(meta_from_tokens(current_token(),current_token()),
            'expected an integer not\n\t' + current_token().value)

  elif token.type == 'IF':
    advance()
    prem = parse_term()
    if current_token().type != 'THEN':
      raise ParseError(meta_from_tokens(current_token(),current_token()),
            'expected keyword "then" after premise of "if" formula, not\n\t' \
            + current_token().value \
            + '\nwhile parsing\n' \
            + '\tformula ::= "if" formula "then" formula')
    advance()
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
    return Call(meta, None,
                Var(meta, None, 'char_fun'),
                [Lambda(meta, None, [('_',None)], Bool(meta, None, False))])

  elif token.type == 'FUN' or token.type == 'Λ':
    advance()
    type_params = parse_type_parameters()
    params = parse_var_list()
    if current_token().type != 'LBRACE':
      raise ParseError(meta_from_tokens(token, current_token()),
            'expected "{" after parameters of fun, not\n\t' \
            + current_token().value)
    advance()
    body = parse_term()
    if current_token().type != 'RBRACE':
      raise ParseError(meta_from_tokens(token, previous_token()),
            'expected "}" after body of "fun", not\n\t' + current_token().value)
    advance()
    meta = meta_from_tokens(token, previous_token())
    if len(type_params) > 0:
      return Generic(meta, None, type_params, Lambda(meta, None, params, body))
    else:
      return Lambda(meta, None, params, body)

  elif token.type == 'GENERIC':
    advance()
    params = parse_ident_list()
    if current_token().type != 'LBRACE':
      raise ParseError(meta_from_tokens(token, current_token()),
            'expected "{" after parameters of "generic", not\n\t' \
            + current_token().value)
    advance()
    body = parse_term()
    if current_token().type != 'RBRACE':
      raise ParseError(meta_from_tokens(token, current_token()),
            'expected "}" after body of "generic", not\n\t' \
            + current_token().value)
    advance()
    meta = meta_from_tokens(token, previous_token())
    return Generic(meta, None, params, body)
    
  elif token.type == 'LESSTHAN':
    advance()
    type_params = parse_ident_list()
    if current_token().type != 'MORETHAN':
      raise ParseError(meta_from_tokens(token, previous_token()),
            'expected closing ">" after type parameters')
    advance()
    body = parse_term()
    meta = meta_from_tokens(token, previous_token())
    result = body
    for j, ty in enumerate(reversed(type_params)):
      result = All(meta, None, (ty, TypeType(meta)), (j, len(type_params)), result)
    return result
    
  elif token.type == 'LPAR':
    advance()
    while_parsing = 'while parsing parenthesized term\n' \
        + '\tterm ::= "(" term ")"\n'

    term = parse_term()
    if current_token().type != 'RPAR':
      raise ParseError(meta_from_tokens(current_token(), current_token()),
            'expected closing parenthesis ")", not\n\t' \
            + current_token().value + '\n' + while_parsing)
    advance()
    return term

  elif token.type == 'HASH':
    advance()
    term = parse_term()
    if current_token().type != 'HASH':
      raise ParseError(meta_from_tokens(current_token(), current_token()),
            'expected closing hash "#", not\n\t' \
            + current_token().value)
    advance()
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
    return Call(meta, None, Var(meta, None, '-', []), [subject])

  elif token.type == 'NOT':
    advance()
    subject = parse_term_equal()
    meta = meta_from_tokens(token, previous_token())
    return IfThen(meta, None, subject, Bool(meta, None, False))
    
  elif token.type == 'QMARK':
    advance()
    meta = meta_from_tokens(token,token)
    return Hole(meta, None)

  elif token.type == 'SOME':
    advance()
    vars = parse_type_annot_list()
    if current_token().type != 'DOT':
      raise ParseError(meta_from_tokens(token, current_token()),
            'expected "." after parameters of "some", not\n\t' \
            + current_token().value)
    advance()
    body = parse_term()
    return Some(meta_from_tokens(token, previous_token()),
                None, vars, body)

  elif token.type == 'SWITCH':
    advance()
    subject = parse_term()
    if current_token().type != 'LBRACE':
      raise ParseError(meta_from_tokens(current_token(), current_token()),
            'expected "{" after subject of "switch", not\n\t' \
            + current_token().value)
    advance()
    cases = []
    while current_token().type == 'CASE':
      switch_case = parse_switch_case()
      cases.append(switch_case)
    if current_token().type != 'RBRACE':
      raise ParseError(meta_from_tokens(token,current_token()),
            'expected "}" after last case of "switch", not\n\t' \
            + current_token().value)
    advance()
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
    if token.type != 'RSQB':
      raise ParseError(meta_from_tokens(current_token(),current_token()),
            'expected closing bracket "]" at end of list literal, not\n\t' + current_token().value)
    advance()
    return listToNodeList(meta_from_tokens(token,token), lst_terms)
  
  elif token.type == 'DEFINE':
    return parse_define_term()
  
  else:
    try:
      name = parse_identifier()
      meta = meta_from_tokens(token, token)
      var = Var(meta, None, name)
      return var
    except ParseError as e:  
      raise ParseError(meta_from_tokens(token, current_token()),
            'expected a term, not\n\t' + quote(current_token().value))
    except Exception as e:
      raise ParseError(meta_from_tokens(token, previous_token()), "Unexpected error while parsing:\n\t" \
        + str(e))

def parse_array_get():
  while_parsing = 'while parsing array access\n' \
      + '\tterm ::= term "[" term "]"\n'
  term = parse_term_hi()

  while (not end_of_file()) and current_token().type == 'LSQB':
    try:
      start_token = current_token()
      advance()
      index = parse_term()
      if current_token().type != 'RSQB':
        raise ParseError(meta_from_tokens(start_token, current_token()),
              'expected closing "]", not\n\t' \
              + current_token().value)
      term = ArrayGet(meta_from_tokens(start_token, current_token()), None,
                      term, index)
      advance()
    except ParseError as e:
      raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
    except Exception as e:
      raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
        + str(e))

  return term
    
def parse_call():
  while_parsing = 'while parsing function call\n' \
      + '\tterm ::= term "(" term_list ")"\n'
  start_token = current_token()
  term = parse_array_get()

  while (not end_of_file()) and current_token().type == 'LPAR':
    try:
      advance()
      args = parse_term_list('RPAR')
      if current_token().type != 'RPAR':
        msg = 'expected closing parenthesis ")", not\n\t' \
          + current_token().value \
          + '\nPerhaps you forgot a comma?'
        raise ParseError(meta_from_tokens(start_token, previous_token()), msg)
      term = Call(meta_from_tokens(start_token, current_token()), None,
                  term, args)
      advance()
    except ParseError as e:
      raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
    except Exception as e:
      raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
        + str(e))

  return term

def parse_make_array():
  if current_token().value == 'array':
    while_parsing = 'while parsing array creation\n' \
        + '\tterm ::= "array" "(" term ")"\n'
    start_token = current_token()
    advance()
    try:
      if current_token().type != 'LPAR':
        raise ParseError(meta_from_tokens(start_token, current_token()),
                'expected open parenthesis "(", not\n\t' \
                + current_token().value)
      advance()
      arg = parse_term()
      if current_token().type != 'RPAR':
        raise ParseError(meta_from_tokens(start_token, current_token()),
              'expected closing parenthesis ")", not\n\t' \
              + current_token().value)
      term = MakeArray(meta_from_tokens(start_token, current_token()),None,arg)
      advance()
    except ParseError as e:
      raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
    except Exception as e:
      raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
        + str(e))
  else:
    term = parse_call()
  return term


def parse_term_expt():
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
    
def parse_term_mult():
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

def parse_term_add():
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

def parse_term_compare():
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

def parse_term_equal():
  token = current_token()
  term = parse_term_compare()
  while (not end_of_file()) and current_token().value in equal_operators:
    meta = meta_from_tokens(current_token(), current_token())
    opr = current_token().value
    eq = Var(meta, None, '=')
    advance()
    right = parse_term_equal()
    call_meta = meta_from_tokens(token, previous_token())
    if opr == '=':
      term = Call(call_meta, None,
                  eq, [term,right])
    elif opr == '≠' or opr == '/=':
      term = IfThen(call_meta, None, 
                    Call(call_meta, None, eq, [term,right]),
                    Bool(call_meta, None, False))
  return term
    
def parse_term_logic():
  token = current_token()
  term = parse_term_equal()
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

def parse_term_iff():
  token = current_token()
  term = parse_term_logic()
  while (not end_of_file()) and (current_token().value in iff_operators):
    opr = current_token().type
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

def parse_term():
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

def parse_define_term():
  while_parsing = 'while parsing\n' \
      + '\tterm ::= "define" identifier "=" term ";" term\n'
  try:
    start_token = current_token()
    advance()
    name = parse_identifier()
    if current_token().type != 'EQUAL':
        raise ParseError(meta_from_tokens(current_token(),current_token()),
              'expected "=" after name in "define", not\n\t' \
              + quote(current_token().value))
    advance()
    rhs = parse_term_logic()
    if current_token().type != 'SEMICOLON':
        raise ParseError(meta_from_tokens(current_token(),current_token()),
              'expected ";" after right-hand side of "define", not\n\t' \
              + quote(current_token().value))
    advance()
    meta = meta_from_tokens(start_token, previous_token())
    body = parse_term()
    return TLet(meta, None, name, rhs, body)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
      + str(e))
      
def parse_assumption():
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
                  'cases', 'choose', 'conclude', 'conjunct',
                  'definition',
                  'equations', 'evaluate', 'extensionality',
                  'have', 'induction', 'injective', 'obtain',
                  'recall', 'reflexive', 'rewrite',
                  'suffices', 'suppose', 'switch', 'symmetric',
                  'transitive'}

def parse_definition_proof():
  while_parsing = 'while parsing definition:\n' \
      + '\tconclusion ::= "definition" identifier_list_bar\n'
  token = current_token()
  advance()
  try:
    if current_token().type == 'LBRACE':
      advance()
      defs = parse_ident_list()
      if current_token().type != 'RBRACE':
          raise ParseError(meta_from_tokens(current_token(), current_token()),
                'expected closing "}", not\n\t' + current_token().value \
                  + '\nPerhaps you forgot a comma?')
      advance()
    else:
      defs = parse_ident_list_bar()

    if current_token().type == 'AND':
        while_parsing = 'while parsing definition:\n' \
            + '\tconclusion ::= "definition" identifier_list_bar "and" "rewrite" proof_list\n'
        advance()
        if (current_token().type != 'REPLACE') and (current_token().type != 'REWRITE'):
            raise ParseError(meta_from_tokens(current_token(),current_token()),
                  'expected "replace" after "and" and "definition", not\n\t' \
                  + current_token().value)
        advance()
        eqns = parse_proof_list()
        meta = meta_from_tokens(token, previous_token())
        return ApplyDefsGoal(meta,
                              [Var(meta, None, t) for t in defs],
                              Rewrite(meta, eqns))
    elif current_token().type == 'IN':
        while_parsing = 'while parsing definition:\n' \
            + '\tconclusion ::= "definition" identifier_list_bar "in" proof\n'
        advance()
        subject = parse_proof()
        meta = meta_from_tokens(token, previous_token())
        return ApplyDefsFact(meta, [Var(meta, None, t) for t in defs],
                              subject)
    else:
        meta = meta_from_tokens(token, previous_token())
        return ApplyDefs(meta, [Var(meta, None, n) for n in defs])
  except ParseError as e:
      raise e.extend(meta_from_tokens(token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(token, previous_token()), "Unexpected error while parsing:\n\t" \
      + str(e))
      
def parse_recall():
  start_token = current_token()
  advance()
  facts = parse_nonempty_term_list()
  meta = meta_from_tokens(start_token, previous_token())
  return PRecall(meta, facts)
  
def parse_proof_hi():
  token = current_token()
  if token.type == 'APPLY':
    while_parsing = 'while parsing apply-to (use a logical implication)\n' \
        + '\tconclusion ::= "apply" proof "to" proof\n'
    advance()
    try:
      imp = parse_proof()
      if current_token().type != 'TO':
        raise ParseError(meta_from_tokens(current_token(), current_token()),
              'expected "to" after implication part of "apply", not\n\t' \
              + current_token().value)
      advance()
      arg = parse_proof()
      return ModusPonens(meta_from_tokens(token, previous_token()), imp, arg)
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
      subject = parse_proof()
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
      if current_token().type == 'BY':
        advance()
        reason = parse_proof()
      else:
        raise ParseError(meta_from_tokens(current_token(), current_token()),
              'expected the keyword "by" after formula of "conclude", '\
              + 'not\n\t' + current_token().value)
      return PAnnot(meta_from_tokens(token, previous_token()),
                    claim, reason)
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
    if current_token().type != 'OF':
      raise ParseError(meta_from_tokens(current_token(),current_token()),
            'expected keyword "of" after index of "conjunct", not\n\t' \
            + current_token().value)
    advance()
    
    subject = parse_proof()
    meta = meta_from_tokens(token,previous_token())
    return PAndElim(meta, index, subject)
      
  elif token.type == 'DEFINITION':
    return parse_definition_proof()

  elif token.type == 'DOT':
    advance()
    return PTrue(meta_from_tokens(token, token))
  
  elif token.type == 'EQUATIONS':
    advance()
    first = parse_equation()
    rest = parse_equation_list()
    eqs = [first]
    for (lhs, rhs, reason) in rest:
        if lhs == None:
            lhs = eqs[-1][1].copy()
        eqs.append((lhs, rhs, reason))
    result = None
    meta = meta_from_tokens(token, token)
    for (lhs, rhs, reason) in reversed(eqs):
        num_marks = count_marks(lhs) + count_marks(rhs)
        if num_marks == 0 and get_default_mark_LHS():
            new_lhs = Mark(meta, None, lhs)
        else:
            new_lhs = lhs

        eq_proof = PAnnot(meta, mkEqual(meta, new_lhs, rhs), reason)
        if result == None:
            result = eq_proof
        else:
            result = PTransitive(meta, eq_proof, result)
    return result
    
  elif token.type == 'RECALL':
    return parse_recall()
    
  elif token.type == 'INDUCTION':
    return parse_induction()

  elif token.type == 'LPAR':
    advance()
    proof = parse_proof()
    if current_token().type != 'RPAR':
      raise ParseError(meta_from_tokens(current_token(), current_token()),
            'expected closing parenthesis ")" around proof, not\n\t' \
            + current_token().value)
    advance()
    return proof

  elif token.type == 'LBRACE':
    advance()
    proof = parse_proof()
    if current_token().type != 'RBRACE':
      raise ParseError(meta_from_tokens(current_token(), current_token()),
            'expected a closing "}" around proof, not\n\t' \
            + current_token().value)
    advance()
    return proof

  elif token.type == 'QMARK':
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

  elif (token.type == 'REWRITE') or (token.type == 'REPLACE'):
    advance()
    proofs = parse_proof_list()
    if current_token().type == 'IN':
      advance()
      subject = parse_proof()
      meta = meta_from_tokens(token, previous_token())
      return RewriteFact(meta, subject, proofs)
    else:
      meta = meta_from_tokens(token, previous_token())
      return Rewrite(meta, proofs)
    

  elif token.type == 'SWITCH':
    advance()
    subject = parse_term()
    if current_token().type == 'FOR':
        advance()
        defs = parse_ident_list()
    else:
        defs = []
    if current_token().type != 'LBRACE':
      raise ParseError(meta_from_tokens(current_token(), current_token()),
          'expected "{" after subject of "switch", not\n\t' \
          + current_token().value)
    advance()
    cases = []
    while current_token().type == 'CASE':
        c = parse_proof_switch_case()
        cases.append(c)
    if current_token().type != 'RBRACE':
      raise ParseError(meta_from_tokens(token,current_token()),
          'expected "}" after last case of "switch", not\n\t' \
          + current_token().value)
    advance()
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
    close_keyword = closest_keyword(token.value, proof_keywords)
    if close_keyword:
      raise ParseError(meta_from_tokens(token, token),
            'expected a proof.\nDid you mean "' + close_keyword \
            + '" instead of "' + token.value + '"?')
    try:
      name = parse_identifier()
    except ParseError as e:
      raise ParseError(meta_from_tokens(token, current_token()),
                    'expected a proof, not\n\t' + quote(current_token().value),
                    missing=True)
    except Exception as e:
      raise ParseError(meta_from_tokens(token, previous_token()), "Unexpected error while parsing:\n\t" \
        + str(e))

    return PVar(meta_from_tokens(token, token), name)

def parse_proof_list():
  proof_list = []
  proof = parse_proof()
  proof_list.append(proof)
  while (not end_of_file()) and current_token().value == '|':
    advance()
    proof = parse_proof()
    proof_list.append(proof)
  return proof_list

def parse_case():
    start_token = current_token()
    advance()
    label,premise = parse_assumption()
    if current_token().type != 'LBRACE':
      raise ParseError(meta_from_tokens(start_token,current_token()),
            'expected a "{" after assumption of "case", not\n\t' \
            + current_token().value \
            + '\nwhile parsing:\n\t"case" label ":" formula "{" proof "}"')
    advance()
    body = parse_proof()
    if current_token().type != 'RBRACE':
      raise ParseError(meta_from_tokens(start_token,current_token()),
            'expected a "}" after body of "case", not\n\t' + current_token().value)
    advance()
    return (label,premise,body)

def parse_proof_switch_case():
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
    if current_token().type != 'LBRACE':
      raise ParseError(meta_from_tokens(start_token,current_token()),
            'expected a "{" after assumption of "case", not\n\t' \
            + current_token().value \
            + '\nwhile parsing one of the following\n' \
            + '\tswitch_proof_case ::= "case" pattern "{" proof "}"\n' \
            + '\tswitch_proof_case ::= "case" pattern "assume" assumption_list "{" proof "}"')
    advance()
    body = parse_proof()
    if current_token().type != 'RBRACE':
      raise ParseError(meta_from_tokens(start_token,current_token()),
            'expected a "}" after body of case, not\n\t' + current_token().value)
    advance()
    meta = meta_from_tokens(start_token,previous_token())
    return SwitchProofCase(meta, pat, assumptions, body)
    
def parse_proof_med():
    start_token = current_token()
    proof = parse_proof_hi()
    
    while (not end_of_file()) and current_token().type == 'LESSTHAN':
      advance()
      type_list = parse_type_list()
      if current_token().type != 'MORETHAN':
        raise ParseError(meta_from_tokens(start_token,current_token()),
              'expected a closing ">", not\n\t' + current_token().value + '\n'\
              + 'while trying to parse type arguments for instantiation of an "all" formula:\n\t'\
              + 'proof ::= proof "<" type_list ">"')
      advance()
      meta = meta_from_tokens(start_token, previous_token())
      for j, ty in enumerate(type_list):
        proof = AllElimTypes(meta, proof, ty, (j, len(type_list)))
      
    while (not end_of_file()) and current_token().type == 'LSQB':
      advance()
      term_list = parse_nonempty_term_list()
      if current_token().type != 'RSQB':
        raise ParseError(meta_from_tokens(current_token(),current_token()),
              'expected a closing "]", not\n\t' + current_token().value)
      advance()
      meta = meta_from_tokens(start_token, previous_token())
      for j, term in enumerate(term_list):
        proof = AllElim(meta, proof, term, (j, len(term_list)))

    return proof

def parse_proof_statement():
  if end_of_file():
    raise ParseError(meta_from_tokens(previous_token(),previous_token()),
          'expected a proof, not end of file')
      
  token = current_token()
    
  if token.type == 'SUFFICES':
    advance()
    formula = parse_term()
    if current_token().type != 'BY':
      raise ParseError(meta_from_tokens(current_token(), current_token()),
            'expected the keyword "by" after formula of "suffices", not\n\t' \
            + current_token().value)
    advance()
    proof = parse_proof()
    meta = meta_from_tokens(token, previous_token())
    return Suffices(meta, formula, proof, None)
    
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
    return ImpIntro(meta, label, premise, None)

  elif token.type == 'ARBITRARY':
    advance()
    vars = parse_type_annot_list()
    meta = meta_from_tokens(token, previous_token())
    result = None
    for j, var in enumerate(reversed(vars)):
        result = AllIntro(meta, var, (j, len(vars)), result)
    return result
    
  elif token.type == 'CHOOSE':
    advance()
    witnesses = parse_nonempty_term_list()
    meta = meta_from_tokens(token, previous_token())
    return SomeIntro(meta, witnesses, None)
    
  elif token.type == 'OBTAIN':
    advance()
    witnesses = parse_ident_list()
    if current_token().type != 'WHERE':
      raise ParseError(meta_from_tokens(current_token(), current_token()),
            'expected "where" after variables of "obtain", not\n\t' \
            + current_token().value)
    advance()
    label, premise = parse_assumption()
    if current_token().type != 'FROM':
      raise ParseError(meta_from_tokens(current_token(), current_token()),
            'expected "from" after "where" part of "obtain", not\n\t' \
            + current_token().value)
    advance()
    some = parse_proof()
    meta = meta_from_tokens(token, previous_token())
    return SomeElim(meta, witnesses, label, premise, some, None)
    
  elif token.type == 'HAVE':
    return parse_have()

  elif token.type == 'DEFINE':
    return parse_define_proof_stmt()
      
  elif token.type == 'INJECTIVE':
    advance()
    constr = parse_term()
    meta = meta_from_tokens(token, previous_token())
    return PInjective(meta, constr, None)

  elif token.type == 'EXTENSIONALITY':
    advance()
    meta = meta_from_tokens(token, previous_token())
    return PExtensionality(meta, None)

  else:
    return None

def parse_define_proof_stmt():
  while_parsing = 'while parsing\n' \
      + '\tproof_stmt ::= "define" identifier "=" term\n'
  try:
    start_token = current_token()
    token = current_token()
    advance()
    name = parse_identifier()
    if current_token().type != 'EQUAL':
      raise ParseError(meta_from_tokens(current_token(),current_token()),
            'expected "=" after name in "define", not\n\t' \
            + current_token().value)
    advance()
    rhs = parse_term()
    meta = meta_from_tokens(token, previous_token())
    return PTLetNew(meta, name, rhs, None)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
      + str(e))
    

def parse_have():
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
      except ParseError as e:
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
    if end_of_file():
      raise ParseError(meta_from_tokens(start_token, start_token),
            'expected the keyword "by" after formula of "have", not end of file')
    elif current_token().type == 'BY':
      advance()
      because = parse_proof()
    else:        
      raise ParseError(meta_from_tokens(current_token(), current_token()),
            'expected the keyword "by" after formula of "have", ' \
            + 'not\n\t' + current_token().value)
    return PLet(meta_from_tokens(token, previous_token()),
                label, proved, because, None)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
      + str(e))

def parse_proof():
    start_token = previous_token()
    proof_stmt = parse_proof_statement()
    if proof_stmt:
        try:
          body = parse_proof()
        except ParseError as ex:
          if not ex.missing:
              raise ex
          else:
              body = PHole(meta_from_tokens(current_token(), current_token()))
        except Exception as e:
            raise ParseError(meta_from_tokens(current_token(), previous_token()), "Unexpected error while parsing:\n\t" \
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
          if not ex.missing:
              raise ex
          else:
              ret = PHole(meta_from_tokens(current_token(), current_token()))
        except Exception as e:
            raise ParseError(meta_from_tokens(current_token(), previous_token()), "Unexpected error while parsing:\n\t" \
              + str(e))
        return ret

def parse_finishing_proof():
    start_token = current_token()
    proof = parse_proof_med()
    while not end_of_file() and current_token().type == 'COMMA':
      advance()
      right = parse_proof()
      proof = PTuple(meta_from_tokens(start_token, previous_token()), 
                     extract_tuple(proof) + extract_tuple(right))
    return proof

def parse_induction():
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

def parse_induction_case():
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
    if current_token().type != 'LBRACE':
      raise ParseError(meta_from_tokens(current_token(), current_token()),
            'expected "{" after pattern of "case", not\n\t' \
            + current_token().value)
    advance()
    body = parse_proof()
    if current_token().type != 'RBRACE':
      raise ParseError(meta_from_tokens(current_token(), current_token()),
            'expected "}" after body of induction case, not\n\t' \
            + current_token().value)
    advance()
    return IndCase(meta_from_tokens(start_token, previous_token()),
                    pat, ind_hyps, body)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
      + str(e))

def parse_equation():
  lhs = parse_term_compare()
  if current_token().type != 'EQUAL':
      raise ParseError(meta_from_tokens(current_token(), current_token()),
            'expected "=" after left-hand side of equation, not\n\t' \
            + current_token().value)
  advance()
  rhs = parse_term_compare()
  if current_token().type != 'BY':
      raise ParseError(meta_from_tokens(current_token(), current_token()),
            'expected "by" after equation, not\n\t' \
            + current_token().value)
  advance()
  reason = parse_proof()
  return (lhs, rhs, reason)

def parse_half_equation():
  if current_token().value == '...':
    advance()
    if current_token().type != 'EQUAL':
      raise ParseError(meta_from_tokens(current_token(), current_token()),
              'expected "=" after "...", not\n\t' \
              + current_token().value)
    advance()
    rhs = parse_term_compare()
    if current_token().type != 'BY':
        raise ParseError(meta_from_tokens(current_token(), current_token()),
              'expected "by" after equation, not\n\t' \
              + current_token().value)
    advance()
    reason = parse_proof()
    return (None, rhs, reason)
  elif current_token().value == '$':
    advance()
    return parse_equation()
  else:
    raise ParseError(meta_from_tokens(current_token(), current_token()),
          'expected "... = rhs" or "$ lhs = rhs" in "equations", not\n\t' \
          + current_token().value)

def parse_equation_list():
  eqn_list = []
  while current_token().value == '$' or current_token().value == '...':
    eqn = parse_half_equation()
    eqn_list.append(eqn)
  return eqn_list

def parse_theorem():
  while_parsing = 'while parsing\n' \
      + '\tproof_stmt ::= "theorem" identifier ":" formula "proof" proof "end"'
  try:    
    start_token = current_token()
    is_lemma = start_token.type == 'LEMMA'
    advance()
    try:
      name = parse_identifier()
    except ParseError as e:
      if end_of_file():
      
        raise ParseError(meta_from_tokens(start_token, start_token),
          'expected name of theorem, not end of file')
      else:
        raise ParseError(meta_from_tokens(current_token(), current_token()),
          'expected name of theorem, not:\n\t' + current_token().value)
    except Exception as e:
        raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
          + str(e))
    
    if current_token().type != 'COLON':
      raise ParseError(meta_from_tokens(current_token(), current_token()),
            'expected a colon after theorem name, not\n\t' \
            + current_token().value)
    advance()
    what = parse_term()
    if current_token().type != 'PROOF':
      raise ParseError(meta_from_tokens(current_token(), current_token()),
            'expected the keyword "proof" after formula of theorem, not\n\t' \
            + current_token().value)
    advance()
    proof = parse_proof()
    if current_token().type != 'END':
      raise ParseError(meta_from_tokens(current_token(), current_token()),
            'expected the keyword "end" after proof of theorem, not\n\t' \
            + current_token().value)
    advance()
    return Theorem(meta_from_tokens(start_token, previous_token()),
                   name, what, proof, is_lemma)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()),
                   while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
      + str(e))


def parse_union():
  while_parsing = 'while parsing\n' \
      + '\tstatement ::= "union" identifier type_params_opt "{" constructor* "}"\n'
  try:
    start_token = current_token()
    advance()
    name = parse_identifier()
    type_params = parse_type_parameters()

    if current_token().type != 'LBRACE':
      raise ParseError(meta_from_tokens(current_token(), current_token()),
            'expected "{" after name of union, not\n\t' \
            + current_token().value)
    advance()
    constr_list = []
    while current_token().type != 'RBRACE':
      constr = parse_constructor()
      constr_list.append(constr)
    meta = meta_from_tokens(start_token, current_token())
    advance()
    return Union(meta, name, type_params, constr_list, False)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
      + str(e))

def parse_function():
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
      if current_token().type != 'RPAR':
        raise ParseError(meta_from_tokens(start_token, previous_token()),
              'expected a closing parenthesis, not\n\t' \
              + quote(current_token().value))
      advance()

    if current_token().type != 'LBRACE':
      raise ParseError(meta_from_tokens(start_token, current_token()),
            'expected "{" after parameters of function, not\n\t' \
            + current_token().value)
    advance()
    body = parse_term()
    if current_token().type != 'RBRACE':
      raise ParseError(meta_from_tokens(start_token, previous_token()),
            'expected "}" after body of function, not\n\t' + current_token().value)
    advance()
    meta = meta_from_tokens(start_token, previous_token())
    lam = Lambda(meta, None, params, body)
    if len(typarams) > 0:
      fun = Generic(meta, None, typarams, lam)
    else:
      fun = lam
    return Define(meta, name, None, fun, False)
    
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
      + str(e))
      
def parse_gen_rec_function():
  while_parsing = 'while parsing\n' \
      + '\tstatement ::= "recfun" identifier type_params_opt "(" variable_list ")" "->" type "measure" term "{" term "}" "terminates" proof\n'
  try:
    start_token = current_token()
    advance()
    name = parse_identifier()
    typarams = parse_type_parameters()
    
    if current_token().type == 'LPAR':
      advance()
      params = parse_var_list()
      if current_token().type != 'RPAR':
        raise ParseError(meta_from_tokens(start_token, previous_token()),
              'expected a closing parenthesis, not\n\t' \
              + quote(current_token().value))
      advance()

    if current_token().value != '->':
      raise ParseError(meta_from_tokens(current_token(), current_token()),
            'expected "->" between parameter types and return type, not\n\t' \
            + quote(current_token().value))
    advance()
    return_type = parse_type()

    if current_token().type != 'MEASURE':
      raise ParseError(meta_from_tokens(start_token, current_token()),
            'expected "measure" after return type of recfun, not\n\t' \
            + current_token().value)
    advance()
    measure = parse_term()
    
    if current_token().type != 'LBRACE':
      raise ParseError(meta_from_tokens(start_token, current_token()),
            'expected "{" after parameters of function, not\n\t' \
            + current_token().value)
    advance()
    body = parse_term()
    if current_token().type != 'RBRACE':
      raise ParseError(meta_from_tokens(start_token, previous_token()),
            'expected "}" after body of function, not\n\t' + current_token().value)
    advance()

    if current_token().type != 'TERMINATES':
      raise ParseError(meta_from_tokens(start_token, previous_token()),
            'expected "terminates" after "}" in "recfun", not\n\t' \
                       + current_token().value)
    advance()
    terminates = parse_proof()
    
    meta = meta_from_tokens(start_token, previous_token())
    return GenRecFun(meta, name, typarams, params, return_type, measure,
                     Var(meta, None, 'Nat', []), body, terminates, False)
    
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()),
                   while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()),
                     "Unexpected error while parsing:\n\t" + str(e))
    
def parse_recursive_function():
  while_parsing = 'while parsing\n' \
      + '\tstatement ::= "function" identifier type_params_opt' \
      + ' "(" type_list ")"\n\t\t\t "->" type "{" fun_case* "}"\n'
  try:
    start_token = current_token()
    advance()
    name = parse_identifier()
    type_params = parse_type_parameters()

    if current_token().type == 'LPAR':
      paren_start_token = current_token()
      advance()
      param_types = parse_type_list()
      if current_token().type != 'RPAR':
        raise ParseError(meta_from_tokens(paren_start_token, previous_token()),
              'expected a closing parenthesis, not\n\t' \
              + quote(current_token().value))
      advance()

    if current_token().value != '->':
      raise ParseError(meta_from_tokens(current_token(), current_token()),
            'expected "->" between parameter types and return type, not\n\t' \
            + quote(current_token().value))
    advance()
    return_type = parse_type()

    if current_token().type != 'LBRACE':
      raise ParseError(meta_from_tokens(current_token(), current_token()),
            'expected open brace "{" after the return type of the function')
    advance()

    cases = []
    while current_token().type != 'RBRACE':
      fun_case = parse_fun_case()
      cases.append(fun_case)
    advance()
    return RecFun(meta_from_tokens(start_token, previous_token()), name,
                  type_params, param_types, return_type, cases, False)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
      + str(e))
    
def parse_define():
  while_parsing = 'while parsing\n' \
      + '\tproof_stmt ::= "define" identifier "=" term\n'
  try:
    start_token = current_token()
    advance()
    name = parse_identifier()
    if current_token().type == 'COLON':
      advance()
      while_parsing = 'while parsing\n' \
          + '\tproof_stmt ::= "define" identifier ":" type "=" term\n'
      typ = parse_type()
    else:
      typ = None
    if current_token().type != 'EQUAL':
      raise ParseError(meta_from_tokens(current_token(), current_token()),
            'expected "=" after name in "define"')
    advance()
    body = parse_term()
    return Define(meta_from_tokens(start_token, previous_token()),
                   name, typ, body, False)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
      + str(e))
  
def parse_private():
  while_parsing = 'while parsing\n' \
    + '\nstatement ::= "private" statement'
  try: 
    my_token = current_token() 
    advance()
    statement = parse_statement()
    match statement:
      case RecFun(meta, name, type_params, param_types, return_type, cases, isPrivate):
        statement.isPrivate = True
        return statement
      case Define(meta, name, typ, body, isPrivate):
        statement.isPrivate = True
        return statement
      case Union(meta, name, type_params, constr_list, isPrivate):
        statement.isPrivate = True
        return statement
      case _:
        raise ParseError(meta_from_tokens(my_token, my_token), 'expected either function, define, or union after private')

  except ParseError as e:
    raise e.extend(meta_from_tokens(my_token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(my_token, previous_token()), "Unexpected error while parsing:\n\t" \
      + str(e))


statement_keywords = {'assert', 'define', 'function', 'import', 'print', 'theorem',
                      'union'}
    
def parse_statement():
  if end_of_file():
      raise ParseError(meta_from_tokens(previous_token(),previous_token()),
            'expected a statement, not end of file')
  token = current_token()
  if token.type == 'ASSERT':
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
  
  elif token.type == 'DEFINE':
    return parse_define()

  elif token.type == 'FUN':
    return parse_function()

  elif token.type == 'FUNCTION':
    return parse_recursive_function()

  elif token.type == 'RECURSIVE':
    return parse_recursive_function()

  elif token.type == 'RECFUN':
    return parse_gen_rec_function()

  elif token.type == 'IMPORT':
    while_parsing = 'while parsing import\n' \
        + '\tstatement ::= "import" identifier\n'
    advance()
    try:
        name = parse_identifier()
        return Import(meta_from_tokens(token, previous_token()), name)
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
        
  elif token.type == 'THEOREM' or token.type == 'LEMMA':
    return parse_theorem()

  elif token.type == 'UNION':
    return parse_union()
  
  elif token.type == 'PRIVATE':
    return parse_private()

  elif token.type == 'ASSOCIATIVE':
    advance()
    name = parse_identifier()
    typarams = parse_type_parameters()
    advance()
    
    typ = parse_type()
    meta = meta_from_tokens(token, previous_token())
    return Associative(meta, typarams, Var(meta, None, name, []), typ)

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

def parse_type_parameters():
  if current_token().type == 'LESSTHAN':
      advance()
      ident_list = parse_ident_list()
      if current_token().type != 'MORETHAN':
        raise ParseError(meta_from_tokens(current_token(), current_token()),
              'expected closing ">" after type parameters of "fn", not\n\t' \
              + current_token().value)
      advance()
      return ident_list
  else:
      return []
    
def parse_type():
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
    if current_token().type != 'RSQB':
        raise ParseError(meta_from_tokens(start_token, current_token()),
              'expected closing "]", not\n\t' + current_token().value)
    advance()
    return ArrayType(meta_from_tokens(token, previous_token()),
                     elt_type)
  elif token.type == 'LPAR':
    start_token = current_token()
    advance()
    typ = parse_type()
    if current_token().type != 'RPAR':
        raise ParseError(meta_from_tokens(start_token, current_token()),
              'expected closing ")", not\n\t' + current_token().value)
    advance()
    return typ
  else:
    try:
      name = parse_identifier()
    except ParseError as e:
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
      if current_token().type != 'MORETHAN':
          raise ParseError(meta_from_tokens(start_token, previous_token()),
                'expected a closing ">"')
      advance()
    if inst:
        return TypeInst(meta_from_tokens(token, previous_token()),
                        var, arg_types)
    else:
        return var

def parse_function_type():
  while_parsing = 'while parsing\n' \
      + '\ttype ::= "fn" type_params_opt type_list "->" type\n'
  try:
    start_token = current_token()
    advance()
    type_params = parse_type_parameters()
    param_types = parse_type_list()
    if current_token().value != '->':
        raise ParseError(meta_from_tokens(current_token(), current_token()),
              'expected "->" after parameter types, not\n\t' \
              + quote(current_token().value))
    advance()
    return_type = parse_type()
    return FunctionType(meta_from_tokens(start_token, previous_token()),
                        type_params, param_types, return_type)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
      + str(e))
    
    
def parse_type_list():
  typ = parse_type()
  type_list = [typ]
  while current_token().type == 'COMMA':
    advance()
    typ = parse_type()
    type_list.append(typ)
  return type_list

def parse_term_list(end):
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

def parse_nonempty_term_list():
  trm = parse_term()
  trm_list = [trm]
  while current_token().type == 'COMMA':
    advance()
    trm = parse_term()
    trm_list.append(trm)
  return trm_list
    
def parse_constructor():
  while_parsing = 'while parsing\n' \
      + '\tconstructor ::= identifier | identifier "(" type_list ")"'
  try:  
    start_token = current_token()
    name = parse_identifier()

    if current_token().type == 'LPAR':
      advance()
      param_types = parse_type_list()
      if current_token().type != 'RPAR':
        raise ParseError(meta_from_tokens(start_token, previous_token()),
              'missing closing parenthesis')
      advance()
    else:
      param_types = []
    meta = meta_from_tokens(start_token, previous_token())
    return Constructor(meta, name, param_types)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
      + str(e))
    

def parse_constructor_pattern():
  start_token = current_token()
  constr_name = parse_identifier()
  ident_list = []
  if current_token().type == 'LPAR':
    start_token = current_token()
    advance()
    ident = parse_identifier()
    ident_list.append(ident)
    while current_token().type == 'COMMA':
      advance()
      ident = parse_identifier()
      ident_list.append(ident)
    if current_token().type != 'RPAR':
      raise ParseError(meta_from_tokens(start_token, previous_token()),
            'expected a closing parenthesis')
    advance()
  return PatternCons(meta_from_tokens(start_token, previous_token()),
                     Var(meta_from_tokens(start_token,
                                          start_token),
                         None, constr_name, []),
                     ident_list)
    

def parse_pattern():
  if current_token().value == '0':
    advance()
    meta = meta_from_tokens(current_token(), current_token())
    return PatternCons(meta, Var(meta, None, 'zero', []), [])
  if current_token().type == 'LSQB' and next_token().type == 'RSQB':
    advance()
    advance()
    meta = meta_from_tokens(current_token(), current_token())
    return PatternCons(meta, Var(meta, None, 'empty', []), [])
  elif current_token().type == 'TRUE':
    advance()
    meta = meta_from_tokens(current_token(), current_token())
    return PatternBool(meta, True)
  elif current_token().type == 'FALSE':
    advance()
    meta = meta_from_tokens(current_token(), current_token())
    return PatternBool(meta, False)
  else:
    start_token = current_token()
    try:
      return parse_constructor_pattern()
    except ParseError as e:
      raise ParseError(meta_from_tokens(start_token, current_token()),
            'expected a pattern, not\n\t' + quote(current_token().value))
    except Exception as e:
      raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
        + str(e))

def parse_pattern_list():
  pat = parse_pattern()
  if current_token().type == 'COMMA':
    advance()
    ident_list = parse_ident_list()
    return [pat] + ident_list
  else:
    return [pat]
      
def parse_ident_list():
  ident = parse_identifier()
  ident_list = [ident]
  while current_token().type == 'COMMA':
    advance()
    ident = parse_identifier()
    ident_list.append(ident)
  return ident_list

def parse_single_or_repeat():
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
      
def parse_ident_list_bar():
  ident_list = parse_single_or_repeat()
  while current_token().value == '|':
    advance()
    ident_list += parse_single_or_repeat()
  return ident_list

def parse_type_annot_list():
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

def parse_var_list():
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
  
def parse_fun_case():
  while_parsing = 'while parsing\n' \
      + '\tfun_case ::= identifier "(" param_list ")" "=" term\n'
  try:    
    start_token = current_token()
    rator = parse_identifier()
    rator_meta = meta_from_tokens(start_token, previous_token())
    
    if current_token().type == 'LPAR':
      lpar_token = current_token()
      advance()
      pat_list = parse_pattern_list()
      if current_token().type != 'RPAR':
        raise ParseError(meta_from_tokens(lpar_token, previous_token()),
              'expected closing parenthesis')
      advance()
    if current_token().type != 'EQUAL':
      raise ParseError(meta_from_tokens(current_token(), current_token()),
            'expected "=" and then a term, not\n\t' + current_token())
    advance()
    body = parse_term()
    meta = meta_from_tokens(start_token, previous_token())
    return FunCase(meta, Var(rator_meta, None, rator, []),
                   pat_list[0], pat_list[1:], body)
  except ParseError as e:
    raise e.extend(meta_from_tokens(start_token, previous_token()), while_parsing)
  except Exception as e:
    raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
      + str(e))

def quote(str):
    return '"' + str + '"'

def parse_switch_case():
    while_parsing = 'while parsing\n' \
        + '\tswitch_case ::= "case" pattern "{" term "}"'
    start_token = current_token()
    advance()
    try:
        pattern = parse_pattern()
    except ParseError as e:
        raise e.extend(meta_from_tokens(start_token, current_token()), while_parsing)
    except Exception as e:
        raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
          + str(e))
    
    if current_token().type != 'LBRACE':
      raise ParseError(meta_from_tokens(current_token(),current_token()),
            'expected a "{" after pattern of case, not\n\t' \
            + quote(current_token().value)).extend(meta_from_tokens(start_token, current_token()), while_parsing)
    advance()
    try:
      body = parse_term()
    except ParseError as e:
      raise e.extend(meta_from_tokens(start_token, current_token()), while_parsing)
    except Exception as e:
      raise ParseError(meta_from_tokens(start_token, previous_token()), "Unexpected error while parsing:\n\t" \
        + str(e))
            
    if current_token().type != 'RBRACE':
      raise ParseError(meta_from_tokens(current_token(),current_token()),
            'expected a "}" after body of case, not\n\t' \
            + quote(current_token().value)).extend(meta_from_tokens(start_token, current_token()), while_parsing)
    advance()
    return SwitchCase(meta_from_tokens(start_token, previous_token()),
                      pattern, body)
