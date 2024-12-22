# The motivation for this recursive-descent version of the parser
# is to provide better error messages. -Jeremy

from abstract_syntax import *
from lark import Lark, Token, logger, exceptions, tree
from error import *
from edit_distance import edit_distance

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

mult_operators = {'*', '/', '%', '∘', '.o.'}
add_operators = {'+', '-', '∪', '|', '∩', '&', '⨄', '.+.', '++' }
compare_operators = {'<', '>', '≤', '<=', '>', '≥', '>=', '⊆', '(=', '∈', 'in'}
equal_operators = {'=', '≠', '!='}
iff_operators = {'iff', "<=>", "⇔"}

to_unicode = {'.o.': '∘', '|': '∪', '&': '∩', '.+.': '⨄', '<=': '≤', '>=': '≥',
              '(=': '⊆', 'in': '∈', '.0.': '∅', '<=>': '⇔', 'iff': '⇔'}

lark_parser = None

def init_parser():
  global lark_parser
  lark_file = get_deduce_directory() + "/Deduce.lark"
  lark_parser = Lark(open(lark_file, encoding="utf-8").read(),
                     start='program', parser='lalr',
                     debug=True, propagate_positions=True)

# The current_position needs to be a global so that the changes to the
# current_position don't get discarded when an exception is
# thrown. -Jeremy

current_position = 0
token_list = []

def current_token():
    return token_list[current_position]

def next_token():
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
      error(meta_from_tokens(previous_token(), previous_token()),
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
    error(meta_from_tokens(token, token),
          'expected an identifier, not\n\t' + quote(token.value))

def meta_from_tokens(start_token, end_token):
    meta = Meta()
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
      error(meta_from_tokens(current_token(), current_token()),
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
      error(meta_from_tokens(current_token(),current_token()),
            'expected "<" after subject of instantiation ("@"), not\n\t' \
            + current_token().value \
            + '\nwhile parsing\n' \
            + '\tterm ::= "@" term "<" type_list ">"')
    advance()
    type_args = parse_type_list()
    if current_token().type != 'MORETHAN':
      error(meta_from_tokens(current_token(),current_token()),
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
      error(meta_from_tokens(current_token(),current_token()),
            'expected an integer not\n\t' + current_token().value)

  elif token.type == 'IF':
    advance()
    prem = parse_term()
    if current_token().type != 'THEN':
      error(meta_from_tokens(current_token(),current_token()),
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
    params = parse_var_list()
    if current_token().type != 'LBRACE':
      error(meta_from_tokens(token, current_token()),
            'expected "{" after parameters of fun, not\n\t' \
            + current_token().value)
    advance()
    body = parse_term()
    if current_token().type != 'RBRACE':
      error(meta_from_tokens(token, previous_token()),
            'expected "}" after body of "fun", not\n\t' + current_token().value)
    advance()
    return Lambda(meta_from_tokens(token, previous_token()),
                   None, params, body)

  elif token.type == 'GENERIC':
    advance()
    params = parse_ident_list()
    if current_token().type != 'LBRACE':
      error(meta_from_tokens(token, current_token()),
            'expected "{" after parameters of "generic", not\n\t' \
            + current_token().value)
    advance()
    body = parse_term()
    if current_token().type != 'RBRACE':
      error(meta_from_tokens(token, current_token()),
            'expected "}" after body of "generic", not\n\t' \
            + current_token().value)
    advance()
    meta = meta_from_tokens(token, previous_token())
    return Generic(meta, None, params, body)
    
  elif token.type == 'LESSTHAN':
    advance()
    type_params = parse_ident_list()
    if current_token().type != 'MORETHAN':
        error(meta_from_tokens(token, previous_token()),
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
      error(meta_from_tokens(current_token(), current_token()),
            'expected closing parentheses, not\n\t' \
            + current_token().value + '\n' + while_parsing)
    advance()
    return term

  elif token.type == 'HASH':
    advance()
    term = parse_term()
    if current_token().type != 'HASH':
      error(meta_from_tokens(current_token(), current_token()),
            'expected closing parentheses, not\n\t' \
            + current_token().value)
    advance()
    meta = meta_from_tokens(token, previous_token())
    return Mark(meta, None, term)

  elif token.value == '─':
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
      error(meta_from_tokens(token, current_token()),
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
      error(meta_from_tokens(current_token(), current_token()),
            'expected "{" after subject of switch, not\n\t' \
            + current_token().value)
    advance()
    cases = []
    while current_token().type == 'CASE':
      switch_case = parse_switch_case()
      cases.append(switch_case)
    if current_token().type != 'RBRACE':
      error(meta_from_tokens(token,current_token()),
            'expected "}" after last case of switch, not\n\t' \
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
      error(meta_from_tokens(current_token(),current_token()),
            'expected closing bracket \']\', not\n\t' + current_token().value)
    advance()
    return listToNodeList(meta_from_tokens(token,token), lst_terms)
    
  else:
    try:
      name = parse_identifier()
      meta = meta_from_tokens(token, token)
      var = Var(meta, None, name)
      return var
    except Exception as e:  
      error(meta_from_tokens(token, current_token()),
            'expected a term, not\n\t' + quote(current_token().value))

def parse_call():
  while_parsing = 'while parsing function call\n' \
      + '\tterm ::= term "(" term_list ")"\n'
  term = parse_term_hi()

  while (not end_of_file()) and current_token().type == 'LPAR':
    try:
      start_token = current_token()
      advance()
      args = parse_term_list()
      if current_token().type != 'RPAR':
        error(meta_from_tokens(start_token, current_token()),
              'expected closing parenthesis ")", not\n\t' \
              + current_token().value)
      term = Call(meta_from_tokens(start_token, current_token()), None,
                  term, args)
      advance()
    except Exception as e:
      meta = meta_from_tokens(start_token, previous_token())
      raise Exception(str(e) + '\n' + error_header(meta) + while_parsing)

  return term
    
def parse_term_mult():
  term = parse_call()

  while (not end_of_file()) and current_token().value in mult_operators:
    start_token = current_token()
    rator = Var(meta_from_tokens(current_token(), current_token()),
                None, to_unicode.get(current_token().value, current_token().value))
    advance()
    right = parse_term_mult()
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
    right = parse_term_add()
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
    if opr == '=':
      term = Call(meta_from_tokens(token, previous_token()), None,
                  eq, [term,right])
    elif opr == '≠' or opr == '!=':
      term = IfThen(meta, None, 
                    Call(meta, None, eq, [term,right]),
                    Bool(meta, None, False))
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

def parse_term():
  if end_of_file():
      error(meta_from_tokens(previous_token(),previous_token()),
            'expected a term, not end of file')
      
  token = current_token()

  if token.type == 'DEFINE':
    return parse_define_term()
  else:
    term = parse_term_logic()
    if (not end_of_file()) and (current_token().value in iff_operators):
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

def parse_define_term():
  while_parsing = 'while parsing\n' \
      + '\tterm ::= "define" identifier "=" term ";" term\n'
  try:
    start_token = current_token()
    advance()
    name = parse_identifier()
    if current_token().type != 'EQUAL':
        error(meta_from_tokens(current_token(),current_token()),
              'expected "=" after name in "define", not\n\t' \
              + quote(current_token().value))
    advance()
    rhs = parse_term_logic()
    if current_token().type != 'SEMICOLON':
        error(meta_from_tokens(current_token(),current_token()),
              'expected ";" after right-hand side of "define", not\n\t' \
              + quote(current_token().value))
    advance()
    meta = meta_from_tokens(start_token, previous_token())
    body = parse_term()
    return TLet(meta, None, name, rhs, body)
  except Exception as e:
    meta = meta_from_tokens(start_token, previous_token())
    raise Exception(str(e) + '\n' + error_header(meta) + while_parsing)
      
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

proof_keywords = {'apply', 'arbitrary',
                  'choose', 'conclude', 'conjunct',
                  'definition',
                  'enable', 'equations', 'extensionality',
                  'have', 'induction', 'obtain',
                  'reflexive', 'rewrite',
                  'suffices', 'suppose', 'switch', 'symmetric',
                  'transitive'}

def parse_definition_proof():
  token = current_token()
  advance()
  if current_token().type == 'LBRACE':
    advance()
    defs = parse_ident_list()
    if current_token().type != 'RBRACE':
        error(meta_from_tokens(current_token(), current_token()),
              'expected closing "}", not\n\t' + current_token().value)
    advance()
  else:
    defn = parse_identifier()
    defs = [defn]

  if current_token().type == 'AND':
      advance()
      if current_token().type != 'REWRITE':
          error(meta_from_tokens(current_token(),current_token()),
                'expected "rewrite" after "and" and "definition", not\n\t' \
                + current_token().value)
      advance()
      eqns = parse_proof_list()
      meta = meta_from_tokens(token, previous_token())
      return ApplyDefsGoal(meta,
                            [Var(meta, None, t) for t in defs],
                            Rewrite(meta, eqns))
  elif current_token().type == 'IN':
      advance()
      subject = parse_proof()
      meta = meta_from_tokens(token, previous_token())
      return ApplyDefsFact(meta, [Var(meta, None, t) for t in defs],
                            subject)
  else:
      meta = meta_from_tokens(token, previous_token())
      return ApplyDefs(meta, [Var(meta, None, n) for n in defs])

def parse_recall():
  start_token = current_token()
  advance()
  facts = parse_term_list()
  meta = meta_from_tokens(start_token, previous_token())
  return PRecall(meta, facts)
  
def parse_proof_hi():
  token = current_token()
  if token.type == 'APPLY':
    advance()
    imp = parse_proof()
    if current_token().type != 'TO':
      error(meta_from_tokens(current_token(), current_token()),
            'expected "to" after implication part of "apply", not\n\t' \
            + current_token().value)
    advance()
    arg = parse_proof()
    return ModusPonens(meta_from_tokens(token, previous_token()), imp, arg)

  elif token.type == 'CASES':
    advance()
    subject = parse_proof()
    cases = []
    while (not end_of_file()) and current_token().type == 'CASE':
        c = parse_case()
        cases.append(c)
    meta = meta_from_tokens(token, previous_token())
    return Cases(meta, subject, cases)
    
  elif token.type == 'CONCLUDE':
    advance()
    claim = parse_term()
    if current_token().type == 'BY':
      advance()
      reason = parse_proof()
    else:
      error(meta_from_tokens(current_token(), current_token()),
            'expected the keyword "by" after formula of "conclude", '\
            + 'not\n\t' + current_token().value)
    return PAnnot(meta_from_tokens(token, previous_token()),
                  claim, reason)

  elif token.type == 'CONJUNCT':
    advance()
    meta = meta_from_tokens(current_token(),current_token())
    index = int(current_token().value)
    advance()
    if current_token().type != 'OF':
      error(meta_from_tokens(current_token(),current_token()),
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
      error(meta_from_tokens(current_token(), current_token()),
            'expected a closing parentheses, not\n\t' \
            + current_token().value)
    advance()
    return proof

  elif token.type == 'LBRACE':
    advance()
    proof = parse_proof()
    if current_token().type != 'RBRACE':
      error(meta_from_tokens(current_token(), current_token()),
            'expected a closing "}", not\n\t' \
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

  elif token.type == 'REWRITE':
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
        error(meta_from_tokens(current_token(), current_token()),
              'expected "{" after subject of "switch"')
    advance()
    cases = []
    while current_token().type == 'CASE':
        c = parse_proof_switch_case()
        cases.append(c)
    if current_token().type != 'RBRACE':
        error(meta_from_tokens(current_token(), current_token()),
              'expected closing "}" after cases of "switch"')
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
    for kw in proof_keywords:
        if edit_distance(token.value, kw) <= 2:
            error(meta_from_tokens(token, token),
                  'did you mean "' + kw \
                  + '" instead of "' + current_token().value + '"?')

    try:
      name = parse_identifier()
    except Exception as e:
      missing_error(meta_from_tokens(token, current_token()),
                    'expected a proof, not\n\t' + quote(current_token().value))
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
      error(meta_from_tokens(start_token,current_token()),
            'expected a "{" after assumption of "case", not\n\t' \
            + current_token().value \
            + '\nwhile parsing:\n\t"case" label ":" formula "{" proof "}"')
    advance()
    body = parse_proof()
    if current_token().type != 'RBRACE':
      error(meta_from_tokens(start_token,current_token()),
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
      error(meta_from_tokens(start_token,current_token()),
            'expected a "{" after assumption of "case", not\n\t' \
            + current_token().value \
            + '\nwhile parsing one of the following\n' \
            + '\tswitch_proof_case ::= "case" pattern "{" proof "}"\n' \
            + '\tswitch_proof_case ::= "case" pattern "assume" assumption_list "{" proof "}"')
    advance()
    body = parse_proof()
    if current_token().type != 'RBRACE':
      error(meta_from_tokens(start_token,current_token()),
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
        error(meta_from_tokens(start_token,current_token()),
              'expected a closing ">", not\n\t' + current_token().value + '\n'\
              + 'while trying to parse type arguments for instantiation of an "all" formula:\n\t'\
              + 'proof ::= proof "<" type_list ">"')
      advance()
      meta = meta_from_tokens(start_token, previous_token())
      for j, ty in enumerate(type_list):
        proof = AllElimTypes(meta, proof, ty, (j, len(type_list)))
      
    while (not end_of_file()) and current_token().type == 'LSQB':
      advance()
      term_list = parse_term_list()
      if current_token().type != 'RSQB':
        error(meta_from_tokens(current_token(),current_token()),
              'expected a closing "]", not\n\t' + current_token().value)
      advance()
      meta = meta_from_tokens(start_token, previous_token())
      for j, term in enumerate(term_list):
        proof = AllElim(meta, proof, term, (j, len(term_list)))

    return proof

def parse_proof_statement():
  if end_of_file():
      error(meta_from_tokens(previous_token(),previous_token()),
            'expected a proof, not end of file')
      
  token = current_token()
    
  if token.type == 'SUFFICES':
    advance()
    formula = parse_term()
    if current_token().type != 'BY':
      error(meta_from_tokens(current_token(), current_token()),
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
    except Exception as e:
      error(meta_from_tokens(token, current_token()),
            'expected an assumption:\n\t"assume" label ":" formula\n' \
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
    witnesses = parse_term_list()
    meta = meta_from_tokens(token, previous_token())
    return SomeIntro(meta, witnesses, None)
    
  elif token.type == 'OBTAIN':
    advance()
    witnesses = parse_ident_list()
    if current_token().type != 'WHERE':
      error(meta_from_tokens(current_token(), current_token()),
            'expected "where" after variables of "obtain", not\n\t' \
            + current_token().value)
    advance()
    label, premise = parse_assumption()
    if current_token().type != 'FROM':
      error(meta_from_tokens(current_token(), current_token()),
            'expected "from" after "where" part of "obtain", not\n\t' \
            + current_token().value)
    advance()
    some = parse_proof()
    meta = meta_from_tokens(token, previous_token())
    return SomeElim(meta, witnesses, label, premise, some, None)
    
  elif token.type == 'ENABLE':
    advance()
    if current_token().type != 'LBRACE':
        error(meta_from_tokens(current_token(), current_token()),
              'expected "{" after "enable"')
    advance()
    defs = parse_ident_list()
    if current_token().type != 'RBRACE':
        error(meta_from_tokens(current_token(), current_token()),
              'expected closing "}" in "enable"')
    advance()
    meta = meta_from_tokens(token, previous_token())
    return EnableDefs(meta, [Var(meta, None, x) for x in defs], None)
      
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
        error(meta_from_tokens(current_token(),current_token()),
              'expected "=" after name in "define", not\n\t' \
              + current_token().value)
    advance()
    rhs = parse_term()
    meta = meta_from_tokens(token, previous_token())
    return PTLetNew(meta, name, rhs, None)
  except Exception as e:
    meta = meta_from_tokens(start_token, current_token())
    raise Exception(str(e) + '\n' + error_header(meta) + while_parsing)
    

def parse_have():
  while_parsing = 'while parsing\n' \
      + '\tproof_stmt ::= "have" identifier ":" formula "by" proof\n' \
      + '\tproof_stmt ::= "have" ":" formula "by" proof\n'
  try:  
    start_token = current_token()
    token = start_token
    advance()
    if current_token().type != 'COLON':
      try:
        label = parse_identifier()
      except Exception as e:
        error(meta_from_tokens(current_token(), current_token()),
            'expected an identifier or colon after "have", not\n\t' \
            + current_token().value)
    else:
      label = '_'
    if current_token().type != 'COLON':
      error(meta_from_tokens(current_token(), current_token()),
            'expected a colon after label of "have", not\n\t' \
            + current_token().value)
    advance()
    proved = parse_term()
    if current_token().type == 'BY':
      advance()
      because = parse_proof()
    else:        
      error(meta_from_tokens(current_token(), current_token()),
            'expected the keyword "by" after formula of "have", ' \
            + 'not\n\t' + current_token().value)
    return PLet(meta_from_tokens(token, previous_token()),
                label, proved, because, None)
  except Exception as e:
    meta = meta_from_tokens(start_token, previous_token())
    raise Exception(str(e) + '\n' + error_header(meta) + while_parsing)

def parse_proof():
    proof_stmt = parse_proof_statement()
    if proof_stmt:
        try:
          body = parse_proof()
        except Exception as ex:
          if hasattr(ex, 'last') or not hasattr(ex, 'missing'):
              raise ex
          else:
              last_error(meta_from_tokens(current_token(), current_token()),
                         'missing conclusion after\n\t' + str(proof_stmt))
              
        if isinstance(proof_stmt, AllIntro):
            proof_stmt.set_body(body)
        else:
            proof_stmt.body = body
        return proof_stmt
    else:
        return parse_finishing_proof()

def parse_finishing_proof():
    start_token = current_token()
    proof = parse_proof_med()
    while current_token().type == 'COMMA':
      advance()
      right = parse_proof()
      proof = PTuple(meta_from_tokens(start_token, previous_token()), 
                    [proof, right])
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
  except Exception as e:
    meta = meta_from_tokens(start_token, previous_token())
    raise Exception(str(e) + '\n' + error_header(meta) + while_parsing)

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
      error(meta_from_tokens(current_token(), current_token()),
            'expected "{" after pattern of "case", not\n\t' \
            + current_token().value)
    advance()
    body = parse_proof()
    if current_token().type != 'RBRACE':
      error(meta_from_tokens(current_token(), current_token()),
            'expected "}" after body of induction case, not\n\t' \
            + current_token().value)
    advance()
    return IndCase(meta_from_tokens(start_token, previous_token()),
                    pat, ind_hyps, body)
  except Exception as e:
    meta = meta_from_tokens(start_token, previous_token())
    raise Exception(str(e) + '\n' + error_header(meta) + while_parsing)

def parse_equation():
  lhs = parse_term_compare()
  if current_token().type != 'EQUAL':
      error(meta_from_tokens(current_token(), current_token()),
            'expected "=" after left-hand side of equation, not\n\t' \
            + current_token().value)
  advance()
  rhs = parse_term_compare()
  if current_token().type != 'BY':
      error(meta_from_tokens(current_token(), current_token()),
            'expected "by" after equation, not\n\t' \
            + current_token().value)
  advance()
  reason = parse_proof()
  return (lhs, rhs, reason)

def parse_half_equation():
  if current_token().value == '...':
    advance()
    if current_token().type != 'EQUAL':
      error(meta_from_tokens(current_token(), current_token()),
              'expected "=" after "...", not\n\t' \
              + current_token().value)
    advance()
    rhs = parse_term_compare()
    if current_token().type != 'BY':
        error(meta_from_tokens(current_token(), current_token()),
              'expected "by" after equation, not\n\t' \
              + current_token().value)
    advance()
    reason = parse_proof()
    return (None, rhs, reason)
  elif current_token().value == '$':
    advance()
    return parse_equation()
  else:
    error(meta_from_tokens(current_token(), current_token()),
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
    advance()
    try:
      name = parse_identifier()
    except Exception as e:
      error(meta_from_tokens(current_token(), current_token()),
            'expected name of theorem, not:\n\t' + current_token().value)

    if current_token().type != 'COLON':
      error(meta_from_tokens(current_token(), current_token()),
            'expected a colon after theorem name, not\n\t' \
            + current_token().value)
    advance()
    what = parse_term()
    if current_token().type != 'PROOF':
      error(meta_from_tokens(current_token(), current_token()),
            'expected the keyword "proof" after formula of theorem, not\n\t' \
            + current_token().value)
    advance()
    proof = parse_proof()
    if current_token().type != 'END':
      error(meta_from_tokens(current_token(), current_token()),
            'expected the keyword "end" after proof of theorem, not\n\t' \
            + current_token().value)
    advance()
    return Theorem(meta_from_tokens(start_token, previous_token()),
                   name, what, proof, False)
  except Exception as e:
    meta = meta_from_tokens(start_token, previous_token())
    raise Exception(str(e) + '\n' + error_header(meta) + while_parsing)


def parse_union():
  while_parsing = 'while parsing\n' \
      + '\tstatement ::= "union" identifier type_params_opt "{" constructor* "}"\n'
  try:
    start_token = current_token()
    advance()
    name = parse_identifier()
    type_params = parse_type_parameters()

    if current_token().type != 'LBRACE':
      error(meta_from_tokens(current_token(), current_token()),
            'expected "{" after name of union, not\n\t' \
            + current_token().value)
    advance()
    constr_list = []
    while current_token().type != 'RBRACE':
      constr = parse_constructor()
      constr_list.append(constr)
    meta = meta_from_tokens(start_token, current_token())
    advance()
    return Union(meta, name, type_params, constr_list)
  except Exception as e:
    meta = meta_from_tokens(start_token, current_token())
    raise Exception(str(e) + '\n' + error_header(meta) + while_parsing)

def parse_function():
  while_parsing = 'while parsing\n' \
      + '\tstatement ::= "function" identifier type_params_opt' \
      + ' "(" type_list ")"\n\t\t\t "->" type "{" fun_case* "}"\n'
  try:
    start_token = current_token()
    advance()
    name = parse_identifier()
    type_params = parse_type_parameters()

    if current_token().type == 'LPAR':
      start_token = current_token()
      advance()
      param_types = parse_type_list()
      if current_token().type != 'RPAR':
        error(meta_from_tokens(start_token, previous_token()),
              'expected a closing parenthesis, not\n\t' \
              + quote(current_token().value))
      advance()

    if current_token().value != '->':
      error(meta_from_tokens(current_token(), current_token()),
            'expected "->" between parameter types and return type, not\n\t' \
            + quote(current_token().value))
    advance()
    return_type = parse_type()

    if current_token().type != 'LBRACE':
      error(meta_from_tokens(current_token(), current_token()),
            'expected open brace "{" after the return type of the function')
    advance()

    cases = []
    while current_token().type != 'RBRACE':
      fun_case = parse_fun_case()
      cases.append(fun_case)
    advance()
    return RecFun(meta_from_tokens(start_token, previous_token()), name,
                  type_params, param_types, return_type, cases)
  except Exception as e:
    meta = meta_from_tokens(start_token, current_token())
    raise Exception(str(e) + '\n' + error_header(meta) + while_parsing)
    
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
      error(meta_from_tokens(current_token(), current_token()),
            'expected "=" after name in "define"')
    advance()
    body = parse_term()
    return Define(meta_from_tokens(start_token, previous_token()),
                   name, typ, body)
  except Exception as e:
      meta = meta_from_tokens(start_token, previous_token())
      raise Exception(str(e) + '\n' + error_header(meta) + while_parsing)

  
statement_keywords = {'assert', 'define', 'function', 'import', 'print', 'theorem',
                      'union'}
    
def parse_statement():
  if end_of_file():
      error(meta_from_tokens(previous_token(),previous_token()),
            'expected a statement, not end of file')
  token = current_token()
  if token.type == 'ASSERT':
    while_parsing = 'while parsing assert\n' \
        + '\tstatement ::= "assert" formula\n'
    advance()
    try:
        body = parse_term()
        return Assert(meta_from_tokens(token, previous_token()), body)
    except Exception as e:
      meta = meta_from_tokens(token, previous_token())
      raise Exception(str(e) + '\n' + error_header(meta) + while_parsing)
  
  elif token.type == 'DEFINE':
    return parse_define()

  elif token.type == 'FUNCTION':
    return parse_function()

  elif token.type == 'IMPORT':
    while_parsing = 'while parsing import\n' \
        + '\tstatement ::= "import" identifier\n'
    advance()
    try:
        name = parse_identifier()
        return Import(meta_from_tokens(token, previous_token()), name)
    except Exception as e:
      meta = meta_from_tokens(token, previous_token())
      raise Exception(str(e) + '\n' + error_header(meta) + while_parsing)

  elif token.type == 'PRINT':
    while_parsing = 'while parsing\n' \
        + '\tstatement ::= "print" term\n'
    advance()
    try:
        subject = parse_term()
        meta = meta_from_tokens(token, previous_token())
        return Print(meta, subject)
    except Exception as e:
        meta = meta_from_tokens(token, previous_token())
        raise Exception(str(e) + '\n' + error_header(meta) + while_parsing)
        
  elif token.type == 'THEOREM' or token.type == 'LEMMA':
    return parse_theorem()

  elif token.type == 'UNION':
    return parse_union()

  else:
    for kw in statement_keywords:
        if edit_distance(token.value, kw) <= 2:
            error(meta_from_tokens(token, token),
                  'did you mean "' + kw \
                  + '" instead of "' + token.value + '"?')
      
    error(meta_from_tokens(token, token),
          'expected a statement, not\n\t' + token.value)

def parse_type_parameters():
  if current_token().type == 'LESSTHAN':
      advance()
      ident_list = parse_ident_list()
      if current_token().type != 'MORETHAN':
        error(meta_from_tokens(current_token(), current_token()),
              'expected closing ">" after type parameters of "fn", not\n\t' \
              + current_token().value)
      advance()
      return ident_list
  else:
      return []
    
def parse_type():
  if end_of_file():
      error(meta_from_tokens(previous_token(),previous_token()),
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
  elif token.type == 'LPAR':
    start_token = current_token()
    advance()
    typ = parse_type()
    if current_token().type != 'RPAR':
        error(meta_from_tokens(start_token, current_token()),
              'expected closing ")", not\n\t' + current_token().value)
    advance()
    return typ
  else:
    try:
      name = parse_identifier()
    except Exception as e:
      error(meta_from_tokens(token, current_token()),
            'expected a type, not\n\t' + quote(current_token().value))
    var = Var(meta_from_tokens(token,token), None, name)
    inst = False
    
    if current_token().type == 'LESSTHAN':
      inst = True
      start_token = current_token()
      advance()
      arg_types = parse_type_list()
      if current_token().type != 'MORETHAN':
          error(meta_from_tokens(start_token, previous_token()),
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
        error(meta_from_tokens(current_token(), current_token()),
              'expected "->" after parameter types, not\n\t' \
              + quote(current_token().value))
    advance()
    return_type = parse_type()
    return FunctionType(meta_from_tokens(start_token, previous_token()),
                        type_params, param_types, return_type)
  except Exception as e:
    meta = meta_from_tokens(start_token, current_token())
    raise Exception(str(e) + '\n' + error_header(meta) + while_parsing)
    
    
def parse_type_list():
  typ = parse_type()
  type_list = [typ]
  while current_token().type == 'COMMA':
    advance()
    typ = parse_type()
    type_list.append(typ)
  return type_list

def parse_term_list():
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
        error(meta_from_tokens(start_token, previous_token()),
              'missing closing parenthesis')
      advance()
    else:
      param_types = []
    meta = meta_from_tokens(start_token, previous_token())
    return Constructor(meta, name, param_types)
  except Exception as e:
    meta = meta_from_tokens(start_token, current_token())
    raise Exception(str(e) + '\n' + error_header(meta) + while_parsing)
    

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
      error(meta_from_tokens(start_token, previous_token()),
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
    except Exception as e:
      error(meta_from_tokens(start_token, current_token()),
            'expected a pattern, not\n\t' + quote(current_token().value))

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

def parse_type_annot_list():
  start_tok = current_token()
  ident = parse_identifier()
  if current_token().type == 'COLON':
    advance()
    ty = parse_type()
  else:
    error(meta_from_tokens(current_token(), current_token()), "Missing type annotation. Expected ':' followed by a type.\n" \
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
      error(meta_from_tokens(current_token(), current_token()), "Missing type annotation. Expected ':' followed by a type.\n" \
          + error_header(meta_from_tokens(start_tok, current_token())) \
          + 'while parsing\n\ttype_annot_list ::= identifier ":" type' \
          + '\n\ttype_annot_list ::= identifier ":" type "," type_annot_list')
    type_annot_list.append((ident, ty))
  return type_annot_list

def parse_var_list():
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
    name = parse_identifier()

    if current_token().type == 'LPAR':
      lpar_token = current_token()
      advance()
      pat_list = parse_pattern_list()
      if current_token().type != 'RPAR':
        error(meta_from_tokens(lpar_token, previous_token()),
              'expected closing parenthesis')
      advance()
    if current_token().type != 'EQUAL':
      error(meta_from_tokens(current_token(), current_token()),
            'expected "=" and then a term, not\n\t' + current_token())
    advance()
    body = parse_term()
    return FunCase(meta_from_tokens(start_token, previous_token()),
                   pat_list[0], pat_list[1:], body)
  except Exception as e:
    meta = meta_from_tokens(start_token, current_token())
    raise Exception(str(e) + '\n' + error_header(meta) + while_parsing)

def quote(str):
    return '"' + str + '"'

def parse_switch_case():
    while_parsing = '\nwhile parsing\n' \
        + '\tswitch_case ::= "case" pattern "{" term "}"'
    start_token = current_token()
    advance()
    try:
        pattern = parse_pattern()
    except Exception as e:
        raise Exception(str(e) + while_parsing)
    if current_token().type != 'LBRACE':
      error(meta_from_tokens(start_token,current_token()),
            'expected a "{" after pattern of case, not\n\t' \
            + quote(current_token().value) + while_parsing)
    advance()
    try:
      body = parse_term()
    except Exception as e:
      raise Exception(str(e) + while_parsing)
            
    if current_token().type != 'RBRACE':
      error(meta_from_tokens(start_token,current_token()),
            'expected a "}" after body of case, not\n\t' \
            + quote(current_token().value) + while_parsing)
    advance()
    return SwitchCase(meta_from_tokens(start_token, previous_token()),
                      pattern, body)
