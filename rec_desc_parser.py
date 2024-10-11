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
compare_operators = {'<', '>', '≤', '<=', '>', '>=', '⊆', '(=', '∈', 'in'}
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

def parse(program_text, trace = False, error_expected = False):
  lexed = lark_parser.lex(program_text)
  token_list = []
  for token in lexed:
    if trace:
      print(repr(token))
    token_list.append(token)

  stmts = []
  i = 0
  while i < len(token_list):
    stmt, i = parse_statement(token_list, i)
    stmts.append(stmt)
  return stmts

def parse_identifier(token_list, i):
  token = token_list[i]
  if token.type == 'IDENT':
    return (token.value, i + 1)
  elif token.value == 'operator':
    i = i + 1
    return (to_unicode.get(token_list[i].value, token_list[i].value), i + 1)
  else:
    error(meta_from_tokens(token, token),
          'expected an identifier, not ' + token.value)

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

def parse_term_hi(token_list, i):
  token = token_list[i]

  if token.type == 'ALL':
    i = i + 1
    vars, i = parse_var_list(token_list, i)
    if token_list[i].type != 'DOT':
      error(meta_from_tokens(token, token_list[i]),
            'expected a `.` after parameters of `all`, not\n\t' \
            + token_list[i].value)
    i = i + 1
    body, i = parse_term(token_list, i)
    return (All(meta_from_tokens(token, token_list[i-1]),
                None, vars, body), i)
    
  elif token.type == 'AT':
    i = i + 1
    subject, i = parse_term_hi(token_list, i)
    if token_list[i].type != 'LESSTHAN':
      error(meta_from_tokens(token_list[i],token_list[i]),
            'expected `<` after subject of instantiation (`@`), not\n\t' \
            + token_list[i].value)
    i = i + 1
    type_args, i = parse_type_list(token_list, i)
    if token_list[i].type != 'MORETHAN':
      error(meta_from_tokens(token_list[i],token_list[i]),
            'expected closing `>` after type arguments of instantiation (`@`)' \
            + ' , not\n\t' + token_list[i].value)
    i = i + 1
    meta = meta_from_tokens(token, token_list[i-1])
    return (TermInst(meta, None, subject, type_args), i)

  elif token.type == 'DEFINE':
    i = i + 1
    name, i = parse_identifier(token_list, i)
    if token_list[i].type != 'EQUAL':
        error(meta_from_tokens(token_list[i],token_list[i]),
              'expected `=` after name in `define`, not\n\t' \
              + token_list[i].value)
    i = i + 1
    rhs, i = parse_term(token_list, i)
    meta = meta_from_tokens(token, token_list[i-1])
    body, i = parse_term(token_list, i)
    return (TLet(meta, None, name, rhs, body), i)

  elif token.type == 'FALSE':
    return (Bool(meta_from_tokens(token_list[i],token_list[i]),
                 None, False), i + 1)

  elif token.type == 'INT' or token.value == '0':
    return (intToNat(meta_from_tokens(token,token), int(token.value)), i + 1)

  elif token.type == 'IF':
    i = i + 1
    prem, i = parse_term(token_list, i)
    if token_list[i].type != 'THEN':
      error(meta_from_tokens(token_list[i],token_list[i]),
            'expected keyword `then` after premise of `if` formula, not\n\t' \
            + token_list[i].value)
    i = i + 1
    conc, i = parse_term(token_list, i)

    if token_list[i].type == 'ELSE':
      i = i + 1
      els, i = parse_term(token_list, i)
      return (Conditional(meta_from_tokens(token, token_list[i-1]), None,
                          prem, conc, els), i)
    else:
      return (IfThen(meta_from_tokens(token, token_list[i-1]),
                     None, prem, conc), i)

  elif token.value == '∅' or token.value == '.0.':
    i = i + 1
    meta = meta_from_tokens(token, token)
    return (Call(meta, None,
                Var(meta, None, 'char_fun'),
                [Lambda(meta, None, [('_',None)], Bool(meta, None, False))],
                 False), i)

  elif token.type == 'FUN' or token.type == 'Λ':
    start = i
    i = i + 1
    params, i = parse_var_list(token_list, i)
    if token_list[i].type != 'LBRACE':
      error(meta_from_tokens(token_list[start],token_list[i]),
            'expected a `{` after parameters of fun, not\n\t' \
            + token_list[i].value)
    i = i + 1
    body, i = parse_term(token_list, i)
    if token_list[i].type != 'RBRACE':
      error(meta_from_tokens(token, token_list[i-1]),
            'expected a `}` after body of fun, not\n\t' + token_list[i].value)
    i = i + 1
    return (Lambda(meta_from_tokens(token, token_list[i-1]),
                   None, params, body), i)

  elif token.type == 'GENERIC':
    i = i + 1
    params, i = parse_ident_list(token_list, i)
    if token_list[i].type != 'LBRACE':
      error(meta_from_tokens(token_list[start],token_list[i]),
            'expected a `{` after parameters of `generic`, not\n\t' \
            + token_list[i].value)
    i = i + 1
    body, i = parse_term(token_list, i)
    if token_list[i].type != 'RBRACE':
      error(meta_from_tokens(token, token_list[i]),
            'expected a `}` after body of `generic`, not\n\t' \
            + token_list[i].value)
    i = i + 1
    meta = meta_from_tokens(token, token_list[i-1])
    return (Generic(meta, None, params, body), i)
    
  elif token.type == 'LESSTHAN':
    i = i + 1
    type_params, i = parse_ident_list(token_list, i)
    if token_list[i].type != 'MORETHAN':
        error(meta_from_tokens(token, token_list[i-1]),
              'expected closing `>` after type parameters')
    i = i + 1
    body, i = parse_term(token_list, i)
    meta = meta_from_tokens(token, token_list[i-1])
    return (All(meta, None,
                [(v, TypeType(meta)) for v in type_params],
                body), i)
    
  elif token.type == 'LPAR':
    i = i + 1
    term, i = parse_term(token_list, i)
    if token_list[i].type != 'RPAR':
      error(meta_from_tokens(token_list[i], token_list[i]),
            'expected a closing parentheses, not\n\t' \
            + token_list[i].value)
    i = i + 1
    return (term, i)

  elif token.type == 'LBRACE':
    i = i + 1
    term, i = parse_term(token_list, i)
    if token_list[i].type != 'RBRACE':
      error(meta_from_tokens(token_list[i], token_list[i]),
            'expected a closing parentheses, not\n\t' \
            + token_list[i].value)
    i = i + 1
    meta = meta_from_tokens(token, token_list[i-1])
    return (Mark(meta, None, term), i)

  elif token.value == '─':
    i = i + 1
    meta = meta_from_tokens(token,token)
    return (Omitted(meta, None), i)
    
  elif token.type == 'NOT':
    i = i + 1
    subject, i = parse_term_equal(token_list, i)
    meta = meta_from_tokens(token, token_list[i-1])
    return (IfThen(meta, None, subject, Bool(meta, None, False)), i)
    
  elif token.type == 'QMARK':
    i = i + 1
    meta = meta_from_tokens(token,token)
    return (Hole(meta, None), i)

  elif token.type == 'SOME':
    i = i + 1
    vars, i = parse_var_list(token_list, i)
    if token_list[i].type != 'DOT':
      error(meta_from_tokens(token, token_list[i]),
            'expected a `.` after parameters of `some`, not\n\t' \
            + token_list[i].value)
    i = i + 1
    body, i = parse_term(token_list, i)
    return (Some(meta_from_tokens(token, token_list[i-1]),
                None, vars, body), i)

  elif token.type == 'SWITCH':
    start = i
    i = i + 1
    subject, i = parse_term(token_list, i)
    if token_list[i].type != 'LBRACE':
      error(meta_from_tokens(token_list[i], token_list[i]),
            'expected `{` after subject of switch, not\n\t' \
            + token_list[i].value)
    i = i + 1
    cases = []
    while token_list[i].type == 'CASE':
      switch_case, i = parse_switch_case(token_list, i)
      cases.append(switch_case)
    if token_list[i].type != 'RBRACE':
      error(meta_from_tokens(token_list[start],token_list[i]),
            'expected a `}` after last case of switch, not\n\t' \
            + token_list[i].value)
    i = i + 1
    return (Switch(meta_from_tokens(token, token_list[i-1]), None,
                   subject, cases), i)

  elif token.type == 'TRUE':
    return (Bool(meta_from_tokens(token_list[i],token_list[i]),
                 None, True), i + 1)

  elif token.type == 'LSQB':
    i = i + 1
    if token_list[i].type == 'RSQB':
        return (listToNodeList(meta_from_tokens(token,token), []), i + 1)
    lst_terms = []
    term, i = parse_term(token_list, i)
    lst_terms.append(term)
    token = token_list[i]
    while token.type == 'COMMA':
      i = i + 1
      term, i = parse_term(token_list, i)
      lst_terms.append(term)
      token = token_list[i]
    if token.type != 'RSQB':
      error(meta_from_tokens(token_list[i],token_list[i]),
            'expected a closing brace \']\', not\n\t' + token_list[i].value)
    return (listToNodeList(meta_from_tokens(token,token), lst_terms), i + 1)
    
  else:
    try:
      start = i
      name, i = parse_identifier(token_list, i)
      meta = meta_from_tokens(token_list[start], token_list[i-1])
      var = Var(meta, None, name)
      return (var, i)
    except Exception as e:  
      error(meta_from_tokens(token,token_list[i]),
            'expected a term or formula\n' + str(e))

def parse_call(token_list, i):
  term, i = parse_term_hi(token_list, i)

  while i < len(token_list) and token_list[i].type == 'LPAR':
    start = i
    i = i + 1
    args, i = parse_term_list(token_list, i)
    if token_list[i].type != 'RPAR':
      error(meta_from_tokens(token_list[start], token_list[i-1]),
            'expected a closing parenthesis')
    i = i + 1
    term = Call(meta_from_tokens(token_list[start], token_list[i-1]), None,
                term, args, False)

  return (term, i)
    
def parse_term_mult(token_list, i):
  term, i = parse_call(token_list, i)

  while i < len(token_list) and token_list[i].value in mult_operators:
    start = i
    rator = Var(meta_from_tokens(token_list[i], token_list[i]),
                None, to_unicode.get(token_list[i].value,token_list[i].value))
    i = i + 1
    right, i = parse_term_mult(token_list, i)
    term = Call(meta_from_tokens(token_list[start], token_list[i-1]), None,
                rator, [term,right], True)
    
  return (term, i)

def parse_term_add(token_list, i):
  token = token_list[i]
  term, i = parse_term_mult(token_list, i)

  while i < len(token_list) and token_list[i].value in add_operators:
    rator = Var(meta_from_tokens(token_list[i], token_list[i]),
                None, to_unicode.get(token_list[i].value, token_list[i].value))
    i = i + 1
    right, i = parse_term_add(token_list, i)
    term = Call(meta_from_tokens(token, token_list[i-1]), None,
                rator, [term,right], True)
    
  return (term, i)

def parse_term_compare(token_list, i):
  token = token_list[i]
  term, i = parse_term_add(token_list, i)

  while i < len(token_list) and token_list[i].value in compare_operators:
    rator = Var(meta_from_tokens(token_list[i], token_list[i]),
                None, to_unicode.get(token_list[i].value, token_list[i].value))
    i = i + 1
    right, i = parse_term_compare(token_list, i)
    term = Call(meta_from_tokens(token, token_list[i-1]), None,
                rator, [term,right], True)
    
  return term, i

def parse_term_equal(token_list, i):
  token = token_list[i]
  term, i = parse_term_compare(token_list, i)
  while i < len(token_list) and token_list[i].value in equal_operators:
    meta = meta_from_tokens(token_list[i], token_list[i])
    opr = token_list[i].value
    eq = Var(meta, None, '=')
    i = i + 1
    right, i = parse_term_equal(token_list, i)
    if opr == '=':
      term = Call(meta_from_tokens(token, token_list[i-1]), None,
                  eq, [term,right], True)
    elif opr == '≠' or opr == '!=':
      term = IfThen(meta, None, 
                    Call(meta, None, eq, [term,right], True),
                    Bool(meta, None, False))
  return term, i
    
def parse_term_log(token_list, i):
  token = token_list[i]
  term, i = parse_term_equal(token_list, i)
  while i < len(token_list) and (token_list[i].type == 'AND'
                                 or token_list[i].type == 'OR'):
    opr = token_list[i].type
    i = i + 1
    right, i = parse_term_log(token_list, i)
    if opr == 'AND':
      term = And(meta_from_tokens(token, token_list[i-1]), None,
                 extract_and(term) + extract_and(right))
    elif opr == 'OR':
      term = Or(meta_from_tokens(token, token_list[i-1]), None,
                 extract_or(term) + extract_or(right))        

  if i < len(token_list) and token_list[i].type == 'COLON':
    i = i + 1
    typ, i = parse_type(token_list, i)
    term = TAnnote(meta_from_tokens(token, token_list[i-1]), None,
                   term, typ)
      
  return term, i

def parse_term(token_list, i):
  token = token_list[i]
  term, i = parse_term_log(token_list, i)
  if i < len(token_list) and (token_list[i].value in iff_operators):
    i = i + 1
    right, i = parse_term_log(token_list, i)
    loc = meta_from_tokens(token, token_list[i-1])
    left_right = IfThen(loc, None, term.copy(), right.copy())
    right_left = IfThen(loc, None, right.copy(), term.copy())
    term = And(loc, None, [left_right, right_left])
  
  if i < len(token_list) and token_list[i].type == 'COLON':
    i = i + 1
    typ, i = parse_type(token_list, i)
    term = TAnnote(meta_from_tokens(token, token_list[i-1]), None,
                   term, typ)
      
  return term, i

def parse_assumption(token_list, i):
  if token_list[i].type == 'COLON':
    label = '_'
  else:
    label,i = parse_identifier(token_list, i)
  if token_list[i].type == 'COLON':
    i = i + 1
    premise, i = parse_term(token_list, i)
    return label,premise,i
  else:
    return label,None,i

proof_keywords = {'apply', 'arbitrary',
                  'choose', 'conclude', 'conjunct',
                  'definition',
                  'enable', 'equations', 'extensionality',
                  'have', 'induction', 'obtain',
                  'reflexive', 'rewrite',
                  'suffices', 'suppose', 'switch', 'symmetric',
                  'transitive'}

def parse_definition_proof(token_list, i):
  token = token_list[i]
  i = i + 1
  if token_list[i].type == 'LBRACE':
    i = i + 1
    defs, i = parse_ident_list(token_list, i)
    if token_list[i].type != 'RBRACE':
        error(meta_from_tokens(token_list[i], token_list[i]),
              'expected closing `}`, not\n\t' + token_list[i].value)
    i = i + 1
  else:
    defn, i = parse_identifier(token_list, i)
    defs = [defn]

  if token_list[i].type == 'AND':
      i = i + 1
      if token_list[i].type != 'REWRITE':
          error(meta_from_tokens(token_list[i],token_list[i]),
                'expected `rewrite` after `and` and `definition`, not\n\t' \
                + token_list[i].value)
      i = i + 1
      eqns, i = parse_proof_list(token_list, i)
      meta = meta_from_tokens(token, token_list[i-1])
      return (ApplyDefsGoal(meta,
                            [Var(meta, None, t) for t in defs],
                            Rewrite(meta, eqns)), i)
  elif token_list[i].type == 'IN':
      i = i + 1
      subject, i = parse_proof(token_list, i)
      meta = meta_from_tokens(token, token_list[i-1])
      return (ApplyDefsFact(meta, [Var(meta, None, t) for t in defs],
                            subject), i)
  else:
      meta = meta_from_tokens(token, token_list[i-1])
      return (ApplyDefs(meta, [Var(meta, None, n) for n in defs]), i)

def parse_recall(token_list, i):
  start = i
  i = i + 1
  facts,i = parse_term_list(token_list, i)
  meta = meta_from_tokens(token_list[start], token_list[i-1])
  return (PFrom(meta, facts), i)
  
def parse_proof_hi(token_list, i):
  token = token_list[i]
  if token.type == 'APPLY':
    i = i + 1
    imp,i = parse_proof(token_list, i)
    if token_list[i].type != 'TO':
      error(meta_from_tokens(token_list[i], token_list[i]),
            'expected `to` after implication part of `apply`, not\n\t' \
            + token_list[i].value)
    i = i + 1
    arg,i = parse_proof(token_list, i)
    return ModusPonens(meta_from_tokens(token, token_list[i-1]), imp, arg), i

  elif token.type == 'ARBITRARY':
    i = i + 1
    vars, i = parse_var_list(token_list, i)
    body, i = parse_proof(token_list, i)
    return (AllIntro(meta_from_tokens(token, token_list[i-1]), vars, body), i)
    
  elif token.type == 'CASES':
    i = i + 1
    subject, i = parse_proof(token_list, i)
    cases = []
    while i < len(token_list) and token_list[i].type == 'CASE':
        c, i = parse_case(token_list, i)
        cases.append(c)
    meta = meta_from_tokens(token, token_list[i-1])
    return (Cases(meta, subject, cases), i)
    
  elif token.type == 'CHOOSE':
    i = i + 1
    witnesses, i = parse_term_list(token_list, i)
    meta = meta_from_tokens(token, token_list[i-1])
    body, i = parse_proof(token_list, i)
    return (SomeIntro(meta, witnesses, body), i)
    
  elif token.type == 'CONCLUDE':
    i = i + 1
    claim, i = parse_term(token_list, i)
    if token_list[i].type == 'BY':
      i = i + 1
      reason, i = parse_proof(token_list, i)
    else:
      error(meta_from_tokens(token_list[i], token_list[i]),
            'expected the keyword `by` after formula of `conclude`, '\
            + 'not\n\t' + token_list[i].value)
    return (PAnnot(meta_from_tokens(token, token_list[i-1]),
                   claim, reason), i)

  elif token.type == 'CONJUNCT':
    i = i + 1
    meta = meta_from_tokens(token_list[i],token_list[i])
    index = int(token_list[i].value)
    i = i + 1
    if token_list[i].type != 'OF':
      error(meta_from_tokens(token_list[i],token_list[i]),
            'expected keyword `of` after index of `conjunct`, not\n\t' \
            + token_list[i].value)
    i = i + 1
    
    subject, i = parse_proof(token_list, i)
    meta = meta_from_tokens(token,token_list[i-1])
    return (PAndElim(meta, index, subject), i)
      
  elif token.type == 'DEFINE':
    i = i + 1
    name, i = parse_identifier(token_list, i)
    if token_list[i].type != 'EQUAL':
        error(meta_from_tokens(token_list[i],token_list[i]),
              'expected `=` after name in `define`, not\n\t' + token_list[i].value)
    i = i + 1
    rhs, i = parse_term(token_list, i)
    meta = meta_from_tokens(token, token_list[i-1])
    body, i = parse_proof(token_list, i)
    return (PTLetNew(meta, name, rhs, body), i)
      
  elif token.type == 'DEFINITION':
    return parse_definition_proof(token_list, i)

  elif token.type == 'DOT':
    i = i + 1
    return PTrue(meta_from_tokens(token, token)), i
  
  elif token.type == 'ENABLE':
    i = i + 1
    if token_list[i].type != 'LBRACE':
        error(meta_from_tokens(token_list[i], token_list[i]),
              'expected `{` after `enable`')
    i = i + 1
    defs, i = parse_ident_list(token_list, i)
    if token_list[i].type != 'RBRACE':
        error(meta_from_tokens(token_list[i], token_list[i]),
              'expected closing `}` in `enable`')
    i = i + 1
    body, i = parse_proof(token_list, i)
    meta = meta_from_tokens(token, token_list[i-1])
    return (EnableDefs(meta,
                       [Var(meta, None, x) for x in defs],
                       body), i)
      
  elif token.type == 'EQUATIONS':
    i = i + 1
    first, i = parse_equation(token_list, i)
    rest, i = parse_equation_list(token_list, i)
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
    return result, i    
    
  elif token.type == 'EXTENSIONALITY':
    i = i + 1
    body, i = parse_proof(token_list, i)
    meta = meta_from_tokens(token, token_list[i-1])
    return (PExtensionality(meta, body), i)

  elif token.type == 'RECALL':
    return parse_recall(token_list, i)
    
  elif token.type == 'HAVE':
    i = i + 1
    if token_list[i].type != 'COLON':
      label,i = parse_identifier(token_list, i)
    else:
      label = '_'
    if token_list[i].type != 'COLON':
      error(meta_from_tokens(token_list[i], token_list[i]),
            'expected a colon after label of `have`, not\n\t' \
            + token_list[i].value)
    i = i + 1
    proved,i = parse_term(token_list, i)
    if token_list[i].type == 'BY':
      i = i + 1
      because,i = parse_proof(token_list, i)
    else:        
      error(meta_from_tokens(token_list[i], token_list[i]),
            'expected the keyword `by` after formula of `have`, ' \
            + 'not\n\t' + token_list[i].value)
    body,i = parse_proof(token_list, i)
    return PLet(meta_from_tokens(token, token_list[i-1]),
                label, proved, because, body), i
  
  elif token.type == 'INDUCTION':
    i = i + 1
    typ, i = parse_type(token_list, i)
    cases = []
    while token_list[i].type == 'CASE':
        c, i = parse_induction_case(token_list, i)
        cases.append(c)
    return (Induction(meta_from_tokens(token, token_list[i-1]), typ, cases), i)
        
  elif token.type == 'INJECTIVE':
    i = i + 1
    constr, i = parse_term(token_list, i)
    body, i = parse_proof(token_list, i)
    meta = meta_from_tokens(token, token_list[i-1])
    return (PInjective(meta, constr, body), i)

  elif token.type == 'LPAR':
    i = i + 1
    proof, i = parse_proof(token_list, i)
    if token_list[i].type != 'RPAR':
      error(meta_from_tokens(token_list[i], token_list[i]),
            'expected a closing parentheses, not\n\t' \
            + token_list[i].value)
    i = i + 1
    return proof, i

  elif token.type == 'LBRACE':
    i = i + 1
    proof, i = parse_proof(token_list, i)
    if token_list[i].type != 'RBRACE':
      error(meta_from_tokens(token_list[i], token_list[i]),
            'expected a closing `}`, not\n\t' \
            + token_list[i].value)
    i = i + 1
    return proof, i

  elif token.type == 'OBTAIN':
    i = i + 1
    witnesses, i = parse_ident_list(token_list, i)
    if token_list[i].type != 'WHERE':
      error(meta_from_tokens(token_list[i], token_list[i]),
            'expected `where` after variables of `obtain`, not\n\t' \
            + token_list[i].value)
    i = i + 1
    label, premise, i = parse_assumption(token_list, i)
    if token_list[i].type != 'FROM':
      error(meta_from_tokens(token_list[i], token_list[i]),
            'expected `from` after `where` part of `obtain`, not\n\t' \
            + token_list[i].value)
    i = i + 1
    some, i = parse_proof(token_list, i)
    body, i = parse_proof(token_list, i)
    meta = meta_from_tokens(token, token_list[i-1])
    return (SomeElim(meta, witnesses, label, premise, some, body), i)
    
  elif token.type == 'QMARK':
    i = i + 1
    meta = meta_from_tokens(token, token)
    return (PHole(meta), i)

  elif token.type == 'SORRY':
    i = i + 1
    meta = meta_from_tokens(token,token)
    return (PSorry(meta), i)

  elif token.type == 'HELP':
    i = i + 1
    subject, i = parse_proof(token_list, i)
    meta = meta_from_tokens(token,token_list[i-1])
    return (PHelpUse(meta, subject), i)

  elif token.type == 'REFLEXIVE':
    i = i + 1
    meta = meta_from_tokens(token, token)
    return (PReflexive(meta), i)

  elif token.type == 'REWRITE':
    i = i + 1
    proofs, i = parse_proof_list(token_list, i)
    if token_list[i].type == 'IN':
      i = i + 1
      subject, i = parse_proof(token_list, i)
      meta = meta_from_tokens(token, token_list[i-1])
      return (RewriteFact(meta, subject, proofs), i)
    else:
      meta = meta_from_tokens(token, token_list[i-1])
      return (Rewrite(meta, proofs), i)
    
  elif token.type == 'SUFFICES':
    i = i + 1
    formula, i = parse_term(token_list, i)
    if token_list[i].type != 'BY':
      error(meta_from_tokens(token_list[i], token_list[i]),
            'expected the keyword `by` after formula of `suffices`, not\n\t' \
            + token_list[i].value)
    i = i + 1
    proof, i = parse_proof(token_list, i)
    meta = meta_from_tokens(token, token_list[i-1])
    body, i = parse_proof(token_list, i)
    return (Suffices(meta, formula, proof, body), i)
    
  elif token.type == 'SUPPOSE' or token.type == 'ASSUME':
    start = i
    i = i + 1
    try:
      label,premise,i = parse_assumption(token_list, i)
    except Exception as e:
      error(meta_from_tokens(token, token_list[i]),
            'expected an assumption:\n\t"assume" label ":" formula\n' \
            + str(e))
      
    meta = meta_from_tokens(token,token_list[i-1])
    body,i = parse_proof(token_list, i)
    return ImpIntro(meta, label, premise, body), i

  elif token.type == 'SWITCH':
    i = i + 1
    subject, i = parse_term(token_list, i)
    if token_list[i].type == 'FOR':
        i = i + 1
        defs, i = parse_ident_list(token_list, i)
    else:
        defs = []
    if token_list[i].type != 'LBRACE':
        error(meta_from_tokens(token_list[i], token_list[i]),
              'expected `{` after subject of `switch`')
    i = i + 1
    cases = []
    while token_list[i].type == 'CASE':
        c, i = parse_proof_switch_case(token_list, i)
        cases.append(c)
    if token_list[i].type != 'RBRACE':
        error(meta_from_tokens(token_list[i], token_list[i]),
              'expected closing `}` after cases of `switch`')
    i = i + 1
    meta = meta_from_tokens(token, token_list[i-1])
    if len(defs) == 0:
        return (SwitchProof(meta, subject, cases), i)
    else:
        return (ApplyDefsGoal(meta, [Var(meta, None, t) for t in defs],
                              SwitchProof(meta, subject, cases)), i)
    
  elif token.type == 'SYMMETRIC':
    i = i + 1
    eq, i = parse_proof(token_list, i)
    meta = meta_from_tokens(token, token)
    return (PSymmetric(meta, eq), i)

  elif token.type == 'TRANSITIVE':
    i = i + 1
    eq1, i = parse_proof(token_list, i)
    eq2, i = parse_proof(token_list, i)
    meta = meta_from_tokens(token, token)
    return (PTransitive(meta, eq1, eq2), i)

  else:
    for kw in proof_keywords:
        if edit_distance(token.value, kw) <= 2:
            error(meta_from_tokens(token, token),
                  'did you mean `' + kw \
                  + '` instead of `' + token_list[i].value + '`?')

    try:
      name, i = parse_identifier(token_list, i)
    except Exception as e:
      error(meta_from_tokens(token, token_list[i]),
            'expected a proof\n' + str(e))
    return (PVar(meta_from_tokens(token, token), name), i)

def parse_proof_list(token_list, i):
  proof_list = []
  proof, i = parse_proof(token_list, i)
  proof_list.append(proof)
  while i < len(token_list) and token_list[i].value == '|':
    i = i + 1
    proof, i = parse_proof(token_list, i)
    proof_list.append(proof)
  return (proof_list, i)      

def parse_case(token_list, i):
    start = i
    i = i + 1
    label,premise, i = parse_assumption(token_list, i)
    if token_list[i].type != 'LBRACE':
      error(meta_from_tokens(token_list[start],token_list[i]),
            'expected a `{` after assumption of `case`, not\n\t' \
            + token_list[i].value)
    i = i + 1
    body, i = parse_proof(token_list, i)
    if token_list[i].type != 'RBRACE':
      error(meta_from_tokens(token_list[start],token_list[i]),
            'expected a `}` after body of case, not\n\t' + token_list[i].value)
    i = i + 1
    return ((label,premise,body), i)

def parse_proof_switch_case(token_list, i):
    start = i
    i = i + 1
    pat, i = parse_pattern(token_list, i)
    if token_list[i].type == 'SUPPOSE' or token_list[i].type == 'ASSUME':
        i = i + 1
        assumptions = []
        label,asm, i = parse_assumption(token_list, i)
        assumptions.append((label,asm))
        while token_list[i].type == 'COMMA':
            i = i + 1
            label,asm, i = parse_assumption(token_list, i)
            assumptions.append((label,asm))
    else:
        assumptions = []
    if token_list[i].type != 'LBRACE':
      error(meta_from_tokens(token_list[start],token_list[i]),
            'expected a `{` after assumption of `case`, not\n\t' \
            + token_list[i].value)
    i = i + 1
    body, i = parse_proof(token_list, i)
    if token_list[i].type != 'RBRACE':
      error(meta_from_tokens(token_list[start],token_list[i]),
            'expected a `}` after body of case, not\n\t' + token_list[i].value)
    i = i + 1
    meta = meta_from_tokens(token_list[start],token_list[i-1])
    return (SwitchProofCase(meta, pat, assumptions, body), i)    
    
def parse_proof_med(token_list, i):
    start = i
    proof, i = parse_proof_hi(token_list, i)
    
    while i < len(token_list) and token_list[i].type == 'LESSTHAN':
      i = i + 1
      type_list, i = parse_type_list(token_list, i)
      if token_list[i].type != 'MORETHAN':
        error(meta_from_tokens(token_list[i],token_list[i]),
              'expected a closing `>`, not\n\t' + token_list[i].value)
      i = i + 1
      proof = AllElimTypes(meta_from_tokens(token_list[start], token_list[i-1]),
                           proof, type_list)
      
    while i < len(token_list) and token_list[i].type == 'LSQB':
      i = i + 1
      term_list, i = parse_term_list(token_list, i)
      if token_list[i].type != 'RSQB':
        error(meta_from_tokens(token_list[i],token_list[i]),
              'expected a closing `]`, not\n\t' + token_list[i].value)
      i = i + 1
      proof = AllElim(meta_from_tokens(token_list[start], token_list[i-1]),
                      proof, term_list)

    return (proof, i)
    
def parse_proof(token_list, i):
    start = i
    proof, i = parse_proof_med(token_list, i)
    while token_list[i].type == 'COMMA':
      i = i + 1
      right, i = parse_proof(token_list, i)
      proof = PTuple(meta_from_tokens(token_list[start], token_list[i-1]), 
                    [proof, right])
    return proof, i

def parse_induction_case(token_list, i):
    start = i
    i = i + 1
    pat, i = parse_pattern(token_list, i)
    ind_hyps = []
    if token_list[i].type == 'SUPPOSE' or token_list[i].type == 'ASSUME':
      i = i + 1
      label,ih, i = parse_assumption(token_list, i)
      ind_hyps.append((label,ih))
      while token_list[i].type == 'COMMA':
          i = i + 1
          label,ih, i = parse_assumption(token_list, i)
          ind_hyps.append((label,ih))
    if token_list[i].type != 'LBRACE':
      error(meta_from_tokens(token_list[i], token_list[i]),
            'expected `{` after pattern of `case`, not\n\t' \
            + token_list[i].value)
    i = i + 1
    body, i = parse_proof(token_list, i)
    if token_list[i].type != 'RBRACE':
      error(meta_from_tokens(token_list[i], token_list[i]),
            'expected `}` after body of induction case, not\n\t' \
            + token_list[i].value)
    i = i + 1
    return (IndCase(meta_from_tokens(token_list[start], token_list[i-1]),
                    pat, ind_hyps, body), i)

def parse_equation(token_list, i):
  lhs, i = parse_term_compare(token_list, i)
  if token_list[i].type != 'EQUAL':
      error(meta_from_tokens(token_list[i], token_list[i]),
            'expected `=` after left-hand side of equation, not\n\t' \
            + token_list[i].value)
  i = i + 1
  rhs, i = parse_term_compare(token_list, i)
  if token_list[i].type != 'BY':
      error(meta_from_tokens(token_list[i], token_list[i]),
            'expected `by` after equation, not\n\t' \
            + token_list[i].value)
  i = i + 1
  reason, i = parse_proof(token_list, i)
  return (lhs, rhs, reason), i

def parse_half_equation(token_list, i):
  if token_list[i].value == '|':
    i = i + 1
    eqn, i = parse_equation(token_list, i)
    return eqn, i
  elif token_list[i].value == '...':
    i = i + 1
    if token_list[i].type != 'EQUAL':
      error(meta_from_tokens(token_list[i], token_list[i]),
              'expected `=` after `...`, not\n\t' \
              + token_list[i].value)
    i = i + 1
    rhs, i = parse_term_compare(token_list, i)
    if token_list[i].type != 'BY':
        error(meta_from_tokens(token_list[i], token_list[i]),
              'expected `by` after equation, not\n\t' \
              + token_list[i].value)
    i = i + 1
    reason, i = parse_proof(token_list, i)
    return (None, rhs, reason), i
  else:
    error(meta_from_tokens(token_list[i], token_list[i]),
          'expected `... = rhs` or `| lhs = rhs` in `equations`, not\n\t' \
          + token_list[i].value)

def parse_equation_list(token_list, i):
  eqn_list = []
  while token_list[i].value == '|' or token_list[i].value == '...':
    eqn, i = parse_half_equation(token_list, i)
    eqn_list.append(eqn)
  return eqn_list, i

def parse_theorem(token_list, i):
  start = i
  i = i + 1
  try:
    name, i = parse_identifier(token_list, i)
  except Exception as e:
    error(meta_from_tokens(token_list[i], token_list[i]),
          'expected name of theorem, not:\n\t' + token_list[i].value)
        
  if token_list[i].type != 'COLON':
    error(meta_from_tokens(token_list[i], token_list[i]),
          'expected a colon after theorem name, not\n\t' \
          + token_list[i].value)
  i = i + 1
  what, i = parse_term(token_list, i)
  if token_list[i].type != 'PROOF':
    error(meta_from_tokens(token_list[i], token_list[i]),
          'expected the keyword `proof` after formula of theorem, not\n\t' \
          + token_list[i].value)
  i = i + 1
  proof, i = parse_proof(token_list, i)
  if token_list[i].type != 'END':
    error(meta_from_tokens(token_list[i], token_list[i]),
          'expected the keyword `end` after proof of theorem, not\n\t' \
          + token_list[i].value)
  i = i + 1
  return Theorem(meta_from_tokens(token_list[start], token_list[i-1]),
                 name, what, proof, False), i

def parse_union(token_list, i):
  start = i
  i = i + 1
  name, i = parse_identifier(token_list, i)
  type_params, i = parse_type_parameters(token_list, i)

  if token_list[i].type != 'LBRACE':
    error(meta_from_tokens(token_list[i], token_list[i]),
          'expected `{` after name of union, not\n\t' \
          + token_list[i].value)
  i = i + 1
  constr_list = []
  while token_list[i].type != 'RBRACE':
    constr, i = parse_constructor(token_list, i)
    constr_list.append(constr)
  i = i + 1

  meta = meta_from_tokens(token_list[start], token_list[i-1])
  return Union(meta, name, type_params, constr_list), i

def parse_function(token_list, i):
  begin = i
  i = i + 1
  name, i = parse_identifier(token_list, i)
  type_params, i = parse_type_parameters(token_list, i)

  if token_list[i].type == 'LPAR':
    start = i
    i = i + 1
    param_types, i = parse_type_list(token_list, i)
    if token_list[i].type != 'RPAR':
      error(meta_from_tokens(token_list[start], token_list[i-1]),
            'expected a closing parenthesis')
    i = i + 1

  if token_list[i].value != '->':
    error(meta_from_tokens(token_list[i], token_list[i]),
          'expected `->` between function parameter types and return type')
  i = i + 1
  return_type, i = parse_type(token_list, i)

  if token_list[i].type != 'LBRACE':
    error(meta_from_tokens(token_list[i], token_list[i]),
          'expected open brace `{` after the return type of the function')
  i = i + 1

  cases = []
  while token_list[i].type != 'RBRACE':
    fun_case, i = parse_fun_case(token_list, i)
    cases.append(fun_case)
  i = i + 1
  return RecFun(meta_from_tokens(token_list[begin], token_list[i-1]), name,
                type_params, param_types, return_type, cases), i
    
def parse_define(token_list, i):
  start = i
  i = i + 1
  name, i = parse_identifier(token_list, i)
  if token_list[i].type == 'COLON':
    i = i + 1
    typ, i = parse_type(token_list, i)
  else:
    typ = None
  if token_list[i].type != 'EQUAL':
    error(meta_from_tokens(token_list[i], token_list[i]),
          'expected `=` after name in `define`')
  i = i + 1
  body, i = parse_term(token_list, i)  
  return (Define(meta_from_tokens(token_list[start], token_list[i-1]),
                 name, typ, body), i)

statement_keywords = {'assert', 'define', 'function', 'import', 'print', 'theorem',
                      'union'}
    
def parse_statement(token_list, i):
  token = token_list[i]
  if token.type == 'ASSERT':
    i = i + 1
    body, i = parse_term(token_list, i)
    return (Assert(meta_from_tokens(token, token_list[i-1]), body), i)
  elif token.type == 'DEFINE':
    return parse_define(token_list, i)
  elif token.type == 'FUNCTION':
    return parse_function(token_list, i)
  elif token.type == 'IMPORT':
    i = i + 1
    name, i = parse_identifier(token_list, i)
    return (Import(meta_from_tokens(token, token_list[i-1]), name), i)
  elif token.type == 'PRINT':
    i = i + 1
    subject, i = parse_term(token_list, i)
    meta = meta_from_tokens(token, token_list[i-1])
    return (Print(meta, subject), i)
  elif token.type == 'THEOREM' or token.type == 'LEMMA':
    return parse_theorem(token_list, i)
  elif token.type == 'UNION':
    return parse_union(token_list, i)
  else:
    for kw in statement_keywords:
        if edit_distance(token.value, kw) <= 2:
            error(meta_from_tokens(token, token),
                  'did you mean `' + kw \
                  + '` instead of `' + token.value + '`?')
      
    error(meta_from_tokens(token, token),
          'expected a statement, not\n\t' + token.value)

def parse_type_parameters(token_list, i):
  if token_list[i].type == 'LESSTHAN':
      i = i + 1
      ident_list, i = parse_ident_list(token_list, i)
      if token_list[i].type != 'MORETHAN':
        error(meta_from_tokens(token_list[i], token_list[i]),
              'expected closing `>` after type parameters of `fn`, not\n\t' \
              + token_list[i].value)
      i = i + 1
      return ident_list, i
  else:
      return [], i
    
def parse_type(token_list, i):
  token = token_list[i]
  if token.type == 'BOOL':
    return BoolType(meta_from_tokens(token,token)), i + 1
  if token.type == 'TYPE':
    return TypeType(meta_from_tokens(token,token)), i + 1
  elif token.type == 'FN':
    i = i + 1
    type_params, i = parse_type_parameters(token_list, i)
    param_types, i = parse_type_list(token_list, i)
    if token_list[i].value != '->':
        error(meta_from_tokens(token_list[i], token_list[i]),
              'expected `->` after parameter types in this function type')
    i = i + 1
    return_type, i = parse_type(token_list, i)
    return (FunctionType(meta_from_tokens(token, token_list[i-1]),
                         type_params, param_types, return_type), i)
  elif token.type == 'LPAR':
    start = i
    i = i + 1
    typ, i = parse_type(token_list, i)
    if token_list[i].type != 'RPAR':
        error(meta_from_tokens(token_list[start], token_list[i]),
              'expected closing `)`, not\n\t' + token_list[i].value)
    i = i + 1
    return typ, i
  else:
    try:
      name, i = parse_identifier(token_list, i)
    except Exception as e:
      error(meta_from_tokens(token, token_list[i]),
            'expected a type\n' + str(e))
    var = Var(meta_from_tokens(token,token), None, name)
    inst = False
    
    if token_list[i].type == 'LESSTHAN':
      inst = True
      start = i
      i = i + 1
      arg_types, i = parse_type_list(token_list, i)
      if token_list[i].type != 'MORETHAN':
          error(meta_from_tokens(token_list[start], token_list[i-1]),
                'expected a closing `>`')
      i = i + 1
    if inst:
        return TypeInst(meta_from_tokens(token, token_list[i-1]),
                        var, arg_types), i
    else:
        return var, i
    
def parse_type_list(token_list, i):
  typ, i = parse_type(token_list, i)
  type_list = [typ]
  while token_list[i].type == 'COMMA':
    i = i + 1
    typ, i = parse_type(token_list, i)
    type_list.append(typ)
  return type_list, i

def parse_term_list(token_list, i):
  trm, i = parse_term(token_list, i)
  trm_list = [trm]
  while token_list[i].type == 'COMMA':
    i = i + 1
    trm, i = parse_term(token_list, i)
    trm_list.append(trm)
  return trm_list, i
    
def parse_constructor(token_list, i):
  token = token_list[i]
  name, i = parse_identifier(token_list, i)

  if token_list[i].type == 'LPAR':
    i = i + 1
    param_types, i = parse_type_list(token_list, i)
    if token_list[i].type != 'RPAR':
      error(meta_from_tokens(token, token_list[i-1]),
            'missing closing parenthesis')
    i = i + 1
  else:
    param_types = []
  meta = meta_from_tokens(token, token_list[i-1])
  return Constructor(meta, name, param_types), i

def parse_pattern(token_list, i):
  if token_list[i].value == '0':
    i = i + 1
    meta = meta_from_tokens(token_list[i], token_list[i])
    return PatternCons(meta, Var(meta, None, 'zero'), []), i
  if token_list[i].type == 'LSQB' and token_list[i+1].type == 'RSQB':
    i = i + 2
    meta = meta_from_tokens(token_list[i], token_list[i])
    return PatternCons(meta, Var(meta, None, 'empty'), []), i
  elif token_list[i].type == 'TRUE':
    i = i + 1
    meta = meta_from_tokens(token_list[i], token_list[i])
    return (PatternBool(meta, True), i)
  elif token_list[i].type == 'FALSE':
    i = i + 1
    meta = meta_from_tokens(token_list[i], token_list[i])
    return (PatternBool(meta, False), i)
  else:
    begin = i
    constr_name, i = parse_identifier(token_list, i)
    ident_list = []
    if token_list[i].type == 'LPAR':
      start = i
      i = i + 1
      ident, i = parse_identifier(token_list, i)
      ident_list.append(ident)
      while token_list[i].type == 'COMMA':
        i = i + 1
        ident, i = parse_identifier(token_list, i)
        ident_list.append(ident)
      if token_list[i].type != 'RPAR':
        error(meta_from_tokens(token_list[start], token_list[i-1]),
              'expected a closing parenthesis')
      i = i + 1
    return PatternCons(meta_from_tokens(token_list[begin], token_list[i-1]),
                       Var(meta_from_tokens(token_list[begin],token_list[begin]),
                           None, constr_name),
                       ident_list), i

def parse_pattern_list(token_list, i):
  pat, i = parse_pattern(token_list, i)
  if token_list[i].type == 'COMMA':
    i = i + 1
    ident_list, i = parse_ident_list(token_list, i)
    return ([pat] + ident_list), i
  else:
    return [pat], i
      
def parse_ident_list(token_list, i):
  ident, i = parse_identifier(token_list, i)
  ident_list = [ident]
  while token_list[i].type == 'COMMA':
    i = i + 1
    ident, i = parse_identifier(token_list, i)
    ident_list.append(ident)
  return ident_list, i

def parse_var_list(token_list, i):
  ident, i = parse_identifier(token_list, i)
  if token_list[i].type == 'COLON':
    i = i + 1
    ty, i = parse_type(token_list, i)
  else:
    ty = None
  var_list = [(ident,ty)]
  
  while token_list[i].type == 'COMMA':
    i = i + 1
    ident, i = parse_identifier(token_list, i)
    if token_list[i].type == 'COLON':
      i = i + 1
      ty, i = parse_type(token_list, i)
    else:
      ty = None
    var_list.append((ident, ty))
  return var_list, i
  
def parse_fun_case(token_list, i):
  begin = i
  name, i = parse_identifier(token_list, i)
  
  if token_list[i].type == 'LPAR':
    start = i
    i = i + 1
    pat_list, i = parse_pattern_list(token_list, i)
    if token_list[i].type != 'RPAR':
      error(meta_from_tokens(token_list[start], token_list[i-1]),
            'expected closing parenthesis')
    i = i + 1
  if token_list[i].type != 'EQUAL':
    error(meta_from_tokens(token_list[i], token_list[i]),
          'expected `=` and then a term, not\n\t' + token_list[i])
  i = i + 1
  body, i = parse_term(token_list, i)
  return FunCase(meta_from_tokens(token_list[begin], token_list[i-1]),
                 pat_list[0], pat_list[1:], body), i

def parse_switch_case(token_list, i):
    start = i
    i = i + 1
    pattern, i = parse_pattern(token_list, i)
    if token_list[i].type != 'LBRACE':
      error(meta_from_tokens(token_list[start],token_list[i]),
            'expected a `{` after pattern of case, not\n\t' + token_list[i].value)
    i = i + 1
    body, i = parse_term(token_list, i)
    if token_list[i].type != 'RBRACE':
      error(meta_from_tokens(token_list[start],token_list[i]),
            'expected a `}` after body of case, not\n\t' + token_list[i].value)
    i = i + 1
    return SwitchCase(meta_from_tokens(token_list[start], token_list[i-1]),
                      pattern, body), i
