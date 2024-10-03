from abstract_syntax import *
from lark import Lark, Token, logger, exceptions, tree
from error import *

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
    return (token_list[i].value, i + 1)
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
  if token.type == 'INT' or token.value == '0':
    return (intToNat(meta_from_tokens(token,token), int(token.value)), i + 1)
  elif token.type == 'TRUE':
    return (Bool(meta_from_tokens(token_list[i],token_list[i]),
                 None, True), i + 1)
  elif token.type == 'FALSE':
    return (Bool(meta_from_tokens(token_list[i],token_list[i]),
                 None, False), i + 1)
  elif token.type == 'LPAR':
    i = i + 1
    term, i = parse_term(token_list, i)
    if token_list[i].type != 'RPAR':
      error(meta_from_tokens(token_list[i], token_list[i]),
            'expected a closing parentheses, not\n\t' \
            + token_list[i].value)
    i = i + 1
    return (term, i)
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
    return Switch(meta_from_tokens(token, token_list[i-1]), None,
                  subject, cases), i
  elif token.type == 'FUN' or token.type == 'Λ':
    i = i + 1
    params, i = parse_ident_list(token_list, i)
    if token_list[i].type != 'LBRACE':
      error(meta_from_tokens(token_list[start],token_list[i]),
            'expected a `{` after parameters of fun, not\n\t' + token_list[i].value)
    i = i + 1
    body, i = parse_term(token_list, i)
    if token_list[i].type != 'RBRACE':
      error(meta_from_tokens(token, token_list[i]),
            'expected a `}` after body of fun, not\n\t' + token_list[i].value)
    i = i + 1
    return (Lambda(meta_from_tokens(token, token_list[i-1]), None, params, body), i)
  else:
    try:
      start = i
      name, i = parse_identifier(token_list, i)
      var = Var(meta_from_tokens(token_list[start], token_list[i-1]), None, name)
      return var,i
    except Exception as e:  
      error(meta_from_tokens(token_list[i],token_list[i]),
            'expected a term or formula, not\n\t' + token_list[i].value)
  
def parse_term(token_list, i):
  token = token_list[i]
  if token.type == 'IF':
    i = i + 1
    prem, i = parse_term(token_list, i)
    if token_list[i].type != 'THEN':
      error(meta_from_tokens(token_list[i],token_list[i]),
            'expected keyword `then` after premise of `if` formula, not\n\t' \
            + token_list[i].value)
    i = i + 1
    conc, i = parse_term(token_list, i)
    return IfThen(meta_from_tokens(token, token_list[i-1]), None, prem, conc),i
  
  else:
    term, i = parse_term_hi(token_list, i)
    if i < len(token_list):
      while token_list[i].type == 'AND':
        i = i + 1
        right, i = parse_term_hi(token_list, i)
        term = And(meta_from_tokens(token, token_list[i-1]), None,
                   extract_and(term) + extract_and(right))

      if token_list[i].type == 'LPAR':
        start = i
        i = i + 1
        args, i = parse_term_list(token_list, i)
        if token_list[i].type != 'RPAR':
          error(meta_from_tokens(token_list[start], token_list[i-1]),
                'expected a closing parenthesis')
        i = i + 1
        term = Call(meta_from_tokens(token, token_list[i-1]), None,
                    term, args, False)

      if token_list[i].type == 'SLASH':
        rator = Var(meta_from_tokens(token_list[i], token_list[i]),
                    None, '/')
        i = i + 1
        right, i = parse_term(token_list, i)
        term = Call(meta_from_tokens(token, token_list[i-1]), None,
                    rator, [term,right], True)

      if token_list[i].type == 'EQUAL':
        rator = Var(meta_from_tokens(token_list[i], token_list[i]),
                    None, '=')
        i = i + 1
        right, i = parse_term(token_list, i)
        term = Call(meta_from_tokens(token, token_list[i-1]), None,
                    rator, [term,right], True)
      
    return term, i

def parse_assumption(token_list, i):
  label,i = parse_identifier(token_list, i)
  if token_list[i].type == 'COLON':
    i = i + 1
    premise = parse_term(token_list, i)
    return label,premise,i
  else:
    return label,None,i

def parse_proof_hi(token_list, i):
  token = token_list[i]
  if token.type == 'SUPPOSE':
    i = i + 1
    label,premise,i = parse_assumption(token_list, i)
    meta = meta_from_tokens(token,token_list[i-1])
    body,i = parse_proof(token_list, i)
    return ImpIntro(meta, label, premise, body), i
  
  elif token.type == 'APPLY':
    i = i + 1
    imp,i = parse_proof(token_list, i)
    if token_list[i].type != 'TO':
      error(meta_from_tokens(token_list[i], token_list[i]),
            'expected `to` after implication part of `apply`, not\n\t' \
            + token_list[i].value)
    i = i + 1
    arg,i = parse_proof(token_list, i)
    return ModusPonens(meta_from_tokens(token, token_list[i-1]), imp, arg), i
  
  elif token.type == 'HAVE':
    i = i + 1
    label,i = parse_identifier(token_list, i)
    if token_list[i].type != 'COLON':
      error(meta_from_tokens(token_list[i], token_list[i]),
            'expected a colon after label of `have`, not\n\t' \
            + token_list[i].value)
    i = i + 1
    proved,i = parse_term(token_list, i)
    if token_list[i].type != 'BY':
      error(meta_from_tokens(token_list[i], token_list[i]),
            'expected the keyword `by` after formula of `have`, not\n\t' \
            + token_list[i].value)
    i = i + 1
    because,i = parse_proof(token_list, i)
    body,i = parse_proof(token_list, i)
    return PLet(meta_from_tokens(token, token_list[i-1]),
                label, proved, because, body), i
  
  elif token.type == 'DOT':
    i = i + 1
    return PTrue(meta_from_tokens(token, token)), i
  
  elif token.type == 'LPAR':
    i = i + 1
    proof, i = parse_proof(token_list, i)
    if token_list[i].type != 'RPAR':
      error(meta_from_tokens(token_list[i], token_list[i]),
            'expected a closing parentheses, not\n\t' \
            + token_list[i].value)
    i = i + 1
    return proof, i
    
  else:
    name, i = parse_identifier(token_list, i)
    return PVar(meta_from_tokens(token, token), name), i
  
def parse_proof(token_list, i):
    start = i
    proof, i = parse_proof_hi(token_list, i)
    while token_list[i].type == 'COMMA':
      i = i + 1
      right, i = parse_proof_hi(token_list, i)
      proof = PTuple(meta_from_tokens(token_list[start], token_list[i-1]), 
                    [proof, right])
    return proof, i

def parse_theorem(token_list, i):
  i = i + 1
  name, i = parse_identifier(token_list, i)
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
  return Theorem(meta_from_tokens(token, token_list[i-1]),
                 name, what, proof, False), i

def parse_union(token_list, i):
  start = i
  i = i + 1
  name, i = parse_identifier(token_list, i)
  # todo: parse optional type parameters

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
  return Union(meta, name, [], constr_list), i

def parse_function(token_list, i):
  begin = i
  i = i + 1
  name, i = parse_identifier(token_list, i)
  # todo: parse optional type parameters
  type_params = []

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
    
def parse_statement(token_list, i):
  token = token_list[i]
  if token.type == 'THEOREM':
    return parse_theorem(token_list, i)
  elif token.type == 'UNION':
    return parse_union(token_list, i)
  elif token.type == 'IMPORT':
    i = i + 1
    name, i = parse_identifier(token_list, i)
    return Import(meta_from_tokens(token, token_list[i-1]), name), i
  elif token.type == 'FUNCTION':
    return parse_function(token_list, i)
  elif token.type == 'DEFINE':
    return parse_define(token_list, i)
  elif token.type == 'ASSERT':
    i = i + 1
    body, i = parse_term(token_list, i)
    return (Assert(meta_from_tokens(token, token_list[i-1]), body), i)
  else:
    error(meta_from_tokens(token, token),
          'expected a statement, not\n\t' + token_list[i].value)

def parse_type(token_list, i):
  token = token_list[i]
  if token.type == 'BOOL':
    return BoolType(meta_from_tokens(token,token)), i + 1
  elif token.type == 'FN':
    # TODO: handle type parameters
    i = i + 1
    param_types, i = parse_type_list(token_list, i)
    if token_list[i].value != '->':
        error(meta_from_tokens(token_list[i], token_list[i]),
              'expected `->` after parameter types in this function type')
    i = i + 1
    return_type, i = parse_type(token_list, i)
    return (FunctionType(meta_from_tokens(token, token_list[i-1]),
                         [], param_types, return_type), i)
  else:
    name, i = parse_identifier(token_list, i)
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
