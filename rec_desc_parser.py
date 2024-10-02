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
  if token.type == 'TRUE':
    return Bool(meta_from_tokens(token_list[i],token_list[i]),
                None, True), i + 1
  elif token.type == 'FALSE':
    return Bool(meta_from_tokens(token_list[i],token_list[i]),
                None, False), i + 1
  elif token.type == 'LPAR':
    i = i + 1
    term, i = parse_term(token_list, i)
    if token_list[i].type != 'RPAR':
      error(meta_from_tokens(token_list[i], token_list[i]),
            'expected a closing parentheses, not\n\t' \
            + token_list[i].value)
    i = i + 1
    return term, i
  else:
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
    while token_list[i].type == 'AND':
      i = i + 1
      right, i = parse_term_hi(token_list, i)
      term = And(meta_from_tokens(token, token_list[i-1]), None,
                 [term, right])
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
  
def parse_statement(token_list, i):
  token = token_list[i]
  if token.type == 'THEOREM':
    name, i = parse_identifier(token_list, i + 1)
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
  else:
    error(meta_from_tokens(token, token),
          'expected a statement, not\n\t' + token_list[i].value)

