from abstract_syntax import *
import dataclasses
from dataclasses import dataclass
from lark import Lark, Token, Tree, logger

from lark import logger
import logging
#logger.setLevel(logging.DEBUG)

filename = '???'

def set_filename(fname):
    global filename
    filename = fname

def get_filename():
    global filename
    return filename
    
##################################################
# Concrete Syntax Parser
##################################################

lark_parser = Lark(open("./Deduce.lark").read(), start='program', parser='lalr',
                   debug=True, propagate_positions=True)

##################################################
# Parsing Concrete to Abstract Syntax
##################################################

def parse_tree_to_str_list(e):
    if e.data == 'empty':
        return tuple([])
    elif e.data == 'single':
        return tuple([str(e.children[0].value)])
    elif e.data == 'push':
        return tuple([str(e.children[0].value)]) \
            + parse_tree_to_str_list(e.children[1])
    else:
        raise Exception('parse_tree_to_str_list, unexpected ' + str(e))

def parse_tree_to_list(e):
    if e.data == 'empty':
        return tuple([])
    elif e.data == 'single':
        return tuple([parse_tree_to_ast(e.children[0])])
    elif e.data == 'push':
        return tuple([parse_tree_to_ast(e.children[0])]) \
            + parse_tree_to_list(e.children[1])
    elif e.data == 'empty_binding':
        return tuple([])
    elif e.data == 'single_binding':
        ident = parse_tree_to_ast(e.children[0])
        typ = parse_tree_to_ast(e.children[1])
        return tuple([(str(ident.value),typ)])
    elif e.data == 'push_binding':
        ident = parse_tree_to_ast(e.children[0])
        typ = parse_tree_to_ast(e.children[1])
        return tuple([(str(ident.value),typ)]) + parse_tree_to_list(e.children[2])
    else:
        raise Exception('parse_tree_to_str_list, unexpected ' + str(e))

def extract_and(frm):
    match frm:
      case And(loc, args):
        return args
      case _:
       return [frm]

def extract_or(frm):
    match frm:
      case Or(loc, args):
        return args
      case _:
       return [frm]

def parse_tree_to_case(e):
    tag = str(e.children[0].value)
    body = parse_tree_to_ast(e.children[1])
    return (tag, body)

def parse_tree_to_case_list(e):
    if e.data == 'single':
        return (parse_tree_to_case(e.children[0]),)
    elif e.data == 'push':
        return (parse_tree_to_case(e.children[0]),) \
            + parse_tree_to_case_list(e.children[1])
    else:
        raise Exception('unrecognized as a type list ' + repr(e))
    
infix_ops = {'add', 'sub', 'mul', 'div', 'int_div', 'mod', 'circ',
             'and', 'or','equal', 'not_equal',
             'less', 'greater', 'less_equal', 'greater_equal'}

prefix_ops = {'neg', 'not'}

operator_symbol = {'add': '+', 'sub': '-', 'mul': '*', 'div': '/', 'circ': '∘',
                   'int_div': 'div', 'mod': '%', 'neg':'-', 
                   'and': 'and', 'or':'or', 'not': 'not',
                   'equal': '=', 'not_equal': '≠',
                   'less': '<', 'greater': '>',
                   'less_equal': '≤', 'greater_equal': '≥'}

impl_num = 0
def next_impl_num():
    global impl_num
    ret = impl_num
    impl_num += 1
    return ret
    
def extract_tuple(pf):
    match pf:
      case PTuple(loc, pfs):
        return pfs
      case _:
       return [pf]
   
def parse_tree_to_ast(e):
    if isinstance(e, Token):
        return e
    
    e.meta.filename = filename

    if e.data == 'nothing':
        return None
    # formulas
    elif e.data == 'term_formula':
        return parse_tree_to_ast(e.children[0])
    elif e.data == 'if_then_formula':
       return IfThen(e.meta,
                     parse_tree_to_ast(e.children[0]),
                     parse_tree_to_ast(e.children[1]))
    elif e.data == 'and_formula':
       left = parse_tree_to_ast(e.children[0])
       right = parse_tree_to_ast(e.children[1])
       return And(e.meta, extract_and(left) + extract_and(right))
    elif e.data == 'or_formula':
       left = parse_tree_to_ast(e.children[0])
       right = parse_tree_to_ast(e.children[1])
       return Or(e.meta, extract_or(left) + extract_or(right))
    elif e.data == 'all_formula':
        return All(e.meta,
                   parse_tree_to_list(e.children[0]),
                   parse_tree_to_ast(e.children[1]))
    elif e.data == 'some_formula':
        return Some(e.meta,
                    parse_tree_to_list(e.children[0]),
                    parse_tree_to_ast(e.children[1]))
    
    # types
    elif e.data == 'type_name':
      return Var(e.meta, str(e.children[0].value))
    elif e.data == 'int_type':
      return IntType(e.meta)
    elif e.data == 'bool_type':
      return BoolType(e.meta)
    elif e.data == 'type_type':
      return TypeType(e.meta)
    elif e.data == 'function_type':
      return FunctionType(e.meta,
                          [str(tok.value) for tok in parse_tree_to_list(e.children[0])],
                          parse_tree_to_list(e.children[1]),
                          parse_tree_to_ast(e.children[2]))
    elif e.data == 'type_inst':
      return TypeInst(e.meta, Var(e.meta, str(e.children[0].value)),
                      parse_tree_to_list(e.children[1]))
    # terms
    elif e.data == 'let_term':
        return TLet(e.meta, str(e.children[0].value),
                    parse_tree_to_ast(e.children[1]),
                    parse_tree_to_ast(e.children[2]))
    elif e.data == 'annote_type':
        return TAnnote(e.meta, parse_tree_to_ast(e.children[0]),
                       parse_tree_to_ast(e.children[1]))
    elif e.data == 'term_inst':
        return TermInst(e.meta, parse_tree_to_ast(e.children[0]),
                        parse_tree_to_list(e.children[1]))
    elif e.data == 'term_var':
        return Var(e.meta, str(e.children[0].value))
    elif e.data == 'conditional':
        return Conditional(e.meta,
                           parse_tree_to_ast(e.children[0]),
                           parse_tree_to_ast(e.children[1]),
                           parse_tree_to_ast(e.children[2]))
    elif e.data == 'int':
        # return Int(e.meta, int(e.children[0]))
        return intToNat(e.meta, int(e.children[0]))
    elif e.data == 'true_literal':
        return Bool(e.meta, True)
    elif e.data == 'false_literal':
        return Bool(e.meta, False)
    elif e.data == 'field_access':
        subject = parse_tree_to_ast(e.children[0])
        field_name = str(e.children[1].value)
        return FieldAccess(e.meta, subject, field_name)
    elif e.data == 'call':
        rator = parse_tree_to_ast(e.children[0])
        rands = parse_tree_to_list(e.children[1])
        return Call(e.meta, rator, rands, False)
    elif e.data == 'lambda':
        return Lambda(e.meta,
                      parse_tree_to_str_list(e.children[0]),
                      parse_tree_to_ast(e.children[1]))
    elif e.data == 'generic':
        return Generic(e.meta,
                       parse_tree_to_str_list(e.children[0]),
                       parse_tree_to_ast(e.children[1]))
    elif e.data in infix_ops:
        return Call(e.meta, Var(e.meta, operator_symbol[e.data]),
                    [parse_tree_to_ast(c) for c in e.children],
                    True)
    elif e.data in prefix_ops:
        return Call(e.meta, Var(e.meta, operator_symbol[e.data]),
                    [parse_tree_to_ast(c) for c in e.children],
                    False)
    elif e.data == 'switch_case':
        e1 , e2 = e.children
        return SwitchCase(e.meta, parse_tree_to_ast(e1), parse_tree_to_ast(e2))
    elif e.data == 'switch':
        e1 , e2 = e.children
        return Switch(e.meta, parse_tree_to_ast(e1), parse_tree_to_list(e2))
    
    # proofs
    if e.data == 'proof_var':
        return PVar(e.meta, str(e.children[0].value))
    elif e.data == 'modus_ponens':
        e1, e2 = e.children
        return ModusPonens(e.meta, parse_tree_to_ast(e1), parse_tree_to_ast(e2))
    elif e.data == 'true_proof':
        return PTrue(e.meta)
    elif e.data == 'hole_proof':
        return PHole(e.meta)
    elif e.data == 'refl_proof':
        return PReflexive(e.meta)
    elif e.data == 'sym_proof':
        e1 = e.children[0]
        eq1 = parse_tree_to_ast(e1)
        return PSymmetric(e.meta, eq1)
    elif e.data == 'trans_proof':
        e1, e2 = e.children
        eq1 = parse_tree_to_ast(e1)
        eq2 = parse_tree_to_ast(e2)
        return PTransitive(e.meta, eq1, eq2)
    elif e.data == 'injective_proof':
        e1, e2 = e.children
        constr = parse_tree_to_ast(e1)
        eq = parse_tree_to_ast(e2)
        return PInjective(e.meta, constr, eq)
    elif e.data == 'paren':
        return parse_tree_to_ast(e.children[0])
    elif e.data == 'let':
        return PLet(e.meta,
                    str(e.children[0].value),
                    parse_tree_to_ast(e.children[1]),
                    parse_tree_to_ast(e.children[2]),
                    parse_tree_to_ast(e.children[3]))
    elif e.data == 'annot':
        return PAnnot(e.meta,
                      parse_tree_to_ast(e.children[0]),
                      parse_tree_to_ast(e.children[1]))
    elif e.data == 'tuple':
       left = parse_tree_to_ast(e.children[0])
       right = parse_tree_to_ast(e.children[1])
       return PTuple(e.meta, extract_tuple(left) + extract_tuple(right))
    elif e.data == 'imp_intro':
        label = str(e.children[0].value)
        body = parse_tree_to_ast(e.children[1])
        return ImpIntro(e.meta, label, None, body)
    elif e.data == 'all_intro':
        vars = parse_tree_to_list(e.children[0])
        body = parse_tree_to_ast(e.children[1])
        return AllIntro(e.meta, vars, body)
    elif e.data == 'all_elim':
        univ = parse_tree_to_ast(e.children[0])
        args = parse_tree_to_list(e.children[1])
        return AllElim(e.meta, univ, args)
    elif e.data == 'some_intro':
        witnesses = parse_tree_to_list(e.children[0])
        body = parse_tree_to_ast(e.children[1])
        return SomeIntro(e.meta, witnesses, body)
    elif e.data == 'some_elim':
        witnesses = [tok.value for tok in parse_tree_to_list(e.children[0])]
        label = parse_tree_to_ast(e.children[1])
        some = parse_tree_to_ast(e.children[2])
        body = parse_tree_to_ast(e.children[3])
        return SomeElim(e.meta, witnesses, label, some, body)
    elif e.data == 'imp_intro_explicit':
        label = str(e.children[0].value)
        premise = parse_tree_to_ast(e.children[1])
        body = parse_tree_to_ast(e.children[2])
        return ImpIntro(e.meta, label, premise, body)
    elif e.data == 'cases':
        return Cases(e.meta,
                     parse_tree_to_ast(e.children[0]),
                     parse_tree_to_case_list(e.children[1]))
    elif e.data == 'induction':
        typ = parse_tree_to_ast(e.children[0])
        cases = parse_tree_to_list(e.children[1])
        return Induction(e.meta, typ, cases)
    elif e.data == 'switch_pf_case':
        pat = parse_tree_to_ast(e.children[0])
        body = parse_tree_to_ast(e.children[1])
        return SwitchProofCase(e.meta, pat, body)
    elif e.data == 'switch_proof':
        subject = parse_tree_to_ast(e.children[0])
        cases = parse_tree_to_list(e.children[1])
        return SwitchProof(e.meta, subject, cases)
    elif e.data == 'ind_case':
        pat = parse_tree_to_ast(e.children[0])
        body = parse_tree_to_ast(e.children[1])
        return IndCase(e.meta, pat, body)
    elif e.data == 'apply_defs_goal':
        definitions = parse_tree_to_list(e.children[0])
        body = parse_tree_to_ast(e.children[1])
        return ApplyDefsGoal(e.meta, definitions, body)
    elif e.data == 'apply_defs_fact':
        definitions = parse_tree_to_list(e.children[0])
        subject = parse_tree_to_ast(e.children[1])
        body = parse_tree_to_ast(e.children[2])
        return ApplyDefsFact(e.meta, definitions, subject, body)
    elif e.data == 'rewrite_goal':
        eq = parse_tree_to_ast(e.children[0])
        body = parse_tree_to_ast(e.children[1])
        return RewriteGoal(e.meta, eq, body)
    elif e.data == 'rewrite_fact':
        subject = parse_tree_to_ast(e.children[0])
        eq = parse_tree_to_ast(e.children[1])
        return RewriteFact(e.meta, subject, eq)
    elif e.data == 'equation':
        lhs = parse_tree_to_ast(e.children[0])
        rhs = parse_tree_to_ast(e.children[1])
        reason = parse_tree_to_ast(e.children[2])
        return (lhs, rhs, reason)
    elif e.data == 'half_equation':
        rhs = parse_tree_to_ast(e.children[0])
        reason = parse_tree_to_ast(e.children[1])
        return (rhs, reason)
    elif e.data == 'equations_proof':
        first = parse_tree_to_ast(e.children[0])
        rest = parse_tree_to_list(e.children[1])
        eqs = [first]
        for (rhs, reason) in rest:
            lhs = eqs[-1][1].copy()
            eqs.append((lhs, rhs, reason))
        result = None
        for (lhs, rhs, reason) in reversed(eqs):
            eq_proof = PAnnot(e.meta, mkEqual(e.meta, lhs, rhs), reason)
            if result == None:
                result = eq_proof
            else:
                result = PTransitive(e.meta, eq_proof, result)
        return result
    
    # constructor declaration
    elif e.data == 'constr_id':
        return Constructor(e.meta, str(e.children[0].value), [])
    elif e.data == 'constr_apply':
        param_types = parse_tree_to_list(e.children[1])
        return Constructor(e.meta, str(e.children[0].value), param_types)
    
    # union definitions
    elif e.data == 'union':
        return Union(e.meta, str(e.children[0].value),
                     [str(tok.value) for tok in parse_tree_to_list(e.children[1])],
                     parse_tree_to_list(e.children[2]))
    
    # theorem definitions
    elif e.data == 'theorem':
        return Theorem(e.meta,
                       str(e.children[0].value),
                       parse_tree_to_ast(e.children[1]),
                       parse_tree_to_ast(e.children[2]))

    # patterns in function definitions
    elif e.data == 'pattern_id':
        return PatternCons(e.meta, Var(e.meta, str(e.children[0].value)), [])
    elif e.data == 'pattern_zero':
        return PatternCons(e.meta, Var(e.meta, 'zero'), [])
    elif e.data == 'pattern_true':
        return PatternBool(e.meta, True)
    elif e.data == 'pattern_false':
        return PatternBool(e.meta, False)
    elif e.data == 'pattern_apply':
        params = parse_tree_to_str_list(e.children[1])
        return PatternCons(e.meta, Var(e.meta, str(e.children[0].value)), params)
    
    # case of a recursive function
    elif e.data == 'fun_case':
        pp = parse_tree_to_list(e.children[1])
        return FunCase(e.meta, pp[0], pp[1:],
                       parse_tree_to_ast(e.children[2]))
    # recursive functions
    elif e.data == 'rec_fun':
        return RecFun(e.meta, str(e.children[0].value),
                      [str(tok.value) for tok in parse_tree_to_list(e.children[1])],
                      parse_tree_to_list(e.children[2]),
                      parse_tree_to_ast(e.children[3]),
                      parse_tree_to_list(e.children[4]))

    # term definition
    elif e.data == 'define':
        return Define(e.meta, str(e.children[0].value), 
                      None,
                      parse_tree_to_ast(e.children[1]))
    elif e.data == 'define_annot':
        return Define(e.meta, str(e.children[0].value), 
                      parse_tree_to_ast(e.children[1]),
                      parse_tree_to_ast(e.children[2]))

    # import module/file
    elif e.data == 'import':
        return Import(e.meta, str(e.children[0].value))
    
    # whole program
    elif e.data == 'program':
        return parse_tree_to_list(e.children[0])
    elif e.data == 'proof_hi' and e.children == []:
        # TODO: improve this error message!
        raise Exception('unexpected end of proof after the semicolon')
    else:
        raise Exception('unhandled parse tree', e)

def parse(s, trace = False):
    lexed = lark_parser.lex(s)
    if trace:
        print('tokens: ')
        for word in lexed:
            print(repr(word))
        print('')
    parse_tree = lark_parser.parse(s)
    if trace:
        print('parse tree: ')
        print(parse_tree)
        print('')
    ast = parse_tree_to_ast(parse_tree)
    if trace:
        print('abstract syntax tree: ')
        print(ast)
        print('')
    return ast
