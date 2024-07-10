from abstract_syntax import *
import dataclasses
from dataclasses import dataclass
from lark import Lark, Token, Tree, logger
from error import *

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

def parse_tree_to_list(e, parent):
    if e.data == 'empty':
        return tuple([])
    elif e.data == 'single':
        return tuple([parse_tree_to_ast(e.children[0], parent)])
    elif e.data == 'push':
        return tuple([parse_tree_to_ast(e.children[0], parent)]) \
            + parse_tree_to_list(e.children[1], parent)
    elif e.data == 'empty_binding':
        return tuple([])
    elif e.data == 'single_binding':
        ident = parse_tree_to_ast(e.children[0], parent)
        typ = parse_tree_to_ast(e.children[1], parent)
        return tuple([(ident,typ)])
    elif e.data == 'single_var':
        ident = parse_tree_to_ast(e.children[0], parent)
        return tuple([(ident,None)])
    elif e.data == 'push_binding':
        ident = parse_tree_to_ast(e.children[0], parent)
        typ = parse_tree_to_ast(e.children[1], parent)
        return tuple([(ident,typ)]) + parse_tree_to_list(e.children[2], parent)
    elif e.data == 'push_var':
        ident = parse_tree_to_ast(e.children[0], parent)
        return tuple([(ident,None)]) + parse_tree_to_list(e.children[1], parent)
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
    body = parse_tree_to_ast(e.children[1], e)
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
             'less', 'greater', 'less_equal', 'greater_equal',
             'subset_equal', 'union_op', 'intersect', 'membership', 'multiset_sum'}

prefix_ops = {'neg', 'not'}

operator_symbol = {'add': '+', 'sub': '-', 'mul': '*', 'div': '/', 'circ': '∘',
                   'int_div': 'div', 'mod': '%', 'neg':'-', 
                   'and': 'and', 'or':'or', 'not': 'not',
                   'equal': '=', 'not_equal': '≠',
                   'less': '<', 'greater': '>',
                   'less_equal': '≤', 'greater_equal': '≥',
                   'subset_equal': '⊆', 'union_op': '∪', 'intersect': '∩',
                   'membership': '∈', 'multiset_sum': '⨄'}

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
   
def parse_tree_to_ast(e, parent):
    if isinstance(e, Token):
        return e
    
    e.meta.filename = filename

    if e.data == 'nothing':
        return None
    # formulas
    elif e.data == 'term_formula':
        return parse_tree_to_ast(e.children[0], e)
    elif e.data == 'if_then_formula':
       return IfThen(e.meta,
                     parse_tree_to_ast(e.children[0], e),
                     parse_tree_to_ast(e.children[1], e))
    elif e.data == 'and_formula':
       left = parse_tree_to_ast(e.children[0], e)
       right = parse_tree_to_ast(e.children[1], e)
       return And(e.meta, extract_and(left) + extract_and(right))
       #return And(e.meta, [left,right])
    elif e.data == 'or_formula':
       left = parse_tree_to_ast(e.children[0], e)
       right = parse_tree_to_ast(e.children[1], e)
       return Or(e.meta, extract_or(left) + extract_or(right))
       #return Or(e.meta, [left, right])
    elif e.data == 'logical_not':
       subject = parse_tree_to_ast(e.children[0], e)
       return IfThen(e.meta, subject, Bool(e.meta, False))
    elif e.data == 'all_formula':
        return All(e.meta,
                   parse_tree_to_list(e.children[0], e),
                   parse_tree_to_ast(e.children[1], e))
    elif e.data == 'alltype_formula':
        vars = parse_tree_to_list(e.children[0], e)
        return All(e.meta,
                   [(v, TypeType(e.meta)) for v in vars],
                   parse_tree_to_ast(e.children[1], e))
    elif e.data == 'some_formula':
        return Some(e.meta,
                    parse_tree_to_list(e.children[0], e),
                    parse_tree_to_ast(e.children[1], e))
    
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
                          parse_tree_to_list(e.children[0], e),
                          parse_tree_to_list(e.children[1], e),
                          parse_tree_to_ast(e.children[2], e))
    elif e.data == 'type_inst':
      return TypeInst(e.meta, Var(e.meta, str(e.children[0].value)),
                      parse_tree_to_list(e.children[1], e))
    # terms
    elif e.data == 'define_term':
        return TLet(e.meta, str(e.children[0].value),
                    parse_tree_to_ast(e.children[1], e),
                    parse_tree_to_ast(e.children[2], e))
    elif e.data == 'annote_type':
        return TAnnote(e.meta, parse_tree_to_ast(e.children[0], e),
                       parse_tree_to_ast(e.children[1], e))
    elif e.data == 'term_inst':
        return TermInst(e.meta, parse_tree_to_ast(e.children[0], e),
                        parse_tree_to_list(e.children[1], e))
    elif e.data == 'term_var':
        return Var(e.meta, parse_tree_to_ast(e.children[0], e))
    elif e.data == 'conditional':
        return Conditional(e.meta,
                           parse_tree_to_ast(e.children[0], e),
                           parse_tree_to_ast(e.children[1], e),
                           parse_tree_to_ast(e.children[2], e))
    elif e.data == 'int':
        return intToNat(e.meta, int(e.children[0]))
    elif e.data == 'ident':
        return str(e.children[0].value)
    elif e.data == 'true_literal':
        return Bool(e.meta, True)
    elif e.data == 'false_literal':
        return Bool(e.meta, False)
    elif e.data == 'emptyset_literal':
        return Call(e.meta,
                    Var(e.meta, 'char_fun'),
                    [Lambda(e.meta, ['_'], Bool(e.meta, False))],
                    False)
    elif e.data == 'field_access':
        subject = parse_tree_to_ast(e.children[0], e)
        field_name = str(e.children[1].value)
        return FieldAccess(e.meta, subject, field_name)
    elif e.data == 'call':
        rator = parse_tree_to_ast(e.children[0], e)
        rands = parse_tree_to_list(e.children[1], e)
        return Call(e.meta, rator, rands, False)
    elif e.data == 'lambda':
        return Lambda(e.meta,
                      parse_tree_to_list(e.children[0], e),
                      parse_tree_to_ast(e.children[1], e))
    elif e.data == 'generic':
        return Generic(e.meta,
                       parse_tree_to_list(e.children[0], e),
                       parse_tree_to_ast(e.children[1], e))
    elif e.data in infix_ops:
        return Call(e.meta, Var(e.meta, operator_symbol[e.data]),
                    [parse_tree_to_ast(c, e) for c in e.children],
                    True)
    elif e.data in prefix_ops:
        return Call(e.meta, Var(e.meta, operator_symbol[e.data]),
                    [parse_tree_to_ast(c, e) for c in e.children],
                    False)
    elif e.data == 'switch_case':
        e1 , e2 = e.children
        return SwitchCase(e.meta, parse_tree_to_ast(e1, e), parse_tree_to_ast(e2, e))
    elif e.data == 'switch':
        e1 , e2 = e.children
        return Switch(e.meta, parse_tree_to_ast(e1, e), parse_tree_to_list(e2, e))
    
    # proofs
    if e.data == 'proof_var':
        return PVar(e.meta, str(e.children[0].value))
    elif e.data == 'modus_ponens':
        e1, e2 = e.children
        return ModusPonens(e.meta, parse_tree_to_ast(e1, e), parse_tree_to_ast(e2, e))
    elif e.data == 'true_proof':
        return PTrue(e.meta)
    elif e.data == 'hole_proof':
        return PHole(e.meta)
    elif e.data == 'sorry_proof':
        return PSorry(e.meta)
    elif e.data == 'refl_proof':
        return PReflexive(e.meta)
    elif e.data == 'sym_proof':
        e1 = e.children[0]
        eq1 = parse_tree_to_ast(e1, e)
        return PSymmetric(e.meta, eq1)
    elif e.data == 'trans_proof':
        e1, e2 = e.children
        eq1 = parse_tree_to_ast(e1, e)
        eq2 = parse_tree_to_ast(e2, e)
        return PTransitive(e.meta, eq1, eq2)
    elif e.data == 'injective_proof':
        e1, e2 = e.children
        constr = parse_tree_to_ast(e1, e)
        eq = parse_tree_to_ast(e2, e)
        return PInjective(e.meta, constr, eq)
    elif e.data == 'extensionality_proof':
        e1 = e.children[0]
        eq1 = parse_tree_to_ast(e1, e)
        return PExtensionality(e.meta, eq1)
    elif e.data == 'paren':
        return parse_tree_to_ast(e.children[0], e)
    elif e.data == 'let':
        return PLet(e.meta,
                    str(e.children[0].value),
                    parse_tree_to_ast(e.children[1], e),
                    parse_tree_to_ast(e.children[2], e),
                    parse_tree_to_ast(e.children[3], e))
    elif e.data == 'define_term_proof':
        return PTLet(e.meta,
                     str(e.children[0].value),
                     parse_tree_to_ast(e.children[1], e),
                     parse_tree_to_ast(e.children[2], e))
    elif e.data == 'annot':
        return PAnnot(e.meta,
                      parse_tree_to_ast(e.children[0], e),
                      parse_tree_to_ast(e.children[1], e))
    elif e.data == 'term_proof':
        return PTerm(e.meta,
                     parse_tree_to_ast(e.children[0], e),
                     parse_tree_to_ast(e.children[1], e),
                     parse_tree_to_ast(e.children[2], e))
    elif e.data == 'tuple':
       left = parse_tree_to_ast(e.children[0], e)
       right = parse_tree_to_ast(e.children[1], e)
       return PTuple(e.meta, extract_tuple(left) + extract_tuple(right))
    elif e.data == 'conjunct':
       subject = parse_tree_to_ast(e.children[1], e)
       return PAndElim(e.meta, int(e.children[0].value), subject)
    elif e.data == 'imp_intro':
        label = str(e.children[0].value)
        body = parse_tree_to_ast(e.children[1], e)
        return ImpIntro(e.meta, label, None, body)
    elif e.data == 'all_intro':
        vars = parse_tree_to_list(e.children[0], e)
        body = parse_tree_to_ast(e.children[1], e)
        return AllIntro(e.meta, vars, body)
    elif e.data == 'all_elim':
        univ = parse_tree_to_ast(e.children[0], e)
        args = parse_tree_to_list(e.children[1], e)
        return AllElim(e.meta, univ, args)
    elif e.data == 'some_intro':
        witnesses = parse_tree_to_list(e.children[0], e)
        body = parse_tree_to_ast(e.children[1], e)
        return SomeIntro(e.meta, witnesses, body)
    elif e.data == 'some_elim':
        witnesses = parse_tree_to_list(e.children[0], e)
        label = parse_tree_to_ast(e.children[1], e)
        some = parse_tree_to_ast(e.children[2], e)
        body = parse_tree_to_ast(e.children[3], e)
        return SomeElim(e.meta, witnesses, label, None, some, body)
    elif e.data == 'some_elim_explicit':
        witnesses = parse_tree_to_list(e.children[0], e)
        label = parse_tree_to_ast(e.children[1], e)
        prop = parse_tree_to_ast(e.children[2], e)
        some = parse_tree_to_ast(e.children[3], e)
        body = parse_tree_to_ast(e.children[4], e)
        return SomeElim(e.meta, witnesses, label, prop, some, body)
    elif e.data == 'imp_intro_explicit':
        label = str(e.children[0].value)
        premise = parse_tree_to_ast(e.children[1], e)
        body = parse_tree_to_ast(e.children[2], e)
        return ImpIntro(e.meta, label, premise, body)
    elif e.data == 'case':
        tag = str(e.children[0].value)
        body = parse_tree_to_ast(e.children[1], e)
        return (tag, None, body)
    elif e.data == 'case_annot':
        tag = str(e.children[0].value)
        frm = parse_tree_to_ast(e.children[1], e)
        body = parse_tree_to_ast(e.children[2], e)
        return (tag, frm, body)
    elif e.data == 'cases':
        return Cases(e.meta,
                     parse_tree_to_ast(e.children[0], e),
                     parse_tree_to_list(e.children[1], e))
    elif e.data == 'induction':
        typ = parse_tree_to_ast(e.children[0], e)
        cases = parse_tree_to_list(e.children[1], e)
        return Induction(e.meta, typ, cases)
    elif e.data == 'switch_pf_case':
        pat = parse_tree_to_ast(e.children[0], e)
        body = parse_tree_to_ast(e.children[1], e)
        return SwitchProofCase(e.meta, pat, [], body)
    elif e.data == 'switch_pf_case_assume':
        pat = parse_tree_to_ast(e.children[0], e)
        assms = parse_tree_to_list(e.children[1], e)
        body = parse_tree_to_ast(e.children[2], e)
        return SwitchProofCase(e.meta, pat, assms, body)
    elif e.data == 'switch_proof':
        subject = parse_tree_to_ast(e.children[0], e)
        cases = parse_tree_to_list(e.children[1], e)
        return SwitchProof(e.meta, subject, cases)
    elif e.data == 'ind_case':
        pat = parse_tree_to_ast(e.children[0], e)
        body = parse_tree_to_ast(e.children[1], e)
        return IndCase(e.meta, pat, [], body)
    elif e.data == 'ind_case_assume':
        pat = parse_tree_to_ast(e.children[0], e)
        ind_hyps = parse_tree_to_list(e.children[1], e)
        body = parse_tree_to_ast(e.children[2], e)
        return IndCase(e.meta, pat, ind_hyps, body)
    elif e.data == 'apply_defs_goal':
        definitions = parse_tree_to_list(e.children[0], e)
        body = parse_tree_to_ast(e.children[1], e)
        return ApplyDefsGoal(e.meta, [Var(e.meta, t) for t in definitions],
                             body)
    elif e.data == 'apply_defs_goal_one':
        definition = parse_tree_to_ast(e.children[0], e)
        body = parse_tree_to_ast(e.children[1], e)
        return ApplyDefsGoal(e.meta, [Var(e.meta, definition)], body)
    elif e.data == 'apply_defs_fact':
        definitions = parse_tree_to_list(e.children[0], e)
        subject = parse_tree_to_ast(e.children[1], e)
        return ApplyDefsFact(e.meta,
                             [Var(e.meta, t) for t in definitions],
                             subject)
    elif e.data == 'apply_defs_fact_one':
        definition = parse_tree_to_ast(e.children[0], e)
        subject = parse_tree_to_ast(e.children[1], e)
        return ApplyDefsFact(e.meta,
                             [Var(e.meta, definition)],
                             subject)
    elif e.data == 'enable_defs':
        definitions = parse_tree_to_list(e.children[0], e)
        subject = parse_tree_to_ast(e.children[1], e)
        return EnableDefs(e.meta,
                          [Var(e.meta, t) for t in definitions],
                          subject)
    elif e.data == 'enable_def':
        definition = parse_tree_to_ast(e.children[0], e)
        subject = parse_tree_to_ast(e.children[1], e)
        return EnableDefs(e.meta,
                          [Var(e.meta, definition)],
                          subject)
    elif e.data == 'rewrite_goal':
        eqns = parse_tree_to_list(e.children[0], e)
        body = parse_tree_to_ast(e.children[1], e)
        return RewriteGoal(e.meta, eqns, body)
    elif e.data == 'rewrite_fact':
        eqns = parse_tree_to_list(e.children[0], e)
        subject = parse_tree_to_ast(e.children[1], e)
        return RewriteFact(e.meta, subject, eqns)
    elif e.data == 'equation':
        lhs = parse_tree_to_ast(e.children[0], e)
        rhs = parse_tree_to_ast(e.children[1], e)
        reason = parse_tree_to_ast(e.children[2], e)
        return (lhs, rhs, reason)
    elif e.data == 'half_equation':
        rhs = parse_tree_to_ast(e.children[0], e)
        reason = parse_tree_to_ast(e.children[1], e)
        return (rhs, reason)
    elif e.data == 'hole_in_middle_proof':
        return PHole(e.meta)
    elif e.data == 'equations_proof':
        first = parse_tree_to_ast(e.children[0], e)
        rest = parse_tree_to_list(e.children[1], e)
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
        param_types = parse_tree_to_list(e.children[1], e)
        return Constructor(e.meta, str(e.children[0].value), param_types)
    
    # union definitions
    elif e.data == 'union':
        return Union(e.meta, str(e.children[0].value),
                     parse_tree_to_list(e.children[1], e),
                     parse_tree_to_list(e.children[2], e))
    
    # theorem definitions
    elif e.data == 'theorem':
        return Theorem(e.meta,
                       str(e.children[0].value),
                       parse_tree_to_ast(e.children[1], e),
                       parse_tree_to_ast(e.children[2], e))

    # patterns in function definitions
    elif e.data == 'pattern_id':
        id = parse_tree_to_ast(e.children[0], e)
        return PatternCons(e.meta, Var(e.meta, id), [])
        #return PatternCons(e.meta, Var(e.meta, str(e.children[0].value)), [])
    elif e.data == 'pattern_zero':
        return PatternCons(e.meta, Var(e.meta, 'zero'), [])
    elif e.data == 'pattern_true':
        return PatternBool(e.meta, True)
    elif e.data == 'pattern_false':
        return PatternBool(e.meta, False)
    elif e.data == 'pattern_apply':
        params = parse_tree_to_list(e.children[1], e)
        return PatternCons(e.meta, Var(e.meta, str(e.children[0].value)), params)
    
    # case of a recursive function
    elif e.data == 'fun_case':
        pp = parse_tree_to_list(e.children[1], e)
        return FunCase(e.meta, pp[0], pp[1:],
                       parse_tree_to_ast(e.children[2], e))
    # recursive functions
    elif e.data == 'rec_fun':
        return RecFun(e.meta, parse_tree_to_ast(e.children[0], e),
                      parse_tree_to_list(e.children[1], e),
                      parse_tree_to_list(e.children[2], e),
                      parse_tree_to_ast(e.children[3], e),
                      parse_tree_to_list(e.children[4], e))

    # term definition
    elif e.data == 'define':
        return Define(e.meta, parse_tree_to_ast(e.children[0], e), 
                      None,
                      parse_tree_to_ast(e.children[1], e))
    elif e.data == 'define_annot':
        return Define(e.meta, parse_tree_to_ast(e.children[0], e), 
                      parse_tree_to_ast(e.children[1], e),
                      parse_tree_to_ast(e.children[2], e))

    # import module/file
    elif e.data == 'import':
        return Import(e.meta, str(e.children[0].value))

    # assert formula
    elif e.data == 'assert':
        return Assert(e.meta, parse_tree_to_ast(e.children[0], e))

    # print term
    elif e.data == 'print':
        return Print(e.meta, parse_tree_to_ast(e.children[0], e))

    # whole program
    elif e.data == 'program':
        return parse_tree_to_list(e.children[0], None)
    
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
    ast = parse_tree_to_ast(parse_tree, None)
    if trace:
        print('abstract syntax tree: ')
        print(ast)
        print('')
    return ast
