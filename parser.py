from abstract_syntax import *
import dataclasses
from dataclasses import dataclass
from lark import Lark, Token, Tree, logger, exceptions
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


deduce_directory = '???'

def set_deduce_directory(dir):
    global deduce_directory
    deduce_directory = dir

def get_deduce_directory():
    global deduce_directory
    return deduce_directory

##################################################
# Concrete Syntax Parser
##################################################

lark_parser = None

def init_parser():
  global lark_parser
  lark_file = get_deduce_directory() + "/Deduce.lark"
  lark_parser = Lark(open(lark_file, encoding="utf-8").read(),
                     start='program', parser='lalr',
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
    elif e.data == 'repeat':
        num = int(e.children[0])
        item = parse_tree_to_ast(e.children[1], parent)
        return tuple(num * [item])
    elif e.data == 'push':
        return tuple([parse_tree_to_ast(e.children[0], parent)]) \
            + parse_tree_to_list(e.children[1], parent)
    elif e.data == 'push_repeat':
        num = int(e.children[0])
        item = parse_tree_to_ast(e.children[1], parent)
        rest = parse_tree_to_list(e.children[2], parent)
        return tuple(num * [item]) + rest
    elif e.data == 'empty_binding':
        return tuple([])
    elif e.data == 'single_binding':
        ident = parse_tree_to_ast(e.children[0], parent)
        typ = parse_tree_to_ast(e.children[1], parent)
        return tuple([(ident,typ)])
    elif e.data == 'single_anon_binding':
        typ = parse_tree_to_ast(e.children[0], parent)
        return tuple([('_',typ)])
    elif e.data == 'single_var':
        ident = parse_tree_to_ast(e.children[0], parent)
        return tuple([(ident,None)])
    elif e.data == 'push_binding':
        ident = parse_tree_to_ast(e.children[0], parent)
        typ = parse_tree_to_ast(e.children[1], parent)
        return tuple([(ident,typ)]) + parse_tree_to_list(e.children[2], parent)
    elif e.data == 'push_anon_binding':
        typ = parse_tree_to_ast(e.children[0], parent)
        return tuple([('_',typ)]) + parse_tree_to_list(e.children[1], parent)
    elif e.data == 'push_var':
        ident = parse_tree_to_ast(e.children[0], parent)
        return tuple([(ident,None)]) + parse_tree_to_list(e.children[1], parent)
    else:
        raise Exception('parse_tree_to_str_list, unexpected ' + str(e))

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
    
infix_ops = {'add', 'sub', 'nat_sub', 'mul', 'div', 'mod', 'circ',
             'and', 'or','equal', 'not_equal',
             'less', 'greater', 'less_equal', 'greater_equal',
             'subset_equal', 'union_op', 'intersect', 'membership',
             'multiset_sum',
             'append'}

prefix_ops = {'neg', 'not'}

operator_symbol = {'add': '+', 'sub': '-', 'mul': '*', 'div': '/', 'circ': '∘', 'nat_sub': '⊝',
                   'mod': '%', 'neg':'-', 
                   'and': 'and', 'or':'or', 'not': 'not',
                   'equal': '=', 'not_equal': '≠',
                   'less': '<', 'greater': '>',
                   'less_equal': '≤', 'greater_equal': '≥',
                   'subset_equal': '⊆', 'union_op': '∪', 'intersect': '∩',
                   'membership': '∈', 'multiset_sum': '⨄', 'append': '++'}

impl_num = 0
def next_impl_num():
    global impl_num
    ret = impl_num
    impl_num += 1
    return ret
    
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
       return IfThen(e.meta, None,
                     parse_tree_to_ast(e.children[0], e),
                     parse_tree_to_ast(e.children[1], e))
    elif e.data == 'iff_formula':
        left = parse_tree_to_ast(e.children[0], e)
        right = parse_tree_to_ast(e.children[1], e)
        return And(e.meta, None, extract_and(IfThen(e.meta, None, left.copy(), right.copy())) 
                               + extract_and(IfThen(e.meta, None, right.copy(), left.copy())))
    elif e.data == 'and_formula':
       left = parse_tree_to_ast(e.children[0], e)
       right = parse_tree_to_ast(e.children[1], e)
       return And(e.meta, None, extract_and(left) + extract_and(right))
    elif e.data == 'or_formula':
       left = parse_tree_to_ast(e.children[0], e)
       right = parse_tree_to_ast(e.children[1], e)
       return Or(e.meta, None, extract_or(left) + extract_or(right))
    elif e.data == 'logical_not':
       subject = parse_tree_to_ast(e.children[0], e)
       return IfThen(e.meta, None, subject, Bool(e.meta, None, False))
    elif e.data == 'all_formula':
        vars = parse_tree_to_list(e.children[0], e)
        body = parse_tree_to_ast(e.children[1], e)
        result = body
        for i, var in enumerate(reversed(vars)):
            result = All(e.meta, None, var, (i, len(vars)), result)
        return result
    elif e.data == 'alltype_formula':
        vars = parse_tree_to_list(e.children[0], e)
        body = parse_tree_to_ast(e.children[1], e)
        result = body
        for i, ty in enumerate(reversed(vars)):
            result = All(e.meta, None, (ty, TypeType(e.meta)), (i, len(vars)), result)
        return result
    elif e.data == 'some_formula':
        return Some(e.meta, None,
                    parse_tree_to_list(e.children[0], e),
                    parse_tree_to_ast(e.children[1], e))
    
    # types
    elif e.data == 'type_name':
      return Var(e.meta, None, str(e.children[0].value), [])
    elif e.data == 'int_type':
      return IntType(e.meta)
    elif e.data == 'bool_type':
      return BoolType(e.meta)
    elif e.data == 'array_type':
      elt_type = parse_tree_to_ast(e.children[0])
      return ArrayType(e.meta, elt_type)
    elif e.data == 'type_type':
      return TypeType(e.meta)
    elif e.data == 'function_type':
      return FunctionType(e.meta,
                          parse_tree_to_list(e.children[0], e),
                          parse_tree_to_list(e.children[1], e),
                          parse_tree_to_ast(e.children[2], e))
    elif e.data == 'type_inst':
      return TypeInst(e.meta, Var(e.meta, None, str(e.children[0].value), []),
                      parse_tree_to_list(e.children[1], e))
    # terms
    elif e.data == 'define_term':
        return TLet(e.meta, None, str(e.children[0].value),
                    parse_tree_to_ast(e.children[1], e),
                    parse_tree_to_ast(e.children[2], e))
    elif e.data == 'annote_type':
        return TAnnote(e.meta, None, parse_tree_to_ast(e.children[0], e),
                       parse_tree_to_ast(e.children[1], e))
    elif e.data == 'term_inst':
        return TermInst(e.meta, None,
                        parse_tree_to_ast(e.children[0], e),
                        parse_tree_to_list(e.children[1], e),
                        False)
    elif e.data == 'array_get':
        return ArrayGet(e.meta, None,
                        parse_tree_to_ast(e.children[0], e),
                        parse_tree_to_ast(e.children[1], e))
    elif e.data == 'make_array':
        return MakeArray(e.meta, None,
                         parse_tree_to_ast(e.children[0], e))
    elif e.data == 'mark':
        return Mark(e.meta, None, parse_tree_to_ast(e.children[0], e))
    elif e.data == 'list_literal':
        return listToNodeList(e.meta, parse_tree_to_list(e.children[0], e))
    elif e.data == 'term_var':
        return Var(e.meta, None, parse_tree_to_ast(e.children[0], e), [])
    elif e.data == 'conditional':
        return Conditional(e.meta, None,
                           parse_tree_to_ast(e.children[0], e),
                           parse_tree_to_ast(e.children[1], e),
                           parse_tree_to_ast(e.children[2], e))
    elif e.data == 'int':
        return intToNat(e.meta, int(e.children[0]))
    elif e.data == 'pos_int':
        return intToDeduceInt(e.meta, int(e.children[0].value), 'PLUS')
    elif e.data == 'neg_int':
        arg = parse_tree_to_ast(e.children[0], e)
        return Call(e.meta, None, Var(e.meta, None, '-'), [arg])
    elif e.data == 'hole_term':
        return Hole(e.meta, None)
    elif e.data == 'omitted_term':
        return Omitted(e.meta, None)
    elif e.data == 'ident':
        return str(e.children[0].value)
    elif e.data == 'ident_div':
        return '/'
    elif e.data == 'ident_append':
        return '++'
    elif e.data == 'ident_union':
        return '∪'
    elif e.data == 'ident_intersect':
        return '∩'
    elif e.data == 'ident_member':
        return '∈'
    elif e.data == 'ident_multiset_sum':
        return '⨄'
    elif e.data == 'ident_subset_equal':
        return '⊆'
    elif e.data == 'ident_less_equal':
        return '≤'
    elif e.data == 'ident_greater_equal':
        return '≥'
    elif e.data == 'ident_not_equal':
        return '≠'
    elif e.data == 'ident_circ':
        return '∘'
    elif e.data == 'true_literal':
        return Bool(e.meta, None, True)
    elif e.data == 'false_literal':
        return Bool(e.meta, None, False)
    elif e.data == 'emptyset_literal':
        return Call(e.meta, None,
                    Var(e.meta, None, 'char_fun', []),
                    [Lambda(e.meta, None, [('_',None)],
                            Bool(e.meta, None, False))])
    # elif e.data == 'field_access':
        # subject = parse_tree_to_ast(e.children[0], e)
        # field_name = str(e.children[1].value)
        # return FieldAccess(e.meta, None, subject, field_name)
    elif e.data == 'call':
        rator = parse_tree_to_ast(e.children[0], e)
        rands = parse_tree_to_list(e.children[1], e)
        return Call(e.meta, None, rator, rands)
    elif e.data == 'lambda':
        typarams = parse_tree_to_list(e.children[0], e)
        params = parse_tree_to_list(e.children[1], e)
        body = parse_tree_to_ast(e.children[2], e)
        if len(typarams) > 0:
            return Generic(e.meta, None, typarams, Lambda(e.meta, None, params, body))
        else:
            return Lambda(e.meta, None, params, body)
    elif e.data == 'generic':
        return Generic(e.meta, None,
                       parse_tree_to_list(e.children[0], e),
                       parse_tree_to_ast(e.children[1], e))
    elif e.data == 'not_equal':
        kids = [parse_tree_to_ast(c, e) for c in e.children]
        return IfThen(e.meta, None, 
                      Call(e.meta, None, Var(e.meta, None, '=', []),
                           kids),
                      Bool(e.meta, None, False))
    elif e.data in infix_ops:
        return Call(e.meta, None, Var(e.meta, None, operator_symbol[e.data], []),
                    [parse_tree_to_ast(c, e) for c in e.children])
    elif e.data in prefix_ops:
        return Call(e.meta, None, Var(e.meta, None, operator_symbol[e.data], []),
                    [parse_tree_to_ast(c, e) for c in e.children])
    elif e.data == 'switch_case':
        e1 , e2 = e.children
        return SwitchCase(e.meta, parse_tree_to_ast(e1, e),
                          parse_tree_to_ast(e2, e))
    elif e.data == 'switch':
        e1 , e2 = e.children
        return Switch(e.meta, None, parse_tree_to_ast(e1, e),
                      parse_tree_to_list(e2, e))
    
    # proofs
    if e.data == 'proof_var':
        return PVar(e.meta, str(e.children[0].value))
    elif e.data == 'single_proof':
        return parse_tree_to_ast(e.children[0], e)
    elif e.data == 'push_proof':
        proof_stmt = parse_tree_to_ast(e.children[0], e)
        if len(e.children) == 1:
            meta = Meta() # Put the location of the 'Hole' at the start of the next line
            meta.empty = False
            meta.filename = e.meta.filename
            meta.line = e.meta.end_line+1
            meta.column = 0
            meta.end_line = e.meta.end_line+1
            meta.end_column = 0
            body = PHole(meta)
        else:
            body = parse_tree_to_ast(e.children[1], e)
        if isinstance(proof_stmt, AllIntro):
            proof_stmt.set_body(body)
        else:
            proof_stmt.body = body
        return proof_stmt
    elif e.data == 'modus_ponens':
        e1, e2 = e.children
        return ModusPonens(e.meta, parse_tree_to_ast(e1, e),
                           parse_tree_to_ast(e2, e))
    elif e.data == 'true_proof':
        return PTrue(e.meta)
    elif e.data == 'hole_proof':
        return PHole(e.meta)
    elif e.data == 'sorry_proof':
        return PSorry(e.meta)
    elif e.data == 'help_use_proof':
        return PHelpUse(e.meta, parse_tree_to_ast(e.children[0], e))
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
        constr = parse_tree_to_ast(e.children[0], e)
        return PInjective(e.meta, constr, None)
    elif e.data == 'extensionality_proof':
        return PExtensionality(e.meta, None)
    elif e.data == 'paren':
        return parse_tree_to_ast(e.children[0], e)
    elif e.data == 'let':
        return PLet(e.meta,
                    str(e.children[0].value),
                    parse_tree_to_ast(e.children[1], e),
                    parse_tree_to_ast(e.children[2], e),
                    None)
    elif e.data == 'let_anon':
        return PLet(e.meta,
                    '_',
                    parse_tree_to_ast(e.children[0], e),
                    parse_tree_to_ast(e.children[1], e),
                    None)
    elif e.data == 'define_term_proof':
        return PTLetNew(e.meta,
                        str(e.children[0].value),
                        parse_tree_to_ast(e.children[1], e),
                        None)
    elif e.data == 'annot':
        return PAnnot(e.meta,
                      parse_tree_to_ast(e.children[0], e),
                      parse_tree_to_ast(e.children[1], e))
    elif e.data == 'conclude_from':
        return PAnnot(e.meta,
                      parse_tree_to_ast(e.children[0], e),
                      PRecall(e.meta, parse_tree_to_list(e.children[1], e)))
    elif e.data == 'suffices':
        return Suffices(e.meta,
                        parse_tree_to_ast(e.children[0], e),
                        parse_tree_to_ast(e.children[1], e),
                        None)
    elif e.data == 'tuple':
       left = parse_tree_to_ast(e.children[0], e)
       right = parse_tree_to_ast(e.children[1], e)
       return PTuple(e.meta, extract_tuple(left) + extract_tuple(right))
    elif e.data == 'conjunct':
       subject = parse_tree_to_ast(e.children[1], e)
       return PAndElim(e.meta, int(e.children[0].value), subject)
    elif e.data == 'imp_intro':
        label = str(e.children[0].value)
        return ImpIntro(e.meta, label, None, None)
    elif e.data == 'imp_intro_explicit':
        label = str(e.children[0].value)
        premise = parse_tree_to_ast(e.children[1], e)
        return ImpIntro(e.meta, label, premise, None)
    elif e.data == 'imp_intro_anon':
        premise = parse_tree_to_ast(e.children[0], e)
        return ImpIntro(e.meta, '_', premise, None)
    elif e.data == 'all_intro':
        vars = parse_tree_to_list(e.children[0], e)
        result = None
        for i, var in enumerate(reversed(vars)):
            result = AllIntro(e.meta, var, (i, len(vars)), result)
        return result
    elif e.data == 'all_elim':
        univ = parse_tree_to_ast(e.children[0], e)
        args = parse_tree_to_list(e.children[1], e)
        result = univ
        for i,var in enumerate(args):
            result = AllElim(e.meta, result, var, (i, len(args)))
        return result
    elif e.data == 'all_elim_types':
        univ = parse_tree_to_ast(e.children[0], e)
        type_args = parse_tree_to_list(e.children[1], e)
        result = univ
        for i, ty in enumerate(type_args):
            result = AllElimTypes(e.meta, result, ty, (e ,len(type_args)))
        return result
    elif e.data == 'some_intro':
        witnesses = parse_tree_to_list(e.children[0], e)
        return SomeIntro(e.meta, witnesses, None)
    elif e.data == 'some_elim':
        witnesses = parse_tree_to_list(e.children[0], e)
        label = parse_tree_to_ast(e.children[1], e)
        some = parse_tree_to_ast(e.children[2], e)
        return SomeElim(e.meta, witnesses, label, None, some, None)
    elif e.data == 'some_elim_explicit':
        witnesses = parse_tree_to_list(e.children[0], e)
        label = parse_tree_to_ast(e.children[1], e)
        prop = parse_tree_to_ast(e.children[2], e)
        some = parse_tree_to_ast(e.children[3], e)
        return SomeElim(e.meta, witnesses, label, prop, some, None)
    elif e.data == 'case':
        tag = str(e.children[0].value)
        body = parse_tree_to_ast(e.children[1], e)
        return (tag, None, body)
    elif e.data == 'case_annot':
        tag = str(e.children[0].value)
        frm = parse_tree_to_ast(e.children[1], e)
        body = parse_tree_to_ast(e.children[2], e)
        return (tag, frm, body)
    elif e.data == 'case_annot_nolabel':
        frm = parse_tree_to_ast(e.children[0], e)
        body = parse_tree_to_ast(e.children[1], e)
        return ('_', frm, body)
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
    elif e.data == 'switch_proof_for':
        subject = parse_tree_to_ast(e.children[0], e)
        definitions = parse_tree_to_list(e.children[1], e)
        cases = parse_tree_to_list(e.children[2], e)
        return ApplyDefsGoal(e.meta, [Var(e.meta, None, t, []) \
                                      for t in definitions],
                             SwitchProof(e.meta, subject, cases))
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
        return ApplyDefsGoal(e.meta, [Var(e.meta, None, t, []) for t in definitions],
                             body)
    elif e.data == 'eval_goal':
        return EvaluateGoal(e.meta)
    elif e.data == 'eval_fact':
        subject = parse_tree_to_ast(e.children[0], e)
        return EvaluateFact(e.meta, subject)
    elif e.data == 'apply_defs_goal_one':
        definition = parse_tree_to_ast(e.children[0], e)
        return ApplyDefsGoal(e.meta, [Var(e.meta, None, definition, [])], None)
    elif e.data == 'apply_defs_fact':
        definitions = parse_tree_to_list(e.children[0], e)
        subject = parse_tree_to_ast(e.children[1], e)
        return ApplyDefsFact(e.meta,
                             [Var(e.meta, None, t, []) for t in definitions],
                             subject)
    elif e.data == 'enable_defs':
        definitions = parse_tree_to_list(e.children[0], e)
        return EnableDefs(e.meta,
                          [Var(e.meta, None, x, []) for x in definitions],
                          None)
    elif e.data == 'reason_definition':
        definitions = parse_tree_to_list(e.children[0], e)
        return ApplyDefs(e.meta, [Var(e.meta, None, t, []) for t in definitions])
    
    elif e.data == 'reason_def_rewrite':
        definitions = parse_tree_to_list(e.children[0], e)
        eqns = parse_tree_to_list(e.children[1], e)
        return ApplyDefsGoal(e.meta,
                             [Var(e.meta, None, t, []) for t in definitions],
                             Rewrite(e.meta, eqns))
    elif e.data == 'enable_def':
        definition = parse_tree_to_ast(e.children[0], e)
        subject = parse_tree_to_ast(e.children[1], e)
        return EnableDefs(e.meta,
                          [Var(e.meta, None, definition, [])],
                          subject)
    elif e.data == 'rewrite_goal':
        eqns = parse_tree_to_list(e.children[0], e)
        return RewriteGoal(e.meta, eqns, None)
    elif e.data == 'rewrite_fact':
        eqns = parse_tree_to_list(e.children[0], e)
        subject = parse_tree_to_ast(e.children[1], e)
        return RewriteFact(e.meta, subject, eqns)
    elif e.data == 'reason_rewrite':
        eqns = parse_tree_to_list(e.children[0], e)
        return Rewrite(e.meta, eqns)
    elif e.data == 'equation':
        lhs = parse_tree_to_ast(e.children[0], e)
        rhs = parse_tree_to_ast(e.children[1], e)
        reason = parse_tree_to_ast(e.children[2], e)
        return (lhs, rhs, reason)
    elif e.data == 'half_equation':
        rhs = parse_tree_to_ast(e.children[0], e)
        reason = parse_tree_to_ast(e.children[1], e)
        return (None, rhs, reason)
    elif e.data == 'hole_in_middle_proof':
        return PHole(e.meta)
    elif e.data == 'equations_proof':
        first = parse_tree_to_ast(e.children[0], e)
        rest = parse_tree_to_list(e.children[1], e)
        eqs = [first]
        for (lhs,rhs, reason) in rest:
            if lhs == None:
                lhs = eqs[-1][1].copy()
            eqs.append((lhs, rhs, reason))
        result = None
        for (lhs, rhs, reason) in reversed(eqs):
            num_marks = count_marks(lhs) + count_marks(rhs)
            if num_marks == 0 and get_default_mark_LHS():
                new_lhs = Mark(e.meta, None, lhs)
            else:
                new_lhs = lhs
            
            eq_proof = PAnnot(e.meta, mkEqual(e.meta, new_lhs, rhs), reason)
            if result == None:
                result = eq_proof
            else:
                result = PTransitive(e.meta, eq_proof, result)
        return result
    elif e.data == 'recall_proof':
        args = parse_tree_to_list(e.children[0], e)
        return PRecall(e.meta, args)
    elif e.data == 'ident_proof_error':
        error(e.meta, "parsing error: " + repr(e))
    
    # constructor declaration
    elif e.data == 'constructor_id':
        return Constructor(e.meta, str(e.children[0].value), [])
    elif e.data == 'constructor_apply':
        param_types = parse_tree_to_list(e.children[1], e)
        return Constructor(e.meta, str(e.children[0].value), param_types)
    
    # union definitions
    elif e.data == 'union':
        return Union(e.meta, str(e.children[0].value),
                     parse_tree_to_list(e.children[1], e),
                     parse_tree_to_list(e.children[2], e), False)
    
    # theorem definitions
    elif e.data == 'theorem':
        return Theorem(e.meta,
                       str(e.children[0].value),
                       parse_tree_to_ast(e.children[1], e),
                       parse_tree_to_ast(e.children[2], e),
                       isLemma = False)
    elif e.data == 'lemma':
        return Theorem(e.meta,
                       str(e.children[0].value),
                       parse_tree_to_ast(e.children[1], e),
                       parse_tree_to_ast(e.children[2], e),
                       isLemma = True)
    elif e.data == 'assoc_decl':
        op_var = parse_tree_to_ast(e.children[0], e)
        typarams = parse_tree_to_list(e.children[1], e)
        typ = parse_tree_to_ast(e.children[2], e)
        return Associative(e.meta, typarams, Var(e.meta, None, op_var, []), typ)

    # patterns in function definitions
    elif e.data == 'pattern_id':
        id = parse_tree_to_ast(e.children[0], e)
        return PatternCons(e.meta, Var(e.meta, None, id, []), [])
        #return PatternCons(e.meta, Var(e.meta, str(e.children[0].value)), [])
    elif e.data == 'pattern_zero':
        return PatternCons(e.meta, Var(e.meta, None, 'zero', []), [])
    elif e.data == 'pattern_true':
        return PatternBool(e.meta, True)
    elif e.data == 'pattern_false':
        return PatternBool(e.meta, False)
    elif e.data == 'pattern_empty_list':
        return PatternCons(e.meta, Var(e.meta, None, 'empty', []), [])
    elif e.data == 'pattern_apply':
        params = parse_tree_to_list(e.children[1], e)
        return PatternCons(e.meta,
                           Var(e.meta, None, str(e.children[0].value), []),
                           params)
    
    # case of a recursive function
    elif e.data == 'fun_case':
        rator = parse_tree_to_ast(e.children[0], e)
        pp = parse_tree_to_list(e.children[1], e)
        return FunCase(e.meta, Var(e.meta, None, rator, []), pp[0], pp[1:],
                       parse_tree_to_ast(e.children[2], e))
    # functions
    elif e.data == 'fun':
        name = parse_tree_to_ast(e.children[0], e)
        typarams = parse_tree_to_list(e.children[1], e)
        params = parse_tree_to_list(e.children[2], e)
        body = parse_tree_to_ast(e.children[3], e)
        lam = Lambda(e.meta, None, params, body)
        if len(typarams) > 0:
            fun = Generic(e.meta, None, typarams, lam)
        else:
            fun = lam
        return Define(e.meta, name, None, fun, False)
    
    # recursive functions
    elif e.data == 'rec_fun':
        return RecFun(e.meta, parse_tree_to_ast(e.children[0], e),
                      parse_tree_to_list(e.children[1], e),
                      parse_tree_to_list(e.children[2], e),
                      parse_tree_to_ast(e.children[3], e),
                      parse_tree_to_list(e.children[4], e), False)

    # term definition
    elif e.data == 'define':
        return Define(e.meta, parse_tree_to_ast(e.children[0], e), 
                      None,
                      parse_tree_to_ast(e.children[1], e), False)
    elif e.data == 'define_annot':
        return Define(e.meta, parse_tree_to_ast(e.children[0], e), 
                      parse_tree_to_ast(e.children[1], e),
                      parse_tree_to_ast(e.children[2], e), False)

    # import module/file
    elif e.data == 'import':
        return Import(e.meta, str(e.children[0].value))

    # assert formula
    elif e.data == 'assert':
        return Assert(e.meta, parse_tree_to_ast(e.children[0], e))

    # print term
    elif e.data == 'print':
        return Print(e.meta, parse_tree_to_ast(e.children[0], e))

    elif e.data == 'private':
        statement = parse_tree_to_ast(e.children[0], e)
        statement.isPrivate = True
        return statement

    # whole program
    elif e.data == 'program':
        if e.children == []: # Allowing for empty programs
            return []
        else:
            return parse_tree_to_list(e.children[0], None)
    
    else:
        raise Exception('unhandled parse tree', e)

def token_str(token, program_text):
    return program_text[token.start_pos:token.end_pos]

def parse(program_text, trace = False, error_expected = False):
  try:    
    # if trace:
    #     print('lexing!')
    # lexed = lark_parser.lex(program_text)
    # if trace:
    #     print('tokens: ')
    #     for word in lexed:
    #         print(repr(word))
    #     print('')
    if trace:
        print('parsing!')
    parse_tree = lark_parser.parse(program_text)
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

  except exceptions.UnexpectedToken as t:
      if error_expected:
          raise Exception()
      else:
          print(get_filename() + ":" + str(t.token.line) + "." + str(t.token.column) \
                + "-" + str(t.token.end_line) + "." + str(t.token.end_column) + ": " \
                + "error in parsing, unexpected token: " + token_str(t.token, program_text) + '\n' \
                + "(The error may be immediately before this token.)")

          exit(1)
        
