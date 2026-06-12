from abstract_syntax import (
    All, AllElim, AllElimTypes, AllIntro, And, ApplyDefsFact,
    ApplyDefsGoal, ArrayGet, ArrayType, Assert, Associative, Auto,
    Bool, BoolType, Call, Cases, Conditional, Constructor,
    Define, EvaluateFact, EvaluateGoal, Export, FunCase, FunctionType,
    GenRecFun, Generic, Hole, IfThen, ImpIntro, Import,
    IndCase, Induction, Inductive, IntType, Lambda, MakeArray,
    Mark, Module, ModusPonens, Omitted, Or, PAndElim,
    PAnnot, PExtensionality, PHelpUse, PHole, PInjective, PLet,
    PRecall, PReflexive, PSorry, PSymmetric, PTLetNew, PTransitive,
    PTrue, PTuple, PVar, PatternBool, PatternCons, PatternTerm,
    Postulate, Predicate, Print, RecFun, RewriteFact, RewriteGoal,
    Rule, RuleInduction, RuleInductionCase, RuleInversion, SimplifyFact,
    SimplifyGoal, Some, SomeElim, SomeIntro, Statement, Suffices, Switch,
    SwitchCase, SwitchProof, SwitchProofCase, TAnnote, TLet, Term, TermInst,
    Theorem, Trace, Proof, TypeAlias, TypeInst, TypeType, Union, Var,
    ViewDecl, count_marks, extract_and, extract_or, extract_tuple,
    get_default_mark_LHS, intToNat, listToNodeList, mkEqualVar, mkIntLit,
    mkUIntLit, remove_mark,
)
import re
from lark import Lark, Token, Tree, exceptions
from lark.tree import Meta
from typing import Any, TypeAlias as TypingTypeAlias, cast
from flags import VerboseLevel
from error import ParseError, lark_unexpected_chars_to_parse_error

filename: str = '???'

def set_filename(fname: str) -> None:
    global filename
    filename = fname

def get_filename() -> str:
    global filename
    return filename


deduce_directory: str = '???'

def set_deduce_directory(dir: str) -> None:
    global deduce_directory
    deduce_directory = dir

def get_deduce_directory() -> str:
    global deduce_directory
    return deduce_directory

##################################################
# Concrete Syntax Parser
##################################################

lark_parser = None

def init_parser() -> None:
  global lark_parser
  lark_file = get_deduce_directory() + "/Deduce.lark"
  lark_parser = Lark(open(lark_file, encoding="utf-8").read(),
                     start='program', parser='lalr',
                     debug=True, propagate_positions=True)

##################################################
# Parsing Concrete to Abstract Syntax
##################################################

ParseNode: TypingTypeAlias = Tree[Token] | Token
ParseParent: TypingTypeAlias = Tree[Token] | None

def _expect_tree(node: ParseNode) -> Tree[Token]:
    if isinstance(node, Token):
        raise Exception('expected parse tree, got token ' + repr(node))
    return node

def _token_child(tree: Tree[Token], index: int) -> Token:
    child = tree.children[index]
    if not isinstance(child, Token):
        raise Exception('expected token child, got parse tree ' + repr(child))
    return child

def _token_text(tree: Tree[Token], index: int) -> str:
    return str(_token_child(tree, index).value)

def parse_tree_to_str_list(e: ParseNode) -> list[str]:
    e = _expect_tree(e)
    if e.data == 'empty':
        return []
    elif e.data == 'single':
        return [_token_text(e, 0)]
    elif e.data == 'push':
        return [_token_text(e, 0)] \
            + parse_tree_to_str_list(e.children[1])
    else:
        raise Exception('parse_tree_to_str_list, unexpected ' + str(e))

def parse_tree_to_list(e: ParseNode, parent: ParseParent) -> list[Any]:
    e = _expect_tree(e)
    # Returns a list to match the recursive-descent parser's convention.
    # The inner 2-tuples like (identifier, typ) are paired data, not collections,
    # and stay as tuples.
    if e.data == 'empty':
        return []
    elif e.data == 'single':
        return [parse_tree_to_ast(e.children[0], parent)]
    elif e.data == 'repeat':
        num = int(_token_text(e, 0))
        item = parse_tree_to_ast(e.children[1], parent)
        return num * [item]
    elif e.data == 'push':
        return [parse_tree_to_ast(e.children[0], parent)] \
            + parse_tree_to_list(e.children[1], parent)
    elif e.data == 'push_repeat':
        num = int(_token_text(e, 0))
        item = parse_tree_to_ast(e.children[1], parent)
        rest = parse_tree_to_list(e.children[2], parent)
        return num * [item] + rest
    elif e.data == 'empty_binding':
        return []
    elif e.data == 'single_binding':
        identifier = parse_tree_to_ast(e.children[0], parent)
        typ = parse_tree_to_ast(e.children[1], parent)
        return [(identifier,typ)]
    elif e.data == 'single_anon_binding':
        typ = parse_tree_to_ast(e.children[0], parent)
        return [('_',typ)]
    elif e.data == 'single_var':
        identifier = parse_tree_to_ast(e.children[0], parent)
        return [(identifier,None)]
    elif e.data == 'push_binding':
        identifier = parse_tree_to_ast(e.children[0], parent)
        typ = parse_tree_to_ast(e.children[1], parent)
        return [(identifier,typ)] + parse_tree_to_list(e.children[2], parent)
    elif e.data == 'push_anon_binding':
        typ = parse_tree_to_ast(e.children[0], parent)
        return [('_',typ)] + parse_tree_to_list(e.children[1], parent)
    elif e.data == 'push_var':
        identifier = parse_tree_to_ast(e.children[0], parent)
        return [(identifier,None)] + parse_tree_to_list(e.children[1], parent)
    else:
        raise Exception('parse_tree_to_str_list, unexpected ' + str(e))

def parse_tree_to_case(e: ParseNode) -> tuple[str, Any]:
    e = _expect_tree(e)
    tag = _token_text(e, 0)
    body = parse_tree_to_ast(e.children[1], e)
    return (tag, body)

def parse_tree_to_case_list(e: ParseNode) -> list[tuple[str, Any]]:
    e = _expect_tree(e)
    if e.data == 'single':
        return [parse_tree_to_case(e.children[0])]
    elif e.data == 'push':
        return [parse_tree_to_case(e.children[0])] \
            + parse_tree_to_case_list(e.children[1])
    else:
        raise Exception('unrecognized as a type list ' + repr(e))

def parse_tree_to_optional_identifier(e: ParseNode) -> str | None:
    e = _expect_tree(e)
    if e.data == 'no_view_inverse':
        return None
    if e.data == 'view_inverse':
        return cast(str, parse_tree_to_ast(e.children[0], e))
    raise Exception('parse_tree_to_optional_identifier, unexpected ' + str(e))
    
infix_ops = {'add', 'sub', 'nat_sub', 'o_sub', 'mul', 'div', 'mod', 'circ', 'pow',
             'and', 'or','equal', 'not_equal',
             'less', 'greater', 'less_equal', 'greater_equal',
             'subset_equal', 'union_op', 'intersect', 'membership',
             'approx_equal', 'approx_less_equal',
             'multiset_sum',
             'append'}

prefix_ops = {'neg', 'not'}

operator_symbol = {'add': '+', 'sub': '-', 'mul': '*', 'div': '/', 'circ': '∘',
                   'nat_sub': '∸',
                   'o_sub': '⊝',
                   'mod': '%', 'neg':'-', 
                   'pow': '^',
                   'and': 'and', 'or':'or', 'not': 'not',
                   'equal': '=', 'not_equal': '≠',
                   'less': '<', 'greater': '>',
                   'less_equal': '≤', 'greater_equal': '≥',
                   'approx_less_equal': '≲', 'approx_equal': '≈',
                   'subset_equal': '⊆', 'union_op': '∪', 'intersect': '∩',
                   'membership': '∈', 'multiset_sum': '⨄', 'append': '++'}

impl_num = 0
def next_impl_num() -> int:
    global impl_num
    ret = impl_num
    impl_num += 1
    return ret

# Any: statement is any declaration node carrying a `visibility` attribute;
# this is a duck-typed setter over the heterogeneous declaration kinds.
def set_visibility(statement: Any, visibility: str) -> None:
    if visibility == 'private':
        statement.visibility = 'private'
    elif visibility == 'opaque':
        statement.visibility = 'opaque'
        statement.file_defined = get_filename()
    elif visibility == 'public':
        statement.visibility = 'public'
    else:
        statement.visibility = 'public'
        
def build_equations_proof(loc: Meta, eqs: list[tuple[Term, Term, Proof]]) -> Proof:
    result: Proof | None = None
    for (lhs, rhs, reason) in reversed(eqs):
        num_marks = count_marks(lhs) + count_marks(rhs)
        if num_marks == 0 and get_default_mark_LHS():
            new_lhs = Mark(loc, None, lhs)
        else:
            new_lhs = lhs

        eq_proof = PAnnot(loc, mkEqualVar(loc, new_lhs, rhs), reason)
        if result == None:
            result = eq_proof
        else:
            result = PTransitive(loc, eq_proof, result)
    assert result is not None  # the equations grammar yields >= 1 step
    return result
        
# Any: the lark-tree -> AST dispatch boundary. This is dispatched on the
# grammar rule name and so is polymorphic over every node kind the grammar
# can produce (Term/Formula/Proof/Type/Pattern/Statement, plus bare str
# identifiers and tuples), with no single static return type. The
# parse_tree_to_{list,case,case_list} helpers and set_visibility below
# inherit that same dynamic boundary.
def parse_tree_to_ast(e: ParseNode, parent: ParseParent) -> Any:
    if isinstance(e, Token):
        return e
    
    setattr(e.meta, 'filename', filename)

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
      return Var(e.meta, None, _token_text(e, 0))
    elif e.data == 'int_type':
      return IntType(e.meta)
    elif e.data == 'bool_type':
      return BoolType(e.meta)
    elif e.data == 'array_type':
      elt_type = parse_tree_to_ast(e.children[0], e)
      return ArrayType(e.meta, elt_type)
    elif e.data == 'type_type':
      return TypeType(e.meta)
    elif e.data == 'function_type':
      return FunctionType(e.meta,
                          parse_tree_to_list(e.children[0], e),
                          parse_tree_to_list(e.children[1], e),
                          parse_tree_to_ast(e.children[2], e))
    elif e.data == 'function_type_paren':
      first_param = parse_tree_to_ast(e.children[1], e)
      rest_params = parse_tree_to_list(e.children[2], e)
      return FunctionType(e.meta,
                          parse_tree_to_list(e.children[0], e),
                          [first_param] + rest_params,
                          parse_tree_to_ast(e.children[3], e))
    elif e.data == 'type_inst':
      return TypeInst(e.meta, Var(e.meta, None, _token_text(e, 0)),
                      parse_tree_to_list(e.children[1], e))
    # terms
    elif e.data == 'define_term':
        return TLet(e.meta, None, _token_text(e, 0),
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
        return Var(e.meta, None, parse_tree_to_ast(e.children[0], e))
    elif e.data == 'conditional':
        return Conditional(e.meta, None,
                           parse_tree_to_ast(e.children[0], e),
                           parse_tree_to_ast(e.children[1], e),
                           parse_tree_to_ast(e.children[2], e))
    elif e.data == 'int':
        num = int(_token_text(e, 0))
        return mkUIntLit(e.meta, num)
    elif e.data == 'nat':
        return Call(e.meta, None, Var(e.meta, None, 'lit'),
                    [intToNat(e.meta, int(_token_text(e, 0)[1:]))])
    elif e.data == 'pos_int':
        return mkIntLit(e.meta, int(_token_text(e, 0)), 'PLUS')
    elif e.data == 'neg_int':
        arg = parse_tree_to_ast(e.children[0], e)
        return Call(e.meta, None, Var(e.meta, None, '-'), [arg])
    elif e.data == 'hole_term':
        return Hole(e.meta, None)
    elif e.data == 'named_hole_term':
        return Hole(e.meta, None)
    elif e.data == 'omitted_term':
        return Omitted(e.meta, None)
    elif e.data == 'identifier':
        return _token_text(e, 0)
    elif e.data == 'identifier_div':
        return '/'
    elif e.data == 'identifier_append':
        return '++'
    elif e.data == 'identifier_union':
        return '∪'
    elif e.data == 'identifier_intersect':
        return '∩'
    elif e.data == 'identifier_member':
        return '∈'
    elif e.data == 'identifier_multiset_sum':
        return '⨄'
    elif e.data == 'identifier_nat_sub':
        return '∸'
    elif e.data == 'identifier_subset_equal':
        return '⊆'
    elif e.data == 'identifier_less_equal':
        return '≤'
    elif e.data == 'identifier_greater_equal':
        return '≥'
    elif e.data == 'identifier_not_equal':
        return '≠'
    elif e.data == 'identifier_circ':
        return '∘'
    elif e.data == 'true_literal':
        return Bool(e.meta, None, True)
    elif e.data == 'false_literal':
        return Bool(e.meta, None, False)
    elif e.data == 'emptyset_literal':
        return Call(e.meta, None, Var(e.meta, None, 'empty_set'), [])
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
                      Call(e.meta, None, Var(e.meta, None, '='),
                           kids),
                      Bool(e.meta, None, False))
    elif e.data in infix_ops:
        return Call(e.meta, None, Var(e.meta, None, operator_symbol[e.data]),
                    [parse_tree_to_ast(c, e) for c in e.children])
    elif e.data in prefix_ops:
        return Call(e.meta, None, Var(e.meta, None, operator_symbol[e.data]),
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
        return PVar(e.meta, _token_text(e, 0))
    elif e.data == 'single_proof':
        return parse_tree_to_ast(e.children[0], e)
    elif e.data == 'push_proof':
        proof_stmt = parse_tree_to_ast(e.children[0], e)
        if len(e.children) == 1:
            meta: Any = Meta()  # type: ignore[no-untyped-call,unused-ignore]
            meta.empty = False
            meta.filename = getattr(e.meta, 'filename', filename)
            meta.line = e.meta.end_line+1
            meta.column = 0
            meta.end_line = e.meta.end_line+1
            meta.end_column = 0
            body = PHole(meta)
            #body = PTrue(meta)
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
    elif e.data == 'contradict':
        child1 = parse_tree_to_ast(e.children[0], e)
        child2 = parse_tree_to_ast(e.children[0], e)
        return ModusPonens(e.meta, child1, child2)
    elif e.data == 'true_proof':
        return PTrue(e.meta)
    elif e.data == 'hole_proof':
        return PHole(e.meta)
    elif e.data == 'named_hole_proof':
        return PHole(e.meta)
    elif e.data == 'implicit_hole_proof':
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
                    _token_text(e, 0),
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
                        _token_text(e, 0),
                        parse_tree_to_ast(e.children[1], e),
                        None)
    elif e.data == 'annot':
        return PAnnot(e.meta,
                      parse_tree_to_ast(e.children[0], e),
                      parse_tree_to_ast(e.children[1], e))
    elif e.data == 'annot_stmt':
        return PAnnot(e.meta,
                      parse_tree_to_ast(e.children[0], e),
                      None)
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
       return PAndElim(e.meta, int(_token_text(e, 0)), subject)
    elif e.data == 'imp_intro':
        label = _token_text(e, 0)
        return ImpIntro(e.meta, label, None, None)
    elif e.data == 'imp_intro_explicit':
        label = _token_text(e, 0)
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
            result = AllElimTypes(e.meta, result, ty, (i, len(type_args)))
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
        tag = _token_text(e, 0)
        body = parse_tree_to_ast(e.children[1], e)
        return (tag, None, body)
    elif e.data == 'case_annot':
        tag = _token_text(e, 0)
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
    elif e.data == 'rule_induction':
        hyp = _token_text(e, 0)
        cases = parse_tree_to_list(e.children[1], e)
        return RuleInduction(e.meta, hyp, cases)
    elif e.data == 'rule_inversion':
        hyp = _token_text(e, 0)
        cases = parse_tree_to_list(e.children[1], e)
        return RuleInversion(e.meta, hyp, cases)
    elif e.data == 'rule_induction_case':
        rule_name = _token_text(e, 0)
        body = parse_tree_to_ast(e.children[1], e)
        return RuleInductionCase(e.meta, rule_name, body)
    elif e.data == 'switch_proof_case':
        pat = parse_tree_to_ast(e.children[0], e)
        body = parse_tree_to_ast(e.children[1], e)
        return SwitchProofCase(e.meta, pat, [], body)
    elif e.data == 'switch_proof_case_assume':
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
        return ApplyDefsGoal(e.meta, [Var(e.meta, None, t) \
                                      for t in definitions],
                             SwitchProof(e.meta, subject, cases))
    elif e.data == 'induction_case':
        pat = parse_tree_to_ast(e.children[0], e)
        body = parse_tree_to_ast(e.children[1], e)
        return IndCase(e.meta, pat, [], body)
    elif e.data == 'induction_case_assume':
        pat = parse_tree_to_ast(e.children[0], e)
        ind_hyps = parse_tree_to_list(e.children[1], e)
        body = parse_tree_to_ast(e.children[2], e)
        return IndCase(e.meta, pat, ind_hyps, body)
    elif e.data == 'expand':
        definitions = parse_tree_to_list(e.children[0], e)
        return ApplyDefsGoal(e.meta, [Var(e.meta, None, t) for t in definitions],
                             None)
    elif e.data == 'eval_goal':
        return EvaluateGoal(e.meta)
    elif e.data == 'eval_fact':
        subject = parse_tree_to_ast(e.children[0], e)
        return EvaluateFact(e.meta, subject)
    elif e.data == 'apply_defs_fact':
        definitions = parse_tree_to_list(e.children[0], e)
        subject = parse_tree_to_ast(e.children[1], e)
        return ApplyDefsFact(e.meta,
                             [Var(e.meta, None, t) for t in definitions],
                             subject)
    elif e.data == 'rewrite_goal':
        eqns = parse_tree_to_list(e.children[0], e)
        return RewriteGoal(e.meta, eqns, None)
    elif e.data == 'rewrite_fact':
        eqns = parse_tree_to_list(e.children[0], e)
        subject = parse_tree_to_ast(e.children[1], e)
        return RewriteFact(e.meta, subject, eqns)
    elif e.data == 'simplify_goal':
        givens = parse_tree_to_list(e.children[0], e)
        return SimplifyGoal(e.meta, None, givens)
    elif e.data == 'simplify_fact':
        givens = parse_tree_to_list(e.children[0], e)
        subject = parse_tree_to_ast(e.children[1], e)
        return SimplifyFact(e.meta, subject, givens)
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
    elif e.data == 'equation_proof':
        first = parse_tree_to_ast(e.children[0], e)
        eqs = [first]
        return build_equations_proof(e.meta, eqs)
        
    elif e.data == 'equations_proof':
        first = parse_tree_to_ast(e.children[0], e)
        rest = parse_tree_to_list(e.children[1], e)
        eqs = [first]
        for (lhs,rhs, reason) in rest:
            if lhs == None:
                # `... = rhs` chains: inherit the previous step's RHS,
                # stripping any mark via `remove_mark` so each step gets
                # its own. Previously this used `.copy()` and relied on
                # a `Mark.copy` bug that dropped the mark.
                lhs = remove_mark(eqs[-1][1])
            eqs.append((lhs, rhs, reason))
        return build_equations_proof(e.meta, eqs)
    elif e.data == 'recall_proof':
        args = parse_tree_to_list(e.children[0], e)
        return PRecall(e.meta, args)
    elif e.data == 'ident_proof_error':
        raise ParseError(e.meta, "parsing error: " + repr(e))
    elif e.data == 'reason':
        return parse_tree_to_ast(e.children[0], e)
        
    # constructor declaration
    elif e.data == 'constructor_id':
        return Constructor(e.meta, _token_text(e, 0), [])
    elif e.data == 'constructor_apply':
        param_types = parse_tree_to_list(e.children[1], e)
        return Constructor(e.meta, _token_text(e, 0), param_types)
    
    # union definitions
    elif e.data == 'union':
        visibility = parse_tree_to_ast(e.children[0], e)
        statement = Union(e.meta, _token_text(e, 1),
                          parse_tree_to_list(e.children[2], e),
                          parse_tree_to_list(e.children[3], e))
        set_visibility(statement, visibility)
        return statement

    elif e.data == 'type_alias':
        visibility = parse_tree_to_ast(e.children[0], e)
        statement = TypeAlias(e.meta, _token_text(e, 1),
                              parse_tree_to_list(e.children[2], e),
                              parse_tree_to_ast(e.children[3], e))
        set_visibility(statement, visibility)
        return statement

    # predicate / relation definitions
    elif e.data == 'predicate_declaration' or e.data == 'relation_declaration':
        keyword = 'predicate' if e.data == 'predicate_declaration' else 'relation'
        visibility = parse_tree_to_ast(e.children[0], e)
        name = parse_tree_to_ast(e.children[1], e)
        typarams = parse_tree_to_list(e.children[2], e)
        signature = parse_tree_to_ast(e.children[3], e)
        rules = parse_tree_to_list(e.children[4], e)
        statement = Predicate(e.meta, name, typarams, signature, rules, keyword)
        set_visibility(statement, visibility)
        return statement
    elif e.data == 'predicate_rule':
        return Rule(e.meta, _token_text(e, 0),
                    parse_tree_to_ast(e.children[1], e))
    
    # theorem definitions
    elif e.data == 'theorem':
        visibility = parse_tree_to_ast(e.children[0], e)
        statement = Theorem(e.meta,
                            _token_text(e, 1),
                            parse_tree_to_ast(e.children[2], e),
                            parse_tree_to_ast(e.children[3], e),
                            False)
        set_visibility(statement, visibility)
        return statement
    elif e.data == 'lemma':
        visibility = parse_tree_to_ast(e.children[0], e)
        statement = Theorem(e.meta,
                            _token_text(e, 1),
                            parse_tree_to_ast(e.children[2], e),
                            parse_tree_to_ast(e.children[3], e),
                            True)
        set_visibility(statement, visibility)
        return statement
    elif e.data == 'postulate':
        visibility = parse_tree_to_ast(e.children[0], e)
        statement = Postulate(e.meta,
                              _token_text(e, 1),
                              parse_tree_to_ast(e.children[2], e))
        set_visibility(statement, visibility)
        return statement
    elif e.data == 'associative_declaration':
        op_var = parse_tree_to_ast(e.children[0], e)
        typarams = parse_tree_to_list(e.children[1], e)
        typ = parse_tree_to_ast(e.children[2], e)
        return Associative(e.meta, typarams, Var(e.meta, None, op_var), typ)

    elif e.data == 'auto_declaration':
        pvar = parse_tree_to_ast(e.children[0], e)
        return Auto(e.meta, pvar)
    
    elif e.data == 'inductive_decl':
        ty = parse_tree_to_ast(e.children[0], e)
        thm = parse_tree_to_ast(e.children[1], e)
        return Inductive(e.meta, ty, thm)
    
    
    elif e.data == 'module_declaration':
        return Module(e.meta, parse_tree_to_ast(e.children[0], e))
    
    # patterns in function definitions
    elif e.data == 'pattern_id':
        id = parse_tree_to_ast(e.children[0], e)
        return PatternCons(e.meta, Var(e.meta, None, id), [])
        #return PatternCons(e.meta, Var(e.meta, str(e.children[0].value)), [])
    elif e.data == 'pattern_zero':
        return PatternCons(e.meta, Var(e.meta, None, 'zero'), [])
    elif e.data == 'pattern_true':
        return PatternBool(e.meta, True)
    elif e.data == 'pattern_false':
        return PatternBool(e.meta, False)
    elif e.data == 'pattern_empty_list':
        return PatternCons(e.meta, Var(e.meta, None, 'empty'), [])
    elif e.data == 'pattern_apply':
        params = parse_tree_to_list(e.children[1], e)
        return PatternCons(e.meta,
                           Var(e.meta, None, _token_text(e, 0)),
                           params)
    elif e.data == 'pattern_term':
        params = parse_tree_to_list(e.children[0], e)
        term = parse_tree_to_ast(e.children[1], e)
        return PatternTerm(e.meta, term, list(params))
    
    # case of a recursive function
    elif e.data == 'fun_case':
        rator = parse_tree_to_ast(e.children[0], e)
        pp = parse_tree_to_list(e.children[1], e)
        return FunCase(e.meta, Var(e.meta, None, rator), pp[0], pp[1:],
                       parse_tree_to_ast(e.children[2], e))
    # functions
    elif e.data == 'fun':
        visibility = parse_tree_to_ast(e.children[0], e)
        name = parse_tree_to_ast(e.children[1], e)
        typarams = parse_tree_to_list(e.children[2], e)
        params = parse_tree_to_list(e.children[3], e)
        body = parse_tree_to_ast(e.children[4], e)
        lam = Lambda(e.meta, None, params, body)
        if len(typarams) > 0:
            fun = Generic(e.meta, None, typarams, lam)
        else:
            fun = lam
        statement = Define(e.meta, name, None, fun)
        set_visibility(statement, visibility)
        return statement
    
    # structurally recursive functions
    elif e.data == 'recursive_function':
        visibility = parse_tree_to_ast(e.children[0], e)
        statement = RecFun(e.meta, parse_tree_to_ast(e.children[1], e),
                           parse_tree_to_list(e.children[2], e),
                           parse_tree_to_list(e.children[3], e),
                           parse_tree_to_ast(e.children[4], e),
                           parse_tree_to_list(e.children[5], e))
        set_visibility(statement, visibility)
        return statement

    # general recursion
    elif e.data == 'general_recursive_function':
        visibility = parse_tree_to_ast(e.children[0], e)
        statement = GenRecFun(e.meta,
                              parse_tree_to_ast(e.children[1], e),
                              parse_tree_to_list(e.children[2], e),
                              parse_tree_to_list(e.children[3], e),
                              parse_tree_to_ast(e.children[4], e),
                              parse_tree_to_ast(e.children[5], e),
                              parse_tree_to_ast(e.children[6], e),
                              parse_tree_to_ast(e.children[7], e),
                              parse_tree_to_ast(e.children[8], e))
        set_visibility(statement, visibility)
        return statement

    elif e.data == 'view_declaration':
        visibility = parse_tree_to_ast(e.children[0], e)
        statement = ViewDecl(e.meta,
                             str(e.children[1]),
                             parse_tree_to_list(e.children[2], e),
                             parse_tree_to_ast(e.children[3], e),
                             parse_tree_to_ast(e.children[4], e),
                             parse_tree_to_ast(e.children[5], e),
                             parse_tree_to_ast(e.children[6], e),
                             parse_tree_to_ast(e.children[7], e),
                             parse_tree_to_optional_identifier(e.children[8]))
        set_visibility(statement, visibility)
        return statement
        
    # term definition
    elif e.data == 'define':
        visibility = parse_tree_to_ast(e.children[0], e)
        statement = Define(e.meta, parse_tree_to_ast(e.children[1], e), 
                           None,
                           parse_tree_to_ast(e.children[2], e))
        set_visibility(statement, visibility)
        return statement
        
    elif e.data == 'define_annot':
        visibility = parse_tree_to_ast(e.children[0], e)
        statement = Define(e.meta, parse_tree_to_ast(e.children[1], e), 
                           parse_tree_to_ast(e.children[2], e),
                           parse_tree_to_ast(e.children[3], e))
        set_visibility(statement, visibility)
        return statement
        
    # import module/file
    elif e.data == 'import':
        visibility = parse_tree_to_ast(e.children[0], e)
        statement = Import(e.meta, _token_text(e, 1))
        vis = 'public' if visibility == 'public' else 'private'
        set_visibility(statement, vis)
        return statement

    elif e.data == 'import_using' or e.data == 'import_hiding':
        visibility = parse_tree_to_ast(e.children[0], e)
        names = parse_tree_to_ast(e.children[2], e)
        if e.data == 'import_using':
            statement = Import(e.meta, _token_text(e, 1), using=names)
        else:
            statement = Import(e.meta, _token_text(e, 1), hiding=names)
        vis = 'public' if visibility == 'public' else 'private'
        set_visibility(statement, vis)
        return statement

    elif e.data == 'import_filter_list':
        return [parse_tree_to_ast(c, e) for c in e.children]

    elif e.data == 'export':
        return Export(e.meta, _token_text(e, 0))
        
    # assert formula
    elif e.data == 'assert':
        return Assert(e.meta, parse_tree_to_ast(e.children[0], e))

    # print term
    elif e.data == 'print':
        return Print(e.meta, parse_tree_to_ast(e.children[0], e))

    # visibility
    elif (e.data == 'public'):
        return 'public'
    elif (e.data == 'private'):
        return 'private'
    elif (e.data == 'opaque'):
        return 'opaque'
    elif (e.data == 'default'):
        return 'default'
    
    # trace
    elif e.data == 'trace':
        return Trace(e.meta, Var(e.meta, None, parse_tree_to_ast(e.children[0], e)))
    
    # whole program
    elif e.data == 'program':
        if e.children == []: # Allowing for empty programs
            return []
        else:
            return parse_tree_to_list(e.children[0], None)
    
    else:
        raise Exception('unhandled parse tree', e)

def token_str(token: Token, program_text: str) -> str:
    return program_text[token.start_pos:token.end_pos]

def parse_program_tree(parse_tree: Tree[Token]) -> list[Statement]:
    return cast(list[Statement], parse_tree_to_ast(parse_tree, None))

def parse(program_text: str,
          trace: "bool | VerboseLevel" = False,
          error_expected: bool = False) -> "list[Statement]":
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
    assert lark_parser is not None, "init_parser() must be called before parse()"
    parse_tree = lark_parser.parse(program_text)
    if trace:
        print('parse tree: ')
        print(parse_tree)
        print('')
    ast = parse_program_tree(parse_tree)
    if trace:
        print('abstract syntax tree: ')
        print(ast)
        print('')
    return ast

  except exceptions.UnexpectedCharacters as e:
      if error_expected:
          raise Exception()
      # The default lark lexer message is parser-internal noise (and
      # actively misleading for backslash: "Expected one of: DOT, ..."
      # reads as "you forgot a period"). Route through the shared
      # helper so `\` gets a Deduce-flavored hint and other stray
      # characters at least get a clean header. Raise the ParseError
      # directly (matching rec_desc_parser) so library/LSP callers can
      # read `.location` / `.message_body` instead of dropping into
      # the unstructured-exception traceback path.
      raise lark_unexpected_chars_to_parse_error(e, get_filename())
  except exceptions.UnexpectedToken as t:
      if error_expected:
          raise Exception()
      else:
          # Route through ParseError so library/LSP callers see a
          # structured diagnostic with `.location` / `.message_body`,
          # matching the recursive-descent parser. Without this, the
          # LSP/MCP `check_file` path falls into
          # `_format_unstructured_exception` and prints a Python
          # traceback for an ordinary syntax error (issue #933).
          hint = ''
          if t.token.type == 'LESSTHAN':
              preceding = program_text[:t.token.start_pos]
              m = re.search(r'\bdefine\s+([^\W\d]\w*)\s*\Z', preceding)
              if m:
                  name = m.group(1)
                  hint = ('\n`define` does not take type parameters.'
                          ' For a generic value, put the type parameters'
                          ' on the right:\n'
                          '\tdefine ' + name + ' : fn <T> ... -> ... = generic T { ... }\n'
                          'or use `fun`/`recursive`:\n'
                          '\tfun ' + name + '<T>(...) { ... }\n'
                          '\trecursive ' + name + '<T>(...) -> ... { ... }')
          meta = Meta()  # type: ignore[no-untyped-call,unused-ignore]
          meta.empty = False
          setattr(meta, 'filename', get_filename())
          meta.line = t.token.line
          meta.column = t.token.column
          meta.start_pos = t.token.start_pos
          meta.end_line = t.token.end_line
          meta.end_column = t.token.end_column
          meta.end_pos = t.token.end_pos
          msg = ("error in parsing, unexpected token: "
                 + token_str(t.token, program_text) + '\n'
                 + "(The error may be immediately before this token.)"
                 + hint)
          raise ParseError(meta, msg)
        
