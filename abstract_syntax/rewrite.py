"""``Mark``-driven rewriting machinery used by ``replace``/``rewrite``.

Scope: the primitives that locate ``Mark`` nodes inside a formula, swap
them out for a replacement, and drive the formula-matching used by
``rewrite`` proofs. Includes ``count_marks``/``find_mark``/``MarkException``,
the overloaded ``replace_mark`` family, ``remove_mark``, the equation
``rewrite_aux``/``try_rewrite``/``formula_match`` engine, conjunction and
disjunction flatteners (``extract_and``/``extract_or``), ``auto_rewrites``,
and the small module-level state (``default_mark_LHS`` toggle,
``num_rewrites`` counter, ``call_arity``/``call_head_name`` helpers used
to drive the matcher).

Goes here:
  * a new rewriting heuristic or matching primitive
  * any helper that operates over the ``Mark`` placeholder, the auto-rewrite
    cache, or the rewrite counter

Does NOT go here:
  * the ``Mark`` AST node itself (``terms``)
  * the proof rules that invoke rewriting (``proofs``); their checker
    logic lives in ``proof_checker`` / ``checker_*``
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from .core import *
from .terms import *
from .proofs import *
from .declarations import *
from .env import *
from .literals import *

if TYPE_CHECKING:
    from .ops import callable_name, flatten_assoc, flatten_assoc_list, is_associative

_FormulaMatchNode = Term | Type | SwitchCase | RecFun | GenRecFun

############# Marks for controlling rewriting and definitions ##################

default_mark_LHS = True

def set_default_mark_LHS(b: bool) -> None:
  global default_mark_LHS
  default_mark_LHS = b
  
def get_default_mark_LHS() -> bool:
  global default_mark_LHS
  return default_mark_LHS

@dataclass
class MarkException(BaseException):
    subject: Term

def count_marks(formula: AST) -> int:
  match formula:
    case Mark(_, _, subject):
      return 1 + count_marks(subject)
    case TermInst(_, _, subject, _, _):
      return count_marks(subject)
    case Var() | OverloadedVar() | ResolvedVar():
      return 0
    case Bool(_, _, _):
      return 0
    case And(_, _, args):
      return sum([count_marks(arg) for arg in args])
    case Or(_, _, args):
      return sum([count_marks(arg) for arg in args])
    case IfThen(_, _, prem, conc):
      return count_marks(prem) + count_marks(conc)
    case All(_, _, _, _, frm2):
      return count_marks(frm2)
    case Some(_, _, _, frm2):
      return count_marks(frm2)
    case Call(_, _, rator, args):
      return count_marks(rator) + sum([count_marks(arg) for arg in args])
    case Switch(_, _, subject, cases):
      ls : list[int] = [count_marks(c) for c in cases]
      return count_marks(subject) + sum(ls)
    case SwitchCase(_, _, body):
      return count_marks(body)
    case RecFun(_, _, _, _, _, cases):
      return 0
    case GenRecFun(_, _, _, _, _, _, _, body, _):
      return 0
    case Conditional(_, _, cond, thn, els):
      return count_marks(cond) + count_marks(thn) + count_marks(els)
    case Lambda(_, _, _, body):
      return count_marks(body)
    case Generic(_, _, _, body):
      return count_marks(body)
    case TAnnote(_, _, subject, _):
      return count_marks(subject)
    case TLet(_, _, _, rhs, body):
      return count_marks(rhs) + count_marks(body)
    case Hole(_, _):
      return 0
    case Omitted(_, _):
      return 0
    case ArrayGet(_, _, arr, ind):
      return count_marks(arr) + count_marks(ind)
    case Array(_, _, elements):
      return sum([count_marks(elt) for elt in elements])
    case MakeArray(_, _, subject):
      return count_marks(subject)
    case _:
      internal_error(formula.location, 'in count_marks function, unhandled ' + str(formula))

def find_mark(formula: AST) -> None:
  match formula:
    case Mark(_, _, subject):
      raise MarkException(subject)
    case TermInst(_, _, subject, _, _):
      find_mark(subject)
    case Var() | OverloadedVar() | ResolvedVar():
      pass
    case Bool(_, _, _):
      pass
    case And(_, _, args):
      for and_arg in args:
          find_mark(and_arg)
    case Or(_, _, args):
      for or_arg in args:
          find_mark(or_arg)
    case IfThen(_, _, prem, conc):
      find_mark(prem)
      find_mark(conc)
    case All(_, _, _, _, frm2):
      find_mark(frm2)
    case Some(_, _, _, frm2):
      find_mark(frm2)
    case Call(_, _, rator, args):
      find_mark(rator)
      for call_arg in args:
          find_mark(call_arg)
    case Switch(_, _, subject, cases):
      find_mark(subject)
      for c in cases:
          find_mark(c)
    case SwitchCase(_, _, body):
      find_mark(body)
    case RecFun(_, _, _, _, _, cases):
      pass
    case Conditional(_, _, cond, thn, els):
      find_mark(cond)
      find_mark(thn)
      find_mark(els)
    case Lambda(_, _, _, body):
      find_mark(body)
    case Generic(_, _, _, body):
      find_mark(body)
    case TAnnote(_, _, subject, _):
      find_mark(subject)
    case TLet(_, _, _, rhs, body):
      find_mark(rhs)
      find_mark(body)
    case Hole(_, _):
      pass
    case ArrayGet(_, _, arr, ind):
      find_mark(arr)
      find_mark(ind)
    case Array(_, _, elements):
      for elt in elements:
          find_mark(elt)
    case MakeArray(_, _, subject):
      find_mark(subject)
    case _:
      internal_error(formula.location, 'in find_mark function, unhandled ' + str(formula))

@overload
def replace_mark(formula: Formula, replacement: Formula) -> Formula: ...

@overload
def replace_mark(formula: Formula, replacement: Term) -> Formula: ...

@overload
def replace_mark(formula: Term, replacement: Formula) -> Term: ...

@overload
def replace_mark(formula: Term, replacement: Term) -> Term: ...

@overload
def replace_mark(formula: SwitchCase, replacement: Term) -> SwitchCase: ...

def replace_mark(formula: Term | SwitchCase, replacement: Term) -> Term | SwitchCase:
  match formula:
    case Mark(loc2, tyof, subject):
      return replacement
    case TermInst(loc2, tyof, subject, tyargs, inferred):
      return TermInst(loc2, tyof, replace_mark(subject, replacement), tyargs, inferred)
    case Var() | OverloadedVar() | ResolvedVar():
      return formula
    case Bool(loc2, tyof, _):
      return formula
    case And(loc2, tyof, args):
      return And(loc2, tyof, [replace_mark(and_arg, replacement) \
                              for and_arg in args])
    case Or(loc2, tyof, args):
      return Or(loc2, tyof, [replace_mark(or_arg, replacement) \
                             for or_arg in args])
    case IfThen(loc2, tyof, prem, conc):
      return IfThen(loc2, tyof, replace_mark(prem, replacement),
                    replace_mark(conc, replacement))
    case All(loc2, tyof, var, pos, frm2):
      return All(loc2, tyof, var, pos, replace_mark(frm2, replacement))
    case Some(loc2, tyof, vars, frm2):
      return Some(loc2, tyof, vars, replace_mark(frm2, replacement))
    case Call(loc2, tyof, rator, args):
      return Call(loc2, tyof, replace_mark(rator, replacement),
                  [replace_mark(arg, replacement) for arg in args])
    case Switch(loc2, tyof, subject, cases):
      return Switch(loc2, tyof, replace_mark(subject, replacement),
                    [replace_mark(c, replacement) for c in cases])
    case SwitchCase(loc2, pat, body):
      return SwitchCase(loc2, pat, replace_mark(body, replacement))
    case RecFun(_, _, typarams, _, _, cases):
      return formula
    case Conditional(loc2, tyof, cond, thn, els):
      return Conditional(loc2, tyof, replace_mark(cond, replacement),
                         replace_mark(thn, replacement),
                         replace_mark(els, replacement))
    case Lambda(loc2, tyof, vars, body):
      return Lambda(loc2, tyof, vars, replace_mark(body, replacement))
    case Generic(loc2, tyof, typarams, body):
      return Generic(loc2, tyof, typarams, replace_mark(body, replacement))
    case TAnnote(loc2, typof, subject, typ):
      return TAnnote(loc2, typof, replace_mark(subject, replacement), typ)
    case TLet(loc2, tyof, var, rhs, body):
      return TLet(loc2, tyof, var, replace_mark(rhs, replacement),
                  replace_mark(body, replacement))
    case Hole(loc2, tyof):
      return formula
    case ArrayGet(loc2, tyof, arr, ind):
      return ArrayGet(loc2, tyof, replace_mark(arr, replacement), replace_mark(ind, replacement))
    case Array(loc2, tyof, elements):
      return Array(loc2, tyof,
                   [replace_mark(elt, replacement) for elt in elements])
    case MakeArray(loc2, tyof, subject):
      return MakeArray(loc2, tyof, replace_mark(subject, replacement))
    case _:
      internal_error(formula.location, 'in replace_mark function, unhandled ' + str(formula))

def remove_mark(formula: Formula) -> Formula:
  num_marks = count_marks(formula)
  if num_marks == 0:
      return formula
  else:
        try:
            find_mark(formula)
            loc:Meta = formula.location
            internal_error(loc, 'in remove_mark, find_mark failed on formula:\n\t' + str(formula))
        except MarkException as ex:
            return replace_mark(formula, ex.subject)

def build_equations_proof(loc: Meta, eqs: list[tuple[Term, Term, Proof]]) -> Proof:
    """Fold a list of ``(lhs, rhs, reason)`` equation steps into a single
    proof, right to left, via transitivity. Shared by both parsers."""
    result: Proof | None = None
    for (lhs, rhs, reason) in reversed(eqs):
        num_marks = count_marks(lhs) + count_marks(rhs)
        if num_marks == 0 and get_default_mark_LHS():
            new_lhs: Term = Mark(loc, None, lhs)
        else:
            new_lhs = lhs
        eq_proof = PAnnot(loc, mkEqualVar(loc, new_lhs, rhs), reason)
        if result == None:
            result = eq_proof
        else:
            result = PTransitive(loc, eq_proof, result)
    assert result is not None  # the equations grammar yields >= 1 step
    return result

def extract_and(frm: Formula) -> list[Formula]:
    match frm:
      case And(_, _, args):
        return args
      case _:
       return [frm]

def extract_or(frm: Formula) -> list[Formula]:
    match frm:
      case Or(_, _, args):
        return args
      case _:
       return [frm]


num_rewrites = 0
rewrite_debug: bool = False

def reset_num_rewrites() -> None:
    global num_rewrites
    num_rewrites = 0

def inc_rewrites() -> None:
    global num_rewrites
    num_rewrites = 1 + num_rewrites

def get_num_rewrites() -> int:
    global num_rewrites
    return num_rewrites

def _rule_lhs(equation: Formula | AutoRewriteRule, env: Env) -> Term:
  if isinstance(equation, AutoRewriteRule):
    return equation.lhs
  lhs, _ = split_equation(equation.location, equation, env)
  return lhs

@overload
def rewrite_aux(loc: Meta, formula: Formula, equation: Formula | AutoRewriteRule, env: Env,
                depth: int = -1) -> Formula: ...

@overload
def rewrite_aux(loc: Meta, formula: Term, equation: Formula | AutoRewriteRule, env: Env,
                depth: int = -1) -> Term: ...

@overload
def rewrite_aux(loc: Meta, formula: SwitchCase, equation: Formula | AutoRewriteRule, env: Env,
                depth: int = -1) -> SwitchCase: ...

def rewrite_aux(loc: Meta, formula: Term | SwitchCase, equation: Formula | AutoRewriteRule,
                env: Env, depth: int = -1) -> Term | SwitchCase:
  if depth == 0:
      return formula
  try:
    rhs = try_rewrite(loc, formula, equation, env)
    inc_rewrites()
    return rhs
  except MatchFailed:
    if get_verbose():
      print('\tno match')
    pass
  match formula:
    case TermInst(loc2, tyof, subject, tyargs, inferred):
      return TermInst(loc2, tyof, rewrite_aux(loc, subject, equation, env, depth - 1),
                      tyargs, inferred)
    case OverloadedVar() | ResolvedVar() | Var():
      return formula
    case Bool(loc2, tyof, _):
      return formula
    case And(loc2, tyof, args):
      return And(loc2, tyof, [rewrite_aux(loc, arg, equation, env, depth - 1) for arg in args])
    case Or(loc2, tyof, args):
      return Or(loc2, tyof, [rewrite_aux(loc, arg, equation, env, depth - 1) for arg in args])
    case IfThen(loc2, tyof, prem, conc):
      return IfThen(loc2, tyof, rewrite_aux(loc, prem, equation, env, depth - 1),
                    rewrite_aux(loc, conc, equation, env, depth - 1))
    case All(loc2, tyof, var, pos, frm2):
      return All(loc2, tyof, var, pos, rewrite_aux(loc, frm2, equation, env, depth - 1))
    case Some(loc2, tyof, vars, frm2):
      return Some(loc2, tyof, vars, rewrite_aux(loc, frm2, equation, env, depth - 1))
    case Call(loc2, tyof, rator, args):
      assoc_name = callable_name(rator)
      is_assoc = assoc_name is not None \
          and is_associative(loc2, assoc_name, formula.typeof, env)
      if get_verbose():
          print('is_assoc? ' + str(is_assoc))
      if is_assoc:
          assert assoc_name is not None
          args = flatten_assoc_list(assoc_name, args)
      new_rator = rewrite_aux(loc, rator, equation, env, depth - 1)
      new_args = [rewrite_aux(loc, arg, equation, env, depth - 1) for arg in args]
      if rewrite_debug and get_verbose():
          print('while trying to rewrite ' + str(formula) + '\n\twith equation ' + str(equation))
          print('new_args: ' + ', '.join([str(arg) for arg in new_args]))
      lhs = _rule_lhs(equation, env)
      arity = call_arity(lhs)
      if get_verbose():
          print('lhs = ' + str(lhs) + '\n\tarity: ' + str(arity)) 
      if is_assoc and len(new_args) > arity and arity > 1:
        # try to rewrite each arity-number of adjacent terms
        i = 0
        output_terms = []
        while i + arity <= len(new_args):
            call_args = new_args[i : i + arity]
            tmp = Call(loc2, tyof, new_rator, call_args)
            old_num_rewrites = get_num_rewrites()
            try:
               new_tmp = rewrite_aux(loc, tmp, equation, env, depth)
            except MatchFailed:
               new_tmp = tmp
            new_num_rewrites = get_num_rewrites()
            if new_num_rewrites == old_num_rewrites:
                if get_verbose():
                    print('replace using: ' + str(equation) \
                          + '\n\tdid not match: ' + str(tmp))
                output_terms.append(new_args[i])
                i = i + 1
            else:
                assert assoc_name is not None
                flat_tmp = flatten_assoc(assoc_name, new_tmp)
                if get_verbose():
                    print('rewrote: ' + str(tmp) + '\n\tinto: ' \
                          + ', '.join([str(a) for a in flat_tmp]))
                output_terms += flat_tmp
                i = i + arity
        if i < len(new_args):
            output_terms += new_args[i:]
        if len(output_terms) > 1:
            return Call(loc2, tyof, new_rator, output_terms)
        else:
            return output_terms[0]
      else: # not an associative rator
        return Call(loc2, tyof, new_rator, new_args)
  
    case Switch(loc2, tyof, subject, cases):
      return Switch(loc2, tyof, rewrite_aux(loc, subject, equation, env, depth - 1),
                    [rewrite_aux(loc, c, equation, env, depth - 1) for c in cases])
    case SwitchCase(loc2, pat, body):
      return SwitchCase(loc2, pat, rewrite_aux(loc, body, equation, env, depth - 1))
    case RecFun(loc, _, typarams, _, _, cases):
      return formula
    case Conditional(loc2, tyof, cond, thn, els):
      return Conditional(loc2, tyof, rewrite_aux(loc, cond, equation, env, depth - 1),
                         rewrite_aux(loc, thn, equation, env, depth - 1),
                         rewrite_aux(loc, els, equation, env, depth - 1))
    case Lambda(loc2, tyof, vars, body):
      return Lambda(loc2, tyof, vars, rewrite_aux(loc, body, equation, env, depth - 1))
  
    case Generic(loc2, tyof, typarams, body):
      return Generic(loc2, tyof, typarams, rewrite_aux(loc, body, equation, env, depth - 1))
  
    case TAnnote(loc2, tyof, subject, typ):
      return TAnnote(loc, tyof, rewrite_aux(loc, subject, equation, env, depth - 1), typ)

    case ArrayGet(loc2, tyof, arr, ind):
      return ArrayGet(loc, tyof, rewrite_aux(loc, arr, equation, env, depth - 1),
                      rewrite_aux(loc, ind, equation, env, depth - 1))

    case Array(loc2, tyof, elements):
      return Array(loc, tyof,
                   [rewrite_aux(loc, elt, equation, env, depth - 1)
                    for elt in elements])

    case MakeArray(loc2, tyof, subject):
      return MakeArray(loc, tyof,
                       rewrite_aux(loc, subject, equation, env, depth - 1))
  
    case TLet(loc2, tyof, var, rhs, body):
      return TLet(loc2, tyof, var, rewrite_aux(loc, rhs, equation, env, depth - 1),
                  rewrite_aux(loc, body, equation, env, depth - 1))
  
    case Hole(loc2, tyof):
      return formula

    case Omitted(loc2, tyof):
      return formula
  
    case Mark(loc, tyof, subject):
      return Mark(loc, tyof, rewrite_aux(loc, subject, equation, env, depth - 1))
  
    case _:
      internal_error(loc, 'internal error in rewrite function, unhandled ' + str(formula))

def try_rewrite(
    loc: Meta,
    formula: Term | SwitchCase,
    equation: Formula | AutoRewriteRule,
    env: Env,
) -> Term:
  if isinstance(equation, AutoRewriteRule):
    rule = equation
  else:
    lhs, rhs = split_equation(loc, equation, env)
    rule = AutoRewriteRule(equation, equation_vars(equation), [], lhs, rhs)
  if rewrite_debug and get_verbose():
      print('try rewrite? ' + str(formula) + '\n\twith equation ' + str(rule.equation))
  matching: dict[str, Term] = {}
  formula_match(loc, rule.variables, rule.lhs, formula, matching, Env(),
                outer_env=env)
  for premise in rule.premises:
      instantiated = premise.substitute(matching)
      if not premise_holds(cast(Formula, instantiated), env):
          if rewrite_debug and get_verbose():
              print('\tpremise did not normalize to true: ' + str(instantiated))
          match_failed(
            loc,
            'conditional rewrite premise did not normalize to true: ' + str(instantiated),
          )
      if rewrite_debug and get_verbose():
          print('\tpremise normalized to true: ' + str(instantiated))
  # print('rewriting using: ' + str(equation) + '\n' \
  #       + '\t' + str(formula) \
  #       + '\t==> ' + str(rhs.substitute(matching)) + '\n')
  if rewrite_debug and get_verbose():
      print('\tmatched LHS, rewriting to the RHS: ' + str(rule.rhs.substitute(matching)))
  return cast(Term, rule.rhs.substitute(matching).reduce(env))

def premise_holds(premise: Formula, env: Env) -> bool:
    old_reduce_all = get_reduce_all()
    old_eval_all = get_eval_all()
    try:
      set_reduce_all(True)
      set_eval_all(True)
      normalized = premise.reduce(env)
    finally:
      set_eval_all(old_eval_all)
      set_reduce_all(old_reduce_all)
    rewritten = auto_rewrites(normalized, env, include_conditionals=False)
    return is_true(cast(Formula, rewritten))

def formula_match(
    loc: Meta,
    vars: list[Term],
    pattern_frm: _FormulaMatchNode,
    frm: _FormulaMatchNode,
    matching: dict[str, Term],
    env: Env,
    numeric_literals: bool = False,
    outer_env: Env | None = None,
) -> None:
  # ``env`` is used for the fallback reduction-based equality check and
  # is intentionally an empty ``Env()`` from ``try_rewrite`` so heavy
  # definitions don't fire during matching. ``outer_env`` is the real
  # caller env, threaded through only for environment-derived metadata
  # such as associativity lookups.
  if outer_env is None:
      outer_env = env
  if rewrite_debug and get_verbose():
    print("formula_match:\n\t" + str(pattern_frm) + "\n\t" + str(frm) + "\n")
    print("\tin  " + ','.join([str(x) for x in vars]))
    print("\twith " + ','.join([x + ' := ' + str(f) for (x,f) in matching.items()]))
  match (pattern_frm, frm):
    case (TermInst(_, _, subject1, tyargs1, _),
          TermInst(_, _, subject2, tyargs2, _)) \
          if len(tyargs1) == len(tyargs2):
      try:
        matching2 = dict(matching)
        for (t1,t2) in zip(tyargs1, tyargs2):
          formula_match(loc, vars, t1, t2, matching2, env,
                        numeric_literals, outer_env=outer_env)
        formula_match(loc, vars, subject1, subject2, matching2, env,
                      numeric_literals, outer_env=outer_env)
        matching.clear()
        matching.update(matching2)
      except MatchFailed:
        formula_match(loc, vars, subject1, frm, matching, env,
                      numeric_literals, outer_env=outer_env)

    case (TermInst(_, _, subject, _, _), _):
      formula_match(loc, vars, subject, frm, matching, env,
                    numeric_literals, outer_env=outer_env)

    case (_, TermInst(_, _, subject, _, _)):
      formula_match(loc, vars, pattern_frm, subject, matching, env,
                    numeric_literals, outer_env=outer_env)

    case _ if isinstance(pattern_frm, VarRef) and isinstance(frm, VarRef) \
              and pattern_frm.get_name() == frm.get_name():
      pass
    case _ if isinstance(pattern_frm, VarRef) and pattern_frm in vars:
      tyvar_name = pattern_frm.get_name()
      if tyvar_name in matching.keys():
        formula_match(loc, vars, matching[tyvar_name], frm, matching, env,
                      numeric_literals, outer_env=outer_env)
      else:
        if not isinstance(frm, Term):
          match_failed(loc, "formula: " + str(frm) + "\n" \
                       + "does not match expected term: " + str(pattern_frm))
        if get_verbose():
            print("formula_match, " + base_name(tyvar_name) + ' := ' + str(frm))
        matching[tyvar_name] = frm
        
    case (Call(_, _, goal_rator, goal_rands),
          Call(loc3, tyof3, rator, rands)):
      if rewrite_debug and get_verbose():
          print("matching Call with Call\n\trator pattern: " + str(goal_rator) + '\n'\
                + '\trator formula: ' + str(rator))
      formula_match(loc, vars, goal_rator, rator, matching, env,
                    numeric_literals, outer_env=outer_env)
      # If the operator is associative, flatten both arg lists so a
      # parenthesized pattern like ``(a * b) * c`` matches the
      # flattened formula ``a * b * c`` regardless of how the user
      # grouped sub-products. Without this, ``replace eq in h`` could
      # fail when the equation LHS hadn't been auto-flattened by reduce.
      op_name = callable_name(rator)
      if op_name is not None \
         and is_associative(loc3, op_name, tyof3, outer_env):
          goal_rands = flatten_assoc_list(op_name, goal_rands)
          rands = flatten_assoc_list(op_name, rands)
      if len(rands) >= len(goal_rands):
        while len(rands) > 0:
          # What is the following for? -Jeremy
          rand: Term
          if len(goal_rands) == 1 and len(rands) > 1:
              rand = Call(loc3, tyof3, rator, rands)
              rands = []
          else:
              rand = rands[0]
              rands = rands[1:]

          goal_rand = goal_rands[0]
          goal_rands = goal_rands[1:]

          new_goal_rand = goal_rand.substitute(matching)
          formula_match(loc, vars, new_goal_rand, rand, matching, env,
                        numeric_literals, outer_env=outer_env)
          
      else:
        match_failed(loc, "formula: " + str(frm) + "\n" \
                     + "does not match expected formula: " + str(pattern_frm))
        
    case (And(_, _, goal_args),
          And(loc3, tyof3, args)):
      for (goal_arg, arg) in zip(goal_args, args):
          new_goal_arg = goal_arg.substitute(matching)
          formula_match(loc, vars, new_goal_arg, arg, matching, env,
                        numeric_literals, outer_env=outer_env)
    case (Or(_, _, goal_args),
          Or(loc3, tyof3, args)):
      for (goal_arg, arg) in zip(goal_args, args):
          new_goal_arg = goal_arg.substitute(matching)
          formula_match(loc, vars, new_goal_arg, arg, matching, env,
                        numeric_literals, outer_env=outer_env)
    case (IfThen(_, _, goal_prem, goal_conc),
          IfThen(loc3, tyof3, prem, conc)):
      formula_match(loc, vars, goal_prem, prem, matching, env,
                    numeric_literals, outer_env=outer_env)
      new_goal_conc = goal_conc.substitute(matching)
      formula_match(loc, vars, new_goal_conc, conc, matching, env,
                    numeric_literals, outer_env=outer_env)
    # UNDER CONSTRUCTION
    case _:
      red_pattern = pattern_frm.reduce(env)
      red_frm = frm.reduce(env)
      if numeric_literals:
        matched = formulas_equal_modulo_numeric_literals(red_pattern, red_frm)
      else:
        matched = red_pattern == red_frm
      if not matched:
          match_failed(loc, "formula: " + str(red_frm) + "\n" \
                       + "does not match expected formula: " + str(red_pattern))

def call_arity(call: Term) -> int:
    match call:
      case Call(_, _, _, args):
        return len(args)
      case _:
        return 1 #raise Exception('call_arity: not a call ' + str(call))

def call_head_name(term: Term) -> str | None:
    match term:
      case Call(_, _, rator, _):
          name = callable_name(rator)
          return base_name(name) if name is not None else None
      case _:
          return None
    
def auto_rewrites(term: Term, env: Env, include_conditionals: bool = True) -> Term:
    # Iterate until we can't rewrite anymore (to a fixed point)
    while True:
        current = get_num_rewrites()
        # Grab all the equations that are applicable to the head constructor
        equations = env.get_auto_rewrites(call_head_name(term))
        # Rewrite using the first equation that matches 
        for eq in equations:
            if eq.premises and not include_conditionals:
                continue
            current_eq = get_num_rewrites()
            term = rewrite_aux(term.location, term, eq, env, 1)
            if current_eq < get_num_rewrites():
               break
        if current == get_num_rewrites():
            break
    return term        
