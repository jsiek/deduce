"""Formula/proof utility logic independent of whole-file orchestration.

File charter:
- Put implication checking, formula instantiation, formula difference
  reporting, explicit rewrite/expand operations, and rewrite/expand hints here.
- This module may depend on already-checked terms and formulas, but it should
  not own top-level declaration processing, recursive-call checks, or proof
  tactic dispatch.
- If a helper primarily synthesizes or checks a proof object, place it in
  ``checker_proofs.py``. If it primarily assigns types to terms, place it in
  ``checker_types.py``.
"""

from collections.abc import Iterable, Mapping, Sequence
from typing import TYPE_CHECKING, TypeAlias, cast

from lark.tree import Meta

from abstract_syntax import (
    All,
    And,
    AST,
    AutoRewriteRule,
    Bool,
    Call,
    Env,
    Formula,
    GenRecFun,
    IfThen,
    Lambda,
    MarkException,
    Or,
    OverloadedVar,
    Pattern,
    PatternCons,
    RecFun,
    ResolvedVar,
    Switch,
    SwitchCase,
    TermBinding,
    TLet,
    Term,
    Type,
    VarRef,
    ViewRecFun,
    base_name,
    count_marks,
    find_mark,
    formula_match,
    formulas_equal_modulo_numeric_literals,
    get_dont_reduce_opaque,
    get_num_rewrites,
    get_reduce_all,
    get_reduced_defs,
    is_equation,
    is_true,
    name2str,
    replace_mark,
    reset_num_rewrites,
    reset_reduced_defs,
    rewrite_aux,
    set_dont_reduce_opaque,
    set_reduce_all,
    split_equation,
)
from checker_common import *
if TYPE_CHECKING:
    from checker_proofs import update_all_head
from checker_types import check_formula
from error import MatchFailed, UserError, internal_error, user_error, warning, wrap_user_error
from flags import get_verbose, print_verbose

SubstitutionValue: TypeAlias = Term | Type | RecFun | GenRecFun
Difference: TypeAlias = tuple[AST, AST]
ImplicationPremise: TypeAlias = tuple[Formula, Formula]

def commute_diff_hint(frm: Formula) -> str:
  """If ``frm`` is an equation ``s = t`` whose two sides are calls of
  the same operator applied to argument lists that differ only by
  reordering, return a hint suggesting an explicit commute step.
  Otherwise return ``''``.

  This catches the beginner trap where ``+`` (or ``*``) is registered
  associative but not commutative: the goal flattens by associativity
  to a form that looks trivially equal, but the closing tactic still
  fails because a commute step has not been applied.
  """
  if not isinstance(frm, Call):
    return ''
  if not (isinstance(frm.rator, VarRef) and frm.rator.get_name() == '='):
    return ''
  if len(frm.args) != 2:
    return ''
  L, R = frm.args
  if not (isinstance(L, Call) and isinstance(R, Call)):
    return ''
  if not (isinstance(L.rator, VarRef) and isinstance(R.rator, VarRef)):
    return ''
  if L.rator.get_name() != R.rator.get_name():
    return ''
  if len(L.args) != len(R.args) or len(L.args) < 2:
    return ''
  if L.args == R.args:
    return ''
  # Multiset equality on argument lists (Term.__eq__ is structural).
  remaining = list(R.args)
  for a in L.args:
    for i, b in enumerate(remaining):
      if a == b:
        del remaining[i]
        break
    else:
      return ''
  if remaining:
    return ''
  op = str(base_name(L.rator.get_name()))
  return ('\nhint: the two sides differ only by reordering arguments of `'
          + op + '`. `' + op + '` is registered associative but not '
          + 'commutative, so commute steps must be applied explicitly. '
          + 'Try a `replace` step with the relevant commute lemma — e.g. '
          + '`replace uint_add_commute[x, y]` for `+` on UInt '
          + '(or `int_add_commute` / `add_commute` for Int / Nat; '
          + '`uint_mult_commute` / `int_mult_commute` / `mult_commute` for `*`). '
          + 'See CheatSheet.md "Equations involving `+` that look trivial".')


def _implies_context(frm1: Formula, frm2: Formula) -> str:
  # The "while proving frm1 implies frm2" note appended to a nested
  # failure so the reported error keeps the enclosing implication goal.
  return '\n\nWhile trying to prove that\n\t' + str(frm1) \
      + '\nimplies\n' + '\t' + str(frm2)

def check_implies(loc: Meta, frm1: Formula, frm2: Formula) -> None:
  if get_verbose():
    print('check_implies? ' + str(frm1) + ' => ' + str(frm2))
  match (frm1, frm2):
    case (_, Bool(loc2, tyof2, True)):
      return
  
    case (_, And(loc2, tyof2, args)):
      try:
        for arg2 in args:
          check_implies(loc, frm1, arg2)
      except UserError as e:
          raise wrap_user_error(e, _implies_context(frm1, frm2)) from e

    case(Or(_, _, args1), _):
      for arg1 in args1:
        try:
          check_implies(loc, arg1, frm2)
        except UserError as e:
          raise wrap_user_error(e, _implies_context(frm1, frm2)) from e
      
    case (Bool(loc2, tyof2, False), _):
      return
  
    case (And(loc2, tyof2, args1), _):
      for arg1 in args1:
        try:
          check_implies(loc, arg1, frm2)
          return
        except UserError:
          # implicit modus ponens
          match arg1:
            case IfThen(_, _, prem, conc):
              try:
                  check_implies(loc, conc, frm2)
                  remaining = [arg for arg in args1 if arg != arg1]
                  if not remaining:
                    continue # no premises left for modus ponens
                  if len(remaining) == 1:
                    rest = remaining[0]
                  else:
                    rest = And(loc2, tyof2, remaining)
                  check_implies(loc, rest, prem)
                  return
              except UserError:
                  pass
            case _:
              pass
          continue
      user_error(loc, '\nCould not prove that\n\t' + str(frm1) + '\n' \
                 + 'implies\n\t' + str(frm2) + '\n' \
                 + 'because we could not prove at least one of\n'
                 + '\n'.join(['\t' + str(arg1) + '   implies   ' + str(frm2)\
                              for arg1 in args1]))
            
    case (_, Or(loc2, tyof2, args2)):
      for arg2 in args2:
        try:
          check_implies(loc, frm1, arg2)
          return
        except UserError:
          continue
      user_error(loc, '\nCould not prove that\n\t' + str(frm1) + '\n' \
                 + 'implies\n\t' + str(frm2) + '\n' \
                 + 'because we could not prove at least one of\n'
                 + '\n'.join(['\t' + str(frm1) + '   implies   ' + str(arg2)\
                              for arg2 in args2]))
      
    case (IfThen(_, _, prem1, conc1), IfThen(loc2, tyof2, prem2, conc2)):
      try:
        check_implies(loc, prem2, prem1)
        check_implies(loc, conc1, conc2)
      except UserError as e:
        raise wrap_user_error(e, _implies_context(frm1, frm2)) from e

    case (All(_, _, var1, _, body1), All(loc2, tyof2, var2, _, body2)):
      try:
          sub = { var2[0]: OverloadedVar(loc2, var1[1], [var1[0]]) }
          body2a = cast(Formula, body2.substitute(sub))
          check_implies(loc, body1, body2a)
      except UserError as e:
        raise wrap_user_error(e, _implies_context(frm1, frm2)) from e

    case (All(_, _, _, _, body1), _):
       matching:dict[str, Term] = {}
       try:
         vars, body = collect_all(frm1)
         formula_match(loc, vars, body, frm2, matching, Env(),
                       numeric_literals=True)
       except MatchFailed as e:
         user_error(loc, '\nCould not prove that\n\t' + str(frm1) \
                    + '\ninstantiates to\n\t' + str(frm2) \
                    + '\nbecause\n' + str(e))
       
    case _:
      if not formulas_equal_modulo_numeric_literals(frm1, frm2):
        diff = isolate_difference(frm1, frm2)
        if diff:
          (small_frm1, small_frm2) = diff
          hint = commute_diff_hint(frm2)
          if small_frm1 != frm1:
              msg = 'error, the proved formula:\n' \
                  + '\t' + str(frm1) + '\n' \
              + 'does not match the goal:\n' \
              + '\t' + str(frm2) + '\n' \
              + 'because\n\t' + str(small_frm1) + '\n\t≠ ' + str(small_frm2) + '\n' 
              user_error(loc, msg + hint)
          else:
              user_error(loc, '\nYou provided a proof of:\n\t' + str(frm1) \
                    + '\nbut that is different from what you need to prove:\n\t' + str(frm2) \
                    + hint)
        else:
            internal_error(loc, 'internal error, could not isolate difference for\n\t' \
                           + str(frm1) + '\nand\n\t' + str(frm2))
                    
def instantiate(loc: Meta, allfrm: Formula, arg: SubstitutionValue) -> Formula:
  match allfrm:
    case All(_, _, (var, _), (s, _), frm):
      sub = { var : arg }
      ret = cast(Formula, frm.substitute(sub))
      if s != 0:
        ret = update_all_head(ret)
      return ret
    case _:
      internal_error(loc, 'expected all formula to instantiate, not ' + str(allfrm))
  
def str_of_env(env: Mapping[str, object]) -> str:
  return '{' + ', '.join([k + ": " + str(e) for (k,e) in env.items()]) + '}'

def pattern_to_term(pat: Pattern) -> Term:
  match pat:
    case PatternCons(loc, constr, params):
      if len(params) > 0:
        ret = Call(loc, None, constr,
                   [ResolvedVar(loc, None, param) for param in params])
        return ret
      else:
        return constr
    case _:
      internal_error(pat.location, "expected a pattern, not " + str(pat))

def rewrite(loc: Meta, formula: Formula, equation: Formula | AutoRewriteRule,
            env: Env) -> Formula:
    num_marks = count_marks(formula)
    if num_marks == 0:
        ret = rewrite_aux(loc, formula, equation, env)
        print_verbose(lambda: '\trewrote ' + str(formula) + '\n\t    ==> ' + str(ret) \
                      + '\n\tusing ' + str(equation))
        return ret
    elif num_marks == 1:
        try:
            find_mark(formula)
            internal_error(loc, 'in replace, find_mark failed on formula:\n\t' + str(formula))
        except MarkException as ex:
            new_subject = rewrite_aux(loc, ex.subject, equation, env)
            return replace_mark(formula, new_subject)
    else:
        internal_error(loc, 'in replace, formula contains more than one mark:\n\t' + str(formula))

def facts_to_str(env: Mapping[str, object]) -> str:
  result = ''
  for (x,p) in env.items():
    if isinstance(p, Formula) or isinstance(p, Term):
      result += x + ': ' + str(p) + '\n'
  return result

def isolate_difference_list(list1: Iterable[AST],
                            list2: Iterable[AST]) -> Difference | None:
  for (t1, t2) in zip(list1, list2):
    diff = _isolate_difference(t1, t2)
    if diff:
      return diff
  return None
  
def isolate_difference(term1: AST, term2: AST) -> Difference:
  diff = _isolate_difference(term1, term2)
  return diff if diff is not None else (term1, term2)

def _isolate_difference(term1: AST, term2: AST) -> Difference | None:
  if get_verbose():
    print('isolate_difference(' + str(term1) + ',' + str(term2) + ')')
  if term1 == term2:
    return None
  else:
    match (term1, term2):
      case (Lambda(l1, _, vs1, body1), Lambda(_, _, vs2, body2)):
        ren = {x: ResolvedVar(l1, t2, y) for ((x,t1),(y,t2)) in zip(vs1, vs2)}
        return _isolate_difference(body1.substitute(ren), body2)
      case (Call(l1, _, fun1, args1), Call(_, _, fun2, args2)):
        if fun1 == fun2:
          if len(args1) == len(args2):
              return isolate_difference_list(args1, args2)
          else:
              return (term1, term2)
        else:
          return _isolate_difference(fun1, fun2)
      case (SwitchCase(l1, p1, body1), SwitchCase(_, p2, body2)):
        if p1 == p2:
          return _isolate_difference(body1, body2)
        else:
          return (p1, p2)
      case (Switch(l1, _, s1, cs1), Switch(_, _, s2, cs2)):
        if s1 == s2:
          return isolate_difference_list(cs1, cs2)
        else:
          return (s1, s2)
      case(And(l1, _, args1), And(_, _, args2)):
        return isolate_difference_list(args1, args2)
      case (All(l1, _, _, _, body1), All(_, _, _, _, body2)):
        return (term1, term2)
      case _:
        return (term1, term2)

def collect_all_if_then(loc: Meta, frm: Formula,
                        env: Env) -> tuple[list[Term], list[ImplicationPremise]]:
    """Returns a list of all variables that need be instantiated, and anythings that need applied"""

    if isinstance(frm, TLet):
      frm = cast(Formula, frm.reduceLets(env))

    match frm:
      case All(loc2, _, var, _, frm):
        (rest_vars, mps) = collect_all_if_then(loc, frm, env)
        x, t = var
        return ([ResolvedVar(loc2, t, x)] + rest_vars, mps)
      case IfThen(loc2, _, prem, conc):
        return ([], [(prem, conc)])
      case And(loc2, _, args):
        mps1: list[ImplicationPremise] = []
        for arg in args:
          try:
            (rest_vars, mps) = collect_all_if_then(loc, arg, env)
          except Exception:
            continue
          # Making the executive decision that we can't apply for alls nested within ands
          if len(rest_vars) > 0: continue
          mps1 += mps
        if len(mps1) == 0:
          user_error(loc, "in 'apply', expected at least one if-then formula as a conjunct of " + str(frm))
        return ([], mps1)
      case _:
        user_error(loc, "in 'apply', expected an if-then formula, not " + str(frm))

def collect_all(frm: Formula) -> tuple[list[Term], Formula]:
    match frm:
      case All(loc2, _, var, _, frm):
        (rest_vars, body) = collect_all(frm)
        x, t = var
        prefix: list[Term] = [ResolvedVar(loc2, t, x)]
        return (prefix + rest_vars, body)
      case _:
        return ([], frm)

def auto_simplified_hint(new_formula: Formula) -> str:
  if is_true(new_formula):
    return '\nThe goal has been simplified to `true`, possibly by an earlier transformation\n' \
           'in this chain or an `auto` rewrite rule. Drop the remaining transformation(s)\n' \
           'and end the step with `.`, or replace the whole step with `evaluate`.'
  return ''


def _ast_mentions_any(node: AST, target_names: set[str]) -> bool:
  # AST traversal: does `node` reference any name in `target_names`?
  # No general `free_vars` is defined across all Term subclasses, so we
  # walk the dataclass fields directly.
  seen: set[int] = set()
  stack: list[object] = [node]
  while stack:
    n = stack.pop()
    nid = id(n)
    if nid in seen:
      continue
    seen.add(nid)
    if isinstance(n, VarRef):
      if isinstance(n, OverloadedVar):
        for nm in n.resolved_names:
          if nm in target_names:
            return True
      else:
        if n.get_name() in target_names:
          return True
    if hasattr(n, '__dict__'):
      for v in vars(n).values():
        if isinstance(v, (list, tuple)):
          stack.extend(v)
        elif isinstance(v, dict):
          stack.extend(v.values())
        elif v is not None and not isinstance(v, (str, int, float, bool)):
          stack.append(v)
  return False


def _expand_would_progress(residual: Formula | Term, defs: Sequence[Term],
                           env: Env) -> bool:
  # Would running `expand_definitions` on `residual` with the same `defs`
  # actually change the formula? Used to gate the "unfold further" hint
  # so it doesn't fire when more expand wouldn't help -- e.g. when the
  # def is stuck because its arg is a free variable rather than a
  # constructor, or when the def has already fully unfolded.
  current = residual
  for var in defs:
    if not isinstance(var, VarRef):
      continue
    try:
      var = var.reduce(env)
    except Exception:
      continue
    if not isinstance(var, VarRef):
      continue
    if isinstance(var, OverloadedVar):
      candidate_names = var.resolved_names
    else:
      candidate_names = [var.get_name()]
    for var_name in candidate_names:
      if var_name not in env.dict:
        continue
      binding = env.dict[var_name]
      if binding.visibility == 'opaque' \
         and binding.module != env.get_current_module():
        continue
      rvar = ResolvedVar(var.location, var.typeof, var_name)
      try:
        rhs = env.get_value_of_term_var(rvar)
      except Exception:
        continue
      if rhs is None:
        continue
      try:
        new = current.substitute({rvar.name: rhs}).reduce(env)
      except Exception:
        continue
      if new != current:
        return True
      current = new
  return False


def _equation_marked_side(formula: Formula | None) -> str | None:
  # Return 'lhs' / 'rhs' if `formula` is an equation `L = R` whose single
  # mark sits on exactly one side (explicit, or implicit from `equations`).
  # Otherwise None.
  if count_marks(formula) != 1:
    return None
  match formula:
    case Call(_, _, rator, [side0, side1]) \
         if isinstance(rator, VarRef) and rator.get_name() == '=':
      marks0 = count_marks(side0)
      marks1 = count_marks(side1)
      if marks0 == 1 and marks1 == 0:
        return 'lhs'
      if marks0 == 0 and marks1 == 1:
        return 'rhs'
      return None
    case _:
      return None


def _defs_mentioned_in(node: AST, defs: Sequence[Term]) -> list[str]:
  # Display names of `defs` (VarRefs) that appear anywhere in `node`.
  result: list[str] = []
  for d in defs:
    if not isinstance(d, VarRef):
      continue
    if isinstance(d, OverloadedVar):
      targets = set(d.resolved_names)
    else:
      targets = {d.get_name()}
    if _ast_mentions_any(node, targets):
      display = base_name(d.get_name())
      if display not in result:
        result.append(display)
  return result


def expand_residual_hint(residual: Formula, defs: Sequence[Term], env: Env,
                         original: Formula | None = None) -> str:
  # When `expand f.` fails and `f` still appears in the residual goal,
  # tell the user the unfolding depth was too shallow. The common case
  # is a recursive function whose body re-introduces its own name; one
  # extra step (`expand f | f.` or `expand 2*f.`) finishes the proof.
  # Only fire when another expand pass would actually change the
  # residual -- otherwise the suggestion is misdirection (e.g. the
  # function is stuck on a variable arg and the real fix is `switch`).
  #
  # `original` is the pre-expansion formula (with marks intact). When it
  # is a marked equation -- explicit `#L# = R` or the implicit-LHS form
  # that `equations` blocks inject -- `expand` only ever rewrites the
  # marked side. Suggesting `N*expand` when the residual `f` lives on the
  # unmarked side is misleading: chaining more expands won't touch it.
  # In that case point the user at the `#...#` workaround instead (the
  # advice already produced by [[expand_backward_mark_hint]] when expand
  # itself fails -- #450).
  still_present = _defs_mentioned_in(residual, defs)
  if not still_present:
    return ''
  marked_side = _equation_marked_side(original) if original is not None else None
  if marked_side is not None and isinstance(residual, Call) \
     and isinstance(residual.rator, VarRef) \
     and residual.rator.get_name() == '=' \
     and len(residual.args) == 2:
    if marked_side == 'lhs':
      marked_residual = residual.args[0]
      unmarked_residual = residual.args[1]
      other_label = 'right-hand side'
    else:
      marked_residual = residual.args[1]
      unmarked_residual = residual.args[0]
      other_label = 'left-hand side'
    if _expand_would_progress(marked_residual, defs, env):
      return _chain_expand_msg(_defs_mentioned_in(marked_residual, defs)
                               or still_present)
    if _expand_would_progress(unmarked_residual, defs, env):
      unmarked_names = _defs_mentioned_in(unmarked_residual, defs) \
                       or still_present
      if len(unmarked_names) == 1:
        listed = '`' + unmarked_names[0] + '`'
      else:
        listed = ', '.join('`' + n + '`' for n in unmarked_names)
      return ('\nThe ' + other_label + ' contains ' + listed \
              + ', but `expand` only unfolds inside the marked subterm. ' \
              'Inside an `equations` block, the left-hand side of each step is ' \
              'implicitly marked. To unfold the ' + other_label \
              + ' instead, wrap that side in `#...#`:\n' \
              '\t# ' + str(unmarked_residual) + ' #')
    return ''
  if not _expand_would_progress(residual, defs, env):
    return ''
  return _chain_expand_msg(still_present)


def _chain_expand_msg(names: list[str]) -> str:
  if len(names) == 1:
    name = names[0]
    return ('\nThe goal still contains `' + name + '`. ' \
            'To unfold it again, chain another expand:\n' \
            '\texpand ' + name + ' | ' + name + '.\n' \
            'or equivalently\n' \
            '\texpand 2*' + name + '.')
  listed = ', '.join('`' + n + '`' for n in names)
  return ('\nThe goal still contains ' + listed + '. ' \
          'Chain another expand with `|` (e.g. `expand f | f.`) or use `N*f` to unfold further.')


def _collect_unfoldable_recfun_names(formula: Formula, env: Env) -> list[str]:
  # Walk `formula`; return display names of any `VarRef` whose binding is
  # a non-opaque recursive function (`recursive`, `generic recursive`,
  # `view recursive`). Used to name concrete `expand` targets in the
  # closed-goal hint below; we deliberately skip `define`/operator
  # bindings here -- `expand` accepts them, but the dominant beginner
  # trip-up is forgetting to unfold a `recursive` definition, and naming
  # only those keeps the hint focused.
  names: list[str] = []
  seen_ids: set[int] = set()
  seen_names: set[str] = set()
  stack: list[object] = [formula]
  while stack:
    n = stack.pop()
    nid = id(n)
    if nid in seen_ids:
      continue
    seen_ids.add(nid)
    if isinstance(n, VarRef):
      if isinstance(n, OverloadedVar):
        candidates = list(n.resolved_names)
      else:
        candidates = [n.get_name()]
      for nm in candidates:
        if nm not in env.dict:
          continue
        binding = env.dict[nm]
        if not isinstance(binding, TermBinding):
          continue
        if not isinstance(binding.defn, (RecFun, GenRecFun, ViewRecFun)):
          continue
        if binding.visibility == 'opaque' \
           and binding.module != env.get_current_module():
          continue
        display = base_name(nm)
        if display in seen_names:
          continue
        seen_names.add(display)
        names.append(display)
    if hasattr(n, '__dict__'):
      for v in vars(n).values():
        if isinstance(v, (list, tuple)):
          stack.extend(v)
        elif isinstance(v, dict):
          stack.extend(v.values())
        elif v is not None and not isinstance(v, (str, int, float, bool)):
          stack.append(v)
  return names


def ground_goal_evaluate_hint(form_red: Formula, formula_red: Formula,
                              env: Env) -> str:
  # Fires when the user supplies `.` (proof of `true`) for a non-`true`
  # goal and that goal would actually evaluate to `true` once recursive
  # definitions are unfolded. Points the beginner at `evaluate` (and
  # names the unfoldable recursive functions, if any, for `expand`) so
  # the bare "proof of true vs. <complex goal>" error isn't a dead end.
  if not is_true(form_red):
    return ''
  if is_true(formula_red):
    return ''
  prev_reduce_all = get_reduce_all()
  prev_dont_reduce_opaque = get_dont_reduce_opaque()
  set_reduce_all(True)
  set_dont_reduce_opaque(True)
  try:
    fully_reduced = formula_red.reduce(env)
  except Exception:
    return ''
  finally:
    set_reduce_all(prev_reduce_all)
    set_dont_reduce_opaque(prev_dont_reduce_opaque)
  if not is_true(fully_reduced):
    return ''
  fns = _collect_unfoldable_recfun_names(formula_red, env)
  base = '\nThe goal is a closed term but is not yet reduced. Try `evaluate`'
  if not fns:
    return base + '.'
  if len(fns) == 1:
    return base + ', or `expand ' + fns[0] + '` to unfold the definition.'
  return base + ', or `expand ' + ' | '.join(fns) \
              + '` to unfold the definitions.'


def expand_backward_mark_hint(formula: Formula, var: Term, env: Env) -> str:
  # When `expand X` fails inside a marked equation `# L # = R` (or the
  # mirrored form), expand only saw the marked side. If unfolding X on
  # the *other* side would succeed, suggest wrapping that side in
  # `#...#`. This is the common newcomer trip-up in `equations` blocks,
  # where the LHS of each step is implicitly marked: an `expand` whose
  # unfolding belongs on the RHS fails with a confusing "could not find
  # a place to expand" error and no pointer at the mark form.
  if count_marks(formula) != 1:
    return ''
  match formula:
    case Call(_, _, rator, [side0, side1]) \
         if isinstance(rator, VarRef) and rator.get_name() == '=':
      marks0 = count_marks(side0)
      marks1 = count_marks(side1)
      if marks0 == 1 and marks1 == 0:
        other = side1
        other_label = 'right-hand side'
      elif marks0 == 0 and marks1 == 1:
        other = side0
        other_label = 'left-hand side'
      else:
        return ''
      if not _expand_would_progress(other, [var], env):
        return ''
      display_name = name2str(var.get_name()) if isinstance(var, VarRef) \
                     else str(var)
      return ('\nThe ' + other_label + ' contains `' + display_name \
              + '`, but `expand` only unfolds inside the marked subterm. ' \
              'Inside an `equations` block, the left-hand side of each step is ' \
              'implicitly marked. To unfold the ' + other_label \
              + ' instead, wrap that side in `#...#`:\n' \
              '\t# ' + str(other) + ' #')
    case _:
      return ''


def replace_backward_mark_hint(formula: Formula, eq: Formula | AutoRewriteRule,
                               env: Env) -> str:
  # Mirror of `expand_backward_mark_hint` for the `replace` tactic: when
  # `replace eq` fails inside a marked equation `# L # = R` because the
  # eq's LHS doesn't appear on the marked side, but it *would* match on
  # the unmarked side, suggest wrapping that side in `#...#`.
  if count_marks(formula) != 1:
    return ''
  match formula:
    case Call(_, _, rator, [side0, side1]) \
         if isinstance(rator, VarRef) and rator.get_name() == '=':
      marks0 = count_marks(side0)
      marks1 = count_marks(side1)
      if marks0 == 1 and marks1 == 0:
        other = side1
        other_label = 'right-hand side'
      elif marks0 == 0 and marks1 == 1:
        other = side0
        other_label = 'left-hand side'
      else:
        return ''
      try:
        reset_num_rewrites()
        rewrite_aux(formula.location, other, eq, env)
      except Exception:
        return ''
      if get_num_rewrites() == 0:
        return ''
      return ('\nThe ' + other_label + ' does contain a match, but `replace` ' \
              'only rewrites inside the marked subterm. Inside an `equations` ' \
              'block, the left-hand side of each step is implicitly marked. ' \
              'To rewrite the ' + other_label + ' instead, wrap that side in `#...#`:\n' \
              '\t# ' + str(other) + ' #')
    case _:
      return ''


def expand_definitions(loc: Meta, formula: Formula, defs: Sequence[Term],
                       env: Env) -> Formula:
  num_marks = count_marks(formula)
  if num_marks == 0:
      new_formula = formula
  elif num_marks == 1:
      try:
          find_mark(formula)
          internal_error(loc, 'in expand_definitions, find_mark failed on formula:\n\t' \
                         + str(formula))
      except MarkException as ex:
          new_formula = ex.subject
  else:
      internal_error(loc, 'in expand, formula contains more than one mark:\n\t' \
                     + str(formula))
  if get_verbose():
      print('expand definitions to formula: ' + str(new_formula))
  # True once an earlier target in this `expand a | b | ...` collapsed the
  # goal to `true` (e.g. via an auto rewrite). Later targets then have nothing
  # left to unfold; we treat that as a no-op so `expand` is order-independent.
  collapsed_by_earlier = False
  for var in defs:
    if not env.term_var_is_defined(var):
      user_error(loc, f"Expected a term or a type variable when attempting to expand {var}." +\
                 f"\n\tIf {var} is a theorem or a lemma, you might want to use 'replace'")
    var = var.reduce(env)
    # it's a bit strange that RecDef's can find there way into defs -Jeremy

    if isinstance(var, VarRef):
      reduced_one = False

      # `var` may be either an OverloadedVar (multi-candidate) or a
      # ResolvedVar (single chosen name). Normalize to a candidate list.
      if isinstance(var, OverloadedVar):
        candidate_names = var.resolved_names
      else:
        candidate_names = [var.get_name()]

      reducible_names = []
      for var_name in candidate_names:
          if var_name in env.dict.keys():
              binding = env.dict[var_name]
              if binding.visibility == 'opaque' \
                 and binding.module != env.get_current_module():
                if len(candidate_names) == 1:
                    user_error(loc, 'Cannot expand opaque definition of '
                          + base_name(var_name))
              else:
                reducible_names.append(var_name)
      
      for var_name in reducible_names:
          if get_verbose():
              print('trying to expand definition of ' + var_name)
          rvar = ResolvedVar(var.location, var.typeof, var_name)
          rhs = env.get_value_of_term_var(rvar)
          if rhs == None:
              user_error(loc, 'could not find definition of ' + str(rvar))
          else:
              reset_reduced_defs()
              if get_verbose():
                  print('definition subst ' + rvar.name + ' => ' + str(rhs))
              new_formula = cast(Formula, new_formula.substitute({rvar.name: rhs}))
              new_formula = new_formula.reduce(env)
              if rvar.name in get_reduced_defs():
                  reduced_one = True
                  if get_verbose():
                      print('expanded definition ' + var_name)
      if get_verbose():
          print('new_formula = ' + str(new_formula))
      if reduced_one and is_true(new_formula):
          collapsed_by_earlier = True
      if not reduced_one:
          if collapsed_by_earlier:
              # An earlier clause already reduced the goal to `true`, so this
              # clause has nothing left to unfold. Allow it (expand stays
              # order-independent w.r.t. early collapse) but warn that it is
              # dead weight so the user can tidy the proof.
              warning(loc, "warning: unused clause '" + name2str(var.name) \
                    + "' in expand: the goal was already simplified to `true` " \
                    + "by an earlier clause, so there is nothing left to " \
                    + "expand. Drop this clause from the expand.")
          else:
              user_error(loc, 'could not find a place to expand definition of ' \
                    + name2str(var.name) \
                    + ' in:\n' + '\t' + str(new_formula) \
                    + auto_simplified_hint(new_formula) \
                    + expand_backward_mark_hint(formula, var, env))

  if num_marks == 0:          
      return check_formula(new_formula, env)
  else:
      return check_formula(replace_mark(formula, new_formula).reduce(env), env)

def apply_rewrites(loc: Meta, formula: Formula,
                   eqns: Sequence[Formula | AutoRewriteRule], env: Env,
                   *, display_formula: Formula | None = None,
                   display_eqns: Sequence[Formula | AutoRewriteRule] | None = None) -> Formula:
  # `formula` is the value rewrites operate over (may be auto-normalized).
  # `display_formula`, if provided, is the pre-normalized form shown in
  # error messages so users see the goal they actually wrote.
  # `display_eqns`, if provided, is a parallel list of the pre-normalized
  # equations used in diagnostics; an entry that auto-rules collapse to
  # `true` would otherwise have no useful printed form.
  num_marks = count_marks(formula)
  if num_marks == 0:
      new_formula = formula
  elif num_marks == 1:
      try:
          find_mark(formula)
          internal_error(loc, 'in apply_rewrites, find_mark failed on formula:\n\t' + str(formula))
      except MarkException as ex:
          new_formula = ex.subject
  else:
      internal_error(loc, 'in rewrite, formula contains more than one mark:\n\t' + str(formula))

  display_seq: Sequence[Formula | AutoRewriteRule] = \
      display_eqns if display_eqns is not None else eqns
  for eq, display_eq in zip(eqns, display_seq):
    if not is_equation(eq):
        msg = 'in replace, expected an equation, not:\n\t' + str(eq) \
              + '\n\twhile replacing ' \
              + ', '.join([str(e) for e in eqns])
        match eq:
            case IfThen(_, _, p, Bool(_, _, False)):
                msg += '\n\n`replace` only rewrites with equations of the form `a = b`.' \
                       '\nSince this hypothesis is `not P`, try `simplify with` instead,' \
                       '\nwhich substitutes\n\t' + str(p) + '\nwith `false` in the goal.'
            case _:
                msg += '\n\n`replace` only rewrites with equations of the form `a = b`.' \
                       '\nFor other boolean hypotheses, use `simplify with` instead.'
        user_error(loc, msg)
    reset_num_rewrites()
    new_formula = rewrite_aux(loc, new_formula, eq, env)
    if get_num_rewrites() == 0:
        (lhs, rhs) = split_equation(loc, eq, env)
        shown_formula = display_formula if display_formula is not None else new_formula
        msg = '\ncould not find any matches for\n\t' + str(lhs) \
              + '\nin\n\t' + str(shown_formula)
        if display_formula is not None and str(shown_formula) != str(new_formula):
            msg += '\n(which auto-rule normalization reduced to:\n\t' \
                   + str(new_formula) + ')'
        msg += '\nwhile trying to replace using the below equation, left to right\n\t' + str(eq) \
               + auto_simplified_hint(new_formula) \
               + replace_backward_mark_hint(formula, eq, env)
        user_error(loc, msg)
    new_formula = new_formula.reduce(env)
      
  if num_marks == 0:          
      return new_formula
  else:
      return replace_mark(formula, new_formula).reduce(env)
