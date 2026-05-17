# mypy: ignore-errors
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

from checker_common import *

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
          context = '\n\nWhile trying to prove that\n\t' + str(frm1) \
              + '\nimplies\n'\
              + '\t' + str(frm2)
          raise wrap_user_error(e, context) from e

    case(Or(_, _, args1), _):
      for arg1 in args1:
        try:
          check_implies(loc, arg1, frm2)
        except UserError as e:
          context = '\n\nWhile trying to prove that\n\t' + str(frm1) \
              + '\nimplies\n'\
              + '\t' + str(frm2)
          raise wrap_user_error(e, context) from e
      
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
        context = '\n\nWhile trying to prove that\n\t' + str(frm1) \
            + '\nimplies\n'\
            + '\t' + str(frm2)
        raise wrap_user_error(e, context) from e

    case (All(_, _, var1, _, body1), All(loc2, tyof2, var2, _, body2)):
      try:
          sub = { var2[0]: OverloadedVar(loc2, var1[1], [var1[0]]) }
          body2a = cast(Formula, body2.substitute(sub))
          check_implies(loc, body1, body2a)
      except UserError as e:
        context = '\n\nWhile trying to prove that\n\t' + str(frm1) \
            + '\nimplies\n'\
            + '\t' + str(frm2)
        raise wrap_user_error(e, context) from e

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
          if small_frm1 != frm1:
              msg = 'error, the proved formula:\n' \
                  + '\t' + str(frm1) + '\n' \
              + 'does not match the goal:\n' \
              + '\t' + str(frm2) + '\n' \
              + 'because\n\t' + str(small_frm1) + '\n\t≠ ' + str(small_frm2) + '\n' 
              user_error(loc, msg)
          else:
              user_error(loc, '\nYou provided a proof of:\n\t' + str(frm1) \
                    + '\nbut that is different from what you need to prove:\n\t' + str(frm2))
        else:
            internal_error(loc, 'internal error, could not isolate difference for\n\t' \
                           + str(frm1) + '\nand\n\t' + str(frm2))
                    
def instantiate(loc: Meta, allfrm: Any, arg: Any) -> Any:
  match allfrm:
    case All(_, _, (var, _), (s, _), frm):
      sub = { var : arg }
      ret = frm.substitute(sub)
      if s != 0:
        ret = update_all_head(ret)
      return ret
    case _:
      internal_error(loc, 'expected all formula to instantiate, not ' + str(allfrm))
  
def str_of_env(env):
  return '{' + ', '.join([k + ": " + str(e) for (k,e) in env.items()]) + '}'

def pattern_to_term(pat: Any) -> Any:
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

def rewrite(loc: Meta, formula: Any, equation: Any, env: Env) -> Any:
    if False and get_verbose():
        print('rewriting ' + str(formula) + '\n\twith ' + str(equation))
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

def facts_to_str(env):
  result = ''
  for (x,p) in env.items():
    if isinstance(p, Formula) or isinstance(p, Term):
      result += x + ': ' + str(p) + '\n'
  return result

def isolate_difference_list(list1, list2):
  for (t1, t2) in zip(list1, list2):
    diff = isolate_difference(t1, t2)
    if diff:
      return diff
  return None
  
def isolate_difference(term1: Any, term2: Any) -> Any:
  if get_verbose():
    print('isolate_difference(' + str(term1) + ',' + str(term2) + ')')
  if term1 == term2:
    return None
  else:
    match (term1, term2):
      case (Lambda(l1, _, vs1, body1), Lambda(_, _, vs2, body2)):
        ren = {x: ResolvedVar(l1, t2, y) for ((x,t1),(y,t2)) in zip(vs1, vs2)}
        return isolate_difference(body1.substitute(ren), body2)
      case (Call(l1, _, fun1, args1), Call(_, _, fun2, args2)):
        if fun1 == fun2:
          if len(args1) == len(args2):
              return isolate_difference_list(args1, args2)
          else:
              return (term1, term2)
        else:
          return isolate_difference(fun1, fun2)
      case (SwitchCase(l1, p1, body1), SwitchCase(_, p2, body2)):
        if p1 == p2:
          return isolate_difference(body1, body2)
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

def collect_all_if_then(loc: Meta, frm: Any, env: Env) -> Any:
    """Returns a list of all variables that need be instantiated, and anythings that need applied"""

    if isinstance(frm, TLet):
      frm = frm.reduceLets(env)

    match frm:
      case All(loc2, _, var, _, frm):
        (rest_vars, mps) = collect_all_if_then(loc, frm, env)
        x, t = var
        return ([ResolvedVar(loc2, t, x)] + rest_vars, mps)
      case IfThen(loc2, _, prem, conc):
        return ([], [(prem, conc)])
      case And(loc2, _, args):
        mps1 = []
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

def collect_all(frm):
    match frm:
      case All(loc2, _, var, _, frm):
        (rest_vars, body) = collect_all(frm)
        x, t = var
        return ([ResolvedVar(loc2, t, x)] + rest_vars, body)
      case _:
        return ([], frm)

def auto_simplified_hint(new_formula):
  if is_true(new_formula):
    return '\nThe goal has been simplified to `true`, possibly by an `auto` rewrite rule.\n' \
           'Finish the proof with `.` (which closes any goal of the form `true`).'
  return ''


def _ast_mentions_any(node, target_names):
  # AST traversal: does `node` reference any name in `target_names`?
  # No general `free_vars` is defined across all Term subclasses, so we
  # walk the dataclass fields directly.
  seen = set()
  stack = [node]
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


def _expand_would_progress(residual, defs, env):
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


def expand_residual_hint(residual: Any, defs: Any, env: Env) -> Any:
  # When `expand f.` fails and `f` still appears in the residual goal,
  # tell the user the unfolding depth was too shallow. The common case
  # is a recursive function whose body re-introduces its own name; one
  # extra step (`expand f | f.` or `expand 2*f.`) finishes the proof.
  # Only fire when another expand pass would actually change the
  # residual -- otherwise the suggestion is misdirection (e.g. the
  # function is stuck on a variable arg and the real fix is `switch`).
  still_present = []
  for d in defs:
    if not isinstance(d, VarRef):
      continue
    if isinstance(d, OverloadedVar):
      targets = set(d.resolved_names)
    else:
      targets = {d.get_name()}
    if _ast_mentions_any(residual, targets):
      display = base_name(d.get_name())
      if display not in still_present:
        still_present.append(display)
  if not still_present:
    return ''
  if not _expand_would_progress(residual, defs, env):
    return ''
  if len(still_present) == 1:
    name = still_present[0]
    return ('\nThe goal still contains `' + name + '`. ' \
            'To unfold it again, chain another expand:\n' \
            '\texpand ' + name + ' | ' + name + '.\n' \
            'or equivalently\n' \
            '\texpand 2*' + name + '.')
  listed = ', '.join('`' + n + '`' for n in still_present)
  return ('\nThe goal still contains ' + listed + '. ' \
          'Chain another expand with `|` (e.g. `expand f | f.`) or use `N*f` to unfold further.')


def expand_backward_mark_hint(formula, var, env):
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


def replace_backward_mark_hint(formula, eq, env):
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


def expand_definitions(loc: Meta, formula: Any, defs: Any, env: Env) -> Any:
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
              new_formula = new_formula.substitute({rvar.name: rhs})
              new_formula = new_formula.reduce(env)
              if rvar.name in get_reduced_defs():
                  reduced_one = True
                  if get_verbose():
                      print('expanded definition ' + var_name)
      if get_verbose():
          print('new_formula = ' + str(new_formula))
      if not reduced_one:
          user_error(loc, 'could not find a place to expand definition of ' \
                + name2str(var.name) \
                + ' in:\n' + '\t' + str(new_formula) \
                + auto_simplified_hint(new_formula) \
                + expand_backward_mark_hint(formula, var, env))

  if num_marks == 0:          
      return check_formula(new_formula, env)
  else:
      return check_formula(replace_mark(formula, new_formula).reduce(env), env)

def apply_rewrites(loc: Meta, formula: Any, eqns: Any, env: Env, *, display_formula: Any = None) -> Any:
  # `formula` is the value rewrites operate over (may be auto-normalized).
  # `display_formula`, if provided, is the pre-normalized form shown in
  # error messages so users see the goal they actually wrote.
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

  for eq in eqns:
    if is_true(eq):
        user_error(loc, 'no need for replace because this equation is handled automatically\n\t' + str(eq))
    if not is_equation(eq):
        user_error(loc, 'in replace, expected an equation, not:\n\t' + str(eq)
                   + '\n\twhile replacing '
                   + ', '.join([str(eq) for eq in eqns]))
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
