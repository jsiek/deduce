# The checking process for programs & proofs has the following steps:
#
# 0. uniquify:
#    Rename all variables to have unique names.
#
# 1. process_declarations:
#    Collects the type environment for the top-level statements, usually
#    from their declared types. (Except for define's without types.)
#
# 2. type_check_stmt:
#    Type check the bodies of functions using the type environment.
#    Perform overload resolution using the types.
#
# 3. collect_env:
#    Collects the proofs (mapping proof labels to their formulas
#              and runtime environment mapping variables to values)
#    and the values (mapping names to their values, for defines a functions)
#    into an environment.
#
# 4. check_proofs:
#    Check that the proofs follow the rules of logic,
#    run the print and assert statements,
#    reduce some formulas and terms automatically.

from dataclasses import dataclass
from typing import List, Optional, Tuple, cast

from abstract_syntax import *
from error import user_error, incomplete_error, internal_error, warning, error_header, Diagnostic, ErrorSink, IncompleteProof, match_failed, MatchFailed, wrap_user_error, get_active_sink, set_active_sink, add_incomplete, add_diagnostic, speculative_probe
from flags import get_verbose, set_verbose, print_verbose, VerboseLevel, get_target_hole_location, get_debugger
import style

imported_modules: set = set()
checked_modules: set = set()

name_id = 0


# ---------------------------------------------------------------------------
# In-proof error collection
# ---------------------------------------------------------------------------
#
# ``check_deduce`` already collects one error per top-level statement.
# Inside a single proof, ``check_proof_of`` recurses; many of those
# recursions are sequential (each subproof's success is the parent's
# premise) but a handful are *sibling-independent*: each conjunct of
# a ``?, ?, ?`` tuple, each arm of a ``switch``, each case of an
# ``induction`` proves the same goal under different hypotheses with
# no value flowing between siblings. Catching and continuing at those
# loops surfaces every hole / failed subgoal in the proof, not just
# the first.
#
# Set by ``check_deduce`` for the duration of a single run with an
# error sink in scope; ``None`` otherwise (CLI / goal_at / MCP all
# leave it ``None`` and keep raise-on-first behaviour).  Mirrors the
# existing ``flags.target_hole_location`` pattern -- a module-level
# flag is how the rest of the checker plumbs run-wide context into
# ``check_proof_of`` without dragging an extra parameter through 50+
# recursive call sites.

def _try_check_proof_of(pf, frm, env):
  """Call ``check_proof_of`` and, when an error sink is active, catch
  any raised exception, append it to the sink, and return normally so
  the surrounding sibling loop continues.

  Use this only at sibling-independent recursion sites (PTuple
  conjuncts, switch / induction / cases arms). At sequential sites a
  failure means the parent can't continue meaningfully -- stick with
  a plain ``check_proof_of`` call there.
  """
  global _active_sink
  try:
    check_proof_of(pf, frm, env)
  except Diagnostic as e:
    if get_active_sink() is None:
      raise
    get_active_sink().add(e)

def generate_proof_name(name):
    """Allocate a fresh label/binder name at proof-check time.

    Uses ``proof_checker.name_id`` rather than a ``UniquifyContext`` —
    these are generated during proof checking (e.g. for synthesised
    induction-case bindings and rule-induction validators), not during
    the uniquify pass. Distinct counter so the names don't collide
    with the ones uniquify already minted."""
    global name_id
    ls = name.split('.')
    new_id = name_id
    name_id += 1
    return ls[0] + '.' + str(new_id)


# ---------------------------------------------------------------------------
# Per-statement cache
# ---------------------------------------------------------------------------
#
# ``check_deduce`` runs three loops over the AST: ``process_declaration``,
# ``type_check_stmt``, and ``collect_env``+``check_proofs``. Each loop's
# work for a given statement is determined by (a) the statement's
# post-uniquify structure and (b) the env coming in. Cache by both, and
# we can skip statements unchanged since the previous run.
#
# Key shape: ``(loop_tag, stmt_hash, chain_hash)``.  ``chain_hash`` is
# a fold over the prior statements' hashes -- equivalent to
# ``env_in_hash`` in the plan, but cheaper to maintain and stable
# across calls (since uniquify is now deterministic).
#
# The cache lives at module level and accumulates across
# ``check_deduce`` calls.  ``lsp/library.py`` clears it when the
# prelude key changes (different prelude => different baseline =>
# cache invalid).

_stmt_cache: dict = {}

# Hits and misses bucketed by loop, for the test instrumentation
# the plan requires ("untouched statements were cache hits").
_cache_stats: dict = {"hits": {}, "misses": {}}


def reset_stmt_cache() -> None:
    """Drop everything in ``_stmt_cache`` and zero the stats.  Called
    by the LSP pipeline when the prelude key changes; tests use it
    to start each fixture from a clean slate."""
    global _stmt_cache
    _stmt_cache.clear()
    _cache_stats["hits"].clear()
    _cache_stats["misses"].clear()


def get_cache_stats() -> dict:
    """Return a copy of the per-loop hit/miss counters."""
    return {
        "hits": dict(_cache_stats["hits"]),
        "misses": dict(_cache_stats["misses"]),
    }


def _record_hit(loop_tag: str) -> None:
    _cache_stats["hits"][loop_tag] = _cache_stats["hits"].get(loop_tag, 0) + 1


def _record_miss(loop_tag: str) -> None:
    _cache_stats["misses"][loop_tag] = _cache_stats["misses"].get(loop_tag, 0) + 1


def _hash_ast(node) -> int:
    """Stable structural hash of a (post-uniquify) AST.

    Skips the ``location`` (Meta) attribute, which carries source
    line/column info that shifts with edits to unrelated parts of
    the file -- we want only the structure + names to participate
    in the hash.

    Memoised on the node via ``__hash_cache__`` so each statement
    is hashed at most once per session, even if it appears in
    several of ``check_deduce``'s loops.
    """
    if node is None:
        return 0
    if isinstance(node, (str, int, bool, float)):
        return hash(node)
    if isinstance(node, (list, tuple)):
        return hash(tuple(_hash_ast(x) for x in node))
    if isinstance(node, dict):
        return hash(
            tuple(sorted((k, _hash_ast(v)) for k, v in node.items()))
        )
    cached = getattr(node, "__hash_cache__", None)
    if cached is not None:
        return cached
    if hasattr(node, "__dict__"):
        items = []
        for k, v in node.__dict__.items():
            if k == "location" or k == "__hash_cache__":
                continue
            items.append((k, _hash_ast(v)))
        h = hash((type(node).__name__, tuple(items)))
        try:
            node.__hash_cache__ = h
        except AttributeError:
            pass
        return h
    return hash(repr(node))


def _collect_referenced_names(node, out=None) -> set:
    """Walk a statement's post-uniquify AST and gather every uniquified
    name it references via ``VarRef`` (``Var`` / ``OverloadedVar`` /
    ``ResolvedVar``) or ``PVar``.

    Used by Step 14's dependency-aware invalidation: a statement's
    cache verdict is keyed on the hashes of the prior statements that
    introduced any of these names, so editing an unrelated theorem
    leaves this statement's entry intact.

    Skips ``location`` (irrelevant), ``__hash_cache__`` (memoisation
    artefact), and ``Import.ast`` (the imported module is checked on
    its own pass, and we treat ``Import`` as a global barrier in the
    caller anyway)."""
    if out is None:
        out = set()
    if node is None or isinstance(node, (str, int, bool, float)):
        return out
    if isinstance(node, (list, tuple)):
        for x in node:
            _collect_referenced_names(x, out)
        return out
    if isinstance(node, dict):
        for v in node.values():
            _collect_referenced_names(v, out)
        return out
    if isinstance(node, VarRef):
        out.add(node.get_name())
        return out
    if isinstance(node, PVar):
        out.add(node.name)
        return out
    if isinstance(node, Import):
        # Imports are treated as a global barrier by the caller; we
        # don't want to recurse into the imported module's AST here.
        return out
    if hasattr(node, "__dict__"):
        for k, v in node.__dict__.items():
            if k in ("location", "__hash_cache__"):
                continue
            _collect_referenced_names(v, out)
    return out


def _collect_defined_names(stmt) -> set:
    """Return the uniquified names a top-level statement introduces.

    Includes the statement's own name plus any auxiliary names it
    creates (union constructors; ``predicate`` rules and the
    auto-synthesised ``<pred>_rule_induction`` / ``_rule_inversion``
    theorems). Statements that don't introduce names (``Assert``,
    ``Print``, ``Auto``, ``Module``, ``Trace``, ``Import``) return
    the empty set; ``Import`` and ``Auto`` are handled separately by
    the caller as global barriers."""
    names: set = set()
    name = getattr(stmt, "name", None)
    if isinstance(name, str):
        names.add(name)
    if isinstance(stmt, Union):
        for con in stmt.alternatives:
            if isinstance(con.name, str):
                names.add(con.name)
    elif isinstance(stmt, Predicate):
        for rule in stmt.rules:
            if isinstance(rule.name, str):
                names.add(rule.name)
        rule_ind = getattr(stmt, "rule_induction_name", None)
        if isinstance(rule_ind, str):
            names.add(rule_ind)
        rule_inv = getattr(stmt, "rule_inversion_name", None)
        if isinstance(rule_inv, str):
            names.add(rule_inv)
    return names


def _is_global_barrier(stmt) -> bool:
    """Statements with global side-effects on later checking.

    ``Import`` brings a module's exports into the environment;
    ``Auto`` registers a rewrite rule consulted by every later
    proof. Conservatively treat both as a barrier: every later
    statement implicitly depends on them, so editing or removing
    one invalidates the cache for everything after."""
    return isinstance(stmt, (Import, Auto))
  
def check_implies(loc, frm1, frm2):
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
          body2a = body2.substitute(sub)
          check_implies(loc, body1, body2a)
      except UserError as e:
        context = '\n\nWhile trying to prove that\n\t' + str(frm1) \
            + '\nimplies\n'\
            + '\t' + str(frm2)
        raise wrap_user_error(e, context) from e

    case (All(_, _, _, _, body1), _):
       matching = {}
       try:
         vars, body = collect_all(frm1)
         formula_match(loc, vars, body, frm2, matching, Env())
       except MatchFailed as e:
         user_error(loc, '\nCould not prove that\n\t' + str(frm1) \
                    + '\ninstantiates to\n\t' + str(frm2) \
                    + '\nbecause\n' + str(e))
       
    case _:
      if frm1 != frm2:
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
                    
def instantiate(loc, allfrm, arg):
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

def pattern_to_term(pat):
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

def rewrite(loc, formula, equation, env):
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
  
def isolate_difference(term1, term2):
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

def collect_all_if_then(loc, frm, env):
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
        
def check_proof(proof, env):
  if get_verbose():
    print('check_proof:')
    print('\t' + str(proof))
  ret = None
  match proof:
    case PRecall(loc, facts):
      results = []
      for fact in facts:
        new_fact = type_check_term(fact, BoolType(loc), env, None, [])
        if new_fact in env.local_proofs():
            results.append(new_fact)
        else:
            user_error(loc, 'Could not find a proof of\n\t' + str(new_fact) \
                  + '\nin the current scope\n' \
                  + style.orange('Givens:') + '\n' + env.proofs_str())
      if len(results) > 1:
          ret = And(loc, BoolType(loc), results)
      elif len(results) == 1:
          ret = results[0]
      else:
          user_error(loc, 'expected some facts after `recall`')

    case EvaluateFact(loc, subject):
      formula = check_proof(subject, env)
      set_reduce_all(True)
      red_formula = formula.reduce(env)
      set_reduce_all(False)
      ret = red_formula
          
    case ApplyDefsFact(loc, definitions, subject):
      formula = check_proof(subject, env)
      new_formula = expand_definitions(loc, formula, definitions, env)
      ret = new_formula
      
    case RewriteFact(loc, subject, equation_proofs):
      formula = check_proof(subject, env)
      eqns = [check_proof(proof, env) for proof in equation_proofs]
      red_formula = formula.reduce(env)
      current_formula = red_formula
      current_formula = apply_rewrites(loc, current_formula, eqns, env,
                                       display_formula=formula)
      ret = current_formula

    case SimplifyFact(loc, subject, givens):
      formula = check_proof(subject, env)
      preds = [check_proof(proof, env) for proof in givens]
      equations = [pred_to_equality(loc, p) for p in preds]
      eqns = [equation.reduce(env) for equation in equations]
      new_formula = apply_rewrites(loc, formula, eqns, env)
      ret = new_formula.reduce(env)
      
    case PHole(loc):
      incomplete_error(loc, 'unfinished proof')
      
    case PSorry(loc):
      user_error(loc, "can't use sorry in context with unknown goal")

    case PHelpUse(loc, proof):
      formula = check_proof(proof, env)
      user_error(loc, proof_use_advice(proof, formula, env))
      
    case PVar(loc, name):
      try:
        ret = env.get_formula_of_proof_var(proof)
        if ret:
            return ret
        else:
            raise UserError('could not find given: ' + name)
      except UserError as e:
        user_error(loc, str(e))
      
    case PTrue(loc):
      ret = Bool(loc, BoolType(loc), True)
      
    case PTLetNew(loc, var, rhs, rest):
      new_rhs = type_synth_term(rhs, env, None, [])
      body_env = env.define_term_var(loc, var, new_rhs.typeof, new_rhs)
      ret = check_proof(rest, body_env)
      
    case PLet(loc, label, frm, reason, rest):
      new_frm = check_formula(frm, env)
      match new_frm:
        case Hole(loc2, tyof):
          proved_formula = check_proof(reason, env)
          user_error(loc, "\nhave " + label + ':\n\t' + str(proved_formula))
        case _:
          _try_check_proof_of(reason, new_frm, env)
          body_env = env.declare_local_proof_var(loc, label, remove_mark(new_frm))
          ret = check_proof(rest, body_env)
      
    case PAnnot(loc, claim, reason):
      new_claim = check_formula(claim, env)
      match new_claim:
        case Hole(loc2, tyof):
          proved_formula = check_proof(reason, env)
          user_error(loc, '\nconclude ' + str(proved_formula))
        case _:
          _try_check_proof_of(reason, new_claim, env)
          ret = remove_mark(new_claim)
      
    case PTuple(loc, pfs):
      frms = [check_proof(pf, env) for pf in pfs]
      ret = And(loc, BoolType(loc), frms)
      
    case PAndElim(loc, which, subject):
      formula = check_proof(subject, env)
      # formula = formula.reduce(env)
      if isinstance(formula, TLet):
        formula = formula.reduceLets(env)
      
      match formula:
        case And(loc2, tyof, args):
          if which >= len(args):
            user_error(loc, 'out of bounds, access to conjunct ' + str(which) \
                       + ' but there are only ' + str(len(args)) + ' conjuncts' \
                       + ' in formula\n\t' + str(formula))
          ret = args[which]
        case _:
          user_error(loc, 'expected a conjunction, not ' + str(formula))
          
    case ImpIntro(loc, label, prem, body):
      if prem is not None:
          new_prem = check_formula(prem, env)
      else:
          new_prem = None
      body_env = env.declare_local_proof_var(loc, label, new_prem)
      conc = check_proof(body, body_env)
      ret = IfThen(loc, BoolType(loc), new_prem, conc)
      
    case AllIntro(loc, var, pos, body):      
      body_env = env
      x, ty = var
      check_type(ty, env)
      if isinstance(ty, TypeType):
        body_env = body_env.declare_type(loc, x)
      else:
        body_env = body_env.declare_term_var(loc, x, ty)
      formula = check_proof(body, body_env)
      ret = All(loc, BoolType(loc), var, pos, formula)
      
    case AllElim(loc, univ, arg, pos):
      allfrm = check_proof(univ, env)

      if isinstance(allfrm, TLet):
        allfrm = allfrm.reduceLets(env)
      
      match allfrm:
        case All(loc2, tyof, var, _, frm):
          sub = {}
          v, ty = var
          try:
            new_arg = type_check_term(arg, ty.substitute(sub), env, None, [])
            if isinstance(new_arg, TermInst):
                new_arg.inferred = False
          except UserError as e:
            if isinstance(ty, TypeType):
              user_error(loc, f"In instantiation of\n\t{str(univ)} : {str(allfrm)}\n" \
                         + f"expected a type argument, but was given '{arg}'")
            else:
              raise e
          if isinstance(ty, TypeType):
            user_error(loc, 'to instantiate:\n\t' + str(univ)+' : '+str(allfrm) \
                       +'\nwith type arguments, instead write:\n\t' \
                       +str(univ) + '<' + str(arg) + '>\n')
        case _:
          user_error(loc, 'expected all formula to instantiate, not ' + str(allfrm) \
                     + '\n' + style.orange('Givens:') + '\n' + env.proofs_str())
      return instantiate(loc, allfrm, new_arg)

    case AllElimTypes(loc, univ, type_arg, _):
      allfrm = check_proof(univ, env)

      if isinstance(allfrm, TLet):
        allfrm = allfrm.reduceLets(env)

      match allfrm:
        case All(loc2, tyof, vars, _, frm):
          sub = {}
          var, ty = vars
          check_type(type_arg, env)
          if not isinstance(ty, TypeType):
              user_error(loc, 'unexpected term parameter ' + str(var) + ' in type instantiation')
          sub[var] = type_arg
        case _:
          user_error(loc, 'expected all formula to instantiate, not ' + str(allfrm))
      return instantiate(loc, allfrm, type_arg)
  
    case ModusPonens(loc, imp, arg):
      ifthen = check_proof(imp, env)
      match ifthen:
        case IfThen(loc2, tyof, prem, conc):
          pass
        case All(loc2, tyof, var, _, body):
          pass
        case And(loc2, tyof, args):
          pass
        case _:
          ifthen = ifthen.reduce(env)
      match ifthen:
        case IfThen(loc2, tyof, prem, conc):
          _try_check_proof_of(arg, prem, env)
          ret = conc.reduce(env)
        case And(loc2, tyof, args):
          vars, imps = collect_all_if_then(loc, ifthen, env)
          arg_frm = check_proof(arg, env)
          rets = []
          for prem, conc in imps:
            try:
              with speculative_probe():
                check_proof_of(arg, prem, env)
              rets.append(conc)
            except UserError:
              pass
          if len(rets) == 1: ret = rets[0]
          elif len(rets) > 1: ret = And(loc2, tyof, rets)
          else:
            user_error(loc, "could not prove that " +str(arg_frm) +
                       " implies at least one of\n\t"\
                       + "\n\t".join([str(p) for p, _ in imps])
                       + "\nfor application of \n\t"+str(ifthen)
                       + "\nto \n\t" + str(arg) + ': ' + str(arg_frm))
        case All(loc2, tyof, _, _, body):
          (vars, imps) = collect_all_if_then(loc, ifthen, env)
          rets = []
          reasons = []
          arg_frm = check_proof(arg, env)
          for prem, conc in imps: 
            try:
              matching = {}
              formula_match(loc, vars, prem, arg_frm, matching, env)
              type_vars = [x for x in vars if isinstance(x.typeof, TypeType)]
              term_vars = [x for x in vars if not isinstance(x.typeof, TypeType)]
              if len(type_vars) > 0:
                var_type = {x.name : x.typeof for x in term_vars}
                formula_matches = [(x,trm) for (x,trm) in matching.items()]
                for (x,trm) in formula_matches:
                    if x in var_type.keys():
                      new_var_type = var_type[x].substitute(matching)
                      type_match(loc, type_vars, new_var_type, trm.typeof, matching)
              for x in vars:
                if x.name not in matching.keys():
                  match_failed(loc, "could not deduce an instantiation for variable "\
                               + str(x) + '\n' \
                               + 'for application of\n\t' + str(ifthen) + '\n'\
                               + 'to\n\t' + str(arg) + ': ' + str(arg_frm))
              rets.append(conc.substitute(matching).reduce(env))
            except MatchFailed as e:
              reasons.append(e)
          if len(rets) == 1: ret = rets[0]
          elif len(rets) > 1: ret = And(loc2, tyof, rets)
          else:
            user_error(loc, "could not deduce an instantiation for any of the variables "\
                  + "for application of \n\t" + str(ifthen) + '\n'\
                  + 'to\n\t' + str(arg) + ': ' + str(arg_frm) + '\n'\
                  + 'because:\n' + '\n\t'.join([str(e) for e in reasons]))
        case _:
          user_error(loc, "in 'apply', expected an if-then formula, not " + str(ifthen))
          
    case PInjective(loc, constr, eq_pf):
      check_type(constr, env)
      if not is_constructor(constr.name, env):
        user_error(loc, 'in injective, expected a constructor, not\n\t' + base_name(constr.name) 
              + givens_str(env))
      formula = check_proof(eq_pf, env)
      (a,b) = split_equation(loc, formula, env)
      match (a,b):
        case (Call(loc2, _, rator1, args1),
              Call(_, _, rator2, args2)) if len(args1) == len(args2):
          f1 = base_name(rator_name(rator1))
          f2 = base_name(rator_name(rator2))
          if f1 != f2:
            user_error(loc, 'in injective, ' + f1 + ' ≠ ' + f2)
          if str(constr) != f1:
            user_error(loc, 'in injective, ' + str(constr) + ' ≠ ' + f1)
          if not is_constructor(rator_name(rator1), env):
            user_error(loc, 'in injective, ' + rator_name(rator1) + ' not a constructor')
          boolty = BoolType(loc)
          eqs = [mkEqual(loc, arg1, arg2) for (arg1,arg2) in zip(args1, args2)]
          if len(eqs) > 1:
              return And(loc, boolty, eqs)
          elif len(eqs) == 1:
              return eqs[0]
          else:
              return Bool(loc, boolty, True)
        case _:
          user_error(loc, 'in injective, non-applicable formula: ' + str(formula))
          
    case PSymmetric(loc, eq_pf):
      frm = check_proof(eq_pf, env)
      (a,b) = split_equation(loc, frm, env)
      return mkEqual(loc, b, a)

    case PTransitive(loc, eq_pf1, eq_pf2):
      eq1 = check_proof(eq_pf1, env)
      eq2 = check_proof(eq_pf2, env)
      (a,b1) = split_equation(loc, eq1, env)
      (b2,c) = split_equation(loc, eq2, env)
      b1r = b1.reduce(env)
      b2r = b2.reduce(env)
      if b1r != b2r:
        user_error(loc, 'error in transitive,\nyou proved\n\t'
              + str(eq1) + '\nand\n\t' + str(eq2) + '\n' \
              + 'but the middle formulas do not match:\n\t' \
              + str(b1r) + '\n≠\n\t' + str(b2r))
      else:
        return mkEqual(loc, a, c)
    case _:
      user_error(proof.location, goal_only_proof_error(proof))
  if get_verbose():
    print('\t=> ' + str(ret))
  return ret

# Tactic-keyword name used for each "goal-only" Proof class. These tactics
# transform the current goal rather than producing a proof of a formula, so
# they can only be checked by `check_proof_of`, not `check_proof`.
GOAL_ONLY_TACTIC_NAME = {
  ApplyDefsGoal: 'expand',
  RewriteGoal: 'replace',
  SimplifyGoal: 'simplify',
  EvaluateGoal: 'evaluate',
  Suffices: 'suffices',
  Induction: 'induction',
  RuleInduction: 'induction',
  RuleInversion: 'cases',
  Cases: 'cases',
  SwitchProof: 'switch',
}

def goal_only_proof_error(proof):
  """Error message for a proof that can only be used in goal-directed mode.

  Detects common user mistakes (e.g. chaining tactics with `|` as in
  ``replace eq | expand X``) and offers actionable advice instead of the
  internal phrase "need to be in goal-directed mode".
  """
  tactic = GOAL_ONLY_TACTIC_NAME.get(type(proof))
  if tactic is None:
    return 'a proof of a formula is expected here, not the tactic\n\t' \
        + str(proof)
  return '`' + tactic + '` is a goal-directed tactic — it transforms ' \
      + 'the current goal, but it does not by itself produce a proof of a ' \
      + 'formula. It cannot be used here.\n\n' \
      + 'If you wrote something like `replace eq | ' + tactic + ' ...` or ' \
      + '`expand f | ' + tactic + ' ...`, note that `|` separates ' \
      + 'arguments to the leading tactic, not a sequence of tactics. ' \
      + 'To run tactics in sequence, write them as separate proof steps:\n' \
      + '\treplace eq\n' \
      + '\t' + tactic + ' ...'

def get_type_args(ty):
  if isinstance(ty, VarRef):
    return []
  match ty:
    case TypeInst(_, ty, type_args):
      return type_args
    case _:
      raise InternalError('unhandled case in get_type_args: ' + repr(ty))

label_count = 0

def reset_label():
    pass

def generate_label():
    global label_count
    l = 'label_' + str(label_count)
    label_count = label_count + 1
    return l
  
def proof_use_advice(proof, formula, env):
    prefix = style.dark_green('Advice about using fact:') + '\n' \
        + '\t' + str(formula) + '\n\n'
    match formula:
      case Bool(loc, _, True):
        return prefix + '\tThe "true" fact is useless.\n'
      case Bool(loc, _, False):
        return prefix \
            + '\tUse this "false" fact to implicitly prove anything!\n'
      case And(loc, _, args):
        return prefix \
            + '\tUse this logical-and to implicitly prove any of its parts:\n' \
            + '\n'.join('\t\t' + str(arg) for arg in args)
      case Or(loc, _, args):
        reset_label()
        return prefix \
            + '\tUse this logical-or by proceeding with a "cases" statement:\n'\
            + '\t\tcases ' + str(proof) + '\n' \
            + '\n'.join(['\t\tcase ' + generate_label() + ' : ' + str(arg) \
                         + ' { ? }' for arg in args])
      case IfThen(loc, _, prem, conc):
        return prefix \
            + '\tApply this if-then formula to a proof of its premise:\n' \
            + '\t\t' + str(prem) + '\n' \
            + '\tto obtain a proof of its conclusion:\n' \
            + '\t\t' + str(conc) + '\n' \
            + '\tby using an apply-to statement:\n' \
            + '\t\tapply ' + str(proof) + ' to ?'
      case All(loc, _, var, (s, _), body):
        vars = [var]
        while s != 0:
          match body:
            case All(_, _, var2, (s, _), body):
              vars.append(var2)

        letters = []
        new_vars = {}
        i = 65
        type_param = False
        for (x,ty) in vars:
          if isinstance(ty, TypeType):
              type_param = True
          letters.append(chr(i))
          new_vars[x] = ResolvedVar(loc,ty, chr(i))
          i = i + 1
        plural = 's' if len(vars) > 1 else ''
        pronoun = 'them' if len(vars) > 1 else 'it'
        
        if type_param:
            how = ' between `<` and `>` like so:\n' \
                + '\t\t ' + str(proof) + '<' + ', '.join(letters) + '>' + '\n'
        else:
            how = ' in square-brackets like so:\n' \
                + '\t\t ' + str(proof) + '[' + ', '.join(letters) + ']' + '\n'
        
        return prefix \
            + '\tInstantiate this all formula with your choice' + plural \
            + ' for ' + ', '.join([base_name(x) for (x,ty) in vars]) + '\n' \
            + '\tby writing ' + pronoun + how \
            + '\tto obtain a proof of:\n' \
            + '\t\t' + str(body.substitute(new_vars))
      case Some(loc, _, vars, body):
        letters = []
        new_vars = {}
        i = 65
        for (x,ty) in vars:
            letters.append(chr(i))
            new_vars[x] = ResolvedVar(loc,ty, chr(i))
            i = i + 1
        new_body = body.substitute(new_vars)
        return prefix \
            + 'To use this "some" formula, proceed with:\n' \
            + '\tobtain ' + ', '.join(letters) + \
            ' where label: ' + str(new_body) + ' from ' + str(proof) +'\n' \
            + 'where ' + ', '.join(letters) \
            + (' are new names of your choice' if len(vars) > 1 \
               else ' is a new name of your choice' ) + ',\n' \
            + 'followed by a proof of the goal.'

      case Call(_, _, rator, [_, _]) if isinstance(rator, VarRef) and rator.get_name() == '=':
        return prefix \
            + '\tYou can use this equality in a replace statement:\n' \
            + '\t\treplace ' + str(proof) + '\n'
      case _:
        return 'Sorry, I have no advice for this kind of formula.'

def make_unique(name, env):
    if name in env:
        return make_unique(name + "'", env)
    else:
        return name

def is_recursive(name, typ):
    match typ:
      case OverloadedVar(_, _, rs):
        return name == rs[0]
      case TypeInst(_, ty, _):
        return is_recursive(name, ty)
      case _:
        return False

def update_all_head(r):
    match r:
      case All(loc2, tyof, var, (s, e), frm):
        if s == 0:  
          return All(loc2, tyof, var, (s, e-1), frm)
        else:
          return All(loc2, tyof, var, (s, e-1), update_all_head(frm))
      case _:
        return r

def gen_conjunct_advice(conjunct, arbs, ihs):
  match conjunct:
    case All(_, _, (n, _), _, b):
      return gen_conjunct_advice(b, arbs + [base_name(n)], ihs)
    case IfThen(_, _, _, b):
      return gen_conjunct_advice(b, arbs, ihs + [f"IH{len(ihs)}"])
    case Call(_, _, _, [arg]):
      withs = ""
      if arbs:
        withs = "with " + ", ".join(arbs) + ". "
      assumes = ""
      if ihs:
        assumes = "assume " + ", ".join(ihs) +" "
      return f"\t\tcase {withs}{arg} {assumes} {'{'}\n\t\t\t?\n{'\t\t}'}"
  pass

def gen_custom_induction_advice(conjuncts):
  return "\n".join([gen_conjunct_advice(c, [], []) for c in conjuncts])

def _custom_induction_expected_cases(conjuncts):
  return gen_custom_induction_advice(conjuncts).replace('\t\t', '\t')

def _custom_induction_case_hint(conjunct):
  return gen_conjunct_advice(conjunct, [], []).replace('\t\t', '\t')

def proof_advice(formula, env):
    prefix = style.dark_green('Advice:') + '\n'

    red_formula = formula.reduce(env)
    if formula != red_formula:
        prefix += '\tThis goal simplifies to\n\t\t' + str(red_formula) + '\n' \
            + '\tConsider using\n\t\tsimplify\n\n'
    
    match formula:
      case Bool(loc, _, True):
        return prefix + '\tYou can prove "true" with a period.\n'
      case Bool(loc, _, False):
        return prefix \
            + '\tProve "false" by proving a contradiction:\n' \
            + '\tif you prove both "P" and "not P", \n' \
            + '\tthen "contradict (recall not P), (recall P)" proves "false".\n'
      case And(loc, _, args):
        return prefix \
            + '\tProve this logical-and formula by proving each of its'\
            + ' parts,\n\tshown below, then combine the proofs with commas.\n' \
            + '\n'.join('\t\t' + str(arg) for arg in args)
      case Or(loc, _, args):
        return prefix \
            + '\tProve this logical-or formula by proving one of its parts:\n' \
            + '\n'.join('\t\t' + str(arg) for arg in args)
      case IfThen(loc, _, prem, conc):
        return prefix \
            + '\tProve this if-then formula with:\n' \
            + '\t\tassume label: ' + str(prem) + '\n' \
            + '\tfollowed by a proof of:\n' \
            + '\t\t' + str(conc)
      case All(loc, _, var, (s, _), body):
        pf = "arbitrary "
        cur = formula
        prev_s = s + 1 # This variable stops spillover into other alls

        while isinstance(cur, All) and cur.pos[0] >= 0 and cur.pos[0] < prev_s:
          pf += f"{base_name(cur.var[0])}:{cur.var[1]}{', ' if cur.pos[0] > 0 else ''}"
          prev_s = cur.pos[0]
          cur = cur.body

        arb_advice = prefix \
            + '\tProve this "all" formula with:\n' \
            + '\t\t' + pf + '\n' \
            + '\tfollowed by a proof of:\n' \
            + '\t\t' + str(cur)

        # NOTE: Maybe we shouldn't give induction advice for non recursively
        # defined unions. However right now we will because I haven't added
        # that check yet. Maybe even suggest a switch instead.
        
        var_x, var_ty = var
        match var_ty:
          # NOTE: These are the types that are handled in get_type_name, and
          # get_def_of_type_var
          case TypeInst() | Var() | OverloadedVar() | ResolvedVar():
            pass
          case _:
            return arb_advice # don't give induction advice for type variables

        # When foralls are generated, the def of type var is not in the environment?
        # Seems to be a problem with extensionality
        # I'm ok for now with just failing the match if this happens
        ty = None
        try:
          ty = env.get_def_of_type_var(get_type_name(var_ty))
        except Exception:
          pass

        match ty:
          case Union(_, name, _, alts):
            has_custom_ind = env.get_inductive(var_ty)

            if ty.visibility == 'opaque':
              binding = env.dict[name]
              if binding.location.filename != env.get_current_module() and not has_custom_ind:
                return arb_advice

            if len(alts) < 2:
              return arb_advice # Can't do induction if there's only one case
                
            ind_advice = '\n\n\tAlternatively, you can try induction with:\n' \
              +  '\t\tinduction ' + str(var_ty) + '\n'

            if has_custom_ind:
              # Do advice based on the theorem
              ind_advice += gen_custom_induction_advice(has_custom_ind["conjuncts"])
            else:
              # Do advice based on the alts of the union
              for alt in alts:
                match alt:
                  case Constructor(loc3, constr_name, param_types):
                    params = [make_unique(type_first_letter(ty)+str(i+1), env)\
                              for i,ty in enumerate(param_types)]
                    ind_advice += '\t\tcase ' + base_name(constr_name)
                    if len(param_types) > 0:
                      ind_advice += '(' + ', '.join(params) + ')'
                    num_recursive = sum([1 if is_recursive(name, ty) else 0 \
                                         for ty in param_types])
                    if num_recursive > 0:
                      rec_params =[(p,ty) for (p,ty) in zip(params,param_types)\
                                   if is_recursive(name, ty)]
                      ind_advice += ' assume '
                      ind_advice += ',\n\t\t\t'.join(['IH' + str(i+1) + ': ' \
                            + str(update_all_head(body.substitute({var_x: ResolvedVar(loc3, param_ty, param)}))) \
                            for i, (param,param_ty) in enumerate(rec_params)])

                    ind_advice += ' {\n\t\t  ?\n\t\t}\n'
                    
            return arb_advice + ind_advice
        
          case _:
            return arb_advice


      case Some(loc, _, vars, body):
        letters = []
        new_vars = {}
        i = 65
        for (x,ty) in vars:
            letters.append(chr(i))
            new_vars[x] = ResolvedVar(loc,ty, chr(i))
            i = i + 1
        return prefix \
            + '\tProve this "some" formula with:\n' \
            + '\t\tchoose ' + ', '.join(letters) + '\n' \
            + '\twhere you replace ' + ', '.join(letters) \
            + ' with your choice(s),\n' \
            + '\tthen prove:\n' \
            + '\t\t' + str(body.substitute(new_vars))
      case Call(_, _, rator, [_, _]) if isinstance(rator, VarRef) and rator.get_name() == '=':
        return prefix \
            + '\tTo prove this equality, one of these statements might help:\n'\
            + '\t\texpand\n' \
            + '\t\treplace\n' \
            + '\t\tequations\n'
      case TLet(_, _, var, _, body):
        return proof_advice(body, env)
      case _:
        for (name, b) in env.dict.items():
            if isinstance(b, ProofBinding) and b.local and b.formula == formula:
                msg = '\nYou can conclude the proof with:\n'
                if base_name(name) == '_':
                    msg += '\trecall ' + str(formula)
                else:
                    msg += '\tconclude ' + str(formula) \
                        + ' by ' + base_name(name)                
                return msg

        return '\n'

def givens_str(env):
    env_str = env.proofs_str()
    if len(env_str) > 0:
        givens = '\n' + style.orange('Givens:') + '\n' + env_str
    else:
        givens = ''
    return givens

def pred_to_equality(meta, pred):
    match pred:
      case IfThen(_, _, p, Bool(_, _, False)):
          return Call(meta, None, ResolvedVar(meta, None, '='),
                      [p , Bool(meta, None, False)])
      case _:
          return Call(meta, None, ResolvedVar(meta, None, '='),
                      [pred , Bool(meta, None, True)])

def _check_rule_induction(proof, goal, env):
  """See `_check_rule_inversion`: same shape, applies the
  `<pred>_rule_induction` theorem instead of the inversion theorem."""
  _check_rule_induction_or_inversion(proof, goal, env, is_inversion=False)

def _check_rule_inversion(proof, goal, env):
  """Desugar `rule inversion <pred> case <r1> { ... } ...` to
     `apply <pred>_rule_inversion[<motive>] to (<case_1>, ..., <case_k>)`.
  Same goal shape as `rule induction`, but each case proves the rule's
  *non*-augmented conjunct (premises in their original form, no
  motive's induction hypothesis paired with recursive premises)."""
  _check_rule_induction_or_inversion(proof, goal, env, is_inversion=True)

def _check_rule_induction_or_inversion(proof, goal, env, is_inversion):
  loc = proof.location
  pred_name_in = proof.hyp_name  # the predicate name after the keyword
  ri_cases = proof.cases
  keyword_phrase = 'rule inversion' if is_inversion else 'rule induction'

  # Strip outer `all` quantifiers and the `if pred(xs) then ...` from
  # the goal.
  binders = []
  rest = goal
  while isinstance(rest, All):
    binders.append(rest.var)
    rest = rest.body
  if not isinstance(rest, IfThen):
    user_error(loc, keyword_phrase + " expects a goal of the form "
          "'all xs. if <pred>(xs) then Q(xs)', got '" + str(goal) + "'")
  pred_call = rest.premise
  q_formula = rest.conclusion
  if not isinstance(pred_call, Call):
    user_error(loc, keyword_phrase + " expects the goal's premise to be a call "
          "to the predicate, got '" + str(pred_call) + "'")

  rator = pred_call.rator
  rator_name = None
  if isinstance(rator, VarRef):
    rator_name = rator.get_name()
  if rator_name != pred_name_in:
    user_error(loc, keyword_phrase + " over '" + base_name(pred_name_in)
          + "' but the goal's premise is a call to '"
          + str(rator) + "'")
  pred_decl = get_predicate_decl(rator_name)
  if pred_decl is None:
    user_error(loc, keyword_phrase + ": '" + base_name(rator_name)
          + "' is not a predicate or relation declared with the "
          "'predicate' or 'relation' keyword")

  # The args of the goal's `pred(xs)` should be the binders' Vars, in
  # order. They give us the motive parameters.
  args = pred_call.args
  arg_names = []
  for a in args:
    if not isinstance(a, VarRef):
      user_error(loc, keyword_phrase + ": predicate arguments in the goal "
            "must be plain variables (got '" + str(a) + "')")
    arg_names.append(a.get_name())
  if len(set(arg_names)) != len(arg_names):
    user_error(loc, keyword_phrase + ": duplicate predicate argument vars in "
          "the goal (motive inference does not yet handle this)")

  arity = len(args)
  param_types = []
  if isinstance(pred_decl.signature, FunctionType):
    param_types = pred_decl.signature.param_types

  # Match user case names to predicate rule names.
  rule_unique_names = [r.name for r in pred_decl.rules]
  user_cases_by_rule = {}
  for c in ri_cases:
    if c.rule_name not in rule_unique_names:
      base = base_name(c.rule_name)
      user_error(c.location,
            keyword_phrase + ": '" + base
            + "' is not a rule of predicate '"
            + base_name(rator_name) + "'")
    if c.rule_name in user_cases_by_rule:
      user_error(c.location,
            keyword_phrase + ": duplicate case for rule '"
            + base_name(c.rule_name) + "'")
    user_cases_by_rule[c.rule_name] = c
  missing = [base_name(rn) for rn in rule_unique_names
             if rn not in user_cases_by_rule]
  if missing:
    user_error(loc, keyword_phrase + ": missing case"
          + ('s' if len(missing) > 1 else '')
          + " for rule" + ('s' if len(missing) > 1 else '') + ": "
          + ', '.join(missing))

  # Build the motive as a lambda whose binders match the goal's outer
  # `all` binders (renaming if needed for cleanliness). The body is the
  # goal's `Q(xs)` with arg-vars left intact (since they're the lambda's
  # own binders).
  motive = Lambda(loc, None,
                  [(arg_names[i], param_types[i].copy())
                   for i in range(arity)],
                  q_formula.copy())

  thm_name = pred_decl.rule_inversion_name if is_inversion \
             else pred_decl.rule_induction_name
  thm_proof = PVar(loc, thm_name)
  with_motive = AllElim(loc, thm_proof, motive, (0, 1))
  case_proofs = [user_cases_by_rule[rn].body
                 for rn in rule_unique_names]
  if len(case_proofs) == 1:
    rules_proof = case_proofs[0]
  else:
    rules_proof = PTuple(loc, case_proofs)
  desugared = ModusPonens(loc, with_motive, rules_proof)

  _try_check_proof_of(desugared, goal, env)

def _check_proof_of_hole(proof, formula, env):
  loc = proof.location
  new_formula = check_formula(remove_mark(formula), env)
  # Uncommented by i ran into a proof where I had to prove
  # (A = A or A = B) which should have just reduced to A = A
  # but it didn't.
  # new_formula = new_formula.reduce(env)
  target = get_target_hole_location()
  if target is not None and (loc.line, loc.column) != target:
    return
  add_incomplete(loc, style.bold_red('incomplete proof') + '\n' \
                   + style.orange('Goal:') + '\n\t' + str(new_formula) + '\n'\
                   + proof_advice(new_formula, env) \
                   + givens_str(env),
                   formula=new_formula, env=env)

def _check_proof_of_sorry(proof, formula, env):
  warning(proof.location, 'unfinished proof')

def _check_proof_of_reflexive(proof, formula, env):
  match formula:
    case Call(_, _, rator, [lhs, rhs]) if isinstance(rator, VarRef) and rator.get_name() == '=':
      lhsNF = lhs.reduce(env)
      rhsNF = rhs.reduce(env)
      if lhsNF != rhsNF:
        (small_lhs, small_rhs) = isolate_difference(lhsNF, rhsNF)
        msg = 'error in proof by reflexive:\n'
        if small_lhs == lhsNF:
          msg = msg + str(lhsNF) + ' ≠ ' + str(rhsNF)
        else:
          msg = msg + str(small_lhs) + ' ≠ ' + str(small_rhs) + '\n' \
            + 'therefore\n' + str(lhsNF) + ' ≠ ' + str(rhsNF)
        user_error(proof.location, msg + '\n' + givens_str(env))
    case _:
      add_diagnostic(proof.location,
                     'reflexive proves an equality, not\n\t' \
                     + str(formula) \
                     + givens_str(env))

def _check_proof_of_symmetric(proof, formula, env):
  loc = proof.location
  (a,b) = split_equation(loc, formula, env)
  flip_formula = mkEqual(loc, b, a)
  _try_check_proof_of(proof.body, flip_formula, env)

def _check_proof_of_transitive(proof, formula, env):
  loc = proof.location
  (a1,c) = split_equation(loc, formula, env)

  eq1 = check_proof(proof.first, env)
  (a2,b) = split_equation(loc, eq1, env)

  _try_check_proof_of(proof.second, mkEqual(loc, b, c), env)

  a1r = a1.reduce(env)
  a2r = a2.reduce(env)
  if remove_mark(a1r) != remove_mark(a2r):
    add_diagnostic(loc, 'for transitive, from proofs of\n'
          + '\t' + str(eq1) + '\n'
          + 'and\n'
          + '\t' + str(b) + ' = ' + str(c) + '\n'
          + 'the transitive rule concludes\n\t' + str(a2) + ' = ' + str(c) + '\n'
          + 'but that does not match the goal\n\t' + str(formula) + '\n'
          + givens_str(env))

def _check_proof_of_extensionality(proof, formula, env):
  loc = proof.location
  (lhs,rhs) = split_equation(loc, formula, env)
  match lhs.typeof:
    case FunctionType(_, [], typs, _):
      names = [generate_proof_name('x') for ty in typs]
      args = [ResolvedVar(loc, None, x) for x in names]
      call_lhs = Call(loc, None, lhs, args)
      call_rhs = Call(loc, None, rhs, args)
      formula = mkEqual(loc, call_lhs, call_rhs)
      for i, v in enumerate(reversed(list(zip(names, typs)))):
        formula = All(loc, None, v, (i, len(names)), formula)
      _try_check_proof_of(proof.body, formula, env)
    case FunctionType(_, ty_params, _, _):
      add_diagnostic(loc, 'extensionality expects function without any type parameters, not ' + str(len(ty_params))
            + givens_str(env))
    case _:
      add_diagnostic(loc, 'extensionality expects a function, not ' + str(lhs.typeof)
            + givens_str(env))

def _check_proof_of_evaluate_goal(proof, formula, env):
  loc = proof.location
  set_reduce_all(True)
  set_dont_reduce_opaque(True)
  red_formula = remove_mark(formula).reduce(env)
  set_reduce_all(False)
  set_dont_reduce_opaque(False)
  if red_formula != Bool(loc, None, True):
    add_diagnostic(loc, 'the goal did not evaluate to `true`, but instead:\n\t' \
          + str(red_formula)
          + givens_str(env))

def _check_proof_of_rewrite_goal(proof, formula, env):
  loc = proof.location
  equations = [check_proof(proof, env) for proof in proof.equations]
  eqns = [equation.reduce(env) for equation in equations]
  new_formula = formula.reduce(env)
  new_formula = apply_rewrites(loc, new_formula, eqns, env,
                               display_formula=formula)
  _try_check_proof_of(proof.body, new_formula, env)

def _check_proof_of_simplify_goal(proof, formula, env):
  loc = proof.location
  preds = [check_proof(proof, env) for proof in proof.givens]
  equations = [pred_to_equality(loc, p) for p in preds]
  eqns = [equation.reduce(env) for equation in equations]
  new_formula = apply_rewrites(loc, formula, eqns, env)
  new_formula = new_formula.reduce(env)
  _try_check_proof_of(proof.body, new_formula, env)

def _check_proof_of_apply_defs_goal(proof, formula, env):
  loc = proof.location
  new_formula = expand_definitions(loc, formula, proof.definitions, env)
  red_formula = new_formula.reduce(env)
  try:
    _try_check_proof_of(proof.body, red_formula, env)
  except UserError as e:
    hint = expand_residual_hint(red_formula, proof.definitions, env)
    if hint:
      raise wrap_user_error(e, hint) from e
    raise

def _check_proof_of_all_intro(proof, formula, env):
  loc = proof.location
  var = proof.var
  body = proof.body
  x, ty = var
  check_type(ty, env)

  if isinstance(formula, TLet):
    formula = formula.reduceLets(env)

  match formula:
    case All(_, _, var2, (s, _), formula2):
      _, ty2 = var2
      if ty != ty2:
        add_diagnostic(loc, "arbitrary expects " + base_name(x)
              + " to have type\n\t" + str(ty2)
              + "\nbut got type\n\t" + str(ty))
        return
      sub = {}
      sub[ var2[0] ] = OverloadedVar(loc, var[1], [ var[0] ])

      frm2 = formula2.substitute(sub)

      if s != 0:
        frm2 = update_all_head(frm2)

      body_env = env.declare_term_vars(loc, [var])
      _try_check_proof_of(body, frm2, body_env)
    case _:
      add_diagnostic(loc, 'arbitrary is proof of an all formula, not\n' \
            + str(formula)
            + givens_str(env))

def _check_proof_of_some_intro(proof, formula, env):
  loc = proof.location
  # room for improvement, if var has type annotation, could type_check the witness
  witnesses = [type_synth_term(trm, env, None, []) for trm in proof.witnesses]

  if isinstance(formula, TLet):
    formula = formula.reduceLets(env)

  match formula:
    case Some(_, _, vars, formula2):
      sub = {var[0]: trm for (var,trm) in zip(vars, witnesses) }
      body_frm = formula2.substitute(sub)
      _try_check_proof_of(proof.body, body_frm, env)
    case _:
      add_diagnostic(loc, "choose expects the goal to start with 'some', not " + str(formula)
            + givens_str(env))

def _check_proof_of_some_elim(proof, formula, env):
  loc = proof.location
  someFormula = check_proof(proof.some, env)

  if isinstance(someFormula, TLet):
    someFormula = someFormula.reduceLets(env)

  match someFormula:
    case Some(loc2, _, vars, formula2):
      sub = {var[0]: ResolvedVar(loc2, None, x) for (var,x) in zip(vars,proof.witnesses)}
      witnessFormula = formula2.substitute(sub)

      witnesses_types = [(x,var[1]) for (var,x) in zip(vars,proof.witnesses)]
      body_env = env.declare_term_vars(loc, witnesses_types)
      if proof.prop:
        prop = check_formula(proof.prop, body_env)
        check_implies(loc, witnessFormula.reduce(env), prop.reduce(body_env))
      else:
        prop = witnessFormula
      body_env = body_env.declare_local_proof_var(loc, proof.label, prop)
      _try_check_proof_of(proof.body, formula, body_env)
    case _:
      add_diagnostic(loc, "obtain expects 'from' to be a proof of a 'some' formula, not " + str(someFormula)
            + givens_str(env))

def _check_proof_of_imp_intro(proof, formula, env):
  loc = proof.location

  if proof.premise is None:
    if isinstance(formula, TLet):
      formula = formula.reduceLets(env)

    match formula:
      case IfThen(_, _, prem, conc):
        body_env = env.declare_local_proof_var(loc, proof.label, prem)
        _try_check_proof_of(proof.body, conc, body_env)
      case _:
        add_diagnostic(proof.location, 'expected proof of ' + str(formula) + \
              '\n\tnot a proof of if-then: ' + str(proof)
              + givens_str(env))
    return

  new_prem1 = check_formula(proof.premise, env)
  match formula:
    case IfThen(_, _, prem2, conc):
      prem1_red = new_prem1.reduce(env)
      prem2_red = prem2.reduce(env)
      if prem1_red != prem2_red:
        (small1, small2) = isolate_difference(prem1_red, prem2_red)
        msg = str(prem1_red) + ' ≠ ' + str(prem2_red) + '\n' \
            + 'because\n' + str(small1) + ' ≠ ' + str(small2)
        add_diagnostic(loc, 'mismatch in premise:\n' + msg
            + givens_str(env))
      body_env = env.declare_local_proof_var(loc, proof.label, new_prem1)
      _try_check_proof_of(proof.body, conc, body_env)
    case _:
      add_diagnostic(proof.location, 'the assume statement is for if-then formula, not ' + str(formula)
            + givens_str(env))

def _check_proof_of_tlet_new(proof, formula, env):
  loc = proof.location
  new_rhs = type_synth_term(proof.rhs, env, None, [])
  body_env = env.define_term_var(loc, proof.var, new_rhs.typeof, new_rhs)
  equation = mkEqual(loc, new_rhs, ResolvedVar(loc, None, proof.var)).reduce(env)
  red_formula = formula.reduce(env)
  if get_verbose():
      print('define ' + str(proof.var) + '\n\trewrite with ' + str(equation) + '\n\tin ' \
            + str(red_formula))
  frm = rewrite(loc, red_formula, equation, env)
  new_body_env = Env({k: ProofBinding(b.location, \
                                      rewrite(loc, b.formula, equation, env), \
                                      b.local, module=env.get_current_module()) \
                      if isinstance(b, ProofBinding) else b \
                       for (k,b) in body_env.dict.items()})
  _try_check_proof_of(proof.body, frm, new_body_env)

def _check_proof_of_let(proof, formula, env):
  loc = proof.location
  new_frm = check_formula(proof.proved, env)
  match new_frm:
    case Hole(_, _):
      proved_formula = check_proof(proof.because, env)
      warning(loc, "\nhave " + base_name(proof.label) + ':\n\t' + str(proved_formula))
      body_env = env.declare_local_proof_var(loc, proof.label, proved_formula)
    case _:
      _try_check_proof_of(proof.because, new_frm, env)
      body_env = env.declare_local_proof_var(loc, proof.label, remove_mark(new_frm))
  _try_check_proof_of(proof.body, formula, body_env)

def _check_proof_of_annot(proof, formula, env):
  loc = proof.location
  new_claim = check_formula(proof.claim, env)
  match new_claim:
    case Hole(_, _):
      _try_check_proof_of(proof.body, formula, env)
      add_diagnostic(loc, '\nneed to show:\n\t' + str(formula)
            + givens_str(env))
    case _:
      claim_red = new_claim.reduce(env)
      formula_red = formula.reduce(env)
      check_implies(loc, remove_mark(claim_red).reduce(env),
                    remove_mark(formula_red).reduce(env))
      _try_check_proof_of(proof.body, claim_red, env)

_CHECK_PROOF_OF_HANDLERS = {
  PHole: _check_proof_of_hole,
  PSorry: _check_proof_of_sorry,
  PReflexive: _check_proof_of_reflexive,
  PSymmetric: _check_proof_of_symmetric,
  PTransitive: _check_proof_of_transitive,
  PExtensionality: _check_proof_of_extensionality,
  EvaluateGoal: _check_proof_of_evaluate_goal,
  RewriteGoal: _check_proof_of_rewrite_goal,
  SimplifyGoal: _check_proof_of_simplify_goal,
  ApplyDefsGoal: _check_proof_of_apply_defs_goal,
  AllIntro: _check_proof_of_all_intro,
  SomeIntro: _check_proof_of_some_intro,
  SomeElim: _check_proof_of_some_elim,
  ImpIntro: _check_proof_of_imp_intro,
  PTLetNew: _check_proof_of_tlet_new,
  PLet: _check_proof_of_let,
  PAnnot: _check_proof_of_annot,
}

def check_proof_of(proof, formula, env):
  if get_verbose():
    print('check_proof_of: ' + str(formula) + '?')
    print('\t' + str(proof))
  handler = _CHECK_PROOF_OF_HANDLERS.get(type(proof))
  if handler is not None:
    return handler(proof, formula, env)
  match proof:
    #  goal is P
    #  suffices Q by r        r proves (if Q then P)
    #  goal is Q
    case Suffices(loc, claim, reason, rest):
      evaluate = False

      match reason:
        case EvaluateGoal(loc2):
           evaluate = True

      if evaluate:
        new_claim = type_check_term(claim, BoolType(loc), env, None, [])
        set_reduce_all(True)
        set_dont_reduce_opaque(True)
        new_formula = formula.reduce(env)
        red_claim = new_claim.reduce(env)
        set_reduce_all(False)
        set_dont_reduce_opaque(False)

        match red_claim:
          case Omitted(loc2, _):
            _try_check_proof_of(rest, new_formula, env)
          case Hole(loc2, _):
            newer_formula = check_formula(new_formula, env)
            warning(loc, '\nsuffices to prove:\n\t' + str(newer_formula))
            check_proof_of(rest, newer_formula, env)
          case _:
            try:
              check_implies(loc, red_claim, new_formula)
            except UserError as e:
              raise wrap_user_error(e, '\n' + style.orange('Givens:') + '\n' + env.proofs_str()) from e
            _try_check_proof_of(rest, new_claim, env)
      else:
        new_claim = type_check_term(claim, BoolType(loc), env, None, [])
        claim_red = new_claim.reduce(env)

        match claim_red:
          case Hole(loc2, _):
            proved_formula = check_proof(reason, env)
            match proved_formula:
              case IfThen(_, _, prem, conc):
                check_implies(loc, conc, formula)
                warning(loc2, '\nsuffices to prove:\n\t' + str(prem))
                _try_check_proof_of(rest, prem, env)
              case _:
                add_diagnostic(loc, 'expected a proof of an "if"-"then" formula, not ' + str(proved_formula)
                      + givens_str(env))
          case Omitted(loc2, _):
            proved_formula = check_proof(reason, env)
            match proved_formula:
              case IfThen(_, _, prem, conc):
                check_implies(loc, conc, formula)
                _try_check_proof_of(rest, prem, env)
              case _:
                add_diagnostic(loc, 'expected a proof of an "if"-"then" formula, not ' + str(proved_formula)
                      + givens_str(env))
          case _:
            imp = IfThen(loc, BoolType(loc), claim_red, formula).reduce(env)
            _try_check_proof_of(reason, imp, env)
            _try_check_proof_of(rest, claim_red, env)

    case PTuple(loc, pfs):
      try:
        with speculative_probe():
          red_formula = formula.reduce(env)
          match red_formula:
            case And(loc2, _, frms):
              for (frm,pf) in zip(frms, pfs):
                check_proof_of(pf, frm, env)
              if len(pfs) < len(frms):
                incomplete_error(loc, 'expected ' + str(len(frms)) + ' proofs but only got '\
                                 + str(len(pfs)))
            case _:
              user_error(loc, 'comma proves logical-and, not ' + str(red_formula))
      except IncompleteProof as ex:
        raise ex
      except UserError as ex1:
        try:
          with speculative_probe():
            form = check_proof(proof, env)
            form_red = form.reduce(env)
            formula_red = formula.reduce(env)
            check_implies(proof.location, form_red, remove_mark(formula_red))
        except UserError as ex2:
          add_diagnostic(loc, 'failed to prove: ' + str(formula) + '\n' \
                + '\tfirst tried each subproof in goal-directed mode, but:\n' \
                + str(ex1) + '\n' \
                + '\tthen tried synthesis mode, but:\n'\
                + str(ex2)
                + givens_str(env))
            
    case Cases(loc, subject, cases):
      sub_frm = check_proof(subject, env)

      # sub_red = sub_frm.reduce(env)
      sub_red = sub_frm
      if isinstance(sub_frm, TLet):
        sub_red = sub_frm.reduceLets(env)

      match sub_red:
        case Or(_, _, frms):
          if len(cases) < len(frms):
              add_diagnostic(loc, "expected " + str(len(frms)) + " cases, not " + str(len(cases))
                    + givens_str(env))
          for (frm, (label,frm2,the_case)) in zip(frms, cases):
            if frm2:
                new_frm2 = check_formula(frm2, env)
            if frm2 and (frm != new_frm2): # was frm != red_frm2
              add_diagnostic(loc, 'case ' + str(new_frm2) + '\ndoes not match alternative in goal: \n' + str(frm)
                    + givens_str(env))
            body_env = env.declare_local_proof_var(loc, label, frm)
            _try_check_proof_of(the_case, formula, body_env)
        case _:
          add_diagnostic(proof.location, "expected 'or', not " + str(sub_red)
                + givens_str(env))
          
    case RuleInduction(loc, _, _):
      _check_rule_induction(proof, formula, env)

    case RuleInversion(loc, _, _):
      _check_rule_inversion(proof, formula, env)

    case Induction(loc, typ, cases):
      check_type(typ, env)

      if isinstance(formula, TLet):
        formula = formula.reduceLets(env)
      match formula:
        case All(_, _, (_,ty), _, frm):
          if typ != ty:
            add_diagnostic(loc, "type of induction: " + str(typ) \
                  + "\ndoes not match the all-formula's type: " + str(ty)
                  + givens_str(env))
        case _:
          add_diagnostic(loc, 'induction expected an all-formula, not ' + str(formula)
                + givens_str(env))
      
      # TODO: Allow for specification of what type to use
      custom_ind = env.get_inductive(typ)

      if custom_ind:
        if get_verbose():
          print(f"Using custom induction for type {typ}")
        conjuncts = custom_ind["conjuncts"]
        fun_name = custom_ind["fun"]
        fun_ty = custom_ind['fun_ty']
        type_vars = custom_ind['tys'] 
        type_subst = {}

        types_elimmed = custom_ind["thm"]

        if len(cases) != len(conjuncts):
          plural = '' if len(conjuncts) == 1 else 's'
          add_diagnostic(loc, 'expected ' + str(len(conjuncts)) \
                + ' case' + plural + ' for custom induction on ' + str(typ) \
                + ', but have ' + str(len(cases)) \
                + '\nExpected cases:\n' + _custom_induction_expected_cases(conjuncts) \
                + givens_str(env))
          return

        if type_vars != []:
          match typ:
            case TypeInst(loc, _, params):
              assert len(type_vars) == len(params) # Enforced by match_induction_fun
              for k, v in zip(type_vars, params):
                type_subst[k] = v
                types_elimmed = AllElimTypes(loc, types_elimmed, v, (0, 1))
            case _:
              internal_error("Expected a type inst")

        pfun = Lambda(loc, fun_ty, [formula.var], formula.body)
        fun_var = ResolvedVar(loc, fun_ty, fun_name)

        annots = []

        for (conjunct, case) in zip(conjuncts, cases):
          conjunct = conjunct.substitute(type_subst)
          new_body = generate_conjunct_body(loc, conjunct, case, fun_var, type_subst, env)
          new_body = ApplyDefsGoal(loc, [fun_var], new_body)

          annot = PAnnot(loc, conjunct, new_body)
          annots.append(annot)
        
        new_pf = PTLetNew(loc, fun_name, pfun, 
                          ApplyDefsFact(loc, [fun_var],
                                        ModusPonens(loc, 
                                                    AllElim(loc, types_elimmed, fun_var,  (0, 1)),
                                                    PTuple(loc, annots))))
        
        if get_verbose():
          print("Generated custom induction:")
          print(new_pf)
        
        _try_check_proof_of(new_pf, formula, env)
      else:
        match env.get_def_of_type_var(get_type_name(typ)):
          case Union(loc2, name, typarams, alts):
            if len(cases) != len(alts):
              add_diagnostic(loc, 'expected ' + str(len(alts)) + ' cases for induction' \
                    + ', but only have ' + str(len(cases))
                    + givens_str(env))
            cases_present = {}
            for (constr,indcase) in zip(alts, cases):
              check_pattern(indcase.pattern, typ, env, cases_present)
              if get_verbose():
                  print('\nCase ' + str(indcase.pattern))
              if indcase.pattern.constructor.name != constr.name:
                add_diagnostic(indcase.location, "expected a case for " + str(base_name(constr.name)) \
                      + " not " + str(base_name(indcase.pattern.constructor.name))
                      + givens_str(env))
              if len(indcase.pattern.parameters) != len(constr.parameters):
                add_diagnostic(indcase.location, "expected " + str(len(constr.parameters)) \
                      + " arguments to " + base_name(constr.name) \
                      + " not " + str(len(indcase.pattern.parameters))
                      + givens_str(env))
              induction_hypotheses = [instantiate(loc, formula,
                                                  ResolvedVar(loc,None, param))
                                      for (param, ty) in 
                                      zip(indcase.pattern.parameters,
                                          constr.parameters)
                                      if is_recursive(name, ty)]
              body_env = env

              if len(typarams) > 0:
                sub = { T: ty for (T,ty) in zip(typarams, typ.arg_types)}
                parameter_types = [p.substitute(sub) for p in constr.parameters]
              else:
                parameter_types = constr.parameters
              body_env = body_env.declare_term_vars(loc,
                                                    zip(indcase.pattern.parameters,
                                                        parameter_types),
                                                    True)

              trm = pattern_to_term(indcase.pattern)
              new_trm = type_check_term(trm, typ, body_env, None, [])
              if isinstance(new_trm, TermInst):
                  new_trm.inferred = False
              pre_goal = instantiate(loc, formula, new_trm)
              goal = check_formula(pre_goal, body_env)

              # fill the rest of the given induction_hypotheses with _ labels
              for i in range(len(indcase.induction_hypotheses), len(induction_hypotheses)):
                indcase.induction_hypotheses.append((generate_proof_name('_'), None))

              for ((x,frm1),frm2) in zip(indcase.induction_hypotheses, induction_hypotheses):
                if frm1 != None:
                  new_frm1 = check_formula(frm1, body_env)
                  if new_frm1 != frm2:
                    (small_frm1,small_frm2) = isolate_difference(new_frm1, frm2)
                    msg = 'incorrect induction hypothesis, expected\n' \
                        + str(frm2) + '\nbut got\n' + str(new_frm1) \
                        + '\nin particular\n' + str(small_frm1) + '\n≠\n' + str(small_frm2) 
                    add_diagnostic(frm1.location, msg
                          + givens_str(body_env))
                body_env = body_env.declare_local_proof_var(loc, x, frm2)

              _try_check_proof_of(indcase.body, goal, body_env)
          case blah:
            add_diagnostic(loc, "induction expected name of union, not " + str(typ)
                  + '\nwhich resolves to\n' + str(blah) + '\nin ' + str(env))

    case SwitchProof(loc, subject, cases):
      new_subject = type_synth_term(subject, env, None, [])
      ty = new_subject.typeof
      match ty:
        case BoolType(loc2):
          # check exhaustiveness
          has_true_case = False
          has_false_case = False
          for scase in cases:
            match scase.pattern:
              case PatternBool(_, True):
                has_true_case = True
              case PatternBool(_, False):
                has_false_case = True
              case _:
                internal_error(loc, 'unhandled case in switch proof')
          if not has_true_case:
            add_diagnostic(loc, 'missing case for true'
                + givens_str(env))
          if not has_false_case:
            add_diagnostic(loc, 'missing case for false'
                + givens_str(env))

          # check each case
          for scase in cases:
            if not isinstance(scase.pattern, PatternBool):
              add_diagnostic(scase.location, "expected pattern 'true' or 'false' in switch on bool"
                    + givens_str(env))
              
            subject_case = Bool(scase.location, BoolType(scase.location), True) if scase.pattern.value \
                           else Bool(scase.location, BoolType(scase.location), False)
            equation = mkEqual(scase.location, new_subject, subject_case)
            predicate = new_subject if scase.pattern.value \
                                    else IfThen(loc, None, new_subject, Bool(loc, None, False))
            
            body_env = env

            if len(scase.assumptions) == 0:
                  scase.assumptions.append((generate_proof_name('_'), None))

            assumptions = [(label, check_formula(asm, body_env) if asm else None) for (label,asm) in scase.assumptions]
            if len(assumptions) == 1:
              if assumptions[0][1] != None and assumptions[0][1] != predicate:
                (small_case_asm, small_eqn) = isolate_difference(assumptions[0][1], predicate)
                msg = 'expected assumption\n' + str(predicate) \
                    + '\nnot\n' + str(assumptions[0][1]) \
                    + '\nbecause\n\t' + str(small_case_asm) + ' ≠ ' + str(small_eqn)
                add_diagnostic(scase.location, msg
                      + givens_str(env))
              body_env = body_env.declare_local_proof_var(loc, assumptions[0][0], predicate)

            if len(assumptions) > 1:
              add_diagnostic(scase.location, 'only one assumption is allowed in a switch case'
                    + givens_str(env))
            frm = rewrite(loc, formula.reduce(env), equation.reduce(env), env)
            new_frm = frm.reduce(env)
            _try_check_proof_of(scase.body, new_frm, body_env)
        case TypeType(_):
          # As far as I know, it is not possible to switch on a type
          add_diagnostic(loc, "In 'switch' expected a term, got " + str(new_subject)
                + givens_str(env))
        case _:
          tname = get_type_name(ty)
          match env.get_def_of_type_var(tname):
            case Union(loc2, name, typarams, alts):
              if len(cases) != len(alts):
                add_diagnostic(loc, 'expected ' + str(len(alts)) + ' cases in switch, but only have ' + str(len(cases))
                      + givens_str(env))
              cases_present = {}
              for (constr,scase) in zip(alts, cases):
                check_pattern(scase.pattern, ty, env, cases_present)
                if scase.pattern.constructor.name != constr.name:
                  add_diagnostic(scase.location, "expected a case for " + str(constr) \
                        + " not " + str(scase.pattern.constructor)
                        + givens_str(env))
                if len(scase.pattern.parameters) != len(constr.parameters):
                  add_diagnostic(scase.location, "expected " + str(len(constr.parameters)) \
                        + " arguments to " + base_name(constr.name) \
                        + " not " + str(len(scase.pattern.parameters))
                        + givens_str(env))
                subject_case = pattern_to_term(scase.pattern)
                body_env = env

                tyargs = get_type_args(ty)
                sub = {T:ty for (T,ty) in zip(typarams, tyargs)}
                constr_params = [ty.substitute(sub) for ty in constr.parameters]
                body_env = body_env.declare_term_vars(loc, zip(scase.pattern.parameters,
                                                               constr_params))
                
                new_subject_case = type_check_term(subject_case, ty, body_env, None, [])
                if isinstance(new_subject_case, TermInst):
                    new_subject_case.inferred = False

                if len(scase.assumptions) == 0:
                  scase.assumptions.append((generate_proof_name('_'), None))
                  
                assumptions = [(label,check_formula(asm, body_env) if asm else None) for (label,asm) in scase.assumptions]
                if len(assumptions) == 1:
                  assumption = mkEqual(scase.location, new_subject, subject_case)
                  new_assumption = type_synth_term(assumption, body_env, None, [])
                  if assumptions[0][1] != None:
                      case_assumption = type_synth_term(assumptions[0][1], body_env, None, [])
                      if case_assumption != new_assumption:
                          add_diagnostic(scase.location, 'in case, expected assume of\n' + str(new_assumption) \
                                + '\nnot\n' + str(case_assumption)
                                + givens_str(body_env))
                  body_env = body_env.declare_local_proof_var(loc, assumptions[0][0], new_assumption)
                if len(assumptions) > 1:
                  add_diagnostic(scase.location, 'only one assumption is allowed in a switch case'
                        + givens_str(body_env))

                if isinstance(new_subject, VarRef):
                  frm = formula.substitute({new_subject.name: new_subject_case})
                else:
                  frm = formula
                red_frm = frm.reduce(body_env)
                _try_check_proof_of(scase.body, red_frm, body_env)
            case _:
              add_diagnostic(loc, "switch expected union type or bool, not " + str(ty)
                    + givens_str(env))
          
    case _:
      try:
        form = check_proof(proof, env)
        form_red = form.reduce(env)
        formula_red = remove_mark(formula).reduce(env)
        check_implies(proof.location, form_red, formula_red)
      except IncompleteProof as e:
        raise e
      except UserError as e:
        # It could be that form is never reduced, such as in a PHelpUse
        # In that case, we don't give 'replace' advice
        replace_advice = ''
        try:
          if is_equation(form_red):
            replace_advice = '\nDid you mean `replace ' + str(proof) + '`?'
        finally:
          raise wrap_user_error(e, replace_advice) from e


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


def expand_residual_hint(residual, defs, env):
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


def expand_definitions(loc, formula, defs, env):
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

def apply_rewrites(loc, formula, eqns, env, *, display_formula=None):
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

    
def type_check_call_funty(loc, new_rator, args, env, recfun, subterms, ret_ty,
                          call, typarams, param_types, return_type):
  is_assoc = is_associative(loc, rator_name(new_rator), return_type, env)
  if get_verbose():
      print('is_assoc? ' + rator_name(new_rator) + ' : ' + str(return_type) + ' = ' + str(is_assoc))
  if (is_assoc and len(args) < len(param_types)) \
      or ((not is_assoc) and len(args) != len(param_types)):
    user_error(loc, 'incorrect number of arguments in call:\n\t' + str(call) \
          + '\n\texpected ' + str(len(param_types)) \
          + ' arguments, not ' + str(len(args)))
  # We force associative operators to have the same param type
  if is_assoc:
    param_types = [param_types[0]] * len(args)

  if len(typarams) == 0:
    new_args = []
    for (param_type, arg) in zip(param_types, args):
      new_args.append(type_check_term(arg, param_type, env, recfun, subterms))
    if ret_ty != None and ret_ty != return_type:
      user_error(loc, 'expected ' + str(ret_ty) \
            + ' but the call returns ' + str(return_type))
    return Call(loc, return_type, new_rator, new_args)
  else:
    #print('type check call to generic: ' + str(call))
    matching = {}
    # If there is an expected return type, match that first.
    type_params = type_names(loc, typarams)
    if ret_ty:
      try:
          type_match(loc, type_params, return_type, ret_ty, matching)
      except MatchFailed:
        new_msg = 'expected type ' + str(ret_ty) + '\n' \
            + '\tbut the call ' + str(call) + '\n' \
            + '\thas return type ' + str(return_type) + '\n\n' \
            + '\tinferred type arguments: ' \
            + ', '.join([base_name(x) + ' := ' + str(ty) \
                         for (x,ty) in matching.items()])
        user_error(call.location, new_msg)
          
    # If we have already deduced the type parameters in the parameter type,
    # then we can check the term. Otherwise, we synthesize the term's type
    # and match it against the parameter type.
    try:
      new_args = []
      for (arg, param_ty) in zip(args, param_types):
          param_type = param_ty.substitute(matching)
          fvs = param_type.free_vars()\
                          .intersection(set([ty.name for ty in type_params]))
          if get_verbose():
            print('arg = ' + str(arg))
            print('param_type = ' + str(param_type))
            print('fvs = ' + ', '.join([base_name(x) for x in fvs]) + '\n')
          if len(fvs) == 0:
            new_arg = type_check_term(arg, param_type, env, recfun, subterms)
          else:
            new_arg = type_synth_term(arg, env, recfun, subterms)
            type_match(loc, type_params, param_type, new_arg.typeof, matching)
          new_args.append(new_arg)
    except (UserError, MatchFailed) as e:
        context = '\n\n\t' + 'in context of call ' + str(call) + '\n' \
            + '\tfunction type: ' + str(FunctionType(loc, typarams, param_types,
                                                     return_type)) + '\n' \
            + '\tinferred type arguments: ' \
            + ', '.join([base_name(x) + ' := ' + str(ty) for (x,ty) in matching.items()])
        raise wrap_user_error(e, context) from e
    
    # Were all the type parameters deduced?
    for x in typarams:
        if x not in matching.keys():
            user_error(loc, 'in call ' + str(call) \
                  + '\n\tcould not deduce a type for ' \
                  + base_name(x) + ' to instantiate ' + str(call.rator) \
                  + '\n\twhose type is: ' + str(new_rator.typeof))

    type_args = [matching[x] for x in typarams]
    inst_params = [p.substitute(matching) for p in param_types]
    inst_return_type = return_type.substitute(matching)
    inst_funty = FunctionType(loc, [], inst_params, inst_return_type)
    inst_rator = TermInst(loc, inst_funty, new_rator, type_args, True)
    ret = Call(loc, inst_return_type, inst_rator, new_args)
    # print('{{{ type deduction for call: ' + str(ret))
    # print('arg_types: ' + ', '.join([str(arg.typeof) for arg in new_args]))
    # print(', '.join([x + ' = ' + str(t) for (x,t) in matching.items()]))
    # print('inst return type = ' + str(inst_return_type))
    # print('env:\n' + env.term_vars_str())
    # print('}}}')
    return ret

def overload_mismatch_annotation(loc, overload_funty, arg_types, ret_ty):
  """Return a short annotation explaining why this overload doesn't fit, or
  ``None`` if neither side matches (in which case the bare overload type is
  already informative on its own). The annotation distinguishes the two
  common confusing cases: arguments line up but the return type is wrong,
  or vice versa."""
  match overload_funty:
    case FunctionType(_, typarams, param_types, return_type):
      type_params = type_names(loc, typarams)
      args_match = (len(param_types) == len(arg_types))
      if args_match:
        m = {}
        try:
          for (pt, at) in zip(param_types, arg_types):
            type_match(loc, type_params, pt, at, m)
        except MatchFailed:
          args_match = False
      ret_matches = True
      if ret_ty is not None:
        m = {}
        try:
          type_match(loc, type_params, return_type, ret_ty, m)
        except MatchFailed:
          ret_matches = False
      if args_match and ret_ty is not None and not ret_matches:
        return 'argument types match, but result type ' + str(return_type) \
               + " doesn't match expected " + str(ret_ty)
      if ret_ty is not None and ret_matches and not args_match:
        return "result type matches, but argument types don't"
      return None
    case _:
      return None

def type_check_call_helper(loc, new_rator, args, env, recfun, subterms, ret_ty, call):
  if get_verbose():
      print('tc_call_helper(' + str(call) + ') rator type: ' + str(new_rator.typeof))
  funty = new_rator.typeof
  match funty:
    case OverloadType(_, overloads):
      num_matches = 0
      for (x, funty) in overloads:
          match funty:
            case FunctionType(_, typarams, param_types, return_type):
              # Preserve the rator's use-site location (e.g. the `+'
              # token in `x + y') on the resolved variable.  Using
              # `loc2' (the FunctionType's declaration site) here
              # would leak the operator's declaration location into
              # every Call.rator, breaking F12 / hover for overloaded
              # operators -- the location info is the only thing the
              # LSP can use to spot the use site.  Non-overloaded
              # names go through the `FunctionType' arm below where
              # ``new_rator'' is passed through unchanged.
              try:
                new_call = type_check_call_funty(loc, ResolvedVar(new_rator.location, funty, x), args, env, recfun,
                                                 subterms, ret_ty, call,
                                                 typarams, param_types, return_type)
                num_matches += 1
              except (UserError, MatchFailed):
                pass
      if num_matches == 0:
          arg_types = [type_synth_term(arg, env, None, []).typeof for arg in args]
          msg = 'could not find a match for function call:\n\t' \
                + str(call) + '\n' \
                + 'argument types: ' + ', '.join([str(t) for t in arg_types]) + '\n'
          if ret_ty is not None:
              msg += 'expected return type: ' + str(ret_ty) + '\n'
          msg += 'overloads:'
          for (x, ty) in overloads:
              annotation = overload_mismatch_annotation(loc, ty, arg_types, ret_ty)
              msg += '\n\t' + str(ty)
              if annotation is not None:
                  msg += '   <-- ' + annotation
          user_error(loc, msg)
      elif num_matches > 1:
          user_error(loc, 'in call to ' + str(new_rator) + '\n'\
                + 'ambiguous overloads:\n' \
                + '\n'.join([error_header(ty.location) + str(ty) for (x,ty) in overloads]))
      else:
          return new_call
    case FunctionType(_, typarams, param_types, return_type):
      return type_check_call_funty(loc, new_rator, args, env, recfun, subterms, ret_ty, call,
                                   typarams, param_types, return_type)
    case _:
      user_error(loc, 'expected operator to have function type, not ' + str(funty))
      
def type_check_call(loc, rator, args, env, recfun, subterms, ret_ty, call):
  if get_verbose():
      print('tc_check_call(' + str(call) + ')')
      print('rator: ' + str(rator))
  new_rator = type_synth_term(rator, env, recfun, subterms)
  return type_check_call_helper(loc, new_rator, args, env, recfun, subterms, ret_ty, call)

recursive_call_count = 0

def get_recursive_call_count():
    global recursive_call_count
    return recursive_call_count

def increment_recursive_call_count():
    global recursive_call_count
    recursive_call_count += 1

def reset_recursive_call_count():
    global recursive_call_count
    recursive_call_count = 0

def check_recursive_call(call, recfun, subterms):
  # print('check_recursive_call(' + repr(call) + ') in ' + str(recfun))
  # print('rator_name = ' + rator_name(call.rator))
  if rator_name(call.rator) != recfun:
      return
  increment_recursive_call_count()

  if isinstance(call.args[0], VarRef):
    if not (call.args[0].get_name() in subterms):
      user_error(call.location, "ill-formed recursive call\n" \
            + "expected first argument to be " \
            + " or ".join([base_name(x) for x in subterms]) \
            + ", not " + str(call.args[0]))
  else:
    user_error(call.location, "ill-formed recursive call\n" \
          + "expected first argument to be " \
          + " or ".join([base_name(x) for x in subterms]) \
          + ", not " + str(call.args[0]))

def _is_recfun_ref(node, recfun):
  if isinstance(node, ResolvedVar):
    return node.name == recfun
  if isinstance(node, OverloadedVar):
    return recfun in node.resolved_names
  if isinstance(node, Var):
    return node.name == recfun
  return False

def _escape_error(loc, recfun):
  user_error(loc,
        "the name '" + base_name(recfun) + "'"
        + " of a recursive function may only appear as the operator"
        + " of a function call within its own body")

def check_no_recfun_escape(term, recfun):
  # Walk ``term`` and raise an error if ``recfun`` (the uniquified
  # name of the enclosing recursive function) appears anywhere other
  # than as the (optionally type-instantiated) operator of a Call.
  # This is the escape analysis from issue #215: it stops a body from
  # smuggling the recursive function out via a let-binding, an
  # argument position, or a return value, which would otherwise let
  # callers loop without the first-argument decreases check.
  if term is None:
    return
  if isinstance(term, VarRef):
    if _is_recfun_ref(term, recfun):
      _escape_error(term.location, recfun)
    return
  match term:
    case Call(_, _, rator, args):
      _check_rator_no_escape(rator, recfun)
      for a in args:
        check_no_recfun_escape(a, recfun)
    case TermInst(_, _, subject, _, _):
      check_no_recfun_escape(subject, recfun)
    case Generic(_, _, _, body):
      check_no_recfun_escape(body, recfun)
    case Conditional(_, _, cond, thn, els):
      check_no_recfun_escape(cond, recfun)
      check_no_recfun_escape(thn, recfun)
      check_no_recfun_escape(els, recfun)
    case TAnnote(_, _, subject, _):
      check_no_recfun_escape(subject, recfun)
    case Lambda(_, _, _, body):
      check_no_recfun_escape(body, recfun)
    case Switch(_, _, subject, cases):
      check_no_recfun_escape(subject, recfun)
      for c in cases:
        check_no_recfun_escape(c.body, recfun)
    case Array(_, _, elements):
      for e in elements:
        check_no_recfun_escape(e, recfun)
    case MakeArray(_, _, subject):
      check_no_recfun_escape(subject, recfun)
    case ArrayGet(_, _, subject, position):
      check_no_recfun_escape(subject, recfun)
      check_no_recfun_escape(position, recfun)
    case TLet(_, _, _, rhs, body):
      check_no_recfun_escape(rhs, recfun)
      check_no_recfun_escape(body, recfun)
    case Mark(_, _, subject):
      check_no_recfun_escape(subject, recfun)
    case And(_, _, args):
      for a in args:
        check_no_recfun_escape(a, recfun)
    case Or(_, _, args):
      for a in args:
        check_no_recfun_escape(a, recfun)
    case IfThen(_, _, premise, conclusion):
      check_no_recfun_escape(premise, recfun)
      check_no_recfun_escape(conclusion, recfun)
    case All(_, _, _, _, body):
      check_no_recfun_escape(body, recfun)
    case Some(_, _, _, body):
      check_no_recfun_escape(body, recfun)
    case Int() | Bool() | Hole() | Omitted():
      pass
    case _:
      # Other AST nodes (e.g. RecFun, GenRecFun appearing as values)
      # are conservatively rejected if they reference the recfun
      # name, allowed otherwise.
      if _is_recfun_ref(term, recfun):
        _escape_error(term.location, recfun)

def _check_rator_no_escape(rator, recfun):
  # At a Call rator position, a direct VarRef to ``recfun`` is the
  # only place the name is legal; TermInst wrapping such a VarRef
  # (the ``@foo<T>(...)`` syntax) is the same shape. Anything else
  # is recursively walked as a non-rator subterm.
  if isinstance(rator, VarRef):
    return
  match rator:
    case TermInst(_, _, subject, _, _):
      _check_rator_no_escape(subject, recfun)
    case _:
      check_no_recfun_escape(rator, recfun)

# Helper for check_type: a bare reference to a generic union (one with N>0
# type parameters) is ill-formed. The arity check used to live in a separate
# `validate_union_type` pass that was only run on union-constructor parameters
# (issue #257); folding it into `check_type` makes every site that accepts a
# user-written type — postulate/define/recursive/theorem signatures, etc. —
# reject `Foo` when it should be `Foo<...>`.
def _check_union_arity(head, given, env):
  if not env.type_var_is_defined(head):
    return
  type_def = env.get_def_of_type_var(head)
  if isinstance(type_def, Union) and len(type_def.type_params) != given:
    user_error(head.location,
          f"Expected union type '{head}' to have "
          f"{len(type_def.type_params)} type arguments, not {given}")

# Validate that ``typ`` is well-formed in ``env`` and return the type
# with every single-candidate ``OverloadedVar`` narrowed to
# ``ResolvedVar``. The returned type may share structure with ``typ``
# when nothing changed; otherwise it's a freshly constructed copy.
# Callers MUST use the returned value, not the original ``typ`` —
# the strict post-typecheck invariant rejects single-candidate
# OverloadedVars, so dropping the return on the floor leaks them.
#
# ``arity_required`` is internal: callers that wrap a bare generic union
# head (TypeInst, GenericUnknownInst) and certain declaration sites (e.g.
# ``inductive Foo by ...``, which legitimately names a union by its bare
# name) pass False to suppress the zero-arity error.
def check_type(typ, env, arity_required=True):
  match typ:
    case OverloadedVar(loc, tyof, rs):
      if not env.type_var_is_defined(typ):
        user_error(loc, 'undefined type variable ' + str(typ))
      if len(rs) > 1:
        user_error(loc, 'type names may not be overloaded ' + str(typ))
      if arity_required:
        _check_union_arity(typ, 0, env)
      # len(rs) == 1: this is a non-overloaded type reference. Promote.
      return ResolvedVar(loc, tyof, rs[0])
    case ResolvedVar(loc, tyof, _):
      if not env.type_var_is_defined(typ):
        user_error(loc, 'undefined type variable ' + str(typ))
      if arity_required:
        _check_union_arity(typ, 0, env)
      return typ
    case IntType(loc) | BoolType(loc) | TypeType(loc):
      return typ
    case FunctionType(loc, typarams, param_types, return_type):
      body_env = env.declare_type_vars(loc, typarams)
      new_param_types = [check_type(ty, body_env) for ty in param_types]
      new_return_type = check_type(return_type, body_env)
      return FunctionType(loc, typarams, new_param_types, new_return_type)
    case TypeInst(loc, inner_typ, arg_types):
      # The head is a generic-union reference applied to ``arg_types``;
      # suppress the bare-head arity check and validate against the
      # actual arg count instead.
      new_inner = check_type(inner_typ, env, arity_required=False)
      if isinstance(new_inner, VarRef):
        _check_union_arity(new_inner, len(arg_types), env)
      new_args = [check_type(ty, env) for ty in arg_types]
      return TypeInst(loc, new_inner, new_args)
    case GenericUnknownInst(loc, inner_typ):
      # Internal node deliberately wrapping an unapplied generic union.
      return GenericUnknownInst(loc, check_type(inner_typ, env, arity_required=False))
    case ArrayType(loc, elt_type):
      return ArrayType(loc, check_type(elt_type, env))
    case _:
      internal_error(typ.location, 'error in check_type: unhandled type ' + repr(typ) + ' ' + str(type(typ)))

def type_first_letter(typ):
  if isinstance(typ, VarRef):
    return typ.get_name()[0]
  match typ:
    case IntType(_):
      return 'i'
    case BoolType(_):
      return 'b'
    case TypeType(_):
      return 't'
    case FunctionType(_, _, _, _):
      return 'f'
    case TypeInst(_, typ, _):
      return type_first_letter(typ)
    case GenericUnknownInst(_, typ):
      return type_first_letter(typ)
    case _:
      print('error in type_first_letter: unhandled type ' + repr(typ))
      exit(-1)

def type_check_term_inst(loc, subject, tyargs, inferred, recfun, subterms, env):
  for ty in tyargs:
      check_type(ty, env)
  new_subject = type_synth_term(subject, env, recfun, subterms)
  ty = new_subject.typeof
  if isinstance(ty, VarRef):
    retty = TypeInst(loc, ty, tyargs)
  else:
    match ty:
      case FunctionType(loc2, typarams, param_types, return_type):
        sub = {x: t for (x,t) in zip(typarams, tyargs)}
        inst_param_types = [t.substitute(sub) for t in param_types]
        inst_return_type = return_type.substitute(sub)
        retty = FunctionType(loc2, [], inst_param_types, inst_return_type)
      case GenericUnknownInst(loc2, union_type):
        retty = TypeInst(loc2, union_type, tyargs)
      case _:
        user_error(loc, 'expected a type name, not ' + str(ty))
  return TermInst(loc, retty, new_subject, tyargs, inferred)

def type_check_term_inst_var(loc, subject_var, tyargs, inferred, env):
  if isinstance(subject_var, VarRef):
      for ty in tyargs:
          check_type(ty, env)
      ty = env.get_type_of_term_var(subject_var)
      if isinstance(ty, VarRef):
        retty = TypeInst(loc, ty, tyargs)
      else:
        match ty:
          case FunctionType(loc3, typarams, param_types, return_type):
            sub = {x: t for (x,t) in zip(typarams, tyargs)}
            inst_param_types = [t.substitute(sub) for t in param_types]
            inst_return_type = return_type.substitute(sub)
            retty = FunctionType(loc3, [], inst_param_types, inst_return_type)
          case GenericUnknownInst(loc3, union_type):
            retty = TypeInst(loc3, union_type, tyargs)
          case _:
            user_error(loc, 'cannot instantiate a term of type ' + str(ty))
      # Subject is now resolved (we've narrowed to its single typed name).
      return TermInst(loc, retty,
                      ResolvedVar(subject_var.location, subject_var.typeof,
                                  subject_var.get_name()),
                      tyargs, inferred)
  internal_error(loc, 'internal error, expected variable, not ' + str(subject_var))

def type_synth_term(term, env, recfun, subterms):
  if get_verbose():
    print('type_synth_term: ' + str(term) + '\n' \
          + '\tin ' + str(recfun))
  match term:
    case Mark(loc, _, subject):
      new_subject = type_synth_term(subject, env, recfun, subterms)
      ret = Mark(loc, new_subject.typeof, new_subject)
  
    case OverloadedVar(loc, _, rs):
      try:
        ty = env.get_type_of_term_var(term)
        if ty == None:
          raise Exception('while type checking, undefined variable ' + str(term) \
                + '\nin scope:\n' + 'str(env)')
      except Exception as e:
        user_error(loc, str(e))
      match ty:
        case GenericUnknownInst(loc2, _):
          user_error(loc, 'Cannot infer type arguments for\n' \
                + '\t' + base_name(rs[0]) + '\nPlease make them explicit.')

      if len(rs) == 1:
          # No real overload — promote to ResolvedVar so downstream
          # code can rely on the type-system narrowing.
          ret = ResolvedVar(loc, ty, rs[0])
      else:
          if get_verbose():
              print('type_synth_term(' + str(term) + ') waiting to resolve name')
          ret = OverloadedVar(loc, ty, rs)

    case ResolvedVar(loc, _, name):
      ty = env.get_type_of_term_var(term)
      if ty is None:
        user_error(loc, 'while type checking, undefined variable ' + str(term))
      match ty:
        case GenericUnknownInst(loc2, _):
          user_error(loc, 'Cannot infer type arguments for\n' \
                + '\t' + base_name(name) + '\nPlease make them explicit.')
      ret = ResolvedVar(loc, ty, name)
      
    case Generic(loc, _, type_params, body):
      body_env = env.declare_type_vars(loc, type_params)
      new_body = type_synth_term(body, body_env, recfun, subterms)
      match new_body.typeof:
        case FunctionType(loc2, [], param_types, return_type):
          ty = FunctionType(loc, type_params, param_types, return_type)
          ret = Generic(loc, ty, type_params, new_body)
        case _:
          user_error(loc, 'body of generic must be a function, not ' \
                + str(new_body.typeof))

    case Lambda(loc, _, params, body):
      for (p,t) in params:
          if t:
              check_type(t, env)
      vars = [p for (p,t) in params]
      param_types = [t for (p,t) in params]
      if any([t == None for t in param_types]):
          user_error(loc, 'Cannot synthesize a type for ' + str(term) + '.\n'\
                + 'Add type annotations to the parameters.')
      body_env = env.declare_term_vars(loc, params)
      new_body = type_synth_term(body, body_env, recfun, subterms)
      typ = FunctionType(loc, [], param_types, new_body.typeof)
      return Lambda(loc, typ, params, new_body)
      
    case TLet(loc, _, var, rhs, body):
      new_rhs = type_synth_term(rhs, env, recfun, subterms)
      body_env = env.declare_term_var(loc, var, new_rhs.typeof)
      new_body = type_synth_term(body, body_env, recfun, subterms)
      ret = TLet(loc, new_body.typeof, var, new_rhs, new_body)
  
    case Conditional(loc, _, cond, thn, els):
      new_cond = type_check_term(cond, BoolType(loc), env, recfun, subterms)
      new_thn = type_synth_term(thn, env, recfun, subterms)
      new_els = type_synth_term(els, env, recfun, subterms)
      if new_thn.typeof != new_els.typeof:
        user_error(loc, 'conditional expects same type for the two branches'\
              + ' but ' + str(new_thn.typeof) + ' ≠ ' + str(new_els.typeof))
      ret = Conditional(loc, new_thn.typeof, new_cond, new_thn, new_els)
      
    case Int(loc, _, value):
      ty = IntType(loc)
      ret = Int(loc, ty, value)
      
    case Bool(loc, _, value):
      ty = BoolType(loc)
      ret = Bool(loc, ty, value)
      
    case And(loc, _, args):
      new_args = [check_formula(arg, env, recfun, subterms) for arg in args]
      ty = BoolType(loc)
      ret = And(loc, ty, new_args)
      
    case Or(loc, _, args):
      new_args = [check_formula(arg, env, recfun, subterms) for arg in args]
      ty = BoolType(loc)
      ret = Or(loc, ty, new_args)
      
    case IfThen(loc, _, prem, conc):
      new_prem = check_formula(prem, env, recfun, subterms)
      new_conc = check_formula(conc, env, recfun, subterms)
      ty = BoolType(loc)
      ret = IfThen(loc, ty, new_prem, new_conc)
      
    case All(loc, _, var, pos, body):
      all_types = None
      x, ty = var
      new_ty = check_type(ty, env)
      if isinstance(new_ty, TypeType):
        if all_types == None or all_types == True:
          all_types = True
        else:
          user_error(loc, 'cannot mix type and term variables in an all formula')
      else:
        if all_types == None or all_types == False:
          all_types = False
        else:
          user_error(loc, 'cannot mix type and term variables in an all formula')
      new_var = (x, new_ty)
      body_env = env.declare_term_vars(loc, [new_var])
      new_body = check_formula(body, body_env, recfun, subterms)
      ret = All(loc, BoolType(loc), new_var, pos, new_body)

    case Some(loc, _, vars, body):
      new_vars = [(x, check_type(ty, env)) for (x, ty) in vars]
      body_env = env.declare_term_vars(loc, new_vars)
      new_body = check_formula(body, body_env, recfun, subterms)
      ret = Some(loc, BoolType(loc), new_vars, new_body)
      
    case MakeArray(loc, _, arg):
      lst = type_synth_term(arg, env, recfun, subterms)
      match lst.typeof:
        case TypeInst(loc2, lst_ty, [elt_type]):
          union_def = lookup_union(loc, lst_ty, env)
          if base_name(union_def.name) == 'List':
            ret = MakeArray(loc, ArrayType(loc, elt_type), lst)
          else:
            user_error(loc, 'expected List, not union ' + union_def.name)
        case _:
          user_error(loc, 'expected List, not ' + str(lst.typeof))

    case ArrayGet(loc, _, array, index):
      new_array = type_synth_term(array, env, recfun, subterms)
      new_index = type_synth_term(index, env, recfun, subterms)
      match new_array.typeof:
        case ArrayType(loc2, elt_type):
          ret = ArrayGet(loc, elt_type, new_array, new_index)
        case _:
          user_error(loc, 'expected an array, not ' + str(new_array.typeof))
          
    case Call(loc, _, (OverloadedVar(loc2, ty2, [op_name, *_])
                       | ResolvedVar(loc2, ty2, op_name)), args) \
        if op_name == '=' or op_name == '≠':
      assert len(args) == 2
      lhs = type_synth_term(args[0], env, recfun, subterms)
      rhs = type_check_term(args[1], lhs.typeof, env, recfun, subterms)
      ty = BoolType(loc)
      if lhs.typeof != rhs.typeof:
          user_error(loc, 'expected arguments of equality to have the same type, but\n' \
                + '\t' + str(lhs.typeof) + ' ≠ ' + str(rhs.typeof))
      ret = Call(loc, ty, ResolvedVar(loc2, ty2, op_name), [lhs, rhs])
        
    case Call(loc, _, rator, args):
      ret = type_check_call(loc, rator, args, env, recfun, subterms, None, term)
      check_recursive_call(ret, recfun, subterms)
      
    case Switch(loc, _, subject, cases):
      new_subject = type_synth_term(subject, env, recfun, subterms)
      ty = new_subject.typeof

      cases_present = {}
      result_type = [None] # boxed to allow mutable update in process_case

      def process_case(c, result_type, cases_present):
        new_env = check_pattern(c.pattern, ty, env, cases_present)
        new_body = type_synth_term(c.body, new_env, recfun, subterms)
        case_type = new_body.typeof
        if result_type[0] == None:
          result_type[0] = case_type
        elif case_type != result_type[0]:
          user_error(c.location, 'bodies of cases must have same type, but ' \
                + str(case_type) + ' ≠ ' + str(result_type[0]))
        return SwitchCase(c.location, c.pattern, new_body)

      new_cases = [process_case(c, result_type, cases_present) \
                   for c in cases]
      ret = Switch(loc, result_type[0], new_subject, new_cases)
      
      # check exhaustiveness
      match ty:
        case BoolType(loc2):
          has_true_case = False
          has_false_case = False
          for scase in cases:
            match scase.pattern:
              case PatternBool(_, True):
                has_true_case = True
              case PatternBool(_, False):
                has_false_case = True
              case _:
                user_error(c.location, 'not an appropriate case for bool\n\t' \
                           + str(scase))
          if not has_true_case:
            user_error(loc, 'missing case for true')
          if not has_false_case:
            user_error(loc, 'missing case for false')
        case _:
          dfn = lookup_union(loc, ty, env)
          match dfn:
            case Union(loc2, name, typarams, alts):
              for alt in alts:
                  if alt.name not in cases_present.keys():
                      user_error(loc, 'this switch is missing a case for: ' \
                            + str(alt))
            case _:
              user_error(loc, 'expected a union type, not ' + str(ty))

    case TermInst(loc, _, subject, tyargs, inferred) if isinstance(subject, VarRef):
      ret = type_check_term_inst_var(loc, subject, tyargs, inferred, env)

    case TermInst(loc, _, subject, tyargs, inferred):
      ret = type_check_term_inst(loc, subject, tyargs, inferred, recfun, subterms, env)

    case TAnnote(loc, _, subject, typ):
      check_type(typ, env)
      ret = type_check_term(subject, typ, env, recfun, subterms)

    case RecFun(loc, name, typarams, params, returns, cases):
      fun_type = FunctionType(loc, typarams, params, returns)
      ret = term
      term.typeof = fun_type
      
    case GenRecFun(loc, name, typarams, params, returns, _, _,
                   body, _):
      param_types = [t for (p,t) in params]
      fun_type = FunctionType(loc, typarams, param_types, returns)
      ret = term
      term.typeof = fun_type
      
    case _:
      if isinstance(term, Type):
        internal_error(term.location, 'type_synth_term called on type ' + str(term))
        ret = TypeType(term.location)
      else:
        user_error(term.location, 'cannot synthesize a type for ' + str(term))
  if get_verbose():
    print('\ttype synth: ' + str(term) + '\n\t=> ' + str(ret) + ' : ' + str(ret.typeof))
  return ret

def type_check_formula(term, env):
  return type_check_term(term, BoolType(term.location), env, None, [])

def type_check_term(term, typ, env, recfun, subterms):
  if get_verbose():
    print('\ntype_check_term: ' + str(term) + ' : ' + str(typ) + '?\n')
  match term:
    case Mark(loc, _, subject):
      new_subject = type_check_term(subject, typ, env, recfun, subterms)
      return Mark(loc, new_subject.typeof, new_subject)
    case Hole(loc, _):
      return Hole(loc, typ)
    case Omitted(loc, _):
      return Omitted(loc, typ)
    case Generic(loc, _, type_params, body):
      match typ:
        case FunctionType(loc2, type_params2, param_types2, return_type2):
          sub = {U: ResolvedVar(loc, None, T) \
                 for (T,U) in zip(type_params, type_params2) }
          new_param_types = [ty.substitute(sub) for ty in param_types2]
          new_return_type = return_type2.substitute(sub)
          body_env = env.declare_type_vars(loc, type_params)
          funty = FunctionType(loc2, [], new_param_types, new_return_type)
          new_body = type_check_term(body, funty, body_env, recfun, subterms)
          return Generic(loc, typ, type_params, new_body)
        case _:
          user_error(loc, 'unexpected generic term, expected ' + str(typ))
        
    case ResolvedVar(loc, _, name):
      var_typ = env.get_type_of_term_var(term)
      if var_typ is None:
        user_error(loc, 'variable ' + str(term) + ' is not defined')
      match (var_typ, typ):
        case (GenericUnknownInst(loc2, union1), TypeInst(_, union2, tyargs)):
          if union1 == union2:
            return TermInst(loc, typ, ResolvedVar(loc, typ, name),
                            tyargs, True)
        case (FunctionType(_, typarams, param_types1, ret_type1),
              FunctionType(loc2, [], param_types2, ret_type2)):
          if len(typarams) > 0:
            matching = {}
            type_params = type_names(loc, typarams)
            try:
              type_match(loc, type_params, ret_type1, ret_type2, matching)
              for (p1, p2) in zip(param_types1, param_types2):
                  type_match(loc, type_params, p1, p2, matching)
              type_args = [matching[x] for x in type_params]
              return TermInst(ResolvedVar(loc, var_typ, name),
                              type_args, True)
            except UserError:
              pass
      if var_typ != typ:
        user_error(loc, 'expected a term of type ' + str(typ) \
                   + '\nbut got term ' + str(term) \
                   + ' of type ' + str(var_typ))
      return ResolvedVar(loc, typ, name)

    case OverloadedVar(loc, _, rs):
      var_typ = env.get_type_of_term_var(term)
      if get_verbose():
          print('var_typ = ' + str(var_typ))
      if var_typ == None:
        user_error(loc, 'variable ' + str(term) + ' is not defined' \
              + '\nin scope:\n' + 'str(env)')
      match (var_typ, typ):
        case (OverloadType(loc2, overloads), _):
          for (x, ty) in overloads:
              if ty == typ:
                  if get_verbose():
                      print('found overload ' + x + ' of type ' + str(typ))
                  return ResolvedVar(loc, typ, x)
          user_error(loc, 'could not find an overload of ' + base_name(rs[0]) \
                + ' of type ' + str(typ) + '\nin: ' + str(var_typ))
        case (GenericUnknownInst(loc2, union1), TypeInst(_, union2, tyargs)):
          if union1 == union2:
              return TermInst(loc, typ, ResolvedVar(loc, typ, rs[0]),
                              tyargs, True)
        case (FunctionType(_, typarams, param_types1, ret_type1),
              FunctionType(loc2, [], param_types2, ret_type2)):
          if len(typarams) > 0:
            matching = {}
            type_params = type_names(loc, typarams)
            try:
              type_match(loc, type_params, ret_type1, ret_type2, matching)
              for (p1, p2) in zip(param_types1, param_types2):
                  type_match(loc, type_params, p1, p2, matching)
              type_args = [matching[x] for x in type_params]
              return TermInst(ResolvedVar(loc, var_typ, rs[0]),
                              type_args, True)
            except UserError:
              pass
      if var_typ != typ:
        user_error(loc, 'expected a term of type ' + str(typ) \
                   + '\nbut got term ' + str(term) \
                   + ' of type ' + str(var_typ))
      return ResolvedVar(loc, typ, rs[0])
  
    case Lambda(loc, _, params, body):
      match typ:
        case FunctionType(loc2, [], param_types, return_type):
          vars = [n for (n,t) in params]
          body_env = env.declare_term_vars(loc, zip(vars, param_types))
          new_body = type_check_term(body, return_type, body_env,
                                     recfun, subterms)
          return Lambda(loc, typ, params, new_body)
        case FunctionType(loc2, ty_params, _, _):
          pretty_params = ", ".join([base_name(x) for x in ty_params])
          plural = 's' if len(ty_params) > 1 else ''
          user_error(loc, f'Expected type parameter{plural} {pretty_params}, ' \
                     + 'but got a lambda.\n\t' + \
                     f'Add generic {pretty_params} {"{ ... }"} around ' + \
                     'the function body.')
        case _:
          user_error(loc, 'expected a term of type ' + str(typ) + '\n'\
                + 'but instead got a lambda')
          
    case TLet(loc, _, var, rhs, body):
      new_rhs = type_synth_term(rhs, env, recfun, subterms)
      body_env = env.declare_term_var(loc, var, new_rhs.typeof)
      new_body = type_check_term(body, typ, body_env, recfun, subterms)
      return TLet(loc, typ, var, new_rhs, new_body)
      
    case Call(loc, _, (OverloadedVar(loc2, _, [op_name, *_])
                       | ResolvedVar(loc2, _, op_name)), args) \
        if op_name == '=' or op_name == '≠':
      new_term = type_synth_term(term, env, recfun, subterms)
      ty = new_term.typeof
      if ty != typ:
        user_error(term.location, 'expected term of type ' + str(typ) \
              + ' but got ' + str(ty))
      return new_term
      
    case Call(loc, _, rator, args):
      ret = type_check_call(loc, rator, args, env, recfun, subterms, typ, term)
      check_recursive_call(ret, recfun, subterms)
      return ret

    case Switch(loc, _, subject, cases):
      new_subject = type_synth_term(subject, env, recfun, subterms)
      ty = new_subject.typeof
      cases_present = {}
      result_type = [None] # boxed to allow mutable update in process_case
      
      def process_case(c, result_type, cases_present):
        new_env = check_pattern(c.pattern, ty, env, cases_present)
        #print('\n$\n' + str(c) + '\nnew env:\n' + str(new_env))
        new_body = type_check_term(c.body, typ, new_env, recfun, subterms)
        case_type = new_body.typeof
        if result_type[0] == None:
          result_type[0] = case_type
        elif case_type != result_type[0]:
          user_error(c.location, 'bodies of cases must have same type, but ' \
                + str(case_type) + ' ≠ ' + str(result_type[0]))
        return SwitchCase(c.location, c.pattern, new_body)

      new_cases = [process_case(c, result_type, cases_present) for c in cases]

      # Check case coverage
      match ty:
        case BoolType(loc2):
          if 'True' not in cases_present.keys():
            user_error(loc, 'missing case for true')
          if 'False' not in cases_present.keys():
            user_error(loc, 'missing case for false')
        case _:
          dfn = lookup_union(loc, ty, env)
          match dfn:
            case Union(loc2, name, typarams, alts):
              for alt in alts:
                  if alt.name not in cases_present.keys():
                      user_error(loc, 'missing a case for:\n\t' \
                            + str(alt))
            case _:
              user_error(loc, 'expected a union type, not ' + str(ty))
      
      return Switch(loc, result_type[0], new_subject, new_cases)
      
    case Conditional(loc, _, cond, thn, els):
      new_cond = type_check_term(cond, BoolType(loc), env, recfun, subterms)
      new_thn = type_check_term(thn, typ, env, recfun, subterms)
      new_els = type_check_term(els, typ, env, recfun, subterms)
      return Conditional(loc, typ, new_cond, new_thn, new_els)
  
    case TermInst(loc, _, subject, tyargs, inferred) if isinstance(subject, VarRef):
      return type_check_term_inst_var(loc, subject, tyargs, inferred, env)

    case TermInst(loc, _, subject, tyargs, inferred):
      return type_check_term_inst(loc, subject, tyargs, inferred, recfun, subterms, env)

    case _:
      if get_verbose():
          print('type_check_term delegating to type_synth_term')
      new_term = type_synth_term(term, env, recfun, subterms)
      ty = new_term.typeof
      if ty != typ:
        user_error(term.location, 'expected term of type ' + str(typ) \
              + ' but got ' + str(ty))
      return new_term
  
def lookup_union(loc, typ, env):
  if isinstance(typ, VarRef):
    return env.get_def_of_type_var(typ)
  match typ:
    case TypeInst(_, inst_typ, _):
      return env.get_def_of_type_var(inst_typ)
    case _:
      user_error(loc, 'expected a union type but instead got ' + str(typ))

def check_constructor_pattern(loc, pat_constr, params, typ, env, cases_present):
  if get_verbose():
    print('check_constructor_pattern: ' + str(pat_constr))
  defn = lookup_union(loc, typ, env)
  if get_verbose():
    print('for union: ' + str(defn))
  match defn:
    case Union(_, _, typarams, alts):
      # example:
      # typ is List<E>
      # union List<T> { empty; node(T, List<T>); }
      # pat_constr == node
      #found_pat_constr = False
      # Candidates the parser/uniquify pass observed for this pattern's
      # constructor. For an OverloadedVar this is the full list; for an
      # already-narrowed ResolvedVar we just have the chosen name.
      if isinstance(pat_constr, OverloadedVar):
        candidates = pat_constr.resolved_names
      else:
        candidates = [pat_constr.get_name()]
      for constr in alts:
        # constr = node(T, List<T>)
        if constr.name in candidates:
          # Narrowing happens via class transition: the surrounding
          # PatternCons gets a new ResolvedVar in place of its old
          # (overloaded) constructor. We return that new node alongside
          # the parameter types so the caller can swap it in. (We don't
          # have the PatternCons here, so the caller does the mutation.)
          if len(typarams) > 0:
            if not hasattr(typ, 'arg_types'):
                internal_error(loc, 'problem in check_constr_pattern with: ' + str(typ))
            sub = { T: ty for (T,ty) in zip(typarams, typ.arg_types)}
            parameter_types = [p.substitute(sub) for p in constr.parameters]
          else:
            parameter_types = constr.parameters
          cases_present[constr.name] = True
          new_constr = ResolvedVar(pat_constr.location,
                                   pat_constr.typeof, constr.name)
          return new_constr, list(zip(params, parameter_types))
      user_error(loc, base_name(pat_constr.get_name()) \
            + ' is not a constructor of union ' + str(defn))
      #return env
    case _:
      user_error(loc, str(typ) + ' is not a union type')
        
def check_pattern(pattern, typ, env, cases_present):
  if get_verbose():
    print('check pattern: ' + str(pattern))
    print('against type: ' + str(typ))
    #print('in env: ' + str(env))
#  pattern.typeof = typ
  match pattern:
    case PatternBool(loc, value):
      match typ:
        case BoolType(_):
          cases_present[str(value)] = True
          return env
        case _:
          user_error(pattern.location, 'expected a pattern of type\n\t' \
                + str(typ) + '\nbut got\n\t' + str(pattern))
    case PatternCons(loc, constr, params):
      new_constr, param_types = check_constructor_pattern(
          loc, constr, params, typ, env, cases_present)
      pattern.constructor = new_constr
      return env.declare_term_vars(loc, param_types)
    case _:
      user_error(pattern.location, 'expected a pattern, not\n\t' \
            + str(pattern))

def check_formula(frm, env, recfun=None, subterms=[]):
  return type_check_term(frm, BoolType(frm.location), env, recfun, subterms)

modules: set = set()

dirty_files: set = set()

def is_modified(filename):
    path = Path(filename)
    last_mod = path.stat().st_mtime
    thm_path = path.with_suffix('.thm')
    if thm_path.exists():
        thm_last_mod = thm_path.stat().st_mtime
        return thm_last_mod < last_mod
    else:
        return True
          
# Strict-positivity check for inductive (union) types.
#
# A constructor parameter type is strictly positive in the union being defined
# (`union_name`) if `union_name` does not appear in any "negative position",
# i.e. to the left of an arrow in a `FunctionType`. Without this restriction
# the type theory is inconsistent: `union Bad { Wrap(fn Bad -> bool) }` admits
# Russell's paradox via `R = Wrap(fun x { not unwrap(x)(x) })`.
#
# When walking through a `TypeInst(D, args)` of some other generic union `D`,
# the polarity for each arg is adjusted by the polarity that `D` uses for that
# parameter. Per-parameter polarities for each generic union are inferred by
# `infer_param_polarities` and stored on the `Union` AST node before this
# check runs. This catches "nested" non-positivity such as
# `union B { Mk(Set<B>) }`, where `Set<X>` is `char_fun(fn X -> bool)` — `Set`'s
# parameter `X` is negative, so `B` ends up in a negative position.
#
# Deduce does not allow forward references between unions, so polarities can be
# computed in source order.
def _flip_polarity(pol):
  return '-' if pol == '+' else '+'

def _lookup_param_polarities(head, env):
  """If `head` resolves to a Union, return its inferred per-parameter polarities
  (or None if not yet inferred)."""
  if not isinstance(head, VarRef):
    return None
  try:
    head_def = env.get_def_of_type_var(head)
  except Exception:
    return None
  if isinstance(head_def, Union):
    return getattr(head_def, 'param_polarities', None)
  return None

def check_strict_positivity(ty, union_name, env, forbidden=False):
  if isinstance(ty, VarRef):
    ref_name = ty.get_name()
    if forbidden and ref_name == union_name:
      user_error(ty.location,
            f"the union '{base_name(union_name)}' must not occur in a "
            f"negative position (to the left of '->') of its own "
            f"constructor parameters; this would make the logic "
            f"inconsistent (Russell's paradox)")
    return
  match ty:
    case TypeInst(_, head, type_args):
      check_strict_positivity(head, union_name, env, forbidden)
      head_pols = _lookup_param_polarities(head, env)
      for i, t in enumerate(type_args):
        if head_pols is not None and i < len(head_pols) and head_pols[i] == '-':
          # Sticky: passing through a negative parameter forbids occurrences
          # in this arg, even under further negations.
          eff_forbidden = True
        else:
          eff_forbidden = forbidden
        check_strict_positivity(t, union_name, env, eff_forbidden)
    case FunctionType(_, _, param_types, return_type):
      for t in param_types:
        check_strict_positivity(t, union_name, env, forbidden=True)
      check_strict_positivity(return_type, union_name, env, forbidden)
    case ArrayType(_, elt_ty):
      check_strict_positivity(elt_ty, union_name, env, forbidden)
    case _:
      pass

# Infer per-parameter polarities for `union_decl` and stash them on the AST
# node as `param_polarities`. The list is mutable and used in-place during a
# fixpoint iteration so self-references read the in-progress polarities. This
# converges in at most |type_params| iterations because polarity is monotone
# (only goes '+' -> '-').
def infer_param_polarities(union_decl, env):
  if not union_decl.type_params:
    union_decl.param_polarities = []
    return

  polarities = ['+'] * len(union_decl.type_params)
  union_decl.param_polarities = polarities  # exposed in-place for self-refs

  type_param_names = set(union_decl.type_params)

  def walk(ty, current):
    if isinstance(ty, VarRef):
      ref_name = ty.get_name()
      if ref_name in type_param_names:
        idx = union_decl.type_params.index(ref_name)
        if current == '-':
          polarities[idx] = '-'
      return
    match ty:
      case TypeInst(_, head, type_args):
        walk(head, current)
        head_pols = _lookup_param_polarities(head, env)
        for i, arg in enumerate(type_args):
          if head_pols is not None and i < len(head_pols) and head_pols[i] == '-':
            # Sticky: descending through a negative parameter records this arg
            # as negative regardless of how deeply further function arrows
            # nest. This matches Coq's strict positivity (no parity flipping).
            eff = '-'
          else:
            eff = current
          walk(arg, eff)
      case FunctionType(_, _, param_types, return_type):
        for t in param_types:
          walk(t, '-')
        walk(return_type, current)
      case ArrayType(_, elt_ty):
        walk(elt_ty, current)
      case _:
        pass

  while True:
    before = list(polarities)
    for con in union_decl.alternatives:
      for ty in con.parameters:
        walk(ty, '+')
    if before == polarities:
      break

# ============================================================
# Predicate / relation validation (phase 2: shape, arity, strict positivity)
# ============================================================
#
# Validates an inductively defined predicate or relation. The Predicate AST
# already went through uniquify, so any free variable in a rule's body has
# already been caught by Var.uniquify with its own did-you-mean message.
# What's left for us:
#
# 1. Signature shape: 'fn ... -> bool' (arity ≥ 1) or 'bool' (arity 0).
# 2. Each rule's conclusion is a call to the predicate, with the right arity.
# 3. Strict positivity: the predicate may not appear in a "negative" position
#    of any rule's premise — under 'not', or to the left of an inner '->'.
#    The predicate at the top of the *outer* implication's conclusion (i.e.
#    the rule's main conclusion) is always positive and is not flagged.
# 4. A soft style hint when the keyword and arity disagree (predicate of
#    arity ≥ 2 → suggest 'relation', and vice versa).
#
# Error messages name the rule (`In rule 'NAME' of predicate 'FOO': ...`) so
# the user can locate which rule misfired without re-reading the whole block.

def _validate_predicate_signature(sig, name, keyword, env):
  check_type(sig, env)
  if isinstance(sig, BoolType):
    return 0, []
  if isinstance(sig, FunctionType):
    if not isinstance(sig.return_type, BoolType):
      user_error(sig.return_type.location,
            "the result type of a " + keyword + " must be 'bool', not '"
            + str(sig.return_type) + "'")
    return len(sig.param_types), sig.param_types
  user_error(sig.location,
        "the type of " + keyword + " '" + base_name(name)
        + "' must be 'bool' or 'fn ... -> bool', not '" + str(sig) + "'")

def _predicate_style_hint(loc, name, keyword, arity):
  if keyword == 'predicate' and arity >= 2:
    warning(loc,
            "style hint: '" + base_name(name) + "' has arity "
            + str(arity) + "; consider 'relation' instead of 'predicate' "
            "for n-ary relations.")
  elif keyword == 'relation' and arity == 1:
    warning(loc,
            "style hint: '" + base_name(name) + "' has arity 1; consider "
            "'predicate' instead of 'relation' for unary properties.")

def _decompose_rule_body(formula):
  """Strip outer 'all' quantifiers, then split optional 'if prem then conc'.
  Returns (binders, premise_or_None, conclusion). The conclusion is whatever
  is left after stripping 'all's and an optional outermost implication."""
  while isinstance(formula, All):
    formula = formula.body
  if isinstance(formula, IfThen):
    return formula.premise, formula.conclusion
  return None, formula

def _validate_predicate_rule_shape(rule, pred_name, keyword, arity, env):
  _, concl = _decompose_rule_body(rule.formula)
  if not isinstance(concl, Call):
    user_error(concl.location,
          "in rule '" + base_name(rule.name) + "' of " + keyword + " '"
          + base_name(pred_name) + "': the rule's conclusion must apply '"
          + base_name(pred_name) + "', but found '" + str(concl) + "'")
  rator = concl.rator
  rator_name = None
  if isinstance(rator, VarRef):
    rator_name = rator.get_name()
  if rator_name != pred_name:
    suggestion = ''
    if rator_name is not None:
      base_rator = base_name(rator_name)
      base_pred = base_name(pred_name)
      if edit_distance(base_rator, base_pred) <= max(2, len(base_pred) // 5):
        suggestion = " (did you mean '" + base_pred + "'?)"
    user_error(concl.location,
          "in rule '" + base_name(rule.name) + "' of " + keyword + " '"
          + base_name(pred_name) + "': the rule's conclusion must apply '"
          + base_name(pred_name) + "', but it applies '" + str(rator)
          + "'" + suggestion)
  if len(concl.args) != arity:
    plural = 's' if arity != 1 else ''
    user_error(concl.location,
          keyword + " '" + base_name(pred_name) + "' takes " + str(arity)
          + " argument" + plural + ", but rule '" + base_name(rule.name)
          + "' applies it to " + str(len(concl.args)))

def _check_predicate_strict_positivity(rule, pred_name, keyword, env):
  premise, _concl = _decompose_rule_body(rule.formula)
  if premise is None:
    return
  _walk_pred_premise(premise, pred_name, keyword, rule, forbidden=False)

def _walk_pred_premise(formula, pred_name, keyword, rule, forbidden):
  """Walk a premise looking for occurrences of the predicate. The
  `forbidden` flag flips on under 'not' / 'if/then' premises and stays on
  through subsequent nesting (sticky semantics, matching the union check)."""
  match formula:
    case Call(loc, _, rator, args):
      ratname = None
      if isinstance(rator, VarRef):
        ratname = rator.get_name()
      if forbidden and ratname == pred_name:
        user_error(loc,
              keyword + " '" + base_name(pred_name) + "' must not occur "
              "in a negative position (under 'not' or to the left of an "
              "inner 'then') of its own introduction rules; this would "
              "make the definition circular and inconsistent.\n"
              "In rule '" + base_name(rule.name) + "'.")
      for a in args:
        _walk_pred_premise(a, pred_name, keyword, rule, forbidden)
    case OverloadedVar(loc, _, rns):
      ref = rns[0]
      if forbidden and ref == pred_name:
        user_error(loc,
              keyword + " '" + base_name(pred_name) + "' must not occur "
              "in a negative position of its own introduction rules.\n"
              "In rule '" + base_name(rule.name) + "'.")
    case IfThen(loc, _, prem, conc):
      _walk_pred_premise(prem, pred_name, keyword, rule, forbidden=True)
      _walk_pred_premise(conc, pred_name, keyword, rule, forbidden)
    case And(loc, _, parts):
      for a in parts:
        _walk_pred_premise(a, pred_name, keyword, rule, forbidden)
    case Or(loc, _, parts):
      for a in parts:
        _walk_pred_premise(a, pred_name, keyword, rule, forbidden)
    case All(loc, _, _, _, body):
      _walk_pred_premise(body, pred_name, keyword, rule, forbidden)
    case Some(loc, _, _, body):
      _walk_pred_premise(body, pred_name, keyword, rule, forbidden)
    case _:
      pass

# --- translation -------------------------------------------------------
#
# Lower a validated `Predicate` to a derivation-tree encoding:
#
#   1. A `union <Pred>Deriv { D_<rule_1>(...) ; D_<rule_2>(...) ; ... }`
#      whose constructors mirror the rules. Each constructor takes the
#      rule's outer `all`-bound variables and one sub-derivation per
#      *recursive* premise (a premise of the form `<pred>(...)`).
#   2. A `recursive is_<pred>_deriv(<Pred>Deriv, T1, ..., Tn) -> bool`
#      that pattern-matches on the derivation and returns true exactly
#      when the derivation justifies that the predicate holds for the
#      given arguments. Each case asserts the conclusion's args, the
#      rule's non-recursive premises, and the validator on each
#      sub-derivation.
#   3. A `define <pred>(x1,...,xn) := some d. is_<pred>_deriv(d, x1,...,xn)`.
#   4. A `postulate <rule_name> : <rule's formula>` per rule.
#
# This encoding is the same one Coq uses internally: the predicate is the
# image of `is_*_deriv` under existential elimination on a strictly
# positive `union`. Because both `induction` (over the derivation `union`)
# and `switch` (on a derivation, for inversion) are existing primitives
# in Deduce, both elimination forms are cheap to add as user-facing sugar
# in follow-up commits.
#
# Limitations of this v1 translation:
#   * Rule premises must be a (possibly empty) conjunction of atoms.
#     Disjunctive premises (`if A or B then ...`) and nested implications
#     are rejected with a clear error pointing at the offending premise.
#   * Higher-order recursive premises (`all m. if Q(m) then pred(m)`) are
#     also rejected — the derivation constructor would need to carry a
#     function `fn ... -> <Pred>Deriv`, which is fine in Deduce but adds
#     enough complexity to defer to a later commit.

@dataclass
class _PremiseInfo:
  atom: object                  # the premise atom, copied
  is_recursive: bool
  orig_idx: int                 # index in the original conjunction (for PAndElim)
  sub_deriv_name: object        # str if recursive (the obtain'd witness), else None
  deriv_label: object           # str if recursive (the obtain'd proof label), else None
  rec_args: object              # list[Term] if recursive (atom.args), else None

@dataclass
class _RuleTranslation:
  rule: object                  # the original Rule
  bound_vars: list              # [(name, type)] outer all-bound
  premise_top: object           # the original premise formula (or None)
  premises: list                # list of _PremiseInfo, in original order
  conclusion_args: list         # the rule conclusion's args, copied
  conclusion_loc: object        # location of the conclusion (for proof spans)
  validator_arg_names: list     # fresh names for the validator's arity-many extra params

  @property
  def recursive_premises(self):
    return [p for p in self.premises if p.is_recursive]

  @property
  def non_recursive_premises(self):
    return [p for p in self.premises if not p.is_recursive]

def _flatten_and(formula):
  if isinstance(formula, And):
    return list(formula.args)
  return [formula]

def _is_recursive_atom(atom, pred_name):
  if not isinstance(atom, Call):
    return False
  rator = atom.rator
  if not isinstance(rator, VarRef):
    return False
  rname = rator.get_name()
  return rname == pred_name

def _premise_too_complex(prem):
  # Anything whose top is something we don't peel away in `_flatten_and`
  # signals a premise shape we won't translate yet. Bare atoms, calls,
  # and conjunctions of those are fine.
  if isinstance(prem, (IfThen, Or, All, Some)):
    return True
  if isinstance(prem, And):
    return any(_premise_too_complex(p) for p in prem.args)
  return False

def _decompose_rule_for_translation(rule, pred_name, keyword):
  formula = rule.formula
  bound_vars = []
  while isinstance(formula, All):
    bound_vars.append(formula.var)
    formula = formula.body
  if isinstance(formula, IfThen):
    premise = formula.premise
    conclusion = formula.conclusion
  else:
    premise = None
    conclusion = formula

  premises = []
  if premise is not None:
    if _premise_too_complex(premise):
      user_error(premise.location,
            "in rule '" + base_name(rule.name) + "' of " + keyword + " '"
            + base_name(pred_name) + "': v1 of the predicate translation "
            "supports only a conjunction of atoms as the rule's premise. "
            "Disjunctive, implicational, or quantified premises will be "
            "supported in a later commit.")
    for idx, atom in enumerate(_flatten_and(premise)):
      if _is_recursive_atom(atom, pred_name):
        premises.append(_PremiseInfo(
          atom=atom.copy(), is_recursive=True, orig_idx=idx,
          sub_deriv_name=generate_proof_name('d'),
          deriv_label=generate_proof_name('deriv'),
          rec_args=[a.copy() for a in atom.args]))
      else:
        premises.append(_PremiseInfo(
          atom=atom.copy(), is_recursive=False, orig_idx=idx,
          sub_deriv_name=None, deriv_label=None, rec_args=None))

  if not isinstance(conclusion, Call):
    user_error(conclusion.location,
          "expected a Call in conclusion of rule '"
          + base_name(rule.name) + "' (validation should have caught this)")
  conclusion_args = [a.copy() for a in conclusion.args]
  validator_arg_names = [generate_proof_name('m') for _ in conclusion_args]

  return _RuleTranslation(rule=rule,
                          bound_vars=bound_vars,
                          premise_top=premise,
                          premises=premises,
                          conclusion_args=conclusion_args,
                          conclusion_loc=conclusion.location,
                          validator_arg_names=validator_arg_names)

def _build_predicate_translation(decl, param_types):
  loc = decl.location
  pred_name = decl.name
  typarams = decl.type_params
  rules = decl.rules
  keyword = decl.original_keyword
  arity = len(param_types)
  base_pred = base_name(pred_name)

  rule_translations = [_decompose_rule_for_translation(r, pred_name, keyword)
                       for r in rules]

  # 1. Build the derivation union.
  deriv_union_name = generate_proof_name(base_pred + 'Deriv')
  constr_names = [generate_proof_name('D_' + base_name(r.name)) for r in rules]

  # The type-arg-applied form of the derivation type, used both as the
  # type of sub-derivations inside constructors and as the existential's
  # binder type below. For arity 0 type params, just a Var; otherwise a
  # TypeInst over the type-param vars.
  if typarams:
    deriv_type_inst = TypeInst(
      loc,
      ResolvedVar(loc, None, deriv_union_name),
      [ResolvedVar(loc, None, t) for t in typarams])
  else:
    deriv_type_inst = ResolvedVar(loc, None, deriv_union_name)

  constructors = []
  for cname, rt in zip(constr_names, rule_translations):
    fields = [t.copy() for (_, t) in rt.bound_vars] + \
             [deriv_type_inst.copy() for _ in rt.recursive_premises]
    constructors.append(Constructor(rt.rule.location, cname, fields))
  deriv_union = Union(loc, deriv_union_name, list(typarams), constructors,
                      visibility='public')

  # 2. Build the validator.
  is_deriv_name = generate_proof_name('is_' + base_pred + '_deriv')
  fun_cases = []
  for cname, rt in zip(constr_names, rule_translations):
    pat_param_names = [v for (v, _) in rt.bound_vars] + \
                      [p.sub_deriv_name for p in rt.recursive_premises]
    pattern = PatternCons(
      rt.rule.location,
      ResolvedVar(rt.rule.location, None, cname),
      pat_param_names)

    clauses = []
    # m_i = conclusion_args[i]
    for (m, c) in zip(rt.validator_arg_names, rt.conclusion_args):
      clauses.append(
        Call(rt.rule.location, BoolType(rt.rule.location),
             ResolvedVar(rt.rule.location, None, '='),
             [ResolvedVar(rt.rule.location, None, m), c.copy()]))
    # non-recursive premises verbatim
    for p in rt.non_recursive_premises:
      clauses.append(p.atom.copy())
    # recursive premise validators
    for p in rt.recursive_premises:
      args = [ResolvedVar(rt.rule.location, None, p.sub_deriv_name)] + \
             [a.copy() for a in p.rec_args]
      clauses.append(
        Call(rt.rule.location, BoolType(rt.rule.location),
             ResolvedVar(rt.rule.location, None, is_deriv_name),
             args))

    if not clauses:
      body = Bool(rt.rule.location, BoolType(rt.rule.location), True)
    elif len(clauses) == 1:
      body = clauses[0]
    else:
      body = And(rt.rule.location, BoolType(rt.rule.location), clauses)

    fun_cases.append(FunCase(
      rt.rule.location,
      ResolvedVar(rt.rule.location, None, is_deriv_name),
      pattern, list(rt.validator_arg_names), body))

  validator_param_types = [deriv_type_inst.copy()] + \
                          [t.copy() for t in param_types]
  has_any_recursive = any(len(rt.recursive_premises) > 0
                          for rt in rule_translations)
  if has_any_recursive:
    validator = RecFun(loc, is_deriv_name, list(typarams),
                       validator_param_types, BoolType(loc), fun_cases,
                       visibility=decl.visibility)
  else:
    # Deduce's `recursive` requires at least one recursive call. When no
    # rule has a recursive premise, lower the validator to a plain `fun`
    # whose body is a `switch` on the derivation. The cases match the
    # `fun_cases` we already built — we just rebuild them as switch cases
    # with the m_i parameters captured by the lambda.
    d_param_name = generate_proof_name('d')
    d_param_var = ResolvedVar(loc, None, d_param_name)
    switch_cases = []
    for fc in fun_cases:
      switch_cases.append(SwitchCase(fc.location, fc.pattern, fc.body))
    switch_term = Switch(loc, BoolType(loc), d_param_var, switch_cases)
    fun_params = [(d_param_name, deriv_type_inst.copy())] + \
                 [(m, t.copy()) for (m, t) in
                  zip(rule_translations[0].validator_arg_names
                      if rule_translations else [], param_types)]
    fun_body = Lambda(loc, None, fun_params, switch_term)
    if typarams:
      fun_body = Generic(loc, None, list(typarams), fun_body)
    validator_typ = FunctionType(loc, list(typarams),
                                 validator_param_types, BoolType(loc))
    validator = Define(loc, is_deriv_name, validator_typ, fun_body,
                       visibility=decl.visibility)

  # 3. Build the predicate's `define` body: fun args { some d. is_*_deriv(d, args) }
  arg_var_names = [generate_proof_name('x') for _ in range(arity)]
  arg_vars = [ResolvedVar(loc, None, x) for x in arg_var_names]
  d_name = generate_proof_name('d')
  is_deriv_call = Call(loc, BoolType(loc),
                       ResolvedVar(loc, None, is_deriv_name),
                       [ResolvedVar(loc, None, d_name)] + arg_vars)
  some_body = Some(loc, BoolType(loc),
                   [(d_name, deriv_type_inst.copy())], is_deriv_call)
  if arity > 0:
    define_body = Lambda(loc, None,
                         [(x, t.copy())
                          for (x, t) in zip(arg_var_names, param_types)],
                         some_body)
  else:
    define_body = some_body
  if typarams:
    define_body = Generic(loc, None, list(typarams), define_body)

  define_decl = Define(loc, pred_name, decl.signature.copy(), define_body,
                       visibility=decl.visibility)

  # 4. Synthesised intro theorems. For each rule we build a Theorem whose
  # statement is the user's rule formula and whose proof:
  #   * `arbitrary` over the bound vars,
  #   * `assume` the premise (if any),
  #   * for each recursive premise, `obtain` the underlying derivation,
  #   * `expand` the predicate, `choose` the rule's derivation
  #     constructor, `expand` the validator, then prove the resulting
  #     conjunction with reflexivity for argument equalities, hypothesis
  #     access for non-recursive premises, and the obtained labels for
  #     recursive premise validators.
  pred_var = lambda l: ResolvedVar(l, None, pred_name)
  is_deriv_var = lambda l: ResolvedVar(l, None, is_deriv_name)
  intro_theorems = []
  for cname, rt in zip(constr_names, rule_translations):
    intro_theorems.append(
      _build_intro_theorem(rt, pred_name, pred_var, is_deriv_var, cname))

  # 5. Synthesised rule-induction and rule-inversion theorems.
  rule_ind_theorem = _build_rule_induction_theorem(
    decl, param_types, rule_translations, constr_names,
    pred_var, is_deriv_var, deriv_type_inst, is_inversion=False)
  rule_inv_theorem = _build_rule_induction_theorem(
    decl, param_types, rule_translations, constr_names,
    pred_var, is_deriv_var, deriv_type_inst, is_inversion=True)

  return [deriv_union, validator, define_decl] + intro_theorems + \
         [rule_ind_theorem, rule_inv_theorem]

def _build_intro_theorem(rt, pred_name, pred_var, is_deriv_var, constr_name):
  """Build a `Theorem` for one rule's intro lemma."""
  loc = rt.rule.location
  hyp_label = generate_proof_name('hyp')
  n_premises = len(rt.premises)

  # Constructor witness: D_<rule>(<bound vars>, <obtained derivation labels>)
  constr_args = [ResolvedVar(loc, None, name) for (name, _) in rt.bound_vars] \
                + [ResolvedVar(loc, None, p.sub_deriv_name)
                   for p in rt.recursive_premises]
  if constr_args:
    constr_witness = Call(loc, None,
                          ResolvedVar(loc, None, constr_name),
                          constr_args)
  else:
    constr_witness = ResolvedVar(loc, None, constr_name)

  # The proof of the validator-body conjunction. Order matches the
  # validator: m_i = c_i for each conclusion arg, then non-recursive
  # premises (in original order), then recursive validators (in original
  # order).
  conjunct_proofs = []
  for _ in rt.conclusion_args:
    conjunct_proofs.append(PReflexive(loc))
  for p in rt.non_recursive_premises:
    if n_premises == 1:
      conjunct_proofs.append(PVar(loc, hyp_label))
    else:
      conjunct_proofs.append(PAndElim(loc, p.orig_idx, PVar(loc, hyp_label)))
  for p in rt.recursive_premises:
    conjunct_proofs.append(PVar(loc, p.deriv_label))

  if not conjunct_proofs:
    inner_proof = PTrue(loc)
  elif len(conjunct_proofs) == 1:
    inner_proof = conjunct_proofs[0]
  else:
    inner_proof = PTuple(loc, conjunct_proofs)

  # expand is_<pred>_deriv to reduce the validator call
  inner_proof = ApplyDefsGoal(loc, [is_deriv_var(loc)], inner_proof)
  # choose the rule's constructor as the existential witness
  inner_proof = SomeIntro(loc, [constr_witness], inner_proof)
  # expand the predicate to expose the existential
  inner_proof = ApplyDefsGoal(loc, [pred_var(loc)], inner_proof)

  # For each recursive premise (innermost-first), wrap in a SomeElim that
  # binds the derivation. Walk in reverse so the first premise ends up as
  # the outermost obtain.
  for p in reversed(rt.recursive_premises):
    is_deriv_call = Call(loc, BoolType(loc), is_deriv_var(loc),
                         [ResolvedVar(loc, None, p.sub_deriv_name)]
                         + [a.copy() for a in p.rec_args])
    if n_premises == 1:
      atom_proof = PVar(loc, hyp_label)
    else:
      atom_proof = PAndElim(loc, p.orig_idx, PVar(loc, hyp_label))
    some_proof = ApplyDefsFact(loc, [pred_var(loc)], atom_proof)
    inner_proof = SomeElim(loc, [p.sub_deriv_name], p.deriv_label,
                           is_deriv_call, some_proof, inner_proof)

  # If there's a premise, wrap in ImpIntro
  if rt.premise_top is not None:
    inner_proof = ImpIntro(loc, hyp_label, rt.premise_top.copy(), inner_proof)

  # Wrap with AllIntro for each bound var (innermost first)
  n_bound = len(rt.bound_vars)
  for i, (vname, vty) in enumerate(reversed(rt.bound_vars)):
    inner_proof = AllIntro(loc, (vname, vty.copy()), (i, n_bound),
                           inner_proof)

  return Theorem(rt.rule.location, rt.rule.name, rt.rule.formula.copy(),
                 inner_proof, False)

# --- rule-induction theorem generator ----------------------------------
#
# For each predicate, generate a theorem `<pred>_rule_induction` that
# states the rule-induction principle. The proof generalises to
# "all d. all xs. if is_<pred>_deriv(d, xs) then M(xs)" and inducts on
# the derivation `union`. Once `rule induction` proof-form sugar lands
# in a follow-up commit, this theorem is the workhorse it desugars to.

def _build_rule_induction_theorem(decl, param_types, rule_translations,
                                  constr_names, pred_var, is_deriv_var,
                                  deriv_type_inst, is_inversion=False):
  """Build the `<pred>_rule_induction` (or `_rule_inversion`) theorem.

  When `is_inversion` is True, generate the strictly weaker inversion
  principle: rule premises are *not* augmented with the motive's
  induction hypothesis, and the per-case premise tuple omits the
  matching `M(<rec args>)` entries. The proof still inducts on the
  derivation `union` (we just don't use the induction hypotheses)."""
  loc = decl.location
  pred_name = decl.name
  base_name(pred_name)
  arity = len(param_types)

  # The theorem's uniquified name was pre-registered in env during
  # Predicate.uniquify so user code referencing `<pred>_rule_induction`
  # (or `_rule_inversion`) resolves correctly.
  thm_name = decl.rule_inversion_name if is_inversion \
             else decl.rule_induction_name

  motive_name = generate_proof_name('M')
  if arity > 0:
    motive_type = FunctionType(loc, [], [t.copy() for t in param_types],
                               BoolType(loc))
  else:
    motive_type = BoolType(loc)

  def motive_var(l):
    return ResolvedVar(l, None, motive_name)

  def apply_motive(args, l=loc):
    if args:
      return Call(l, BoolType(l), motive_var(l), args)
    return motive_var(l)

  def apply_pred(args, l=loc):
    if args:
      return Call(l, BoolType(l), pred_var(l), args)
    return pred_var(l)

  def wrap_alls(formula, vars_with_types):
    n = len(vars_with_types)
    out = formula
    for i, (vname, vty) in enumerate(reversed(vars_with_types)):
      out = All(loc, BoolType(loc), (vname, vty.copy()), (i, n), out)
    return out

  def wrap_all_intros(proof, vars_with_types):
    n = len(vars_with_types)
    out = proof
    for i, (vname, vty) in enumerate(reversed(vars_with_types)):
      out = AllIntro(loc, (vname, vty.copy()), (i, n), out)
    return out

  # ---- statement ----------------------------------------------------------
  rule_conjuncts = []
  for rt in rule_translations:
    if rt.premises:
      augmented = []
      for p in rt.premises:
        augmented.append(p.atom.copy())
        if p.is_recursive and not is_inversion:
          augmented.append(apply_motive([a.copy() for a in p.rec_args]))
      aug_premise = augmented[0] if len(augmented) == 1 \
                    else And(loc, BoolType(loc), augmented)
      conj_inner = IfThen(loc, BoolType(loc), aug_premise,
                          apply_motive([a.copy()
                                        for a in rt.conclusion_args]))
    else:
      conj_inner = apply_motive([a.copy() for a in rt.conclusion_args])
    conj_inner = wrap_alls(conj_inner, list(rt.bound_vars))
    rule_conjuncts.append(conj_inner)

  if not rule_conjuncts:
    rules_hyp_formula = Bool(loc, BoolType(loc), True)
  elif len(rule_conjuncts) == 1:
    rules_hyp_formula = rule_conjuncts[0]
  else:
    rules_hyp_formula = And(loc, BoolType(loc), rule_conjuncts)

  outer_arg_names = [generate_proof_name('x') for _ in range(arity)]
  outer_arg_types_pairs = list(zip(outer_arg_names, param_types))
  pred_call_outer = apply_pred([ResolvedVar(loc, None, x)
                                for x in outer_arg_names])
  main_conc = IfThen(loc, BoolType(loc), pred_call_outer,
                     apply_motive([ResolvedVar(loc, None, x)
                                   for x in outer_arg_names]))
  main_conc = wrap_alls(main_conc, outer_arg_types_pairs)

  full_statement = All(
    loc, BoolType(loc), (motive_name, motive_type), (0, 1),
    IfThen(loc, BoolType(loc), rules_hyp_formula, main_conc))

  # ---- proof body --------------------------------------------------------
  rules_hyp_label = generate_proof_name('rules_hyp')
  helper_label = generate_proof_name('helper')

  # helper formula: all d. all ms. if is_<pred>_deriv(d, ms) then M(ms)
  helper_d_name = generate_proof_name('d')
  helper_m_names = [generate_proof_name('m') for _ in range(arity)]
  helper_m_pairs = list(zip(helper_m_names, param_types))
  helper_validator_call = Call(
    loc, BoolType(loc), is_deriv_var(loc),
    [ResolvedVar(loc, None, helper_d_name)] +
    [ResolvedVar(loc, None, m) for m in helper_m_names])
  helper_inner = IfThen(loc, BoolType(loc), helper_validator_call,
                        apply_motive([ResolvedVar(loc, None, m)
                                      for m in helper_m_names]))
  helper_inner = wrap_alls(helper_inner, helper_m_pairs)
  helper_formula = All(loc, BoolType(loc),
                       (helper_d_name, deriv_type_inst.copy()), (0, 1),
                       helper_inner)

  # ---- per-case proofs ---------------------------------------------------
  ind_cases = []
  for rule_idx, (cname, rt) in enumerate(zip(constr_names, rule_translations)):
    ind_cases.append(_build_rule_induction_case(
      cname, rt, rule_idx, len(rule_translations), pred_var, is_deriv_var,
      apply_motive, apply_pred, rules_hyp_label, arity, param_types,
      wrap_alls, wrap_all_intros, is_inversion))

  helper_proof = Induction(loc, deriv_type_inst.copy(), ind_cases)

  # ---- final assembly ----------------------------------------------------
  final_d_name = generate_proof_name('d')
  final_deriv_label = generate_proof_name('deriv')
  pred_h_label = generate_proof_name('pred_h')

  pred_h_validator = Call(
    loc, BoolType(loc), is_deriv_var(loc),
    [ResolvedVar(loc, None, final_d_name)] +
    [ResolvedVar(loc, None, x) for x in outer_arg_names])

  helper_at_d = AllElim(loc, PVar(loc, helper_label),
                        ResolvedVar(loc, None, final_d_name),
                        (0, 1))
  applied = helper_at_d
  for i, x in enumerate(outer_arg_names):
    applied = AllElim(loc, applied, ResolvedVar(loc, None, x), (i, arity))
  use_helper = ModusPonens(loc, applied, PVar(loc, final_deriv_label))

  pred_h_expanded = ApplyDefsFact(loc, [pred_var(loc)],
                                  PVar(loc, pred_h_label))
  obtain_proof = SomeElim(loc, [final_d_name], final_deriv_label,
                          pred_h_validator, pred_h_expanded, use_helper)

  imp_inner = ImpIntro(loc, pred_h_label, pred_call_outer.copy(),
                       obtain_proof)
  imp_inner = wrap_all_intros(imp_inner, outer_arg_types_pairs)

  proof_body = PLet(loc, helper_label, helper_formula, helper_proof,
                    imp_inner)
  proof_body = ImpIntro(loc, rules_hyp_label, rules_hyp_formula.copy(),
                        proof_body)
  proof_body = AllIntro(loc, (motive_name, motive_type.copy()), (0, 1),
                        proof_body)

  return Theorem(loc, thm_name, full_statement, proof_body, False)

def _build_rule_induction_case(constr_name, rt, rule_idx, n_rules,
                               pred_var, is_deriv_var, apply_motive,
                               apply_pred, rules_hyp_label, arity,
                               param_types, wrap_alls, wrap_all_intros,
                               is_inversion=False):
  """Build one ind_case for the helper's `induction <Deriv>`.

  The case proves: all m1,...,mn. if is_<pred>_deriv(C(<bound>, <subs>), ms)
                                  then M(ms)
  by:
    arbitrary ms;
    assume dh : is_<pred>_deriv(C(...), ms)
    have dh_u := expand is_<pred>_deriv in dh   -- conjunction
    extract m_i = arg_i, recursive validator hits, non-rec premises
    replace each m_i = arg_i in the goal
    rebuild the (M-augmented) premise tuple expected by the rule's
      conjunct of rules_hyp
    apply rules_hyp's conjunct to that
  """
  loc = rt.rule.location
  bound_var_names = [v for (v, _) in rt.bound_vars]
  sub_deriv_names = [p.sub_deriv_name for p in rt.recursive_premises]

  pat_param_names = list(bound_var_names) + list(sub_deriv_names)
  pattern = PatternCons(loc, ResolvedVar(loc, None, constr_name),
                        pat_param_names)

  case_ih_labels = [generate_proof_name('IH') for _ in rt.recursive_premises]
  ind_hyps = []
  for ih_label, p in zip(case_ih_labels, rt.recursive_premises):
    ih_m_names = [generate_proof_name('m') for _ in range(arity)]
    ih_m_vars = [ResolvedVar(loc, None, m) for m in ih_m_names]
    ih_validator = Call(
      loc, BoolType(loc), is_deriv_var(loc),
      [ResolvedVar(loc, None, p.sub_deriv_name)] + ih_m_vars)
    ih_inner = IfThen(loc, BoolType(loc), ih_validator,
                      apply_motive(ih_m_vars))
    ih_inner = wrap_alls(ih_inner, list(zip(ih_m_names, param_types)))
    ind_hyps.append((ih_label, ih_inner))

  m_names = [generate_proof_name('m') for _ in range(arity)]
  m_vars = [ResolvedVar(loc, None, m) for m in m_names]
  m_pairs = list(zip(m_names, param_types))

  constr_args = [ResolvedVar(loc, None, n) for n in bound_var_names] + \
                [ResolvedVar(loc, None, n) for n in sub_deriv_names]
  if constr_args:
    constr_term = Call(loc, None,
                       ResolvedVar(loc, None, constr_name),
                       constr_args)
  else:
    constr_term = ResolvedVar(loc, None, constr_name)

  dh_label = generate_proof_name('dh')
  dh_formula = Call(loc, BoolType(loc), is_deriv_var(loc),
                    [constr_term] + m_vars)

  num_eq = arity
  num_nr = len(rt.non_recursive_premises)
  num_rec = len(rt.recursive_premises)
  total_conjuncts = num_eq + num_nr + num_rec

  dh_unfolded_label = generate_proof_name('dh_u')
  # If total_conjuncts == 1 the validator body isn't a conjunction; we use
  # the unfolded fact directly and conjunct extraction is a no-op.
  def conj_proof(idx):
    if total_conjuncts == 1:
      return PVar(loc, dh_unfolded_label)
    return PAndElim(loc, idx, PVar(loc, dh_unfolded_label))

  # Equality conjuncts: m_i = arg_i. We later `replace` each in the goal.
  eq_proofs = [conj_proof(i) for i in range(num_eq)]

  # Recursive validator hits: indices [num_eq + num_nr ... total_conjuncts)
  rec_validator_proofs = [conj_proof(num_eq + num_nr + i)
                          for i in range(num_rec)]

  # Non-recursive premise atoms: indices [num_eq ... num_eq + num_nr)
  nr_proofs_by_orig_idx = {}
  nr_iter = iter(rt.non_recursive_premises)
  for offset in range(num_nr):
    p = next(nr_iter)
    nr_proofs_by_orig_idx[p.orig_idx] = conj_proof(num_eq + offset)

  rec_validator_by_orig_idx = {}
  rec_iter_idx = 0
  for p in rt.premises:
    if p.is_recursive:
      rec_validator_by_orig_idx[p.orig_idx] = (
        rec_validator_proofs[rec_iter_idx], p)
      rec_iter_idx += 1

  # Build the rules_hyp conjunct proof and the augmented-premise tuple.
  # Rules_hyp's conjunct for this rule has shape
  #   all <bound>. if <augmented premise> then M(<concl args>)
  # Instantiate with the bound vars; modus-ponens with the rebuilt premise.

  # PVar(rules_hyp), narrowed to this rule's conjunct.
  if n_rules == 1:
    conj_of_rules_hyp = PVar(loc, rules_hyp_label)
  else:
    conj_of_rules_hyp = PAndElim(loc, rule_idx, PVar(loc, rules_hyp_label))

  # Instantiate with each bound var.
  applied = conj_of_rules_hyp
  n_bound = len(rt.bound_vars)
  for i, (bv, _) in enumerate(rt.bound_vars):
    applied = AllElim(loc, applied,
                      ResolvedVar(loc, None, bv), (i, n_bound))

  # Build the augmented-premise tuple (in original order):
  #   for each premise atom (orig_idx in rt.premises):
  #     if non-recursive: use its expanded validator conjunct (proof of the
  #       atom verbatim).
  #     if recursive: produce a proof of `<atom> and M(<rec_args>)`:
  #       - <atom> = pred(rec_args). Construct via:
  #           expand pred; choose <sub_deriv_name>; <validator hit>.
  #       - M(rec_args) via the IH:
  #           apply IH[rec_args]... to <validator hit>.
  if rt.premises:
    augmented_proof_parts = []
    for p in rt.premises:
      if p.is_recursive:
        validator_proof, p_info = rec_validator_by_orig_idx[p.orig_idx]
        # Proof of pred(rec_args): expand pred; choose sub_deriv; validator_proof
        atom_proof = ApplyDefsGoal(
          loc, [pred_var(loc)],
          SomeIntro(loc,
                    [ResolvedVar(loc, None, p_info.sub_deriv_name)],
                    validator_proof))
        augmented_proof_parts.append(atom_proof)
        if not is_inversion:
          # Proof of M(rec_args): apply IH[rec_args]... to validator_proof
          ih_idx = list(rt.recursive_premises).index(p_info)
          ih_label = case_ih_labels[ih_idx]
          ih_applied = PVar(loc, ih_label)
          for k, ra in enumerate(p_info.rec_args):
            ih_applied = AllElim(loc, ih_applied, ra.copy(), (k, arity))
          m_proof = ModusPonens(loc, ih_applied, validator_proof)
          augmented_proof_parts.append(m_proof)
      else:
        # Non-recursive: the atom's proof is the validator's matching conjunct.
        augmented_proof_parts.append(nr_proofs_by_orig_idx[p.orig_idx])

    if len(augmented_proof_parts) == 1:
      premise_tuple = augmented_proof_parts[0]
    else:
      premise_tuple = PTuple(loc, augmented_proof_parts)

    final_apply = ModusPonens(loc, applied, premise_tuple)
  else:
    final_apply = applied

  # Replace each m_i with arg_i (so the goal M(m_1,...,m_n) becomes
  # M(arg_1,...,arg_n) which `final_apply` proves).
  if eq_proofs:
    body = RewriteGoal(loc, list(eq_proofs), final_apply)
  else:
    body = final_apply

  # Have dh_unfolded := expand validator in dh, with the right shape.
  if total_conjuncts == 1:
    dh_unfolded_formula = _build_validator_body_formula(
      rt, m_vars, is_deriv_var, pred_var, loc)
  else:
    dh_unfolded_formula = _build_validator_body_formula(
      rt, m_vars, is_deriv_var, pred_var, loc)

  body = PLet(loc, dh_unfolded_label, dh_unfolded_formula,
              ApplyDefsFact(loc, [is_deriv_var(loc)], PVar(loc, dh_label)),
              body)
  body = ImpIntro(loc, dh_label, dh_formula, body)
  body = wrap_all_intros(body, m_pairs)

  return IndCase(loc, pattern, ind_hyps, body)

def _build_validator_body_formula(rt, m_vars, is_deriv_var, pred_var, loc):
  """The conjunction the validator-body unfolds to for this rule."""
  clauses = []
  for (m_var, c) in zip(m_vars, rt.conclusion_args):
    clauses.append(Call(loc, BoolType(loc),
                        ResolvedVar(loc, None, '='),
                        [m_var, c.copy()]))
  for p in rt.non_recursive_premises:
    clauses.append(p.atom.copy())
  for p in rt.recursive_premises:
    clauses.append(Call(
      loc, BoolType(loc), is_deriv_var(loc),
      [ResolvedVar(loc, None, p.sub_deriv_name)] +
      [a.copy() for a in p.rec_args]))
  if not clauses:
    return Bool(loc, BoolType(loc), True)
  if len(clauses) == 1:
    return clauses[0]
  return And(loc, BoolType(loc), clauses)
  """Walk a premise looking for occurrences of the predicate. The
  `forbidden` flag flips on under 'not' / 'if/then' premises and stays on
  through subsequent nesting (sticky semantics, matching the union check)."""
  match formula:
    case Call(loc, _, rator, args):
      ratname = None
      if isinstance(rator, VarRef):
        ratname = rator.get_name()
      if forbidden and ratname == pred_name:
        user_error(loc,
              keyword + " '" + base_name(pred_name) + "' must not occur "
              "in a negative position (under 'not' or to the left of an "
              "inner 'then') of its own introduction rules; this would "
              "make the definition circular and inconsistent.\n"
              "In rule '" + base_name(rule.name) + "'.")
      for a in args:
        _walk_pred_premise(a, pred_name, keyword, rule, forbidden)
    case OverloadedVar(loc, _, rns):
      ref = rns[0]
      if forbidden and ref == pred_name:
        user_error(loc,
              keyword + " '" + base_name(pred_name) + "' must not occur "
              "in a negative position of its own introduction rules.\n"
              "In rule '" + base_name(rule.name) + "'.")
    case IfThen(loc, _, prem, conc):
      _walk_pred_premise(prem, pred_name, keyword, rule, forbidden=True)
      _walk_pred_premise(conc, pred_name, keyword, rule, forbidden)
    case And(loc, _, parts):
      for a in parts:
        _walk_pred_premise(a, pred_name, keyword, rule, forbidden)
    case Or(loc, _, parts):
      for a in parts:
        _walk_pred_premise(a, pred_name, keyword, rule, forbidden)
    case All(loc, _, _, _, body):
      _walk_pred_premise(body, pred_name, keyword, rule, forbidden)
    case Some(loc, _, _, body):
      _walk_pred_premise(body, pred_name, keyword, rule, forbidden)
    case _:
      pass

def process_declaration_visibility(decl : Declaration, env: Env, module_chain, downstream_needs_checking):
  match decl:
    case Define(loc, name, ty, body):
      if ty == None:
        new_body = type_synth_term(body, env, None, [])
        new_ty = new_body.typeof
      else:
        check_type(ty, env)
        new_body = body
        new_ty = ty

      # Only allow overloading of functions
      unique_name = {base_name(n): n for n in env.dict.keys()}
      orig_name = base_name(name)
      if orig_name in unique_name.keys():
          match new_ty:
            case FunctionType(_, _, params, _):
              pass
            case _:
              binding = env.dict[unique_name[orig_name]]
              user_error(loc, 'the name ' + orig_name + ' is already defined:\n' \
                    + error_header(binding.location) \
                    + ' ' + orig_name + ' : ' + str(binding) + '\n' \
                    + 'Only functions may have multiple definitions with the same name.')
      decl.typ = new_ty
      return Define(loc, name, new_ty, new_body,
                    visibility=decl.visibility), \
              env.declare_term_var(loc, name, new_ty,
                                   visibility=decl.visibility)
  
    case RecFun(loc, name, typarams, params, returns, _):
      body_env = env.declare_type_vars(loc, typarams)
      check_type(returns, body_env)
      for t in params:
          check_type(t, body_env)
      fun_type = FunctionType(loc, typarams, params, returns)
      # print('process declaration:')
      # print(decl.pretty_print(4))
      return decl, env.declare_term_var(loc, name, fun_type,
                                        visibility=decl.visibility)

    case GenRecFun(loc, name, typarams, param_pairs, returns, _, measure_ty,
                   body, _):
      body_env = env.declare_type_vars(loc, typarams)
      check_type(returns, body_env)
      for (p,t) in param_pairs:
          if t:
              check_type(t, body_env)
      [p for (p,t) in param_pairs]
      param_types = [t for (p,t) in param_pairs]
      if any([t == None for t in param_types]):
          user_error(loc, 'Add type annotations to the parameters.')

      fun_type = FunctionType(loc, typarams, param_types, returns)
      # print('process declaration:')
      # print(decl.pretty_print(4))
      check_type(measure_ty, env)
      # return? GenRecFun(loc, name, typarams, params, returns, measure, measure_ty, body, terminates)
      # changed to decl
      return (decl, env.declare_term_var(loc, name, fun_type,
                                         visibility=decl.visibility))

    case ViewRecFun(loc, name, typarams, param_pairs, returns, _, _):
      body_env = env.declare_type_vars(loc, typarams)
      check_type(returns, body_env)
      for (p,t) in param_pairs:
          if t:
              check_type(t, body_env)
      param_types = [t for (p,t) in param_pairs]
      if any([t == None for t in param_types]):
          user_error(loc, 'Add type annotations to the parameters.')
      if len(param_pairs) == 0:
          user_error(loc, 'viewrec needs at least one parameter to recurse on.')

      fun_type = FunctionType(loc, typarams, param_types, returns)
      return (decl, env.declare_term_var(loc, name, fun_type,
                                         visibility=decl.visibility))
  
    case Union(loc, name, typarams, alts):
      env = env.define_type(loc, name, decl, decl.visibility)
      # ResolvedVar is a VarRef in the class hierarchy but acts as a
      # Type wherever a Deduce type is named by an identifier (e.g.
      # `T<X>` parses to `TypeInst(typ=ResolvedVar("T"), ...)`).
      # Cast at the construction sites rather than widening every
      # `typ: Type` annotation across abstract_syntax.py.
      union_type = cast(Type, ResolvedVar(loc, None, name))
      body_env = env.declare_type_vars(loc, typarams)
      body_union_type = union_type
      infer_param_polarities(decl, body_env)
      new_alts = []
      for constr in alts:
        constr_type: Type
        if len(constr.parameters) > 0:
          if len(typarams) > 0:
            tyvars = [cast(Type, ResolvedVar(loc, None, p)) for p in typarams]
            return_type: Type = TypeInst(loc, body_union_type, tyvars)
          else:
            return_type = body_union_type
          # Narrow each constructor parameter's type. The check_type
          # return goes back into the new Constructor so the union's
          # AST has ResolvedVars in place of single-candidate
          # OverloadedVars.
          new_params = []
          for ty in constr.parameters:
            new_ty = check_type(ty, body_env)
            check_strict_positivity(new_ty, name, body_env)
            new_params.append(new_ty)
          constr_type = FunctionType(constr.location, typarams,
                                     new_params, return_type)
          new_constr = Constructor(constr.location, constr.name, new_params)
        elif len(typarams) > 0:
          constr_type = GenericUnknownInst(loc, union_type)
          new_constr = constr
        else:
          constr_type = union_type
          new_constr = constr

        env = env.declare_term_var(loc, constr.name, constr_type,
                                   visibility=decl.visibility)
        new_alts.append(new_constr)
      return Union(loc, name, typarams, new_alts, visibility=decl.visibility), env

    case Import(loc, name, ast, visibility=vis):
      old_verbose = get_verbose()
      if get_verbose() == VerboseLevel.CURR_ONLY:
        set_verbose(VerboseLevel.NONE)

      if name in module_chain:
          user_error(loc, 'error, recusive import:\n\t' + name\
                + '\nwhile processing files:\n\t' \
                + ', '.join(module_chain))
      elif name in imported_modules:
          set_verbose(old_verbose)
          if name in dirty_files:
              downstream_needs_checking[0] = True
          return Import(loc, name, ast, visibility=vis), env
      else:
          current_module = env.get_current_module()
          imported_modules.add(name)
          module_chain = [name] + module_chain

          filename = find_file(loc, name)
          needs_checking = [get_check_imports() and is_modified(filename)]

          ast2 = []
          assert ast is not None
          for s in ast:
            new_s, env = process_declaration(s, env, module_chain, needs_checking)
            ast2.append(new_s)

          ast3 = []
          already_done_imports : dict[str, bool] = {}
          for s in ast2:
            new_s = type_check_stmt(s, env, already_done_imports)
            if new_s != None:
              ast3.append(new_s)

          if needs_checking[0]:
              dirty_files.add(name)
              downstream_needs_checking[0] = True
            
          if needs_checking[0] and name not in checked_modules:
              if get_quiet_mode() == False:
                  print('> checking ' + name)
              
          for s in ast3:
            env = collect_env(s, env)

            # TODO: only check if the pf file is newer than the thm file
            if name not in checked_modules and needs_checking[0]:
              check_proofs(s, env)
            
          if name not in checked_modules:
            checked_modules.add(name)  

          set_verbose(old_verbose)

          if needs_checking[0]:
            print_theorems(filename, ast3)
          
          return Import(loc, name, ast3, visibility=decl.visibility), \
              env.declare_module(current_module)

    case Predicate(loc, name, typarams, sig, rules, keyword):
      if typarams:
        # Generic predicates / relations are syntactically accepted but
        # the translation isn't yet finished: the auto-generated intro
        # theorems (and the rule_induction / rule_inversion theorems)
        # would each need an outer `all <T>:type. ...` quantifier, the
        # synthesised proofs would need to thread `arbitrary <T>:type`
        # through, and every internal reference to the predicate /
        # validator / constructors would need explicit type
        # instantiation. None of that is hard, just additive — flagged
        # for a follow-up commit.
        user_error(loc,
              "generic " + keyword + "s (with '<...>' type parameters) "
              "are not yet supported. Drop the type parameter list and "
              "specialise to a concrete type for now; full generics "
              "land in a follow-up commit.")

      body_env = env.declare_type_vars(loc, typarams)

      arity, param_types = _validate_predicate_signature(sig, name, keyword,
                                                         body_env)

      _predicate_style_hint(loc, name, keyword, arity)

      # Register the predicate as a term-var so calls to it in rule bodies
      # type-check correctly. The predicate's full type combines the outer
      # type parameters from `predicate FOO<...>` with anything declared
      # inside the signature itself.
      pred_type: Type
      if isinstance(sig, FunctionType):
        pred_type = FunctionType(sig.location,
                                 list(typarams) + list(sig.type_params),
                                 sig.param_types, sig.return_type)
      else:
        pred_type = sig
      rule_env = body_env.declare_term_var(loc, name, pred_type,
                                           visibility=decl.visibility)

      for rule in rules:
        _validate_predicate_rule_shape(rule, name, keyword, arity, rule_env)
        # Type-check the rule's body. This catches argument-type mismatches
        # in both the conclusion and the premises (which the shape pass does
        # not look at), and is what makes `even(true)` an error here rather
        # than later in the pipeline.
        check_formula(rule.formula, rule_env)

      for rule in rules:
        _check_predicate_strict_positivity(rule, name, keyword, body_env)

      # Translation: lower this predicate to a Define (impredicative
      # encoding) plus one Postulate per rule. The generated decls are
      # threaded through the rest of the pipeline inline (mirroring how
      # Import processes its sub-AST), then stashed on the Predicate AST
      # node so the outer passes can recognise it as already handled.
      translated = _build_predicate_translation(decl, param_types)

      processed = []
      for s in translated:
        new_s, env = process_declaration(s, env, module_chain,
                                         downstream_needs_checking)
        processed.append(new_s)

      typed = []
      inline_imports : dict[str, bool] = {}
      for s in processed:
        new_s = type_check_stmt(s, env, inline_imports)
        if new_s is not None:
          typed.append(new_s)

      for s in typed:
        env = collect_env(s, env)

      decl.translated_ast = typed
      return decl, env

    case _:
      internal_error(decl.location, "unrecognized declaration:\n" + str(decl))


def process_declaration(stmt : Statement, env : Env, module_chain, downstream_needs_checking):
  if get_verbose():
    print('process_declaration(' + str(stmt) + ')')
    
  match stmt:
    case Declaration():
      return process_declaration_visibility(stmt, env, module_chain, downstream_needs_checking)
          
    case Theorem(loc, name, _, _):
      return stmt, env
  
    case Postulate(loc, name, _):
      return stmt, env
  
    case Assert(loc, _):
      return stmt, env
  
    case Print(loc, _):
      return stmt, env

    case Auto(loc, name):
      return stmt, env
  
    case Associative(loc, typarams, _, typeof):
      body_env = env.declare_type_vars(loc, typarams)
      check_type(typeof, body_env)
      return stmt, env
  
    case Export(loc, name):
      return stmt, env
        
    case Module(loc, name):
      return stmt, env.declare_module(name)
    
    case Trace(loc, name):
      return stmt, env
    
    case Inductive(loc, typ, name):
      # `inductive Foo by ...` names a union by its bare name; suppress
      # the generic-arity check so `inductive Foo by ...` works when Foo
      # is a generic union. The `case Inductive(...)` in check_proofs
      # enforces that ``typ`` is a ``VarRef``.
      check_type(typ, env, arity_required=False)
      return stmt, env
  
    case _:
      internal_error(stmt.location, "in process_declaration, unrecognized statement:\n" + str(stmt))

def type_check_fun_case(fun_case, name, params, returns, body_env, cases_present):
    body_env = check_pattern(fun_case.pattern, params[0], body_env, cases_present)
    fun_case.rator = type_synth_term(fun_case.rator, body_env, None, [])
    if len(fun_case.parameters) != len(params[1:]):
      user_error(fun_case.location, 'incorrect number of parameters, '\
            + 'expected ' + str(len(params)))
    body_env = body_env.declare_term_vars(fun_case.location,
                                          zip(fun_case.parameters, params[1:]))
    match fun_case.pattern:
      case PatternCons(_, _, parameters):
        pat_params = parameters
      case PatternBool(_, _):
        pat_params = []
    new_body = type_check_term(fun_case.body, returns, body_env, name, pat_params)
    check_no_recfun_escape(new_body, name)
    return FunCase(fun_case.location, fun_case.rator,
                   fun_case.pattern, fun_case.parameters, new_body)

def _viewrec_function_type(loc, typarams, params, returns):
  new_typarams = [generate_proof_name(t) for t in typarams]
  sub = {x: ResolvedVar(loc, None, y) for (x,y) in zip(typarams, new_typarams)}
  return FunctionType(loc, new_typarams,
                      [t.substitute(sub) for (_, t) in params],
                      returns.substitute(sub))

def _viewrec_placeholder(loc, name, typarams, params, returns, visibility):
  return GenRecFun(loc, name, typarams, params, returns,
                   ResolvedVar(loc, None, params[0][0]), params[0][1],
                   Hole(loc, None), PSorry(loc), True,
                   visibility=visibility)

def _viewrec_recursive_binders(pattern, rec_ty, env):
  binders = []
  match pattern:
    case PatternCons(_, _, params):
      for name in params:
        ty = env.get_type_of_term_var(ResolvedVar(pattern.location, None, name))
        if ty == rec_ty:
          binders.append(name)
  return binders

def type_check_viewrec(stmt, env):
  loc = stmt.location
  name = stmt.name
  typarams = stmt.type_params
  param_pairs = stmt.vars
  returns = stmt.returns
  view = stmt.view
  cases = stmt.cases

  body_env = env.declare_type_vars(loc, typarams)
  checked_params = [(x, check_type(t, body_env)) for (x, t) in param_pairs]
  checked_returns = check_type(returns, body_env)
  fun_type = _viewrec_function_type(loc, typarams, checked_params,
                                    checked_returns)
  fun_value = _viewrec_placeholder(loc, name, typarams, checked_params,
                                   checked_returns, stmt.visibility)
  env = env.define_term_var(loc, name, fun_type, fun_value, stmt.visibility)
  case_env = env.declare_type_vars(loc, typarams)
  case_env = case_env.declare_term_vars(loc, checked_params)

  checked_view = type_synth_term(view, case_env, None, [])
  view_ty = checked_view.typeof
  cases_present = {}
  new_cases = []
  reset_recursive_call_count()
  rec_ty = checked_params[0][1]

  for c in cases:
    new_env = check_pattern(c.pattern, view_ty, case_env, cases_present)
    subterms = _viewrec_recursive_binders(c.pattern, rec_ty, new_env)
    new_body = type_check_term(c.body, checked_returns, new_env, name, subterms)
    check_no_recfun_escape(new_body, name)
    new_cases.append(SwitchCase(c.location, c.pattern, new_body))

  uniondef = lookup_union(loc, view_ty, env)
  for alt in uniondef.alternatives:
    if alt.name not in cases_present.keys():
      user_error(loc, 'viewrec is missing a view case for ' + base_name(alt.name))

  if get_recursive_call_count() == 0:
      user_error(loc, name + ' is declared viewrec, but does not make any recursive calls.\n' \
            + 'Use a "fun" statement instead.')

  body = Switch(loc, checked_returns, checked_view, new_cases)
  measure = ResolvedVar(loc, rec_ty, checked_params[0][0])
  return GenRecFun(loc, name, typarams, checked_params, checked_returns,
                   measure, rec_ty, body, PSorry(loc), True,
                   visibility=stmt.visibility)

def type_check_stmt(stmt, env, error_on_next_import : dict[str, bool]):
  if get_verbose():
    print('type_check_stmt(' + str(stmt) + ')')
  match stmt:
    case Define(loc, name, ty, body):
      if ty == None:
        new_body = body # already type checked in process_declaration
        new_ty = body.typeof
      else:
        new_ty = check_type(ty, env)
        new_body = type_check_term(body, new_ty, env, None, [])
      return Define(loc, name, new_ty, new_body, visibility=stmt.visibility)
        
    case Theorem(loc, name, frm, pf, isLemma):
      new_frm = check_formula(frm, env)
      return Theorem(loc, name, new_frm, pf, isLemma)

    case Postulate(loc, name, frm):
      new_frm = check_formula(frm, env)
      return Postulate(loc, name, new_frm)

    case Predicate():
      # The translation is processed inline during process_declaration
      # (`stmt.translated_ast` is the result). The wrapper itself has
      # nothing more to type-check.
      return stmt

    case RecFun(loc, name, typarams, params, returns, cases):
      # alpha rename the type parameters in the function's type
      new_typarams = [generate_proof_name(t) for t in typarams]
      sub = {x: ResolvedVar(loc, None, y) for (x,y) in zip(typarams, new_typarams)}
      new_params = [p.substitute(sub) for p in params]
      new_returns = returns.substitute(sub)
      fun_type = FunctionType(loc, new_typarams, new_params, new_returns)

      env = env.define_term_var(loc, name, fun_type, stmt.reduce(env),
                                stmt.visibility)
      cases_present: dict = {}
      body_env = env.declare_type_vars(loc, typarams)
      # Narrow params and returns once we have body_env (with the
      # original typarams in scope, since `params`/`returns` reference
      # them, not `new_typarams`).
      checked_params = [check_type(p, body_env) for p in params]
      checked_returns = check_type(returns, body_env)
      reset_recursive_call_count()
      new_cases = [type_check_fun_case(c, name, checked_params, checked_returns,
                                       body_env, cases_present) \
                   for c in cases]
      if get_recursive_call_count() == 0:
          user_error(loc, name + ' is declared recursive, but does not make any recursive calls.\n' \
                + 'Use a "fun" statement instead.')

      # check for completeness of cases
      uniondef = lookup_union(checked_params[0].location, checked_params[0], env)
      for c in uniondef.alternatives:
        if not c.name in cases_present.keys():
          user_error(loc, 'missing function case for ' + base_name(c.name))

      return RecFun(loc, name, typarams, checked_params, checked_returns,
                    new_cases, visibility=stmt.visibility)

    case GenRecFun(loc, name, typarams, param_pairs, returns, measure, measure_ty,
                   body, terminates):
      # alpha rename the type parameters in the function's type
      new_typarams = [generate_proof_name(t) for t in typarams]
      sub = {x: ResolvedVar(loc, None, y) for (x,y) in zip(typarams, new_typarams)}
      new_param_pairs = [(x,p.substitute(sub)) for (x,p) in param_pairs]
      new_returns = returns.substitute(sub)
      fun_type = FunctionType(loc, new_typarams, [t for (x,t) in new_param_pairs],
                              new_returns)

      env = env.define_term_var(loc, name, fun_type, stmt.reduce(env),
                                stmt.visibility)

      body_env = env.declare_type_vars(loc, typarams)
      body_env = body_env.declare_term_vars(loc, param_pairs)
      new_measure = type_check_term(measure, measure_ty, body_env, None, [])

      new_body = type_check_term(body, returns, body_env, None, [])

      new_recfun = GenRecFun(loc, name, typarams, param_pairs, returns,
                             new_measure, measure_ty, new_body, terminates,
                             stmt.trusted_terminates,
                             visibility=stmt.visibility)
      # print('type check stmt:')
      # print(new_recfun.pretty_print(4))
      return new_recfun

    case ViewRecFun(loc, name, typarams, param_pairs, returns, view, cases):
      if len(param_pairs) == 0:
        user_error(loc, 'viewrec needs at least one parameter to recurse on.')
      return type_check_viewrec(stmt, env)
    
    case Trace(loc, var):
      var_ty = env.get_type_of_term_var(var)
      match var_ty:
        case FunctionType(_, _, _, _):
          pass
        case _:
          user_error(var.location, 'trace expects an identifer of type function, but instead got type ' + str(var_ty))
      return stmt
  
    case Union(loc, name, typarams, _):
      return stmt
  
    case Export(loc, name):
        return stmt
    
    case Import(loc, name, _):
      if name in error_on_next_import:
        if error_on_next_import[name]:
          # The first import was from the prelude
          # So instead of erroring we'll error next time
          # and return None to signal that this stmt should be removed
          error_on_next_import[name] = True
          return None # Return none to signify that this stmt should be removed
        else:
          # The user manually imported the module twice, so throw an error
          user_error(loc, "error, module:\n\t" + name + "\nwas imported twice")

      # If loc is empty then this import comes from the prelude
      error_on_next_import[name] = loc.empty
      return stmt
  
    case Assert(loc, frm):
      new_frm = check_formula(frm, env)
      return Assert(loc, new_frm)
  
    case Print(loc, trm):
      new_trm = type_synth_term(trm, env, None, [])
      return Print(loc, new_trm)

    case Auto(loc, name):
      return Auto(loc, name)
  
    case Associative(loc, typarams, op, typ):
      new_op = type_synth_term(op, env, None, [])
      return Associative(loc, typarams, new_op, typ)
  
    case Module(loc, name):
      return stmt

    case Inductive(loc, ty, name):
      return Inductive(loc, ty, name)
  
    case _:
      internal_error(stmt.location,
                     "type checking, unrecognized statement:\n" + str(stmt))

def validate_conjunct(loc, conj, fun):
  match conj:
    case All(loc1, _, (_, ty), _, body):
      # Make sure that  body is valid
      # Am I checking that all parameters are used? No.
      if validate_conjunct(loc, body, fun):
        return conj
      pass
    case Call(loc1, _, rator, args):
      # Make sure rator is correct
      if rator.name != fun:
        user_error(loc1, "Expected call to be " + fun)
      return conj
    case IfThen(loc1, ty, prem, conc):
      # Make sure that prem and conclusion are both calls?
      return IfThen(loc1, ty, validate_conjunct(loc, prem, fun), validate_conjunct(loc, conc, fun))
    case And(loc1, ty, args):
      return And(loc1, ty, [validate_conjunct(loc, a, fun) for a in args])
    case _:
      user_error(loc, "invalid conjunct form")

def extract_conjuncts(prem, fun):
  match prem:
    case And(loc, _, args):
      return [validate_conjunct(loc, c, fun) for c in args]
    case _:
      return [validate_conjunct(prem.location, prem, fun)]

def generate_conjunct_body(loc, conjunct, case, fun_var, subst, env, param_i = 0, case_hint = None):
  if get_verbose():
    print("generate_conjunct_body", conjunct)
  if case_hint is None:
    case_hint = _custom_induction_case_hint(conjunct)
  match conjunct:
    case All(_, _, (name, ty), _, body):
      if len(case.pattern.parameters) <= param_i:
        user_error(case.pattern.location, "custom induction case pattern is missing a bound variable"
              + "\nExpected a case shaped like:\n" + case_hint)
      inst_name = case.pattern.parameters[param_i]
      subst[inst_name]= ResolvedVar(loc, ty, name)
      env = env.declare_term_var(loc, inst_name, ty)
      return AllIntro(loc, (inst_name, ty), (0, 1), 
                      generate_conjunct_body(loc, body, case, fun_var, subst, env, param_i + 1, case_hint))
    case IfThen(loc, ty, _, conc):
      ind_hyp = generate_proof_name("_")
      if len(case.induction_hypotheses) > 0:
        ind_hyp = case.induction_hypotheses[0][0]
        case.induction_hypotheses = case.induction_hypotheses[1:]
      return ImpIntro(loc, ind_hyp, None, generate_conjunct_body(loc, conc, case, fun_var, subst, env, param_i, case_hint))
    case Call(loc, ty, rator, [arg]):
      match case.pattern:
        case PatternTerm(loc, _, _):
          try:
            case.pattern.term = type_check_term(case.pattern.term, arg.typeof.substitute(subst), env, None, [])
          except UserError as e:
            user_error(case.pattern.location, "problem type checking custom induction pattern"
                  + "\nExpected a case shaped like:\n" + case_hint
                  + "\n" + str(e))
          new_case = case.pattern.term.copy()
          new_case = new_case.substitute(subst)
          if new_case != arg:
            user_error(case.pattern.location, "custom induction pattern did not match"
                  + "\nExpected a case shaped like:\n" + case_hint
                  + "\nThe pattern\n\t" + str(case.pattern.term)
                  + "\ndid not match\n\t" + str(arg))

        case PatternBool():
          user_error(case.pattern.location, "boolean patterns are not allowed in custom induction"
                + "\nExpected a case shaped like:\n" + case_hint)
        # TODO: Do I really need to handle constructors without parameters differently?
        case PatternCons(loc, constructor, []):
          if isUInt(arg):
            i = uintToInt(arg)
            if i == 0 and base_name(constructor.name) == 'zero':
              pass
            else:
              user_error(case.pattern.location, "custom induction pattern did not match UInt literal " + str(i)
                    + "\nExpected a case shaped like:\n" + case_hint)
          else:
            arg = type_synth_term(arg, env, False, [])
            constructor = type_check_term(constructor,  arg.typeof, env, False, [])
            if constructor != arg:
              print(type(constructor), constructor, type(arg), arg)
              print(case.pattern.parameters)
              internal_error(loc, "Pattern mismatch !!!")
        case PatternCons(loc, constructor, args):
          match arg: # This is in the actual theorem conjunct
            case Call(loc, ty, rator, call_args):
              constructor = type_check_term(constructor, rator.typeof, env, False, [])
              rator_eq = rator == constructor
              # Need to use subst into args, which are strings
              new_args = [subst[a] for a in args]
              args_eq = len(new_args) == len(call_args) and all([arg1 == arg2 for arg1,arg2 in zip(new_args, call_args)])

              if not (args_eq and rator_eq):
                user_error(case.pattern.location, "custom induction pattern did not match"
                      + "\nExpected a case shaped like:\n" + case_hint)
            case _:
              user_error(case.pattern.location, "custom induction case expected a constructor-like pattern"
                    + "\nExpected a case shaped like:\n" + case_hint)
        case _:
          internal_error("Unsupported pattern type: " + str(type(case.pattern)))
      return case.body
    case _:
      return case.body

def match_induction_generics(frm):
  match frm:
    case All(_, _, (name, ty), _, body) if isinstance(ty, TypeType):
      new_frm, tys = match_induction_generics(body)
      return new_frm, [name] + tys
    case _:
      return frm, []

def match_induction_fun(frm, ty_tys, ind_ty):
  match frm:
    case All(loc, _, (_, FunctionType(_, _, [param_ty], BoolType())), _, body):
      type_mismatch = False
      match param_ty:
        case TypeInst(_, typ, ps):
          if len(ps) != len(ty_tys):
            user_error(loc, "Theorem and predicate should have the same number of type parameters")
          # TODO: Name should be defined for the parameters all the time?
          if not all([isinstance(x, VarRef) and x.name == y for x, y in zip(ps, ty_tys)]):
            print(ps, ty_tys)
            user_error(loc, "Theorem type params don't match function type params for inductive declaration")
          type_mismatch = ind_ty != typ
        case Var() | OverloadedVar() | ResolvedVar():
          type_mismatch = ind_ty != param_ty
        case _:
          print(type(param_ty), param_ty)
          internal_error(loc, "Should be unreachable but want to handle well?")

      if type_mismatch:
        user_error(loc, "Type mismatch in inductive declaration")
    
      return body, *frm.var
    case _:
      user_error(frm.location, "Expected to see a function from the inductive type to bool")

def match_induction_conjuncts(frm, fun, fun_ty, ind_ty):
  match frm:
    case IfThen(loc, _, prem, conc):
      conjuncts = extract_conjuncts(prem, fun)

      expected_conc = All(loc, None, ('x', ind_ty), (0, 1),
                       Call(loc, fun_ty, ResolvedVar(loc, None, fun), [ResolvedVar(loc, None, 'x')]))

      match conc:
        case All(_, _, (name, _), _, Call(loc, _, rator, [arg])) \
          if rator.name == fun and arg.name == name:
            pass
        case _:
          user_error(conc.location, "Invalid form for inductive conclusion. Expected:\n\t" + str(expected_conc))
      
      return conjuncts
    case _:
      user_error(frm.location, "Invalid form for inductive declaration theorem. \
            Inductive theorems should be of the form: \n\t \
            all P : fn T -> bool. if prem then all x : T. P(x)")

def match_induction(frm, ind_ty):
  new_frm, ty_tys = match_induction_generics(frm)
  new_frm, fun, fun_ty = match_induction_fun(new_frm, ty_tys, ind_ty)
  conjuncts = match_induction_conjuncts(new_frm, fun, fun_ty, ind_ty)

  return {"tys": ty_tys, "conjuncts": conjuncts, "fun": fun, "ind_ty": ind_ty, "fun_ty": fun_ty}

def collect_env(stmt, env : Env):
  if get_verbose():
    print('collect_env(' + str(stmt) + ')')
  match stmt:
    case Define(loc, name, ty, body):
      return env.define_term_var(loc, name, ty, body, stmt.visibility)
      
    case RecFun(loc, name, typarams, params, returns, _):
      fun_type = FunctionType(loc, typarams, params, returns)
      return env.define_term_var(loc, name, fun_type, stmt,
                                 stmt.visibility)

    case GenRecFun(loc, name, typarams, params, returns, _, _,
                  body, _):
      fun_type = FunctionType(loc, typarams, [t for (x,t) in params], returns)
      return env.define_term_var(loc, name, fun_type, stmt,
                                 stmt.visibility)

    case ViewRecFun(loc, name, typarams, params, returns, _, _):
      fun_type = FunctionType(loc, typarams, [t for (x,t) in params], returns)
      return env.define_term_var(loc, name, fun_type, stmt,
                                 stmt.visibility)
      
    case Union(loc, name, typarams, _):
      return env
          
    case Theorem(loc, name, frm, _, _):
      return env.declare_proof_var(loc, name, frm)

    case Postulate(loc, name, frm):
      return env.declare_proof_var(loc, name, frm)

    case Predicate():
      # Already collected inline during process_declaration.
      return env

    case Export(loc, name, _):
      return env

    case Import(loc, name, _):
      return env
  
    case Assert(loc, frm):
      return env
  
    case Print(loc, _):
      return env

    case Module(loc, name):
      return env.declare_module(name)
  
    case Auto(loc, name):
      frm = env.get_formula_of_proof_var(name)
      return env.declare_auto_rewrite(loc, frm)
    
    case Inductive(loc, typ, name):
      frm = env.get_formula_of_proof_var(name)
      if not isinstance(typ, VarRef):
        user_error(loc, "Only able to declare uninstantiated union types inductive")
      return env.declare_inductive(loc, match_induction(frm, typ), name)

      # Types, Predicate.
      # IfThen, Ands, all

      # Check that frm is a valid induction theorem, 
      # then declare it with the things it needs in the environment

        
    case Associative(loc, typarams, op, typ):
      # Example proof of associativity:
      # all U :type. all xs :List<U>, ys :List<U>, zs:List<U>. (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
      m_name = generate_proof_name("m")
      m_var = ResolvedVar(loc, typ, m_name)
      n_name = generate_proof_name("n")
      n_var = ResolvedVar(loc, typ, n_name)
      o_name = generate_proof_name("o")
      o_var = ResolvedVar(loc, typ, o_name)
      def makeOp(left, right):
          return Call(loc, typ, op, [left,right])
      assoc_formula = mkEqual(loc, makeOp(makeOp(m_var, n_var), o_var),
                              makeOp(m_var, makeOp(n_var, o_var)))
      vars = [(m_name, typ), (n_name, typ), (o_name, typ)]
      for i, var in enumerate(reversed(vars)):
        assoc_formula = All(loc, None, var, (i,len(vars)), assoc_formula)
      
      for i, tp_name in enumerate(reversed(typarams)):
        assoc_formula = All(loc, None, (tp_name, TypeType(loc)), (i, len(typarams)), assoc_formula)

      assoc_formula = type_check_formula(assoc_formula, env)

      # determine which overload is for the given typ
      resolved_op = None
      op_ty = env.get_type_of_term_var(op)
      match op_ty:
          case OverloadType(_, overloads):
              for (x, funty) in overloads:
                  match funty:
                      case FunctionType(_, typarams2, param_types, _):
                          try:
                              matching: dict = {}
                              type_match(loc, typarams2, param_types[0], typ, matching)
                              resolved_op = x
                              break
                          except MatchFailed:
                              continue
          case FunctionType(_, typarams2, param_types, _):
              assert isinstance(op, VarRef)
              resolved_op = op.get_name()
      if assoc_formula in env.proofs():
          return env.declare_assoc(loc, resolved_op, typarams, typ)
      else:
          user_error(loc, 'Could not find a proof of\n\t' + str(assoc_formula))
  
    case Trace(loc, function_name):
      return env.declare_tracing(function_name.get_name())

    case _:
      internal_error(stmt.location, "collect_env, unrecognized statement:\n" + str(stmt))


@dataclass
class RecCall:
  vars: List[Tuple[str,Type]]  # variables introduced by switch cases
  conditions: List[Term]
  args: List[Term]    

def add_condition(cond, call):
    return RecCall(call.vars, [cond] + call.conditions, call.args)

def add_vars(vars, call):
    return RecCall(vars + call.vars, call.conditions, call.args)

def find_rec_calls(name, term, env):
  match term:
    case TermInst(loc2, _, subject, _, _):
      return find_rec_calls(name, subject, env)
    case Var() | OverloadedVar() | ResolvedVar():
      return []
    case Bool(loc2, _, _):
      return []
    case And(loc2, _, args):
      return sum([find_rec_calls(name, arg, env) for arg in args], [])
    case Or(loc2, _, args):
      return sum([find_rec_calls(name, arg, env) for arg in args], [])
    case IfThen(loc2, _, prem, conc):
      return find_rec_calls(name, prem, env) + find_rec_calls(name, conc, env)
    case All(loc2, _, _, _, frm2):
      return find_rec_calls(name, frm2, env)
    case Some(loc2, _, _, frm2):
      return find_rec_calls(name, frm2, env)
    case Call(loc2, _, rator, args):
      calls = find_rec_calls(name, rator, env) + \
          sum([find_rec_calls(name, arg, env) for arg in args], [])
      if rator_name(rator) == name:
          return [RecCall([], [], args)] + calls
      else:
          return calls
    case Switch(loc2, _, subject, cases):
      calls = []
      for c in cases:
        c_body_calls = find_rec_calls(name, c.body, env)
        match c.pattern:
          case PatternBool(loc3, value):
            cond = mkEqual(loc3, subject, value)
            new_c_body_calls = [add_condition(cond, call) for call in c_body_calls]
          case PatternCons(loc3, cons, params):
            cond = mkEqual(loc3, subject, pattern_to_term(c.pattern))
            new_c_body_calls = [add_condition(cond, call) for call in c_body_calls]
            cases_present = {}
            new_cons, params_types = check_constructor_pattern(
                loc3, cons, params, subject.typeof, env, cases_present)
            c.pattern.constructor = new_cons
            new_c_body_calls = [add_vars(params_types, call) for call in new_c_body_calls]
        calls += new_c_body_calls
      return calls
  
    case RecFun(_, name, _, params, _, cases):
      return []
    case GenRecFun(_, name, _, params, _, _, _,
                   body, _):
      return []
    case Conditional(loc2, _, cond, thn, els):
      thn_calls = find_rec_calls(name, thn, env)
      els_calls = find_rec_calls(name, els, env)
      new_thn_calls = [add_condition(cond, call) for call in thn_calls]
      not_cond = IfThen(loc2, None, cond, Bool(loc2, None, False))
      new_els_calls = [add_condition(not_cond, call) for call in els_calls]
      return find_rec_calls(name, cond, env) + new_thn_calls + new_els_calls
    case Lambda(loc2, _, _, body):
      return find_rec_calls(name, body, env)
    case Generic(loc2, _, _, body):
      return find_rec_calls(name, body, env)
    case TAnnote(loc2, _, subject, _):
      return find_rec_calls(name, subject, env)
    case ArrayGet(loc2, _, arr, ind):
      return find_rec_calls(name, arr, env) \
          + find_rec_calls(name, ind, env)
    case Array(loc2, _, elements):
      return sum([find_rec_calls(name, elt, env) for elt in elements], [])
    case MakeArray(loc2, _, subject):
      return find_rec_calls(name, subject, env)
    case TLet(loc2, _, _, rhs, body):
      return find_rec_calls(name, rhs, env) \
          + find_rec_calls(name, body, env)
    case Hole(loc2, _):
      return []
    case Omitted(loc2, _):
      return []
    case _:
      internal_error(getattr(term, 'location', None),
                     'in find_rec_calls, unhandled ' + str(term))
    

def check_proofs(stmt, env: Env):
  if get_verbose():
    print('\n\ncheck_proofs(' + str(stmt) + ')')
  # Phase 5 / Step 21 hook: trap before evaluating each top-level
  # statement.  ``get_debugger()`` returns ``None`` in the common case
  # (no debug session attached), so non-debug runs pay one attribute
  # load and a None-check per statement -- well below the noise floor
  # of the surrounding match dispatch.  Step 22: ``env`` is passed in
  # so ``print <expr>`` and breakpoint conditions can be evaluated in
  # the current scope.
  _dbg = get_debugger()
  if _dbg is not None:
    _dbg.on_statement(stmt, env)
  match stmt:
    case Define(loc, name, _, body):
      pass
    case Theorem(loc, name, frm, pf, _):
      if get_verbose():
        print('checking proof of theorem ' + base_name(name))
      _try_check_proof_of(pf, frm, env)
      
    case Postulate(loc, name, frm):
      pass

    case Predicate():
      pass

    case RecFun(loc, name, typarams, params, _, _):
      pass

    case GenRecFun(loc, name, typarams, params, _, measure, _,
                   body, terminates):
      if stmt.trusted_terminates:
        return
      body_env = env.declare_type_vars(loc, typarams)
      
      # find recursive calls in the body
      calls = find_rec_calls(name, body, body_env)
      formulas: list[Formula] = []

      # create a formula Fi for each
      for call in calls:
        lhs = measure.substitute({x: arg for ((x,t),arg) in zip(params,call.args)})
        rhs = measure.copy()
        #less = env.base_to_unique('<') # This doesn't work!
        less_ovlds = env.base_to_overloads('<')
        less = OverloadedVar(loc, None, less_ovlds)
        # `Call` is a Term in the class hierarchy but acts as a Formula
        # when its return type is Bool (here: `<` overloads).
        less_frm = cast(Formula, Call(loc, None, less, [lhs,rhs]))
        condition = And(loc, None, call.conditions) \
            if len(call.conditions) > 0 else None
        # `frm` is a name reused by the outer `match stmt:` Theorem
        # arm at line 5129 (also a Formula); the annotation lives there.
        frm = IfThen(loc, None, condition, less_frm) if condition is not None else less_frm
        i = 0
        for var in reversed(call.vars):
            frm = All(loc, None, var, (i,len(call.vars)),frm)
            i += 1
        formulas.append(frm)

      # combine into formula: all params. F1 and ... and Fn
      formula: Formula
      if len(formulas) > 1:
          formula = And(loc, None, formulas)
      elif len(formulas) == 1:
          formula = formulas[0]
      else:
          user_error(loc, 'There were no recursive calls in the body of this recfun')
      for (x,t) in reversed(params):
          formula = All(loc, None, (x,t), (0,1), formula)
      formula = check_formula(formula, body_env)

      # check that the terminates proof proves the above formula
      _try_check_proof_of(terminates, formula, body_env)
  
    case Union(loc, name, typarams, _):
      pass
  
    case Export(loc, name):
      pass
  
    case Import(loc, name, _):
      pass
  
    case Print(loc, trm):
      set_reduce_all(True)
      set_eval_all(True)
      result = trm.reduce(env)
      set_eval_all(False)
      set_reduce_all(False)
      print(str(result))
      
    case Assert(loc, frm):
      match frm:
        case Call(_, _, rator, [lhs, rhs]) if isinstance(rator, VarRef) and rator.get_name() == '=':
          set_reduce_all(True)
          set_eval_all(True)
          L = lhs.reduce(env)
          R = rhs.reduce(env)
          set_eval_all(False)
          set_reduce_all(False)
          if L == R:
            pass
          else:
              user_error(loc, 'assertion failed:\n' +
                    '\t' + str(L) + ' ≠ ' + str(R) + '\n')
        case IfThen(_, _,
                    Call(_, _, rator, [lhs, rhs]),
                    Bool(_, _, False)) if isinstance(rator, VarRef) and rator.get_name() == '=':
          set_reduce_all(True)
          set_eval_all(True)
          L = lhs.reduce(env)
          R = rhs.reduce(env)
          set_eval_all(False)
          set_reduce_all(False)
          if L != R:
            pass
          else:
              user_error(loc, 'assertion failed:\n' +
                    '\t' + str(L) + ' = ' + str(R) + '\n')
        case _:
          set_reduce_all(True)
          set_eval_all(True)
          result = frm.reduce(env)
          set_eval_all(False)
          set_reduce_all(False)
          match result:
            case Bool(_, _, True):
              pass
            case Bool(_, _, False):
              user_error(loc, 'assertion failed: ' + str(frm))
            case result:
              user_error(loc, 'assertion expected Boolean result, not ' \
                    + str(result))

    case Auto(loc, _):
      pass
  
    case Associative(loc, typarams, _, _):
      pass
  
    case Inductive():
      pass
  
    case Module(loc, name):
      pass

    case Trace(loc, _):
      pass

    case _:
      internal_error(stmt.location, "check_proofs: unrecognized statement:\n" + str(stmt))

  if _dbg is not None:
    _dbg.after_statement(stmt, env)

def check_deduce(ast: List[Statement], module_name: str, modified: bool,
                 tracing_functions: List[str],
                 error_sink: Optional[ErrorSink] = None) -> List[Statement]:
  """Run the four-phase pipeline (process_declarations, type_check_stmt,
  collect_env, check_proofs) over ``ast``.

  ``error_sink``: when ``None`` (default), exceptions raised by any
  phase propagate immediately — the historical CLI / goal_at / MCP
  behaviour. When given an :class:`ErrorSink`, each top-level
  statement runs inside a per-phase try/except: a raised exception is
  appended to the sink, the failing statement is dropped from the
  remaining phases, and processing continues to the next statement.
  ``lsp.query.check`` opts in to this so every user error and every ``?``
  hole in the file becomes a separate diagnostic instead of just the
  first one.

  The recovery boundary is the top-level statement; deep
  ``user_error()`` / ``incomplete_error()`` calls keep raising as before
  (refactoring 200+ raise sites to plumb a sink through every helper
  would require each site to invent a "what to return" continuation,
  with no benefit over a top-loop catch).
  """
  env = Env()
  env = env.declare_module(module_name)
  imported_modules.clear()
  needs_checking = [modified]

  prev_sink = get_active_sink()
  set_active_sink(error_sink)
  try:
    return _check_deduce_body(
      ast, module_name, modified, tracing_functions, error_sink, env, needs_checking
    )
  finally:
    set_active_sink(prev_sink)


def _check_deduce_body(ast, module_name, modified, tracing_functions, error_sink, env, needs_checking):
  """Body of ``check_deduce``, split out so the ``_active_sink``
  push/pop in the caller stays a tidy try/finally."""
  
  def _collect_diagnostic(exc):
    """Append ``exc`` to the sink, or re-raise when no sink is set."""
    if error_sink is None:
      raise exc
    error_sink.add(exc)

  if get_verbose():
      print('--------- Processing Declarations ------------------------')
  # Hash each statement structurally as we go.  Used by the
  # check_proofs cache below; computed here so we visit each AST
  # only once.  ``_hash_ast`` skips the ``location`` field, so two
  # parses of the same source produce matching hashes.
  # ``ast2_pairs`` collects (post-decl AST, hash) pairs only for
  # statements whose declaration phase succeeded; failed statements
  # are dropped here so they don't show up in later phases.
  ast2_pairs = []
  for s in ast:
    sh = _hash_ast(s)
    try:
      new_s, env = process_declaration(s, env, [module_name], needs_checking)
    except Diagnostic as e:
      _collect_diagnostic(e)
      continue
    ast2_pairs.append((new_s, sh))
  if get_verbose():
    for s, _ in ast2_pairs:
      print(s)

  for func_name in tracing_functions:
    # TODO: base_to_unique is a hack so use another function instead
    new_name = env.base_to_unique(func_name)
    if new_name is None:
      print("Couldn't find function to trace:", func_name)
    else:
      env = env.declare_tracing(new_name)

  if get_verbose():
    print('--------- Type Checking ------------------------')
  ast3 = []
  ast3_hashes = []

  error_on_next_import : dict[str, bool] = {}
  for s, sh in ast2_pairs:
    try:
      new_s = type_check_stmt(s, env, error_on_next_import)
    except Diagnostic as e:
      _collect_diagnostic(e)
      continue
    # If None gets returned we want to remove the current statement
    # Which is represented by not appending it to the new ast
    if new_s != None:
      ast3.append(new_s)
      ast3_hashes.append(sh)
  if get_verbose():
    for s in ast3:
      print(s)

  if get_verbose():
    print('--------- Proof Checking ------------------------')
  if module_name not in checked_modules:
    if get_verbose() and needs_checking[0]:
        print('checking ' + module_name)
    # Per-statement cache for ``check_proofs`` (Steps 13 + 14).
    # Earlier loops (``process_declaration``, ``type_check_stmt``)
    # emit AST nodes whose ``Meta`` locations participate in
    # side-effecting behaviour (e.g. the ``target_hole_location``
    # flag used by ``goal_at`` to single out which `?` raises), so
    # caching their outputs across calls would let stale locations
    # leak into a new run.  ``check_proofs`` itself is the bulk of
    # the time and its only persistent effect is "verified" -- safe
    # to cache.
    #
    # Step 14: the cache key is ``(stmt_hash, deps_fingerprint,
    # target, module_name)`` where ``deps_fingerprint`` folds in
    # only the prior statements *this* statement actually references
    # (plus any global-barrier statements -- ``Import`` / ``Auto``
    # -- whose effects are observable everywhere downstream).
    # Editing an unrelated theorem leaves ``deps_fingerprint``
    # unchanged, so the entry hits.
    #
    # ``target`` is in the key so a different ``goal_at`` target
    # doesn't reuse a verdict made under the previous target (a `?`
    # that was previously treated as ``sorry`` should now raise, or
    # vice versa).
    target = get_target_hole_location()
    defined_to_idx: dict = {}
    barrier_idxs: set = set()
    auto_idxs: list = []
    stmt_hashes_so_far: list = []
    for i, (s, sh) in enumerate(zip(ast3, ast3_hashes)):
      try:
        env = collect_env(s, env)
      except Diagnostic as e:
        # collect_env failed -- skip check_proofs for this stmt and
        # the bookkeeping below. Append to ``stmt_hashes_so_far`` so
        # subsequent indices keep lining up with ``ast3`` for the
        # dependency lookup.
        _collect_diagnostic(e)
        stmt_hashes_so_far.append(sh)
        continue
      referenced = _collect_referenced_names(s)
      # ``auto`` declarations register theorems as implicit rewrite
      # rules consulted by every later proof.  A proof can rely on
      # an auto'd theorem without textually referencing it, so each
      # prior ``Auto``'s referenced names also contribute to this
      # statement's dependency set -- editing the auto'd theorem
      # then invalidates downstream proofs that relied on it
      # implicitly.
      for j in auto_idxs:
        referenced |= _collect_referenced_names(ast3[j])
      dep_idxs = set(barrier_idxs)
      for n in referenced:
        j = defined_to_idx.get(n)
        if j is not None:
          dep_idxs.add(j)
      deps_fingerprint = hash(
        tuple(stmt_hashes_so_far[j] for j in sorted(dep_idxs))
      )
      key = ("check_proofs", sh, deps_fingerprint, target, module_name)
      if needs_checking[0]:
        # ``Print`` and ``Assert`` have observable side effects in
        # ``check_proofs`` (printing a value, raising on a failed
        # assertion).  Their cache key is fully determined by the
        # statement's text and its dependency set, so two identical
        # ``print zero`` lines hash to the same key -- caching the
        # verdict would skip the side effect on every duplicate.
        # Bypass the cache for them; ``check_proofs`` on these is
        # cheap anyway.
        try:
          pre_n = len(get_active_sink()) if get_active_sink() is not None else 0
          # Phase 5 / Step 21: when a debugger is attached, every
          # ``check_proofs`` call must run its hooks -- a cache hit
          # would silently skip the trap.  Re-check unconditionally;
          # this also avoids polluting the cache with cache-key
          # collisions caused by debugger-driven reduction order.
          if get_debugger() is not None:
            check_proofs(s, env)
            _record_miss("check_proofs")
          elif isinstance(s, (Print, Assert)):
            check_proofs(s, env)
            _record_miss("check_proofs")
          elif key in _stmt_cache:
            _record_hit("check_proofs")
          else:
            check_proofs(s, env)
            # Don't cache if check_proofs absorbed errors into the
            # sink -- next run must re-check so the diagnostic is
            # re-emitted.
            if get_active_sink() is None or len(get_active_sink()) == pre_n:
              _stmt_cache[key] = True
            _record_miss("check_proofs")
        except Diagnostic as e:
          # Don't update the cache on failure -- next run will
          # re-check this stmt, which is what we want once the user
          # fixes it.
          _collect_diagnostic(e)
      # Bookkeeping for the next iteration -- happens regardless of
      # ``needs_checking`` so the dependency map stays consistent.
      # ``defined_to_idx`` is updated *after* the dep lookup so a
      # statement's self-references (e.g. recursive functions) do
      # not get treated as a self-dependency.
      if _is_global_barrier(s):
        barrier_idxs.add(i)
      if isinstance(s, Auto):
        auto_idxs.append(i)
      for n in _collect_defined_names(s):
        defined_to_idx[n] = i
      stmt_hashes_so_far.append(sh)
    checked_modules.add(module_name)
  # Sanity-check the post-typecheck AST: every variable reference
  # should be ``ResolvedVar`` (or, if a real overload couldn't be
  # resolved, a multi-candidate ``OverloadedVar``). Any pre-uniquify
  # ``Var`` or single-candidate ``OverloadedVar`` is a refactor leak.
  check_post_typecheck_invariants(ast3)
  # Return the post-typecheck AST so callers (lsp.library.check_file,
  # the Deduce-to-C compiler) can read the overload-resolved form.
  # See issue #305.
  return ast3
