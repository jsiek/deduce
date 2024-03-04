# TODO
# check well-formedness of types

from abstract_syntax import *
from error import error
from parser import parse, set_filename
from env import Env

verbose = False

def set_verbose(b):
  global verbose
  verbose = b

def get_verbose():
  global verbose
  return verbose

name_id = 0

def generate_name(name):
    global name_id
    ls = name.split('.')
    new_id = name_id
    name_id += 1
    return ls[0] + '.' + str(new_id)
  
def check_implies(loc, frm1, frm2):
  if verbose:
    print('check_implies? ' + str(frm1) + ' => ' + str(frm2))
  match frm2:
    case Bool(loc, True):
      return
    case And(loc, args):
      for arg2 in args:
        check_implies(loc, frm1, arg2)
    case Or(loc, args):
      for arg2 in args:
        try:
          check_implies(loc, frm1, arg2)
          return
        except Exception as e:
          continue
      error(loc, 'expected ' + str(frm2) + '\nbut only have ' + str(frm1))
    case IfThen(loc2, prem2, conc2):
      match frm1:
        case IfThen(loc1, prem1, conc1):
          check_implies(loc, prem2, prem1)
          check_implies(loc, conc1, conc2)
        case _:
          error(loc, 'expected ' + str(frm2) + '\nbut only have ' + str(frm1))
    case _:
      match frm1:
        case Bool(loc, False):
          return
        case And(loc, args1):
          for arg1 in args1:
            try:
              check_implies(loc, arg1, frm2)
              return
            except Exception as e:
              continue
          error(loc, 'expected ' + str(frm2) + '\nbut only have ' + str(frm1))
        case _:
          if frm1 != frm2:
            error(loc, 'expected ' + str(frm2) + '\nbut only have ' + str(frm1))
            
def instantiate(loc, allfrm, args):
  match allfrm:
    case All(loc2, vars, frm):
      if len(args) == len(vars):
        sub = {var[0]: arg for (var,arg) in zip(vars,args)}
        ret = frm.substitute(sub)
        return ret
      else:
        error(loc, 'expected ' + str(len(vars)) + ' arguments, ' \
              + 'not ' + str(len(args)))
    case _:
      error(loc, 'expected all formula to instantiate, not ' + str(allfrm))
  
def str_of_env(env):
  return '{' + ', '.join([k + ": " + str(e) for (k,e) in env.items()]) + '}'

def pattern_to_term(pat):
  match pat:
    case PatternCons(loc, constr, params):
      if len(params) > 0:
        return Call(loc, TVar(loc, constr), [TVar(loc, param) for param in params],
                    False)
      else:
        return TVar(loc, constr)
    case _:
      error(pat.location, "expected a pattern, not " + str(pat))

def rewrite(loc, formula, equation):
  (lhs, rhs) = split_equation(loc, equation)
  if get_verbose():
    print('rewrite? ' + str(formula) \
          + '\nlhs:     ' + str(lhs) + ' is ' + str(formula == lhs))
  if formula == lhs:
    return rhs
  match formula:
    case TVar(loc2, name):
      return formula
    case And(loc2, args):
      return And(loc2, [rewrite(loc, arg, equation) for arg in args])
    case Or(loc2, args):
      return Or(loc2, [rewrite(loc, arg, equation) for arg in args])
    case IfThen(loc2, prem, conc):
      return IfThen(loc2, rewrite(loc, prem, equation),
                    rewrite(loc, conc, equation))
    case All(loc2, vars, frm2):
      # TODO, deal with variable clash
      return All(loc2, vars, rewrite(loc, frm2, equation))
    # case PrimitiveCall(loc2, op, args):
    #   return PrimitiveCall(loc2, op,
    #                        [rewrite(loc, arg, equation) for arg in args])
    case Call(loc2, rator, args, infix):
      return Call(loc2, rewrite(loc, rator, equation),
                  [rewrite(loc, arg, equation) for arg in args],
                  infix)
    case _:
      return formula
      # error(loc, 'in rewrite, unhandled ' + str(formula))

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
      case (Lambda(l1, vs1, body1), Lambda(l2, vs2, body2)):
        ren = {x: TVar(l1, y) for (x,y) in zip(vs1, vs2)}
        return isolate_difference(body1.substitute(ren), body2)
      case (Call(l1, fun1, args1, infix1), Call(l2, fun2, args2, infix2)):
        if fun1 == fun2:
          return isolate_difference_list(args1, args2)
        else:
          return (fun1, fun2)
      case (SwitchCase(l1, p1, body1), SwitchCase(l2, p2, body2)):
        if p1 == p2:
          return isolate_difference(body1, body2)
        else:
          return (p1, p2)
      case (Switch(l1, s1, cs1), Switch(l2, s2, cs2)):
        if s1 == s2:
          return isolate_difference_list(cs1, cs2)
        else:
          return (s1, s2)
      case _:
        return (term1, term2)
    

def check_proof(proof, env):
  if verbose:
    print('synthesize formula while checking proof') ; print('\t' + str(proof))
  ret = None
  match proof:
    case RewriteFact(loc, subject, equation_proof):
      formula = check_proof(subject, env)
      equation = check_proof(equation_proof, env)
      new_formula = rewrite(loc, formula, equation)
      ret = new_formula
    case PHole(loc):
      error(loc, 'unfinished proof')
    case PVar(loc, name, index):
      # TODO:
      ret = env.get(loc, name, index)
      # problem: IndCase used for switch and induction, but
      # binding structure is different (IH, EQ)
      # (fixed, probably)
      #ret = env.lookup(name)
      if not ret:
        error(loc, 'undefined label ' + name)
    case PTrue(loc):
      ret = Bool(loc, True)
    case PLet(loc, label, frm, reason, rest):
      check_formula(frm, env)
      check_proof_of(reason, frm, env)
      body_env = env.declare_proof_var(loc, label, frm)
      ret = check_proof(rest, body_env)
    case PAnnot(loc, claim, reason):
      check_formula(claim, env, env)
      check_proof_of(reason, claim, env)
      ret = claim
    case PTuple(loc, pfs):
      frms = [check_proof(pf, env) for pf in pfs]
      ret = And(loc, frms)
    case ImpIntro(loc, label, prem, body):
      check_formula(prem, env)
      body_env = env.declare_proof_var(loc, label, prem)
      conc = check_proof(body, body_env)
      ret = IfThen(loc, prem, conc)
    case AllIntro(loc, vars, body):
      body_env = env.declare_term_vars(vars)
      formula = check_proof(body, body_env)
      ret = All(loc, vars, formula)
    case AllElim(loc, univ, args):
      allfrm = check_proof(univ, env)
      arg_types = [type_synth_term(arg, env, None, []) for arg in args]
      match allfrm:
        case All(loc2, vars, frm):
          for ((var,ty), arg_ty) in zip(vars, arg_types):
            if ty != arg_ty:
              error(loc, 'to instantiate: ' + str(allfrm) \
                    + '\nexpected argument of type: ' + str(ty) \
                    + '\nnot: ' + str(arg_ty))
        case _:
          error(loc, 'expected all formula to instantiate, not ' + str(allfrm))
      return instantiate(loc, allfrm, args)
    case Apply(loc, imp, arg):
      ifthen = check_proof(imp, env)
      match ifthen:
        case IfThen(loc, prem, conc):
          check_proof_of(arg, prem, env)
          ret = conc
        case _:
          error(loc, 'expected an if-then, not ' + str(ifthen))
    case PInjective(loc, eq_pf):
      formula = check_proof(eq_pf, env)
      (a,b) = split_equation(loc, formula)
      match (a,b):
        case (Call(loc2,TVar(loc3,f1),[arg1], infix1),
              Call(loc4,TVar(loc5,f2),[arg2]), infix2):
          if f1 != f2:
            error(loc, 'in injective, ' + f1 + ' ≠ ' + f2)
          if not is_constructor(f1, env):
            error(loc, 'in injective, ' + f1 + ' not a constructor')
          return mkEqual(loc, arg1, arg2)
        case _:
          error(loc, 'in injective, non-applicable formula: ' + str(formula))
    case PSymmetric(loc, eq_pf):
      frm = check_proof(eq_pf, env)
      (a,b) = split_equation(loc, frm)
      return mkEqual(loc, b, a)
    case _:
      error(proof.location, 'in check_proof, unhandled ' + str(proof))
  if verbose:
    print('\t=> ' + str(ret))
  return ret


def check_proof_of(proof, formula, env):
  if verbose:
    print('nts: ' + str(formula) + '?')
    print('\t' + str(proof))
  match proof:
    case PHole(loc):
      print('environment:\n' + str(env))
      error(loc, 'unfinished proof:\n' + str(formula))
    
    case PReflexive(loc):
      match formula:
        case Call(loc2, TVar(loc3, '='), [lhs, rhs], _):
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
            error(proof.location, msg)
        case _:
          error(proof.location, 'reflexive proves an equality, not ' \
                + str(formula))
          
    case PSymmetric(loc, eq_pf):
      (a,b) = split_equation(loc, formula)
      flip_formula = mkEqual(loc, b, a)
      check_proof_of(eq_pf, flip_formula, env)

    case PTransitive(loc, eq_pf1, eq_pf2):
      (a1,c) = split_equation(loc, formula)
      eq1 = check_proof(eq_pf1, env)
      (a2,b) = split_equation(loc, eq1)
      check_proof_of(eq_pf2, mkEqual(loc, b, c), env)
      if a1 != a2:
        error(loc, 'for transitive, ' + str(a1) + ' ≠ ' + str(a2))

    case PInjective(loc, eq_pf):
      (a,b) = split_equation(loc, formula)
      flip_formula = mkEqual(loc, Call(loc, TVar(loc,'suc'), [a], False),
                             Call(loc, TVar(loc,'suc'), [b], False))
      check_proof_of(eq_pf, flip_formula, env)
        
    case AllIntro(loc, vars, body):
      match formula:
        case All(loc2, vars2, formula2):
          if len(vars) != len(vars2):
            error(proof.location, 'mismatch in number of variables')
          sub = {}
          index = 0
          for (var,var2) in reversed(list(zip(vars,vars2))):
            sub[ var2[0] ] = TVar(loc, var[0], index)
            index += 1
          frm2 = formula2.substitute(sub)
          body_env = env.declare_term_vars(loc, vars)
          check_proof_of(body, frm2, body_env)

    case ImpIntro(loc, label, None, body):
      match formula:
        case IfThen(loc, prem, conc):
          body_env = env.declare_proof_var(loc, label, prem)
          check_proof_of(body, conc, body_env)
        case _:
          error(proof.location, 'expected proof of if-then, not ' + str(proof))
          
    case ImpIntro(loc, label, prem1, body):
      check_formula(prem1, env)
      match formula:
        case IfThen(loc, prem2, conc):
          prem1_red = prem1.reduce(env)
          prem2_red = prem2.reduce(env)
          if prem1_red != prem2_red:
            error(loc, 'mismatch in premise:\n' \
                  + str(prem1_red) + '\n≠ ' + str(prem2_red))
          body_env = env.declare_proof_var(loc, label, prem1_red)
          check_proof_of(body, conc, body_env)
        case _:
          error(proof.location, 'expected proof of if-then, not ' + str(proof))
      
    case PLet(loc, label, frm, reason, rest):
      check_formula(frm, env)
      check_proof_of(reason, frm, env)
      body_env = env.declare_proof_var(loc, label, frm)
      check_proof_of(rest, formula, body_env)
    case Cases(loc, subject, cases):
      sub_frm = check_proof(subject, env)
      match sub_frm:
        case Or(loc, frms):
          for (frm, (label,case)) in zip(frms, cases):
            body_env = env.declare_proof_var(loc, label, frm)
            check_proof_of(case, formula, body_env)
        case _:
          error(proof.location, "expected 'or', not " + str(sub_frm))
    case Induction(loc, typ, cases):
      match typ:
        case TypeName(l1, n, i):
          tname = typ
        case TypeInst(l1, n, type_args, i):
          tname = TypeName(l1, n, i)
      match env.get_binding_of_type_var(tname).defn:
        case Union(loc2, name, typarams, alts):
          for (constr,indcase) in zip(alts, cases):
            if indcase.pattern.constructor != constr.name:
              error(indcase.location, "expected a case for " + constr.name \
                    + " not " + indcase.pattern.constructor)
            if len(indcase.pattern.parameters) != len(constr.parameters):
              error(indcase.location, "expected " + len(constr.parameters) \
                    + " arguments to " + constr.name \
                    + " not " + len(indcase.pattern.parameters))
            induction_hypotheses = [instantiate(loc, formula, [TVar(loc,param)])
                                    for (param, typ) in 
                                    zip(indcase.pattern.parameters,
                                        constr.parameters)
                                    if typ.name == type_name]
            if len(induction_hypotheses) > 1:
              induction_hypotheses = And(indcase.location, induction_hypotheses)
            elif len(induction_hypotheses) == 1:
              induction_hypotheses = induction_hypotheses[0]
            body_env = env.declare_proof_var(loc, 'IH', induction_hypotheses)
            trm = pattern_to_term(indcase.pattern)
            goal = instantiate(loc, formula, [trm])
            if len(typarams) > 0:
              sub = { T: ty for (T,ty) in zip(typarams, typ.arg_types)}
              parameter_types = [p.substitute(sub) for p in constr.parameters]
            else:
              parameter_types = constr.parameters
            body_env = body_env.declare_term_vars(loc, zip(indcase.pattern.parameters,
                                                           parameter_types))
            check_proof_of(indcase.body, goal, body_env)
        case _:
          error(loc, "induction expected name of union, not " + type_name)

    case SwitchProof(loc, subject, cases):
      ty = type_synth_term(subject, env, None, [])
      match ty:
        case TypeName(loc2, name, index):
          tname = ty
        case _:
          error(loc, 'expected term of union type, not ' + str(ty))
      match env.get_binding_of_type_var(tname).defn:
        case Union(loc2, name, typarams, alts):
          for (constr,scase) in zip(alts, cases):
            if scase.pattern.constructor != constr.name:
              error(scase.location, "expected a case for " + constr.name \
                    + " not " + scase.pattern.constructor)
            if len(scase.pattern.parameters) != len(constr.parameters):
              error(scase.location, "expected " + len(constr.parameters) \
                    + " arguments to " + constr.name \
                    + " not " + len(scase.pattern.parameters))
            body_env = env.declare_proof_var('EQ', mkEqual(scase.location, 
                                                           subject,
                                                           pattern_to_term(scase.pattern)))
            body_env = body_env.declare_term_vars(loc, zip(scase.pattern.parameters,
                                                           constr.parameters))
            check_proof_of(scase.body, formula, body_env)
        case _:
          error(loc, "switch expected union type, not " + type_name)
          
    case RewriteGoal(loc, equation_proof, body):
      equation = check_proof(equation_proof, env)
      new_formula = rewrite(loc, formula, equation)
      check_proof_of(body, new_formula, env)
    case _:
      form = check_proof(proof, env)
      check_implies(proof.location, form.reduce(env), formula.reduce(env))

def type_match(loc, tyvars, param_ty, arg_ty, matching):
  if get_verbose():
    print("type_match(" + str(param_ty) + "," + str(arg_ty) + ")")
    print("\tin  " + str(tyvars))
    print("\twith" + str(matching))
  match (param_ty, arg_ty):
    case (TypeName(l1, n1, i1), TypeName(l2, n2, i2)) if n1 == n2 and i1 == i2:
      pass
    case (TypeName(l1, name, index), _) if param_ty in tyvars:
      if name in matching.keys():
        type_match(loc, tyvars, matching[name], arg_ty, matching)
      else:
        matching[name] = arg_ty
    case (FunctionType(l1, tv1, pts1, rt1), FunctionType(l2, tv2, pts2, rt2)) \
        if len(tv1) == len(tv2) and len(pts1) == len(pts2):
        tyvars = [ty.shift(0, len(tv1)) for ty in tyvars]
        for (pt1, pt2) in zip(pts1, pts2):
          type_match(loc, tyvars, pt1, pt2, matching)
        type_match(loc, tyvars, rt1, rt2, matching)
    case (TypeInst(l1, n1, args1), TypeInst(l2, n2, args2)):
      if n1 != n2 or len(args1) != len(args2):
        error(loc, "argument type: " + str(arg_ty) + "\n" \
              + "does not match parameter type: " + str(param_ty))
      for (arg1, arg2) in zip(args1, args2):
        type_match(loc, tyvars, arg1, arg2, matching)
    # How to handle GenericType?
    case (TypeInst(l1, n1, args1), GenericType(l2, n2)):
      if n1 != n2:
        error(loc, "argument type: " + str(arg_ty) + "\n" \
              + "does not match parameter type: " + str(param_ty))
    case _:
      if param_ty != arg_ty:
        error(loc, "argument type: " + str(arg_ty) + "\n" \
              + "does not match parameter type: " + str(param_ty))
    

def type_names(loc, names):
  index = 0
  result = []
  for n in reversed(names):
    result.insert(0, TypeName(loc, n, index))
    index += 1
  return result

def type_check_call_helper(loc, funty, args, env, recfun, subterms, ret_ty):
  match funty:
    case FunctionType(loc2, typarams, param_types, return_type):
      if len(typarams) == 0:
        for (param_type, arg) in zip(param_types, args):
          type_check_term(arg, param_type, env, recfun, subterms)
        return return_type
      else:
        matching = {}
        # If there is an expected return type, match that first.
        type_params = type_names(loc, typarams)
        if ret_ty:
          type_match(loc, type_params, return_type, ret_ty, matching)
        # If we have already deduced the type parameters in the parameter type,
        # then we can check the term. Otherwise, we synthesize the term's type
        # and match it against the parameter type.
        for (arg, param_ty) in zip(args, param_types):
            param_type = param_ty.substitute(matching)
            fvs = param_type.free_vars().intersection(set(type_params))
            if len(fvs) == 0:
              type_check_term(arg, param_type, env, recfun, subterms)
            else:
              arg_ty = type_synth_term(arg, env, recfun, subterms)
              type_match(loc, type_params, param_type, arg_ty, matching)
        inst_return_type = return_type.substitute(matching)
        return inst_return_type
    case _:
      error(loc, 'expected operator to have function type, not ' + str(funty))
      
def type_check_call(loc, rator, args, env, recfun, subterms, ret_ty):
  ty = type_synth_term(rator, env, recfun, subterms)
  return type_check_call_helper(loc, ty, args, env, recfun, subterms, ret_ty)

def type_check_rec_call(loc, tvar, args, env, recfun, subterms, ret_ty):
  match args[0]:
    case TVar(loc3, arg_name):
        if not (arg_name in subterms):
          error(loc, "ill-formed recursive call, " \
                + "expected first argument to be " \
                + " or ".join(subterms) + ", not " + arg_name)
    case _:
      error(loc, "ill-formed recursive call, " \
            + "expected first argument to be " \
            + " or ".join(subterms) + ", not " + str(args[0]))
  return type_check_call(loc, tvar, args, env, recfun, subterms, ret_ty)

# well-formed types?
def check_type(typ, env):
  match typ:
    case TypeName(loc, name, index):
      b = env.get_binding_of_type_var(typ)
      if not b:
        error(loc, 'undefined type variable ' + str(typ))
    case IntType(loc):
      pass
    case BoolType(loc):
      pass
    case TypeType(loc):
      pass
    case FunctionType(loc, typarams, param_types, return_type):
      env = env.declare_type_vars(loc, typarams)
      for ty in param_types:
        check_type(ty, env)
      check_type(return_type, env)
    case TypeInst(loc, name, arg_types, index):
      for ty in arg_types:
        check_type(ty, env)
      ty = TypeName(loc, name, index)
      b = env.get_binding_of_type_var(ty)
      if not b:
        error(loc, 'undefined type ' + str(ty))
    case GenericType(loc, name, index):
      ty = TypeName(loc, name, index)
      b = env.get_binding_of_type_var(ty)
      if not b:
        error(loc, 'undefined type ' + str(ty))
    case _:
      print('error in check_type: unhandled type ' + str(typ))
      exit(-1)
        
def type_synth_term(term, env, recfun, subterms):
  if get_verbose():
    print('type_synth_term: ' + str(term))
    print('env: ' + str(env))
  match term:
    case TVar(loc, name, index):
      b = env.get_binding_of_term_var(term)
      if not b:
        error(loc, 'undefined variable ' + name + '\nin scope: ' + str(env))
    case TLet(loc, var, rhs, body):
      rhs_ty = type_synth_term(rhs, env, recfun, subterms)
      body_env = env.declare_term_var(loc, var, rhs_ty)
      ret = type_synth_term(body, body_env, recfun, subterms)
    case Conditional(loc, cond, thn, els):
      type_check_term(cond, BoolType(loc), env, recfun, subterms)
      thn_ty = type_synth_term(thn, env, recfun, subterms)
      els_ty = type_synth_term(els, env, recfun, subterms)
      if thn_ty != els_ty:
        error(loc, 'conditional expects same type for the two branches'\
              + ' but ' + str(thn_ty) + ' ≠ ' + str(els_ty))
      return thn_ty
    case Int(loc, value):
      ret = IntType(loc)
    case Bool(loc, value):
      ret = BoolType(loc)
    case And(loc, args):
      for arg in args:
        check_formula(arg, env)
      ret = BoolType(loc)
    case Or(loc, args):
      for arg in args:
        check_formula(arg, env)
      ret = BoolType(loc)
    case IfThen(loc, prem, conc):
      check_formula(prem, env)
      check_formula(conc, env)
      ret = BoolType(loc)
    case All(loc, vars, body):
      body_env = env.declare_term_vars(loc, vars)
      check_formula(body, body_env)      
      ret = BoolType(loc)
    case Some(loc, vars, body):
      body_env = env.declare_term_vars(loc, vars)
      check_formula(body, body_env)
      ret = BoolType(loc)
    case Call(loc, TVar(loc2, name), args, infix) if name == '=' or name == '≠':
      lhs_ty = type_synth_term(args[0], env, recfun, subterms)
      rhs_ty = type_synth_term(args[1], env, recfun, subterms)
      if lhs_ty != rhs_ty:
        error(loc, 'equality expects same type of thing on left and right-hand side'\
              + ' but ' + str(lhs_ty) + ' ≠ ' + str(rhs_ty))
      ret = BoolType(loc)
        
    case Call(loc, TVar(loc2, name, index), args, infix) if name == recfun:
      # recursive call
      ret = type_check_rec_call(loc, TVar(loc2, name, index), args, env,
                                recfun, subterms, None)
    case Call(loc, rator, args, infix):
      # non-recursive call
      ret = type_check_call(loc, rator, args, env, recfun, subterms, None)
    case Switch(loc, subject, cases):
      ty = type_synth_term(subject, env, recfun, subterms)
      # TODO: check for completeness
      result_type = None
      for c in cases:
        new_env = check_pattern(c.pattern, ty, env)
        case_type = type_synth_term(c.body, new_env, recfun, subterms)
        if not result_type:
          result_type = case_type
        elif case_type != result_type:
          error(c.location, 'bodies of cases must have same type, but ' \
                + str(case_type) + ' ≠ ' + str(result_type))
        ret = result_type
    case TermInst(loc, subject, tyargs):
      ty = type_synth_term(subject, env, recfun, subterms)
      match ty:
        case TypeName(loc2, name):
          ret = TypeInst(loc, name, tyargs)
        case FunctionType(loc2, typarams, param_types, return_type):
          ret = ty
        case _:
          error(loc, 'expected a type name, not ' + str(ty))
    case TAnnote(loc, subject, typ):
      type_check_term(subject, typ, env, recfun, subterms)
      ret = typ
    case _:
      error(term.location, 'cannot synthesize a type for ' + str(term))
  if get_verbose():
    print('\t=> ' + str(ret))
  return ret
  
def type_check_term(term, typ, env, recfun, subterms):
  if get_verbose():
    print('type_check_term: ' + str(term) + ' : ' + str(typ) + '?')
  match term:
    case TVar(loc, name, index):
      b = env.get_binding_of_term_var(term)
      if not b:
        error(loc, 'undefined variable ' + name + '\nin scope: ' + str(env))
      if b.typ != typ:
        error(loc, 'expected a term of type ' + str(typ) \
              'but got term ' + str(term) + ' of type ' + str(b.typ))
    case Lambda(loc, vars, body):
      match typ:
        case FunctionType(loc, typarams, param_types, return_type):
          body_env = env.declare_type_vars(loc, typarams)
          body_env = body_env.declare_term_vars(loc, zip(vars, param_types))
          type_check_term(body, return_type, body_env, recfun, subterms)
        case _:
          error(loc, 'expected a term of type ' + str(typ) + '\n'\
                + 'but instead got a lambda')
    case TLet(loc, var, rhs, body):
      rhs_ty = type_synth_term(rhs, env, recfun, subterms)
      body_env = body_env.declare_term_var(loc, var, rhs_ty)
      type_check_term(body, typ, body_env, recfun, subterms)
    case Call(loc, TVar(loc2, name, index), args, infix) if name == '=' or name == '≠':
      ty = type_synth_term(term, env, recfun, subterms)
      if ty != typ:
        error(term.location, 'expected term of type ' + str(typ) + ' but got ' + str(ty))
      
    case Call(loc, TVar(loc2, name, index), args, infix) if name == recfun:
      # recursive call
      type_check_rec_call(loc, TVar(loc2, name, index), args, env,
                          recfun, subterms, typ)
    case Call(loc, rator, args, infix):
      # non-recursive call
      type_check_call(loc, rator, args, env, recfun, subterms, typ)
    case _:
      ty = type_synth_term(term, env, recfun, subterms)
      if ty != typ:
        error(term.location, 'expected term of type ' + str(typ) + ' but got ' + str(ty))

def is_constructor(constr_name, env):
  for (name,defn) in env.items():
    match defn:
      case Union(loc2, name, typarams, alts):
        for constr in alts:
          if constr.name == constr_name:
            return True
      case _:
        continue
  return False
        
def check_constructor_pattern(loc, constr_name, params, typ, env,
                              tyname):
  if get_verbose():
    print('check_constructor_pattern: ' + constr_name)
  defn = env.get_binding_of_type_var(tyname).defn
  if get_verbose():
    print('for union: ' + str(defn))
  match defn:
    case Union(loc2, name, typarams, alts):
      # example:
      # typ is List<E>
      # union List<T> { empty; node(T, List<T>); }
      # constr_name == node
      for constr in alts:
        # constr = node(T, List<T>)
        if constr.name == constr_name:
          if len(typarams) > 0:
            sub = { T: ty for (T,ty) in zip(typarams, typ.arg_types)}
            parameter_types = [p.substitute(sub) for p in constr.parameters]
          else:
            parameter_types = constr.parameters
          env = env.declare_term_vars(zip(params, parameter_types))
      return env
    case _:
      error(loc, tyname + ' is not a union type')
        
def check_pattern(pattern, typ, env):
  match pattern:
    case PatternCons(loc, constr, params):
      match typ:
        case TypeName(loc2, name, index):
          return check_constructor_pattern(loc, constr, params, typ, env, typ)
        case TypeInst(loc2, name, tyargs, index):
          # TODO: handle the tyargs
          return check_constructor_pattern(loc, constr, params, typ, env, TypeName(loc2, name, index))
        case _:
          error(loc, 'expected something of type ' + str(typ) + ' not ' + constr)
    case _:
      error(pattern.location, 'expected a constructor pattern, not ' + str(pattern))

def check_formula(frm, env):
  type_check_term(frm, BoolType(frm.location), env, None, [])

modules = set()

def check_statement(stmt, env):
  if get_verbose():
    print('** check_statement(' + str(stmt) + ')')
  match stmt:
    case Define(loc, name, ty, body):
      if ty == None:
        ty = type_synth_term(body, env, None, [])
      else:
        type_check_term(body, ty, env, None, [])
      return env.define_term_var(loc, name, ty, body.reduce(env))
    case Theorem(loc, name, frm, pf):
      if get_verbose():
        print('checking theorem formula ' + str(frm))
        print(str(env))
      check_formula(frm, env)
      if get_verbose():
        print('checking proof of theorem')
      check_proof_of(pf, frm, env)
      return env.declare_proof_var(loc, name, frm)
    case RecFun(loc, name, typarams, params, returns, cases):
      env = env.define_term_var(loc, name,
                                FunctionType(loc, typarams, params, returns),
                                stmt.reduce(env))
      for fun_case in cases:
        body_env = env.declare_type_vars(loc, typarams)
        body_env = check_pattern(fun_case.pattern, params[0], body_env)
        body_env = body_env.declare_term_vars(loc, zip(fun_case.parameters, params[1:]))
        type_check_term(fun_case.body, returns, body_env,
                        name, fun_case.pattern.parameters)
      return env
    case Union(loc, name, typarams, alts):
      # TODO: check for well-defined types in the constructor definitions
      env = env.define_type(loc, name, stmt)
      body_env = env.declare_type_vars(loc, typarams)
      for constr in alts:
        if len(constr.parameters) > 0:
          if len(typarams) > 0:
            tyvars = [TypeName(loc, p) for p in typarams]
            return_type = TypeInst(loc, name, tyvars, 0)
          else:
            return_type = TypeName(loc, name, 0)
          for ty in constr.parameters:
            check_type(ty, body_env)
          constr_type = FunctionType(constr.location, typarams, constr.parameters,
                                     return_type)
          env = env.declare_term_var(loc, constr.name, constr_type)
        elif len(typarams) > 0:
          env = env.declare_term_var(loc, constr.name, GenericType(loc, name))
        else:
          env = env.declare_term_var(loc, constr.name, TypeName(loc, name, this_index))
      return env
    case Import(loc, name):
      if name not in modules:
        modules.add(name)
        filename = name + ".pf"
        file = open(filename, 'r')
        src = file.read()
        file.close()
        set_filename(filename)
        ast = parse(src, trace=False)
        debruijnize_statements(ast, env)
        if get_verbose():
          print('finished parsing')
        # TODO: cache the proof-checking of files
        if get_verbose():
          print('checking module ' + name)
        for s in ast:
          env = check_statement(s, env)
        if get_verbose():
          print('finished checking module ' + name)
        return env
    case _:
      error(stmt.location, "unrecognized statement:\n" + str(stmt))

def debruijnize_deduce(ast):
  env = Env()
  env = env.declare_term_var(ast.location, '≠', None)
  env = env.declare_term_var(ast.location, '=', None)
  for s in ast:
    env = s.debruijnize(env)
  return env
  
def check_deduce(ast):
  env = Env()
  for s in ast:
    env = check_statement(s, env)
  
