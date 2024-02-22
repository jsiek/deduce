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
    

def check_proof(proof, env, type_env):
  if verbose:
    print('synthesize formula while checking proof') ; print('\t' + str(proof))
  ret = None
  match proof:
    case RewriteFact(loc, subject, equation_proof):
      formula = check_proof(subject, env, type_env)
      equation = check_proof(equation_proof, env, type_env)
      new_formula = rewrite(loc, formula, equation)
      ret = new_formula
    case PHole(loc):
      error(loc, 'unfinished proof')
    case PVar(loc, name, index):
      # TODO:
      # ret = env.get(name, index)
      # problem: IndCase used for switch and induction, but
      # binding structure is different (IH, EQ)
      # (fixed, probably)
      ret = env.lookup(name)
      if not ret:
        error(loc, 'undefined label ' + name)
    case PTrue(loc):
      ret = Bool(loc, True)
    case PLet(loc, label, frm, reason, rest):
      check_formula(frm, env, type_env)
      check_proof_of(reason, frm, env, type_env)
      new_env = env.extend(label, frm)
      ret = check_proof(rest, new_env, type_env)
    case PAnnot(loc, claim, reason):
      check_formula(claim, env, type_env)
      check_proof_of(reason, claim, env, type_env)
      ret = claim
    case PTuple(loc, pfs):
      frms = [check_proof(pf, env, type_env) for pf in pfs]
      ret = And(loc, frms)
    case ImpIntro(loc, label, prem, body):
      check_formula(prem, env, type_env)
      new_env = env.extend(label, prem)
      conc = check_proof(body, new_env, type_env)
      ret = IfThen(loc, prem, conc)
    case AllIntro(loc, vars, body):
      formula = check_proof(body, env, type_env)
      ret = All(loc, vars, formula)
    case AllElim(loc, univ, args):
      allfrm = check_proof(univ, env, type_env)
      arg_types = [type_synth_term(arg, type_env, env, None, []) for arg in args]
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
      ifthen = check_proof(imp, env, type_env)
      match ifthen:
        case IfThen(loc, prem, conc):
          check_proof_of(arg, prem, env, type_env)
          ret = conc
        case _:
          error(loc, 'expected an if-then, not ' + str(ifthen))
    case PInjective(loc, eq_pf):
      formula = check_proof(eq_pf, env, type_env)
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
      frm = check_proof(eq_pf, env, type_env)
      (a,b) = split_equation(loc, frm)
      return mkEqual(loc, b, a)
    case _:
      error(proof.location, 'in check_proof, unhandled ' + str(proof))
  if verbose:
    print('\t=> ' + str(ret))
  return ret


def check_proof_of(proof, formula, env, type_env):
  if verbose:
    print('nts: ' + str(formula) + '?')
    print('\t' + str(proof))
  match proof:
    case PHole(loc):
      print('Facts:\n' + facts_to_str(env))
      error(loc, 'unfinished proof:\n' + str(formula))
    
    case PReflexive(loc):
      match formula:
        case Call(loc2, TVar(loc3, '='), [lhs, rhs], _):
          lhsNF = lhs.reduce(env)
          rhsNF = rhs.reduce(env)
          if lhsNF != rhsNF:
            (lhs,rhs) = isolate_difference(lhsNF, rhsNF)
            msg = 'error in proof by reflexive:\n'
            if lhs == lhsNF:
              msg = msg + str(lhsNF) + ' ≠ ' + str(rhsNF)
            else:
              msg = msg + str(lhs) + ' ≠ ' + str(rhs) + '\n' \
                + 'therefore\n' + str(lhsNF) + ' ≠ ' + str(rhsNF)
            error(proof.location, msg)
        case _:
          error(proof.location, 'reflexive proves an equality, not ' \
                + str(formula))
          
    case PSymmetric(loc, eq_pf):
      (a,b) = split_equation(loc, formula)
      flip_formula = mkEqual(loc, b, a)
      check_proof_of(eq_pf, flip_formula, env, type_env)

    case PTransitive(loc, eq_pf1, eq_pf2):
      (a1,c) = split_equation(loc, formula)
      eq1 = check_proof(eq_pf1, env, type_env)
      (a2,b) = split_equation(loc, eq1)
      check_proof_of(eq_pf2, mkEqual(loc, b, c), env, type_env)
      if a1 != a2:
        error(loc, 'for transitive, ' + str(a1) + ' ≠ ' + str(a2))

    case PInjective(loc, eq_pf):
      (a,b) = split_equation(loc, formula)
      flip_formula = mkEqual(loc, Call(loc, TVar(loc,'suc'), [a], False),
                             Call(loc, TVar(loc,'suc'), [b], False))
      check_proof_of(eq_pf, flip_formula, env, type_env)
        
    case AllIntro(loc, vars, body):
      match formula:
        case All(loc2, vars2, formula2):
          if len(vars) != len(vars2):
            error(proof.location, 'mismatch in number of variables')
          sub = { var2[0]: TVar(loc, var[0]) for (var,var2) in zip(vars,vars2)}
          frm2 = formula2.substitute(sub)
          new_type_env = type_env.extend_all(vars)
          check_proof_of(body, frm2, env, new_type_env)

    case ImpIntro(loc, label, None, body):
      match formula:
        case IfThen(loc, prem, conc):
          new_env = env.extend(label, prem)
          check_proof_of(body, conc, new_env, type_env)
        case _:
          error(proof.location, 'expected proof of if-then, not ' + str(proof))
    case ImpIntro(loc, label, prem1, body):
      check_formula(prem1, env, type_env)
      match formula:
        case IfThen(loc, prem2, conc):
          new_env = env.extend(label, prem2)
          prem1_red = prem1.reduce(env)
          prem2_red = prem2.reduce(env)
          if prem1_red != prem2_red:
            error(loc, 'mismatch in premise:\n' \
                  + str(prem1_red) + '\n≠ ' + str(prem2_red))
          check_proof_of(body, conc, new_env, type_env)
        case _:
          error(proof.location, 'expected proof of if-then, not ' + str(proof))
      
    case PLet(loc, label, frm, reason, rest):
      check_formula(frm, env, type_env)
      check_proof_of(reason, frm, env, type_env)
      new_env = env.extend(label, frm)
      check_proof_of(rest, formula, new_env, type_env)
    case Cases(loc, subject, cases):
      sub_frm = check_proof(subject, env, type_env)
      match sub_frm:
        case Or(loc, frms):
          for (frm, (label,case)) in zip(frms, cases):
            new_env = env.extend(label, frm)
            check_proof_of(case, formula, new_env, type_env)
        case _:
          error(proof.location, "expected 'or', not " + str(sub_frm))
    case Induction(loc, typ, cases):
      match typ:
        case TypeName(l1, n):
          type_name = n
        case TypeInst(l1, n, type_args):
          type_name = n
      match env.lookup(type_name):
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
            new_env = env.extend('IH', induction_hypotheses)
            trm = pattern_to_term(indcase.pattern)
            goal = instantiate(loc, formula, [trm])
            if len(typarams) > 0:
              sub = { T: ty for (T,ty) in zip(typarams, typ.arg_types)}
              parameter_types = [p.substitute(sub) for p in constr.parameters]
            else:
              parameter_types = constr.parameters
            new_type_env = type_env.extend_all(zip(indcase.pattern.parameters,
                                                   parameter_types))
            check_proof_of(indcase.body, goal, new_env, new_type_env)
        case _:
          error(loc, "induction expected name of union, not " + type_name)

    case SwitchProof(loc, subject, cases):
      ty = type_synth_term(subject, type_env, env, None, [])
      match ty:
        case TypeName(loc2, name):
          type_name = name
        case _:
          error(loc, 'expected term of union type, not ' + str(ty))
      match env.lookup(type_name):
        case Union(loc2, name, typarams, alts):
          for (constr,scase) in zip(alts, cases):
            if scase.pattern.constructor != constr.name:
              error(scase.location, "expected a case for " + constr.name \
                    + " not " + scase.pattern.constructor)
            if len(scase.pattern.parameters) != len(constr.parameters):
              error(scase.location, "expected " + len(constr.parameters) \
                    + " arguments to " + constr.name \
                    + " not " + len(scase.pattern.parameters))
            new_env = env.extend('EQ', mkEqual(scase.location, 
                                               subject,
                                               pattern_to_term(scase.pattern)))
            new_type_env = type_env.extend_all(zip(scase.pattern.parameters,
                                                   constr.parameters))
            check_proof_of(scase.body, formula, new_env, new_type_env)
        case _:
          error(loc, "switch expected union type, not " + type_name)
          
    case RewriteGoal(loc, equation_proof, body):
      equation = check_proof(equation_proof, env, type_env)
      new_formula = rewrite(loc, formula, equation)
      check_proof_of(body, new_formula, env, type_env)
    case _:
      form = check_proof(proof, env, type_env)
      check_implies(proof.location, form.reduce(env), formula.reduce(env))

def type_match(loc, tyvars, param_ty, arg_ty, matching):
  if get_verbose():
    print("type_match(" + str(param_ty) + "," + str(arg_ty) + ")")
    print("\tin  " + str(tyvars))
    print("\twith" + str(matching))
  match (param_ty, arg_ty):
    case (TypeName(l1, n1), TypeName(l2, n2)) if n1 == n2:
      pass
    case (TypeName(l1, name), _) if name in tyvars:
      if name in matching.keys():
        type_match(loc, tyvars, matching[name], arg_ty, matching)
      else:
        matching[name] = arg_ty
    case (FunctionType(l1, tv1, pts1, rt1), FunctionType(l2, tv2, pts2, rt2)):
      # TODO, handle the type variables
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
    
      
def type_check_call_helper(loc, funty, args, type_env, env, recfun, subterms, ret_ty):
  match funty:
    case FunctionType(loc2, typarams, param_types, return_type):
      if len(typarams) == 0:
        for (param_type, arg) in zip(param_types, args):
          type_check_term(arg, param_type, type_env, env, recfun, subterms)
        return return_type
      else:
        matching = {}
        # If there is an expected return type, match that first.
        if ret_ty:
          type_match(loc, typarams, return_type, ret_ty, matching)
        # If we have already deduced the type parameters in the parameter type,
        # then we can check the term. Otherwise, we synthesize the term's type
        # and match it against the parameter type.
        for (arg, param_ty) in zip(args, param_types):
            param_type = param_ty.substitute(matching)
            fvs = param_type.free_vars().intersection(set(typarams))
            if len(fvs) == 0:
              type_check_term(arg, param_type, type_env, env, recfun, subterms)
            else:
              arg_ty = type_synth_term(arg, type_env, env, recfun, subterms)
              type_match(loc, typarams, param_type, arg_ty, matching)
        inst_return_type = return_type.substitute(matching)
        return inst_return_type
    case _:
      error(loc, 'expected operator to have function type, not ' + str(funty))
      
def type_check_call(loc, rator, args, type_env, env, recfun, subterms, ret_ty):
  ty = type_synth_term(rator, type_env, env, recfun, subterms)
  return type_check_call_helper(loc, ty, args, type_env, env, recfun, subterms, ret_ty)

def type_check_rec_call(loc, loc2, name, args, type_env, env, recfun, subterms, ret_ty):
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
  return type_check_call(loc, TVar(loc2,name), args, type_env, env,
                         recfun, subterms, ret_ty)


# TODO: add env parameter
def type_synth_term(term, type_env, env, recfun, subterms):
  if get_verbose():
    print('type_synth_term: ' + str(term))
    # print('type_env: ' + \
    #       ', '.join([k + ' : ' + str(t) for (k,t) in type_env.items()]))
  match term:
    case Conditional(loc, cond, thn, els):
      type_check_term(cond, BoolType(loc), type_env, env, recfun, subterms)
      thn_ty = type_synth_term(thn, type_env, env, recfun, subterms)
      els_ty = type_synth_term(els, type_env, env, recfun, subterms)
      if thn_ty != els_ty:
        error(loc, 'conditional expects same type for the two branches'\
              + ' but ' + str(thn_ty) + ' ≠ ' + str(els_ty))
      return thn_ty
    case TLet(loc, var, rhs, body):
      rhs_ty = type_synth_term(rhs, type_env, env, recfun, subterms)
      new_type_env = type_env.extend(var, rhs_ty)
      ret = type_synth_term(body, new_type_env, env, recfun, subterms)
    case Int(loc, value):
      ret = IntType(loc)
    case Bool(loc, value):
      ret = BoolType(loc)
    case And(loc, args):
      for arg in args:
        check_formula(arg, env, type_env)
      ret = BoolType(loc)
    case Or(loc, args):
      for arg in args:
        check_formula(arg, env, type_env)
      ret = BoolType(loc)
    case IfThen(loc, prem, conc):
      check_formula(prem, env, type_env)
      check_formula(conc, env, type_env)
      ret = BoolType(loc)
    case All(loc, vars, body):
      new_type_env = type_env.extend_all(vars)
      check_formula(body, env, new_type_env)      
      ret = BoolType(loc)
    case Some(loc, vars, body):
      new_type_env = type_env.extend_all(vars)
      check_formula(body, env, new_type_env)
      ret = BoolType(loc)
    case TVar(loc, name):
      ret = type_env.lookup(name)
      if not ret:
        error(loc, 'undefined name ' + name \
              + '\nscope: ' + ','.join(type_env.keys()))
    case Call(loc, TVar(loc2, name), args, infix) if name == '=' or name == '≠':
      lhs_ty = type_synth_term(args[0], type_env, env, recfun, subterms)
      rhs_ty = type_synth_term(args[1], type_env, env, recfun, subterms)
      if lhs_ty != rhs_ty:
        error(loc, 'equality expects same type of thing on left and right-hand side'\
              + ' but ' + str(lhs_ty) + ' ≠ ' + str(rhs_ty))
      ret = BoolType(loc)
        
    case Call(loc, TVar(loc2, name), args, infix) if name == recfun:
      # recursive call
      ret = type_check_rec_call(loc, loc2, name, args, type_env, env,
                                recfun, subterms, None)
    case Call(loc, rator, args, infix):
      # non-recursive call
      ret = type_check_call(loc, rator, args, type_env, env, recfun, subterms, None)
    case Switch(loc, subject, cases):
      ty = type_synth_term(subject, type_env, env, recfun, subterms)
      # TODO: check for completeness
      result_type = None
      for c in cases:
        new_type_env = check_pattern(c.pattern, ty, env, type_env)
        case_type = type_synth_term(c.body, new_type_env, env, recfun, subterms)
        if not result_type:
          result_type = case_type
        elif case_type != result_type:
          error(c.location, 'bodies of cases must have same type, but ' \
                + str(case_type) + ' ≠ ' + str(result_type))
        ret = result_type
    case TermInst(loc, subject, tyargs):
      ty = type_synth_term(subject, type_env, env, recfun, subterms)
      match ty:
        case TypeName(loc2, name):
          ret = TypeInst(loc, name, tyargs)
        case FunctionType(loc2, typarams, param_types, return_type):
          ret = ty
        case _:
          error(loc, 'expected a type name, not ' + str(ty))
    case TAnnote(loc, subject, typ):
      type_check_term(subject, typ, type_env, env, recfun, subterms)
      ret = typ
    case _:
      error(term.location, 'cannot synthesize a type for ' + str(term))
  if get_verbose():
    print('\t=> ' + str(ret))
  return ret
  
def type_check_term(term, typ, type_env, env, recfun, subterms):
  if get_verbose():
    print('type_check_term: ' + str(term) + ' : ' + str(typ) + '?')
  match term:
    case TVar(loc, name) if name in type_env.keys() \
                         and isinstance(type_env.lookup(name), GenericType):
      match typ:
        case TypeInst(loc2, name2, arg_types):
          union_name = type_env.lookup(name).name
          if union_name == name2:
            return typ
          else:
            error(loc, 'expected a term of type ' + str(typ) + '\n' \
                  + 'but instead got a term of type ' \
                  + str(type_env.lookup(name)))
        
    case Lambda(loc, vars, body):
      match typ:
        case FunctionType(loc, typarams, param_types, return_type):
          new_type_env = type_env.extend_all(zip(vars, param_types))
          type_check_term(body, return_type, new_type_env, env, recfun, subterms)
        case _:
          error(loc, 'expected a term of type ' + str(typ) + '\n'\
                + 'but instead got a lambda')
    case TLet(loc, var, rhs, body):
      rhs_ty = type_synth_term(rhs, type_env, env, recfun, subterms)
      new_type_env = type_env.extend(var, rhs_ty)
      type_check_term(body, typ, new_type_env, env, recfun, subterms)
    case Call(loc, TVar(loc2, name), args, infix) if name == '=' or name == '≠':
      ty = type_synth_term(term, type_env, env, recfun, subterms)
      if ty != typ:
        error(term.location, 'expected term of type ' + str(typ) + ' but got ' + str(ty))
      
    case Call(loc, TVar(loc2, name), args, infix) if name == recfun:
      # recursive call
      type_check_rec_call(loc, loc2, name, args, type_env, env,
                          recfun, subterms, typ)
    case Call(loc, rator, args, infix):
      # non-recursive call
      type_check_call(loc, rator, args, type_env, env, recfun, subterms, typ)
    case _:
      ty = type_synth_term(term, type_env, env, recfun, subterms)
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
        
def check_constructor_pattern(loc, constr_name, params, typ, env, tyname,
                              type_env):
  if get_verbose():
    print('check_constructor_pattern: ' + constr_name)
  for (name,defn) in env.items():
    if name == tyname:
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
                # print('instantiate constructor: ' + str(sub))
                parameter_types = [p.substitute(sub) for p in constr.parameters]
              else:
                parameter_types = constr.parameters
              type_env = type_env.extend_all(zip(params, parameter_types))
          return type_env
        case _:
          error(loc, tyname + ' is not a union type')
  error(loc, tyname + ' is not a union type')
        
def check_pattern(pattern, typ, env, type_env):
  match pattern:
    case PatternCons(loc, constr, params):
      match typ:
        case TypeName(loc2, name):
          return check_constructor_pattern(loc, constr, params, typ, env, name,
                                           type_env)
        case TypeInst(loc2, name, tyargs):
          # TODO: handle the tyargs
          return check_constructor_pattern(loc, constr, params, typ, env, name,
                                           type_env)
        case _:
          error(loc, 'expected something of type ' + str(typ) + ' not ' + constr)
    case _:
      error(pattern.location, 'expected a constructor pattern, not ' + str(pattern))

def check_formula(frm, env, type_env):
  type_check_term(frm, BoolType(frm.location), type_env, env, None, [])

modules = set()
debruijnized_modules = set()

def check_statement(stmt, env, type_env):
  if get_verbose():
    print('** check_statement(' + str(stmt) + ')')
  match stmt:
    case Define(loc, name, ty, body):
      if ty == None:
        ty = type_synth_term(body, type_env, env, None, [])
      else:
        type_check_term(body, ty, type_env, env, None, [])
      env = env.extend(name, body.reduce(env))
      type_env = type_env.extend(name, ty)
      return (env, type_env)
    case Theorem(loc, name, frm, pf):
      if get_verbose():
        print('checking theorem formula ' + str(frm))
        print('type_env: ' + \
          ', '.join([k + ' : ' + str(t) for (k,t) in type_env.items()]))
      check_formula(frm, env, type_env)
      if get_verbose():
        print('checking proof of theorem')
        print('type_env: ' + \
          ', '.join([k + ' : ' + str(t) for (k,t) in type_env.items()]))
      check_proof_of(pf, frm, env, type_env)
      env = env.extend(name, frm)
      return (env, type_env)
    case RecFun(loc, name, typarams, params, returns, cases):
      type_env = type_env.extend(name, FunctionType(loc, typarams, params,
                                                    returns))
      for fun_case in cases:
        new_type_env = check_pattern(fun_case.pattern, params[0], env,
                                     type_env)
        new_type_env = new_type_env.extend_all(zip(fun_case.parameters,
                                                   params[1:]))
        type_check_term(fun_case.body, returns, new_type_env, env,
                        name, fun_case.pattern.parameters)
      env = env.extend(name, stmt)
      return env, type_env
    case Union(loc, name, typarams, alts):
      # TODO: check for well-defined types in the constructor definitions
      env = env.extend(name, stmt)
      for constr in alts:
        if constr.name in type_env.keys():
          error(loc, 'duplicate constructor name: ' + constr.name)
        if len(constr.parameters) > 0:
          if len(typarams) > 0:
            tyvars = [TypeName(loc, p) for p in typarams]
            return_type = TypeInst(loc, name, tyvars)
          else:
            return_type = TypeName(loc, name)
          type_env = type_env.extend(constr.name,
                                     FunctionType(constr.location,
                                                  typarams,
                                                  constr.parameters,
                                                  return_type))
        elif len(typarams) > 0:
          type_env = type_env.extend(constr.name, GenericType(loc, name))
        else:
          type_env = type_env.extend(constr.name, TypeName(loc, name))
      return (env, type_env)
    case Import(loc, name):
      if name not in modules:
        modules.add(name)
        filename = name + ".pf"
        file = open(filename, 'r')
        src = file.read()
        file.close()
        set_filename(filename)
        ast = parse(src, trace=False)
        if get_verbose():
          print('finished parsing')
        # TODO: cache the proof-checking of files
        if get_verbose():
          print('checking module ' + name)
        #temp = get_verbose()
        #set_verbose(False)
        for s in ast:
          env, type_env = check_statement(s, env, type_env)
        #set_verbose(temp)
        if get_verbose():
          print('finished checking module ' + name)
        return env, type_env
      
    case _:
      error(stmt.location, "unrecognized statement:\n" + str(stmt))


def debruijnize_statements(ast, top_level):
  for s in ast:
    name = s.debruijnize(top_level)
    if name:
      top_level.append(name)
    match s:
      case Import(loc, module_name):
        if module_name not in debruijnized_modules:
          debruijnized_modules.add(module_name)
        filename = module_name + ".pf"
        file = open(filename, 'r')
        src = file.read()
        file.close()
        set_filename(filename)
        ast = parse(src, trace=False)
        debruijnize_statements(ast, top_level)
      case Union(loc, union_name, typarams, alts):
        for con in alts:
          top_level.append(con.name)
      case _:
        pass
  
      
def debruijnize_deduce(ast):
  top_level = ['=','≠']
  debruijnize_statements(ast, top_level)
  
def check_deduce(ast):
  env = Env()
  type_env = Env()
  for s in ast:
    (env,type_env) = check_statement(s, env, type_env)
  
