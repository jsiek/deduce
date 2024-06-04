# TODO
# check well-formedness of types

from abstract_syntax import *
from error import error
from parser import parse, set_filename, get_filename

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
  if get_verbose():
    print('check_implies? ' + str(frm1) + ' => ' + str(frm2))
  match (frm1, frm2):
    case (_, Bool(loc2, True)):
      return
    case (_, And(loc2, args)):
      for arg2 in args:
        check_implies(loc, frm1, arg2)
    case(Or(loc1, args1), _):
      for arg1 in args1:
        try:
          check_implies(loc, arg1, frm2)
        except Exception as e:
          error(loc, 'could not prove\n' + str(frm2) + '\nfrom \n' + str(arg1))
    case (_, Or(loc2, args)):
      for arg2 in args:
        try:
          check_implies(loc, frm1, arg2)
          return
        except Exception as e:
          continue
      error(loc, 'could not satisfy all the parts of\n' + str(frm2) + '\nfrom the formula\n' + str(frm1))
    case (Bool(loc2, False), _):
      return
    case (And(loc2, args1), _):
      for arg1 in args1:
        try:
          check_implies(loc, arg1, frm2)
          return
        except Exception as e:
          continue
      error(loc, 'could not satisfy\n' + str(frm2) + '\nwith any of the parts of\n' + str(frm1))
    case (IfThen(loc1, prem1, conc1), IfThen(loc2, prem2, conc2)):
      check_implies(loc, prem2, prem1)
      check_implies(loc, conc1, conc2)
    case (All(loc1, vars1, body1), All(loc2, vars2, body2)):
      sub = {var2[0]: Var(loc2, var1[0]) for (var1, var2) in zip(vars1, vars2)}
      body2a = body2.substitute(sub)
      check_implies(loc, body1, body2a)
    case _:
      if frm1 != frm2:
        error(loc, 'expected\n' + str(frm2) + '\nbut only have\n' + str(frm1))

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
        ret = Call(loc, constr,
                   [Var(loc, param) for param in params],
                   False)
        # if hasattr(pat, 'typeof'):
        #   ret.typeof = pat.typeof
        return ret
      else:
        return constr
    case _:
      error(pat.location, "expected a pattern, not " + str(pat))

def rewrite(loc, formula, equation):
  (lhs, rhs) = split_equation(loc, equation)
  if get_verbose():
    print('rewrite? ' + str(formula) + ' with equation ' + str(equation) \
          + '\n\t' + str(lhs) + ' =? ' + str(formula) + '\t' + str(formula == lhs))
  if formula == lhs:
    return rhs
  match formula:
    case Var(loc2, name):
      return formula
    case Bool(loc2, val):
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
    case Some(loc2, vars, frm2):
      return Some(loc2, vars, rewrite(loc, frm2, equation))
    case Call(loc2, rator, args, infix):
      call = Call(loc2, rewrite(loc, rator, equation),
                  [rewrite(loc, arg, equation) for arg in args],
                  infix)
      #call.typeof = formula.typeof
      return call
    case Switch(loc2, subject, cases):
      return Switch(loc2, rewrite(loc, subject, equation),
                    [rewrite(loc, c, equation) for c in cases])
    case SwitchCase(loc2, pat, body):
      return SwitchCase(loc2, pat, rewrite(loc, body, equation))
    case RecFunClosure(loc, name, typarams, params, returns, cases, clos_env):
      return formula
    case Conditional(loc2, cond, thn, els):
      return Conditional(loc2, rewrite(loc, cond, equation),
                         rewrite(loc, thn, equation),
                         rewrite(loc, els, equation))
    case Lambda(loc2, vars, body):
      return Lambda(loc2, vars, rewrite(loc, body, equation))
    case Closure(loc2, vars, body, clos_env):
      clos = Closure(loc2, vars, rewrite(loc, body, equation), clos_env)
      clos.typeof = formula.typeof
      return clos
    case DefinedValue(loc2, name, body):
      return DefinedValue(loc2, name, rewrite(loc, body, equation))
    case _:
      # return formula
      error(loc, 'in rewrite, unhandled ' + str(formula))

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
        ren = {x: Var(l1, y) for (x,y) in zip(vs1, vs2)}
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
      case(And(l1, args1), And(l2, args2)):
        return isolate_difference_list(args1, args2)
      case (All(l1, vars1, body1), All(l2, vars2, body2)):
        if len(vars1) != len(vars2):
          return (term1, term2)
        ren = {x: Var(l1,y) for ((x,t1),(y,t2)) in zip(vars1, vars2) }
        return isolate_difference(body1.substitute(ren), body2)
      case _:
        return (term1, term2)
    
def check_proof(proof, env):
  if verbose:
    print('synthesize formula while checking proof') ; print('\t' + str(proof))
  ret = None
  match proof:
    case ApplyDefsFact(loc, definitions, subject):
      defs = [d.reduce(env) for d in definitions]
      formula = check_proof(subject, env)
      new_formula = apply_definitions(loc, formula, defs, env)
      ret = new_formula
    case EnableDefs(loc, definitions, subject):
      defs = [d.reduce(env) for d in definitions]
      old_defs = get_reduce_only()
      set_reduce_only(defs + old_defs)
      ret = check_proof(subject, env)
      set_reduce_only(old_defs)
    case RewriteFact(loc, subject, equation_proofs):
      formula = check_proof(subject, env)
      eqns = [check_proof(proof, env) for proof in equation_proofs]
      new_formula = formula.reduce(env)
      for eq in eqns:
        if not is_equation(eq):
          eq = make_boolean_equation(eq)
        new_formula = rewrite(loc, new_formula, eq)
        new_formula = new_formula.reduce(env)
      ret = new_formula
    case PHole(loc):
      error(loc, 'unfinished proof')
    case PVar(loc, name, index):
      ret = env.get_formula_of_proof_var(proof)
    case PTrue(loc):
      ret = Bool(loc, True)
    case PLet(loc, label, frm, reason, rest):
      check_formula(frm, env)
      check_proof_of(reason, frm, env)
      body_env = env.declare_proof_var(loc, label, frm)
      ret = check_proof(rest, body_env)
    case PAnnot(loc, claim, reason):
      check_formula(claim, env)
      check_proof_of(reason, claim, env)
      ret = claim
    case PTerm(loc, term, because, rest):
      typ = type_synth_term(term, env, None, [])
      frm = check_proof_of(because, term, env)
      ret = check_proof(rest, env)
    case PTuple(loc, pfs):
      frms = [check_proof(pf, env) for pf in pfs]
      ret = And(loc, frms)
    case PAndElim(loc, which, subject):
      formula = check_proof(subject, env)
      match formula:
        case And(loc2, args):
          if which >= len(args):
            error(loc, 'out of bounds, access to conjunct ' + str(which) \
                  + ' but there are only ' + str(len(args)) + ' conjuncts' \
                  + ' in formula\n\t' + str(formula))
          ret = args[which]
        case _:
          error(loc, 'expected a conjunction, not ' + str(formula))
    case ImpIntro(loc, label, prem, body):
      check_formula(prem, env)
      body_env = env.declare_proof_var(loc, label, prem)
      conc = check_proof(body, body_env)
      ret = IfThen(loc, prem, conc)
    case AllIntro(loc, vars, body):
      #body_env = env.declare_term_vars(vars)
      body_env = env
      for (x,ty) in vars:
        if isinstance(ty, TypeType):
          body_env = body_env.declare_type(loc, x)
        else:
          body_env = body_env.declare_term_var(loc, x, ty)
      formula = check_proof(body, body_env)
      ret = All(loc, vars, formula)
    case AllElim(loc, univ, args):
      allfrm = check_proof(univ, env)
      arg_types = [type_synth_term(arg, env, None, []) for arg in args]
      match allfrm:
        case All(loc2, vars, frm):
          sub = {}
          for ((var,ty), (arg,arg_ty)) in zip(vars, zip(args,arg_types)):
            if ty.substitute(sub) != arg_ty:
              error(loc, 'to instantiate: ' + str(allfrm) \
                    + '\nexpected argument of type: ' \
                    + str(ty.substitute(sub)) \
                    + '\nnot: ' + str(arg_ty))
            if isinstance(ty, TypeType):
              sub[var] = arg
        case _:
          error(loc, 'expected all formula to instantiate, not ' + str(allfrm))
      return instantiate(loc, allfrm, args)
    case ModusPonens(loc, imp, arg):
      ifthen = check_proof(imp, env)
      match ifthen:
        case IfThen(loc, prem, conc):
          check_proof_of(arg, prem, env)
          ret = conc
        case _:
          error(loc, 'expected an if-then, not ' + str(ifthen))
    case PInjective(loc, constr, eq_pf):
      formula = check_proof(eq_pf, env)
      (a,b) = split_equation(loc, formula)
      match (a,b):
        case (Call(loc2,Var(loc3,f1),[arg1], infix1),
              Call(loc4,Var(loc5,f2),[arg2]), infix2):
          if f1 != f2:
            error(loc, 'in injective, ' + f1 + ' ≠ ' + f2)
          if constr != f1:
            error(loc, 'in injective, ' + constr + ' ≠ ' + f1)
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

def get_type_name(ty):
  match ty:
    case Var(l1, n, i):
      return ty
    case TypeInst(l1, ty, type_args):
      return get_type_name(ty)

def get_type_args(ty):
  match ty:
    case Var(l1, n, i):
      return []
    case TypeInst(l1, ty, type_args):
      return type_args
    
def check_proof_of(proof, formula, env):
  if verbose:
    print('nts: ' + str(formula) + '?')
    print('\t' + str(proof))
  match proof:
    case PHole(loc):
      error(loc, 'unfinished proof:\n\t' + str(formula.reduce(env)) \
            + '\n\navailable facts:\n' + env.proofs_str())

    case EnableDefs(loc, definitions, subject):
      defs = [d.reduce(env) for d in definitions]
      old_defs = get_reduce_only()
      set_reduce_only(defs + old_defs)
      check_proof_of(subject, formula, env)
      set_reduce_only(old_defs)
      
    case PReflexive(loc):
      match formula:
        case Call(loc2, Var(loc3, '='), [lhs, rhs], _):
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
            error(proof.location, msg + '\n\nfacts:\n' + env.proofs_str())
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
      a1r = a1.reduce(env)
      a2r = a2.reduce(env)
      if a1r != a2r:
        error(loc, 'for transitive, ' + str(a1r) + ' ≠ ' + str(a2r))

    case PInjective(loc, constr, eq_pf):
      if not is_constructor(constr.name, env):
        error(loc, 'in injective, ' + constr.name + ' not a constructor')
      (a,b) = split_equation(loc, formula)
      lhs = Call(loc, constr, [a], False)
      # lhs.typeof = constr
      rhs = Call(loc, constr, [b], False)
      # rhs.typeof = constr
      flip_formula = mkEqual(loc, lhs, rhs)
      check_proof_of(eq_pf, flip_formula, env)

    case PExtensionality(loc, proof):
      (lhs,rhs) = split_equation(loc, formula)
      lhs_type = type_synth_term(lhs, env, None, [])
      match lhs_type:
        case FunctionType(loc2, [], [typ], ret_ty):
          arg_name = generate_name('x')
          arg = Var(loc, arg_name)
          call_lhs = Call(loc, lhs, [arg], False)
          #call_lhs.typeof = ret_ty
          call_rhs = Call(loc, rhs, [arg], False)
          #call_rhs.typeof = ret_ty
          formula = All(loc, [(arg_name, typ)],
                        mkEqual(loc, call_lhs, call_rhs))
          check_proof_of(proof, formula, env)
        case FunctionType(loc2, [], params, ret_ty):
          error(loc, 'extensionality expects function with one input parameter, not ' + str(len(params)))
        case FunctionType(loc2, ty_params, params, ret_ty):
          error(loc, 'extensionality expects function without any type parameters, not ' + str(len(ty_params)))
        case _:
          error(loc, 'extensionality expects a function, not ' + str(lhs.typ))
      
    case AllIntro(loc, vars, body):
      match formula:
        case All(loc2, vars2, formula2):
          if len(vars) != len(vars2):
            error(proof.location, 'mismatch in number of variables')
          sub = {}
          for (var,var2) in reversed(list(zip(vars,vars2))):
            if isinstance(var[1], TypeType):
              sub[ var2[0] ] = Var(loc, var[0])
            else:
              sub[ var2[0] ] = Var(loc, var[0])
          frm2 = formula2.substitute(sub)
          body_env = env.declare_term_vars(loc, vars)
          check_proof_of(body, frm2, body_env)

    case SomeIntro(loc, witnesses, body):
      match formula:
        case Some(loc2, vars, formula2):
          sub = {var[0]: trm for (var,trm) in zip(vars, witnesses) }
          body_frm = formula2.substitute(sub)
          check_proof_of(body, body_frm, env)
        case _:
          error(loc, "choose expects the goal to start with 'some', not " + str(formula))
          
    case SomeElim(loc, witnesses, label, some, body):
      someFormula = check_proof(some, env)
      match someFormula:
        case Some(loc2, vars, formula2):
          sub = {var[0]: Var(loc2, x) for (var,x) in zip(vars,witnesses)}
          witnessFormula = formula2.substitute(sub)
          body_env = env.declare_proof_var(loc, label, witnessFormula)
          witnesses_types = [(x,var[1]) for (var,x) in zip(vars,witnesses)]
          body_env = body_env.declare_term_vars(loc, witnesses_types)
          check_proof_of(body, formula, body_env)
        case _:
          error(loc, "obtain expects 'from' to be a proof of a 'some' formula, not " + str(someFormula))
        
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
        case IfThen(loc2, prem2, conc):
          prem1_red = prem1.reduce(env)
          prem2_red = prem2.reduce(env)
          if prem1_red != prem2_red:
            (small1, small2) = isolate_difference(prem1_red, prem2_red)
            msg = str(small1) + ' ≠ ' + str(small2) + '\n' \
                + 'therefore\n' + str(prem1_red) + ' ≠ ' + str(prem2_red)
            error(loc, 'mismatch in premise:\n' + msg)
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
        case Or(loc1, frms):
          for (frm, (label,frm2,case)) in zip(frms, cases):
            if frm2 and frm != frm2:
              error(loc, 'case ' + str(frm2) + '\ndoes not match\n' + str(frm))
            body_env = env.declare_proof_var(loc, label, frm)
            check_proof_of(case, formula, body_env)
        case _:
          error(proof.location, "expected 'or', not " + str(sub_frm))
    case Induction(loc, typ, cases):
      match formula:
        case All(loc2, [(var,ty)], frm):
          if typ != ty:
            error(loc, "type of induction: " + str(typ) + "\ndoes not match the all-formula's type: " + str(ty))
      match env.get_def_of_type_var(get_type_name(typ)):
        case Union(loc2, name, typarams, alts):
          if len(cases) != len(alts):
            error(loc, 'expected ' + str(len(alts)) + ' cases for induction, but only have ' + str(len(cases)))
          
          for (constr,indcase) in zip(alts, cases):
            if indcase.pattern.constructor.name != constr.name:
              error(indcase.location, "expected a case for " + str(base_name(constr.name)) \
                    + " not " + str(base_name(indcase.pattern.constructor.name)))
            if len(indcase.pattern.parameters) != len(constr.parameters):
              error(indcase.location, "expected " + len(constr.parameters) \
                    + " arguments to " + constr.name \
                    + " not " + len(indcase.pattern.parameters))
            induction_hypotheses = [instantiate(loc, formula, [Var(loc,param)])
                                    for (param, ty) in 
                                    zip(indcase.pattern.parameters,
                                        constr.parameters)
                                    if get_type_name(ty) == get_type_name(typ)]
            body_env = env
            for ((x,frm1),frm2) in zip(indcase.induction_hypotheses, induction_hypotheses):
              if frm1 != None and frm1 != frm2:
                (small_frm1,small_frm2) = isolate_difference(frm1, frm2)
                msg = 'incorrect induction hypothesis, expected\n' + str(frm2) + '\nbut got\n' + str(frm1) \
                  + '\nin particular\n' + str(small_frm1) + '\n≠\n' + str(small_frm2) 
                error(loc, msg)
              body_env = body_env.declare_proof_var(loc, x, frm2)
              
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
        case blah:
          error(loc, "induction expected name of union, not " + str(typ)
                + '\nwhich resolves to\n' + str(blah) + '\nin ' + str(env))

    case SwitchProof(loc, subject, cases):
      ty = type_synth_term(subject, env, None, [])
      match ty:
        case BoolType():
          # check exhaustiveness
          has_true_case = False
          has_false_case = False
          for scase in cases:
            match scase.pattern:
              case PatternBool(l1, True):
                has_true_case = True
              case PatternBool(l1, False):
                has_false_case = True
          if not has_true_case:
            error(loc, 'missing case for true')
          if not has_false_case:
            error(loc, 'missing case for false')
            
          # check each case
          for scase in cases:
            if not isinstance(scase.pattern, PatternBool):
              error(scase.location, "expected pattern 'true' or 'false' in switch on bool")
            subject_case = Bool(scase.location, True) if scase.pattern.value \
                           else Bool(scase.location, False)
            equation = mkEqual(scase.location, subject, subject_case)

            body_env = env
            if len(scase.assumptions) == 1:
              if scase.assumptions[0][1] != None and scase.assumptions[0][1] != equation:
                error(scase.location, 'expected assumption\n' + str(assumption) \
                      + '\nnot\n' + str(scase.assumptions[0][1]))
              body_env = body_env.declare_proof_var(loc, scase.assumptions[0][0], equation)

            if len(scase.assumptions) > 1:
              error(scase.location, 'only one assumption is allowed in a switch case')
            
            frm = rewrite(loc, formula.reduce(env), equation.reduce(env))
            new_frm = frm.reduce(env)
            check_proof_of(scase.body, new_frm, body_env)
        case _:
          tname = get_type_name(ty)
          match env.get_def_of_type_var(tname):
            case Union(loc2, name, typarams, alts):
              if len(cases) != len(alts):
                error(loc, 'expected ' + str(len(alts)) + ' cases in switch, but only have ' + str(len(cases)))
              for (constr,scase) in zip(alts, cases):
                if scase.pattern.constructor.name != constr.name:
                  error(scase.location, "expected a case for " + str(constr) \
                        + " not " + str(scase.pattern.constructor))
                if len(scase.pattern.parameters) != len(constr.parameters):
                  error(scase.location, "expected " + len(constr.parameters) \
                        + " arguments to " + constr.name \
                        + " not " + len(scase.pattern.parameters))
                subject_case = pattern_to_term(scase.pattern)

                body_env = env
                if len(scase.assumptions) == 1:
                  assumption = mkEqual(scase.location, subject, subject_case)
                  if scase.assumptions[0][1] != None and scase.assumptions[0][1] != assumption:
                    error(scase.location, 'expected assumption\n' + str(assumption) \
                          + '\nnot\n' + str(scase.assumptions[0][1]))
                  body_env = body_env.declare_proof_var(loc, scase.assumptions[0][0], assumption)
                if len(scase.assumptions) > 1:
                  error(scase.location, 'only one assumption is allowed in a switch case')
                  
                tyargs = get_type_args(ty)
                sub = {T:ty for (T,ty) in zip(typarams, tyargs)}
                constr_params = [ty.substitute(sub) for ty in constr.parameters]
                body_env = body_env.declare_term_vars(loc, zip(scase.pattern.parameters,
                                                               constr_params))
                if isinstance(subject, Var):
                  frm = formula.substitute({subject.name: subject_case})
                else:
                  frm = formula
                check_proof_of(scase.body, frm, body_env)
            case _:
              error(loc, "switch expected union type, not " + type_name)
          
    case RewriteGoal(loc, equation_proofs, body):
      equations = [check_proof(proof, env) for proof in equation_proofs]
      eqns = [equation.reduce(env) for equation in equations]
      new_formula = formula.reduce(env)
      for eq in eqns:
        if not is_equation(eq):
          eq = make_boolean_equation(eq)
        new_formula = rewrite(loc, new_formula, eq)
        new_formula = new_formula.reduce(env)
      check_proof_of(body, new_formula.reduce(env), env)
    case ApplyDefsGoal(loc, definitions, body):
      defs = [d.reduce(env) for d in definitions]
      new_formula = apply_definitions(loc, formula, defs, env)
      check_proof_of(body, new_formula, env)
    case _:
      form = check_proof(proof, env)
      check_implies(proof.location, form.reduce(env), formula.reduce(env))

def apply_definitions(loc, formula, defs, env):
  old_defs = get_reduce_only()
  set_reduce_only(defs)
  new_formula = formula.reduce(env)
  set_reduce_only(old_defs)
  return new_formula
      
def type_match(loc, tyvars, param_ty, arg_ty, matching):
  if get_verbose():
    print("type_match(" + str(param_ty) + "," + str(arg_ty) + ")")
    print("\tin  " + str(tyvars))
    print("\twith" + str(matching))
  match (param_ty, arg_ty):
    case (Var(l1, n1, i1), Var(l2, n2, i2)) if n1 == n2 and i1 == i2:
      pass
    case (Var(l1, name, index), _) if param_ty in tyvars:
      if name in matching.keys():
        type_match(loc, tyvars, matching[name], arg_ty, matching)
      else:
        matching[name] = arg_ty
    case (FunctionType(l1, tv1, pts1, rt1), FunctionType(l2, tv2, pts2, rt2)) \
        if len(tv1) == len(tv2) and len(pts1) == len(pts2):
        #tyvars = [ty.shift(0, len(tv1)) for ty in tyvars]
        for (pt1, pt2) in zip(pts1, pts2):
          type_match(loc, tyvars, pt1, pt2, matching)
        type_match(loc, tyvars, rt1, rt2, matching)
    case (TypeInst(l1, n1, args1), TypeInst(l2, n2, args2)):
      if n1 != n2 or len(args1) != len(args2):
        error(loc, "argument type: " + str(arg_ty) + "\n" \
              + "does not match parameter type: " + str(param_ty))
      for (arg1, arg2) in zip(args1, args2):
        type_match(loc, tyvars, arg1, arg2, matching)
    # How to handle GenericUnknownInst?
    case (TypeInst(l1, n1, args1), GenericUnknownInst(l2, n2)):
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
    result.insert(0, Var(loc, n, index))
    index += 1
  return result

def type_check_call_helper(loc, funty, args, env, recfun, subterms, ret_ty):
  match funty:
    case FunctionType(loc2, typarams, param_types, return_type):
      if len(args) != len(param_types):
        error(loc, 'incorrect number of arguments, expected ' + str(len(param_types)) + ', not ' + str(len(args)))
      if len(typarams) == 0:
        for (param_type, arg) in zip(param_types, args):
          type_check_term(arg, param_type, env, recfun, subterms)
        if ret_ty != None and ret_ty != return_type:
          error(loc, 'expected ' + str(ret_ty) + ' but the call returns ' + str(return_type))
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
            fvs = param_type.free_vars()\
                            .intersection(set([ty.name for ty in type_params]))
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
    case Var(loc3, arg_name):
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
    case Var(loc, name, index):
      if not env.type_var_is_defined(typ):
        error(loc, 'undefined type variable ' + str(typ) + \
              '\nin ' + str(env))
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
    case TypeInst(loc, typ, arg_types):
      check_type(typ, env)
      for ty in arg_types:
        check_type(ty, env)
    case GenericUnknownInst(loc, typ):
      check_type(typ, env)
    case _:
      print('error in check_type: unhandled type ' + repr(typ) + ' ' + str(type(typ)))
      exit(-1)
        
def type_synth_term(term, env, recfun, subterms):
  if hasattr(term, 'typeof'):
    return term.typeof

  if get_verbose():
    print('type_synth_term: ' + str(term))
    print('env: ' + str(env))
  match term:
    case Var(loc, name, index):
      ret = env.get_type_of_term_var(term)
      if ret == None:
        error(loc, 'while type checking, undefined variable ' + str(term) + '\nin scope:\n' + str(env))
    case Generic(loc, type_params, body):
      body_env = env.declare_type_vars(loc, type_params)
      body_ty = type_synth_term(body, body_env, recfun, subterms)
      ret = GenericType(loc, type_params, body_ty)
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
      ret = thn_ty
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
    case Call(loc, Var(loc2, name), args, infix) if name == '=' or name == '≠':
      lhs_ty = type_synth_term(args[0], env, recfun, subterms)
      type_check_term(args[1], lhs_ty, env, recfun, subterms)
      # rhs_ty = type_synth_term(args[1], env, recfun, subterms)
      # if lhs_ty != rhs_ty:
      #   error(loc, 'equality expects same type of thing on left and right-hand side'\
      #         + ' but ' + str(lhs_ty) + ' ≠ ' + str(rhs_ty))
      ret = BoolType(loc)
        
    case Call(loc, Var(loc2, name, index), args, infix) if name == recfun:
      # recursive call
      ret = type_check_rec_call(loc, Var(loc2, name, index), args, env,
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
        if result_type == None:
          result_type = case_type
        elif case_type != result_type:
          error(c.location, 'bodies of cases must have same type, but ' \
                + str(case_type) + ' ≠ ' + str(result_type))
        ret = result_type
    case TermInst(loc, subject, tyargs):
      ty = type_synth_term(subject, env, recfun, subterms)
      match ty:
        case Var(loc2, name):
          ret = TypeInst(loc, name, tyargs)
        case FunctionType(loc2, typarams, param_types, return_type):
          ret = ty
        case _:
          error(loc, 'expected a type name, not ' + str(ty))
    case TAnnote(loc, subject, typ):
      type_check_term(subject, typ, env, recfun, subterms)
      ret = typ
    case _:
      if isinstance(term, Type):
        ret = TypeType(term.location)
      else:
        error(term.location, 'cannot synthesize a type for ' + str(term))
  if get_verbose():
    print('\t=> ' + str(ret))
  term.typeof = ret
  return ret

def type_check_formula(term, env):
  type_check_term(term, BoolType(term.location), env, None, [])
  
def type_check_term(term, typ, env, recfun, subterms):
  if get_verbose():
    print('type_check_term: ' + str(term) + ' : ' + str(typ) + '?')
  match term:
    case Generic(loc, type_params, body):
      match typ:
        case FunctionType(loc2, type_params2, param_types2, return_type2):
          sub = {U: Var(loc, T) for (T,U) in zip(type_params, type_params2) }
          new_param_types = [ty.substitute(sub) for ty in param_types2]
          new_return_type = return_type2.substitute(sub)
          body_env = env.declare_type_vars(loc, type_params)
          type_check_term(body, FunctionType(loc2, [], new_param_types, new_return_type),
                          body_env, recfun, subterms)
        case _:
          error(loc, 'expected a generic term, not ' + str(term))
        
    case Var(loc, name, index):
      var_typ = env.get_type_of_term_var(term)
      if var_typ == None:
        error(loc, 'undefined variable ' + str(term) + '\nin scope:\n' + str(env))
      if var_typ != typ:
        error(loc, 'expected a term of type ' + str(typ) \
              + '\nbut got term ' + str(term) + ' of type ' + str(var_typ))
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
      body_env = env.declare_term_var(loc, var, rhs_ty)
      type_check_term(body, typ, body_env, recfun, subterms)
    case Call(loc, Var(loc2, name, index), args, infix) if name == '=' or name == '≠':
      ty = type_synth_term(term, env, recfun, subterms)
      if ty != typ:
        error(term.location, 'expected term of type ' + str(typ) + ' but got ' + str(ty))
      
    case Call(loc, Var(loc2, name, index), args, infix) if name == recfun:
      # recursive call
      type_check_rec_call(loc, Var(loc2, name, index), args, env,
                          recfun, subterms, typ)
    case Call(loc, rator, args, infix):
      # non-recursive call
      type_check_call(loc, rator, args, env, recfun, subterms, typ)
    case _:
      ty = type_synth_term(term, env, recfun, subterms)
      if ty != typ:
        error(term.location, 'expected term of type ' + str(typ) + ' but got ' + str(ty))
  term.typeof = typ
  
def lookup_union(loc, typ, env):
  tyname = None
  match typ:
    case Var(loc2, name, index):
      tyname = typ
    case TypeInst(loc2, inst_typ, tyargs):
      tyname = inst_typ
    case _:
      error(loc, str(type) + ' is not a union type')
  return env.get_def_of_type_var(tyname)

def check_constructor_pattern(loc, pat_constr, params, typ, env):
  if get_verbose():
    print('check_constructor_pattern: ' + str(pat_constr))
  defn = lookup_union(loc, typ, env)
  if get_verbose():
    print('for union: ' + str(defn))
  match defn:
    case Union(loc2, name, typarams, alts):
      # example:
      # typ is List<E>
      # union List<T> { empty; node(T, List<T>); }
      # pat_constr == node
      for constr in alts:
        # constr = node(T, List<T>)
        if constr.name == pat_constr.name:
          if len(typarams) > 0:
            sub = { T: ty for (T,ty) in zip(typarams, typ.arg_types)}
            parameter_types = [p.substitute(sub) for p in constr.parameters]
          else:
            parameter_types = constr.parameters
          env = env.declare_term_vars(loc2, zip(params, parameter_types))
      return env
    case _:
      error(loc, str(typ) + ' is not a union type')
        
def check_pattern(pattern, typ, env):
  if get_verbose():
    print('check pattern: ' + str(pattern))
    print('against type: ' + str(typ))
    print('in env: ' + str(env))
  pattern.typeof = typ
  match pattern:
    case PatternCons(loc, constr, params):
      return check_constructor_pattern(loc, constr, params, typ, env)
    case _:
      error(pattern.location, 'expected a constructor pattern, not ' + str(pattern))

def check_formula(frm, env):
  type_check_term(frm, BoolType(frm.location), env, None, [])

modules = set()

def process_declaration(stmt, env):
  if get_verbose():
    print('** process_declaration(' + str(stmt) + ')')
    print('** env: ' + str(env))
  match stmt:
    case Define(loc, name, ty, body):
      if ty == None:
        ty = type_synth_term(body, env, None, [])
      return env.define_term_var(loc, name, ty, body)
    case Theorem(loc, name, frm, pf):
      check_formula(frm, env)
      return env.declare_proof_var(loc, name, frm)
    case RecFun(loc, name, typarams, params, returns, cases):
      fun_type = FunctionType(loc, typarams, params, returns)
      stmt.typeof = fun_type
      return env.define_term_var(loc, name, fun_type, stmt.reduce(env))
    case Union(loc, name, typarams, alts):
      # TODO: check for well-defined types in the constructor definitions
      env = env.define_type(loc, name, stmt)
      union_type = Var(loc, name, 0)
      body_env = env.declare_type_vars(loc, typarams)
      body_union_type = union_type #.shift_type_vars(0, len(typarams))
      for constr in alts:
        if len(constr.parameters) > 0:
          if len(typarams) > 0:
            tyvars = [Var(loc, p) for p in typarams]
            return_type = TypeInst(loc, body_union_type, tyvars)
          else:
            return_type = body_union_type
          for ty in constr.parameters:
            check_type(ty, body_env)
          constr_type = FunctionType(constr.location, typarams, constr.parameters,
                                     return_type)
          env = env.declare_term_var(loc, constr.name, constr_type)
        elif len(typarams) > 0:
          env = env.declare_term_var(loc, constr.name, GenericUnknownInst(loc, union_type))
        else:
          env = env.declare_term_var(loc, constr.name, union_type)
      return env
    case Import(loc, name, ast):
        for s in ast:
          env = process_declaration(s, env)
        for s in ast:
          type_check_stmt(s, env)
        for s in ast:
          check_proofs(s, env)
        return env
    case _:
      error(stmt.location, "unrecognized statement:\n" + str(stmt))

def type_check_stmt(stmt, env):
  if get_verbose():
    print('** type_check_stmt(' + str(stmt) + ')')
    print('** env: ' + str(env))
  match stmt:
    case Define(loc, name, ty, body):
      if ty == None:
        ty = type_synth_term(body, env, None, [])
      else:
        type_check_term(body, ty, env, None, [])
    case Theorem(loc, name, frm, pf):
      pass
    case RecFun(loc, name, typarams, params, returns, cases):
      fun_type = FunctionType(loc, typarams, params, returns)
      stmt.typeof = fun_type
      env = env.define_term_var(loc, name, fun_type, stmt.reduce(env))
      uniondef = lookup_union(loc, params[0], env)
      cases_present = {c.name: False for c in uniondef.alternatives}
      for fun_case in cases:
        body_env = env.declare_type_vars(loc, typarams)
        body_env = check_pattern(fun_case.pattern, params[0], body_env)
        cases_present[fun_case.pattern.constructor.name] = True
        if len(fun_case.parameters) != len(params[1:]):
          error(fun_case.location, 'incorrect number of parameters, expected ' + str(len(params)))
        body_env = body_env.declare_term_vars(loc, zip(fun_case.parameters,
                                                       params[1:]))
        type_check_term(fun_case.body, returns, body_env,
                        name, fun_case.pattern.parameters)

      for (constr,present) in cases_present.items():
        if not present:
          error(loc, 'missing function case for ' + base_name(constr))
    case Union(loc, name, typarams, alts):
      pass
    case Import(loc, name, ast):
      pass
    case _:
      error(stmt.location, "type checking, unrecognized statement:\n" + str(stmt))

def check_proofs(stmt, env):
  if get_verbose():
    print('** check_proofs(' + str(stmt) + ')')
    print('** env: ' + str(env))
  match stmt:
    case Define(loc, name, ty, body):
      pass
    case Theorem(loc, name, frm, pf):
      if get_verbose():
        print('checking proof of theorem')
      check_proof_of(pf, frm, env)
    case RecFun(loc, name, typarams, params, returns, cases):
      pass
    case Union(loc, name, typarams, alts):
      pass
    case Import(loc, name, ast):
      pass
    case _:
      error(stmt.location, "unrecognized statement:\n" + str(stmt))
      
def debruijnize_deduce(ast):
  env = Env()
  env = env.declare_term_var(None, '≠', None)
  env = env.declare_term_var(None, '=', None)
  for s in ast:
    env = s.debruijnize(env)
  return env

def uniquify_deduce(ast):
  env = {}
  env['≠'] = '≠'
  env['='] = '='
  for s in ast:
    s.uniquify(env)
  for s in ast:
    s.uniquify_body(env)

def check_deduce(ast):
  env = Env()
  for s in ast:
    env = process_declaration(s, env)
  for s in ast:
    type_check_stmt(s, env)
  for s in ast:
    check_proofs(s, env)
  
