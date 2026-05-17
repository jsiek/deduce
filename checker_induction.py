# mypy: ignore-errors
from checker_common import *

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
