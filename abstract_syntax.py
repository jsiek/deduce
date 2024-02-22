from dataclasses import dataclass
from lark.tree import Meta
from typing import Any, Tuple, List
from error import error

def copy_dict(d):
  return {k:v for k,v in d.items()}

name_id = 0

def generate_name(name):
    global name_id
    ls = name.split('.')
    new_id = name_id
    name_id += 1
    return ls[0] + '.' + str(new_id)
  
@dataclass
class AST:
    location: Meta

@dataclass
class Term(AST):
    pass

@dataclass
class Formula(AST):
    pass

@dataclass
class Proof(AST):
    pass

@dataclass
class Statement(AST):
    pass

@dataclass
class Type(AST):
    pass

################ Types ######################################

@dataclass
class TypeName(Type):
  name: str
  index: int = -1
  
  def __str__(self):
    return self.name

  def __repr__(self):
    return str(self)

  def __eq__(self, other):
    if not isinstance(other, TypeName):
      return False
    return self.name == other.name

  def free_vars(self):
    return set([self.name])

  def substitute(self, sub):
    if self.name in sub.keys():
      return sub[self.name]
    else:
      return self

  def debruijnize(self, bindings):
    if self.name not in bindings:
      error(self.location, "debruijnize, can't find " + self.name)
    self.index = bindings.index(self.name)
  
@dataclass
class IntType(Type):
    
  def __str__(self):
    return 'int'

  def __repr__(self):
    return str(self)

  def __eq__(self, other):
    return isinstance(other, IntType)

  def free_vars(self):
    return set()

  def substitute(self, sub):
    return self

  def debruijnize(self, bindings):
    pass
  
@dataclass
class BoolType(Type):
  def __str__(self):
    return 'bool'

  def __repr__(self):
    return str(self)

  def __eq__(self, other):
    return isinstance(other, BoolType)

  def free_vars(self):
    return set()

  def substitute(self, sub):
    return self

  def debruijnize(self, bindings):
    pass
  
@dataclass
class TypeType(Type):
  def __str__(self):
    return 'type'

  def __repr__(self):
    return str(self)

  def __eq__(self, other):
    return isinstance(other, TypeType)

  def free_vars(self):
    return set()

  def substitute(self, sub):
    return self

  def debruijnize(self, bindings):
    pass
  
@dataclass
class FunctionType(Type):
  type_params: List[str]
  param_types: List[Type]
  return_type: Type

  def __str__(self):
    if len(self.type_params) > 0:
      prefix = '<' + ','.join([x for x in self.type_params]) + '>'
    else:
      prefix = ''
    return prefix + '(' + ','.join([str(ty) for ty in self.param_types]) + ')'\
      + ' -> ' + str(self.return_type)

  def __eq__(self, other):
    match other:
      case FunctionType(l2, tv2, pts2, rt2):
        ret = True
        for (pt1, pt2) in zip(self.param_types, pts2):
          ret = ret and pt1 == pt2
        return ret and self.return_type == rt2
      case _:
        return False

  def free_vars(self):
    fvs = [pt.free_vars() for pt in self.param_types] \
      + [self.return_type.free_vars()]
    return set().union(*fvs) - set(self.type_params)

  def substitute(self, sub):
      # alpha rename
      new_vars = [generate_name(var) for var in self.type_params]
      ren = {var: TVar(self.location, new_var) \
              for (var,new_var) in zip(self.type_params, new_vars)}
      param_types2 = [pt.substitute(ren) for pt in self.param_types]
      return_type2 = self.return_type.substitute(ren)
      # apply substitution to the rest
      return FunctionType(self.location, new_vars,
                          [pt.substitute(sub) for pt in param_types2],
                          return_type2.substitute(sub))
    
  def debruijnize(self, bindings):
    new_bindings = list(self.type_params) + bindings
    for p in self.param_types:
      p.debruijnize(new_bindings)
    self.return_type.debruijnize(new_bindings)

    
@dataclass
class TypeInst(Type):
  name: str
  arg_types: List[Type]

  def __str__(self):
    return self.name + \
      '<' + ','.join([str(arg) for arg in self.arg_types]) + '>'

  def __repr__(self):
    return str(self)

  def __eq__(self, other):
    match other:
      case TypeInst(l, name, arg_types):
        return self.name == name and \
          all([t1 == t2 for (t1, t2) in zip(self.arg_types, arg_types)])
      case GenericType(l, name):
        return self.name == name
      case _:
        return False

  def free_vars(self):
    return set().union(*[at.free_vars() for at in self.arg_types])

  def substitute(self, sub):
    return TypeInst(self.location, self.name, [ty.substitute(sub) for ty in self.arg_types])

  def debruijnize(self, bindings):
    for ty in self.arg_types:
      ty.debruijnize(bindings)
  
# This is the type of a constructor such as 'empty' of a generic union
# when we do not yet know the type arguments.
@dataclass
class GenericType(Type):
  name: str

  def __str__(self):
    return self.name + '<?>'

  def __eq__(self, other):
    match other:
      case TypeInst(l, name, arg_types):
        return self.name == name
      case GenericType(l, name):
        return self.name == name
      case _:
        return False

  def free_vars(self):
    return set()

  def substitute(self, sub):
    return self

  def debruijnize(self, bindings):
    pass
  
################ Patterns ######################################

@dataclass
class Pattern(AST):
    pass

@dataclass
class PatternCons(Pattern):
  constructor : str
  parameters : List[str]

  def __str__(self):
      return self.constructor + '(' + ",".join(self.parameters) + ')'

  def __repr__(self):
      return str(self)
  
################ Terms ######################################

@dataclass
class Conditional(Term):
  cond: Term
  thn: Term
  els: Term

  def __str__(self):
      return 'if ' + str(self.cond) \
        + ' then ' + str(self.thn) \
        + ' else ' + str(self.els)
    
  def __repr__(self):
      return str(self)
    
  def reduce(self, env):
     cond = self.cond.reduce(env)
     thn = self.thn.reduce(env)
     els = self.els.reduce(env)
     match cond:
       case Bool(l1, True):
         return thn
       case Bool(l1, False):
         return els
       case _:
         return Conditional(self.location, cond, thn, els)
  
  def substitute(self, sub):
    return Conditional(self.location, self.cond.substitute(sub),
                       self.thn.substitute(sub), self.els.substitute(sub))
  
  def debruijnize(self, bindings):
    self.cond.debruijnize(bindings)
    self.thn.debruijnize(bindings)
    self.els.debruijnize(bindings)
    
@dataclass
class TAnnote(Term):
  subject: Term
  typ: Type

  def __str__(self):
      return str(self.subject) + ':' + str(self.typ)
    
  def __repr__(self):
      return str(self)
    
  def reduce(self, env):
    return self.subject.reduce(env)
  
  def substitute(self, sub):
    return TAnnote(self.location, self.subject.substitute(sub),
                   self.typ.substitute(sub))
  
  def debruijnize(self, bindings):
    self.subject.debruijnize(bindings)
    self.typ.debruijnize(bindings)
  
@dataclass
class TVar(Term):
  name: str
  index: int = -1

  def __eq__(self, other):
      if not isinstance(other, TVar):
          return False
      ret = self.name == other.name
      return ret
  
  def __str__(self):
      if self.name == 'zero':
        return '0'
      else:
        return self.name

  def __repr__(self):
      return str(self)
    
  def reduce(self, env):
      res = env.lookup(self.name)
      if res:
          return res
      else:
          return self
  
  def substitute(self, sub):
      if self.name in sub:
          return sub[self.name]
      else:
          return self
        
  def debruijnize(self, bindings):
    if self.name not in bindings:
      error(self.location, "debruijnize, can't find " + self.name)
    self.index = bindings.index(self.name)
  
@dataclass
class Int(Term):
  value: int

  def __eq__(self, other):
      if not isinstance(other, Int):
          return False
      return self.value == other.value
  
  def __str__(self):
    return str(self.value)

  def reduce(self, env):
      return self

  def substitute(self, sub):
      return self

  def debruijnize(self, bindings):
    pass

@dataclass
class FieldAccess(Term):
  subject: Term
  field: str

  def __str__(self):
      return str(self.subject) + "." + self.field

  def __repr__(self):
    return str(self)

  def reduce(self, env):
      # TODO
      return self

  def substitute(self, sub):
    return FieldAccess(self.location, self.subject, self.field)

@dataclass
class Lambda(Term):
  vars: List[str]
  body: Term
  
  def __str__(self):
    return "λ" + ",".join([v for v in self.vars]) + "{" + str(self.body) + "}"

  def __repr__(self):
    return str(self)

  def __eq__(self, other):
      if not isinstance(other, Lambda):
          return False
      ren = {x: TVar(self.location, y) for (x,y) in zip(self.vars, other.vars) }
      new_body = self.body.substitute(ren)
      return new_body == other.body

  def reduce(self, env):
      return self

  def substitute(self, sub):
      # alpha rename the parameters
      new_vars = [generate_name(p) for p in self.vars]
      new_sub = copy_dict(sub)
      for (v,new_v) in zip(self.vars, new_vars):
        new_sub[v] = TVar(self.location, new_v)
      return Lambda(self.location, new_vars, self.body.substitute(new_sub))

  def debruijnize(self, bindings):
    new_bindings = list(self.vars) + bindings
    self.body.debruijnize(new_bindings)

    
def is_match(pattern, arg, subst):
    ret = False
    match (pattern, arg):
      case (PatternCons(loc1, constr, []),
            TVar(loc2, name)):
        ret = constr == name
      case (PatternCons(loc1, constr, params),
            Call(loc2, TVar(loc3, name), args, infix)):
        if constr == name and len(params) == len(args):
            for (k,v) in zip(params, args):
                subst[k] = v
            ret = True
        else:
            ret = False
      case _:
        ret = False
    return ret
        
@dataclass
class Call(Term):
  rator: Term
  args: list[Term]
  infix: bool
  
  def __str__(self):
    if self.infix:
      return str(self.args[0]) + " " + str(self.rator) + " " + str(self.args[1])
    elif isNat(self):
      return str(natToInt(self))
    else:
      return str(self.rator) + "(" + ",".join([str(arg) for arg in self.args]) + ")"

  def __repr__(self):
    return str(self)

  def __eq__(self, other):
      if not isinstance(other, Call):
          return False
      eq_rators = self.rator == other.rator
      # print('eq? ' + str(self.rator) + ' ' + str(other.rator) + ' = ' + str(eq_rators))
      eq_rands = all([arg1 == arg2 for arg1,arg2 in zip(self.args, other.args)])
      # print('eq? ' + str(self.args) + ' ' + str(other.args) + ' = ' + str(eq_rands))
      return eq_rators and eq_rands

  def reduce(self, env):
      fun = self.rator.reduce(env)
      args = [arg.reduce(env) for arg in self.args]
      match fun:
        case Lambda(loc, vars, body):
          new_env = env.extend_all(zip(vars, args))
          ret = body.reduce(new_env)
        case RecFun(loc, name, typarams, params, returns, cases):
          first_arg = args[0]
          rest_args = args[1:]
          for fun_case in cases:
              # alpha rename
              ren = {}
              fun_case_pattern_parameters = []
              for p in fun_case.pattern.parameters:
                  new_p = generate_name(p)
                  ren[p] = TVar(loc, new_p)
                  fun_case_pattern_parameters.append(new_p)
              fun_case_parameters = []
              for p in fun_case.parameters:
                  new_p = generate_name(p)
                  ren[p] = TVar(loc, new_p)
                  fun_case_parameters.append(new_p)
              fun_case_pattern = PatternCons(fun_case.pattern.location,
                                             fun_case.pattern.constructor,
                                             fun_case_pattern_parameters)
              fun_case_body = fun_case.body.substitute(ren)
              subst = {}
              if is_match(fun_case_pattern, first_arg, subst):
                  new_env = env.extend_all([(k, v.reduce(env)) \
                                            for (k,v) in subst.items()])
                  # TODO: not sure if the reduce is needed here -Jeremy
                  bindings = {x:v for (x,v) in zip(fun_case_parameters, rest_args)}
                  new_env = new_env.extend_all([(k, v.reduce(env)) \
                                                for (k,v) in zip(fun_case_parameters, rest_args)])
                  ret = fun_case_body.reduce(new_env)
                  return ret
          ret = Call(self.location, fun, args, self.infix)
        case _:
          ret = Call(self.location, fun, args, self.infix)
      return ret

  def substitute(self, sub):
      return Call(self.location, self.rator.substitute(sub),
                  [arg.substitute(sub) for arg in self.args],
                  self.infix)

  def debruijnize(self, bindings):
    self.rator.debruijnize(bindings)
    for arg in self.args:
      arg.debruijnize(bindings)
    
@dataclass
class SwitchCase(AST):
  pattern: Pattern
  body: Term
  
  def __str__(self):
      return 'case ' + str(self.pattern) + '{' + str(self.body) + '}'

  def __repr__(self):
      return str(self)

  def reduce(self, env):
      # alpha rename the parameters
      new_params = [generate_name(x) for x in self.pattern.parameters]
      ren = {x: TVar(self.location,y) for (x,y) in zip(self.pattern.parameters, new_params)}
      return SwitchCase(self.location,
                        PatternCons(self.pattern.location,
                                    self.pattern.constructor,
                                    new_params),
                        self.body.substitute(ren).reduce(env))
    
  def substitute(self, sub):
      # alpha rename the parameters
      new_params = [generate_name(x) for x in self.pattern.parameters]
      new_sub = copy_dict(sub)
      for x, new_x in zip(self.pattern.parameters, new_params):
        new_sub[x] = TVar(self.location, new_x)
      return SwitchCase(self.location,
                        PatternCons(self.pattern.location,
                                    self.pattern.constructor,
                                    new_params),
                        self.body.substitute(new_sub))

  def debruijnize(self, bindings):
    new_bindings = list(self.pattern.parameters) + bindings
    self.body.debruijnize(new_bindings)

    
  def __eq__(self, other):
    ren = {}
    for (x, y) in zip(self.pattern.parameters, other.pattern.parameters):
        ren[x] = TVar(self.location, y)
    return self.pattern.constructor == other.pattern.constructor \
      and self.body.substitute(ren) == other.body
    
@dataclass
class Switch(Term):
  subject: Term
  cases: List[SwitchCase]

  def __str__(self):
      return 'switch ' + str(self.subject) + '{ ' \
          + ' '.join([str(c) for c in self.cases]) \
          + ' }'

  def __repr__(self):
      return str(self)
  
  def reduce(self, env):
      new_subject = self.subject.reduce(env)
      for c in self.cases:
          # TODO: alpha renaming
          subst = {}
          if is_match(c.pattern, new_subject, subst):
            new_env = env.extend_all(subst.items())
            return c.body.reduce(new_env)
      new_cases = [c.reduce(env) for c in self.cases]
      return Switch(self.location, new_subject, new_cases)
  
  def substitute(self, sub):
      return Switch(self.location, self.subject.substitute(sub),
                    [c.substitute(sub) for c in self.cases])

  def debruijnize(self, bindings):
    self.subject.debruijnize(bindings)
    for c in self.cases:
      c.debruijnize(bindings)
    
  def __eq__(self, other):
    eq_subject = self.subject == other.subject
    eq_cases = all([c1 == c2 for (c1,c2) in zip(self.cases, other.cases)])
    return eq_subject and eq_cases

@dataclass
class TermInst(Term):
  subject: Term
  type_args: List[Type]

  def __str__(self):
    return str(self.subject) + \
      '<' + ','.join([str(ty) for ty in self.type_args]) + '>'

  def __repr__(self):
      return str(self)

  def reduce(self, env):
    # TODO: reduce type_args?
    # return TermInst(self.location, self.subject.reduce(env), self.type_args)
    # Type Erasure?
    return self.subject.reduce(env)

  def substitute(self, sub):
    return TermInst(self.location, self.subject.substitute(sub),
                    [ty.substitute(sub) for ty in self.type_args])
    
  def debruijnize(self, bindings):
    self.subject.debruijnize(bindings)
    for ty in self.type_args:
      ty.debruijnize(bindings)

  
@dataclass
class TLet(Term):
  var: str
  rhs: Term
  body: Term

  def debruijnize(self, bindings):
    self.rhs.debruijnize(bindings)
    new_bindings = [self.var] + bindings
    self.body.debruijnize(new_bindings)
  
################ Formulas ######################################
  
@dataclass
class Bool(Formula):
  value: bool
  def __eq__(self, other):
      if not isinstance(other, Bool):
          return False
      return self.value == other.value
  def __str__(self):
    return 'true' if self.value else 'false'
  def __repr__(self):
    return str(self)
  def reduce(self, env):
    return self
  def substitute(self, sub):
    return self
  def debruijnize(self, bindings):
    pass

@dataclass
class And(Formula):
  args: list[Formula]
  def __str__(self):
    return ' and '.join([str(arg) for arg in self.args])
  def __repr__(self):
    return str(self)
  def __eq__(self, other):
      return all([arg1 == arg2 for arg1,arg2 in zip(self.args, other.args)])
  def reduce(self, env):
    return And(self.location, [arg.reduce(env) for arg in self.args])
  def substitute(self, sub):
    return And(self.location, [arg.substitute(sub) for arg in self.args])
  def debruijnize(self, bindings):
    for arg in self.args:
      arg.debruijnize(bindings)

  
@dataclass
class Or(Formula):
  args: list[Formula]
  def __str__(self):
    return ' or '.join([str(arg) for arg in self.args])
  def __eq__(self, other):
      return all([arg1 == arg2 for arg1,arg2 in zip(self.args, other.args)])
  def reduce(self, env):
    return Or(self.location, [arg.reduce(env) for arg in self.args])
  def substitute(self, sub):
    return Or(self.location, [arg.substitute(sub) for arg in self.args])
  def debruijnize(self, bindings):
    for arg in self.args:
      arg.debruijnize(bindings)

# @dataclass
# class Compare(Formula):
#   op: str
#   args: list[Term]
#   def __str__(self):
#       return str(self.args[0]) + ' ' + self.op + ' ' + str(self.args[1])
  
@dataclass
class IfThen(Formula):
  premise: Formula
  conclusion : Formula
  def __str__(self):
    return 'if ' + str(self.premise) + ' then ' + str(self.conclusion)
  def __repr__(self):
    return str(self)
  def reduce(self, env):
    prem = self.premise.reduce(env)
    conc = self.conclusion.reduce(env)
    if prem == Bool(self.location, False):
      return Bool(self.location, True)
    elif conc == Bool(self.location, True):
      return Bool(self.location, True)
    else:
      return IfThen(self.location, prem, conc)
  def substitute(self, sub):
    return IfThen(self.location, self.premise.substitute(sub),
                  self.conclusion.substitute(sub))
  def debruijnize(self, bindings):
    self.premise.debruijnize(bindings)
    self.conclusion.debruijnize(bindings)

    
@dataclass
class All(Formula):
  vars: list[Tuple[str,Type]]
  body: Formula

  def __str__(self):
    return 'all ' + ",".join([v + ":" + str(t) for (v,t) in self.vars]) \
        + '. ' + str(self.body)

  def reduce(self, env):
    # TODO
    return self

  def __eq__(self, other):
    if not isinstance(other, All):
      return False
    ren = {x[0]: TVar(None, y[0]) for (x,y) in zip(self.vars, other.vars)}
    new_body = self.body.substitute(ren)
    return new_body == other.body

  def substitute(self, sub):
    # alpha rename
    new_vars = [(generate_name(var[0]),var[1]) for var in self.vars]
    ren = {var[0]: TVar(self.location, new_var[0]) \
            for (var,new_var) in zip(self.vars, new_vars)}
    body2 = self.body.substitute(ren)
    # apply the substitution to the body
    return All(self.location, new_vars, body2.substitute(sub))
  
  def debruijnize(self, bindings):
    new_bindings = [x for (x,t) in self.vars] + bindings
    self.body.debruijnize(new_bindings)
    
  
@dataclass
class Some(Formula):
  vars: list[Tuple[str,Type]]
  body: Formula

  def debruijnize(self, bindings):
    new_bindings = [x for (x,t) in self.vars] + bindings
    self.body.debruijnize(new_bindings)
  
################ Proofs ######################################
  
@dataclass
class PVar(Proof):
  name: str
  index: int = -1
  
  def __str__(self):
      return str(self.name) + '@' + str(self.index)

  def debruijnize(self, bindings):
    if self.name not in bindings:
      error(self.location, "debruijnize, can't find " + self.name)
    self.index = bindings.index(self.name)

    
@dataclass
class PLet(Proof):
  label: str
  proved: Formula
  because: Proof
  body: Proof

  def __str__(self):
      return self.label + ': ' + str(self.proved) + ' by ' \
        + str(self.because) + '; ' + str(self.body)

  def debruijnize(self, bindings):
    self.proved.debruijnize(bindings)
    self.because.debruijnize(bindings)
    new_bindings = [self.label] + bindings
    self.body.debruijnize(new_bindings)

    
@dataclass
class PAnnot(Proof):
  claim: Formula
  reason: Proof

  def __str__(self):
      return 'have ' + str(self.claim) + ' by ' + str(self.reason)

  def debruijnize(self, bindings):
    self.claim.debruijnize(bindings)
    self.reason.debruijnize(bindings)
    
@dataclass
class Cases(Proof):
  subject: Proof
  cases: List[Tuple[str,Proof]]

  def debruijnize(self, bindings):
    self.subject.debruijnize(bindings)
    for c in self.cases:
      c.debruijnize(bindings)
  
@dataclass
class Apply(Proof):
  implication: Proof
  arg: Proof

  def __str__(self):
      return 'apply ' + str(self.implication) + ' with ' + str(self.arg)

  def debruijnize(self, bindings):
    self.implication.debruijnize(bindings)
    self.arg.debruijnize(bindings)
    
@dataclass
class ImpIntro(Proof):
  label: str
  premise: Formula
  body: Proof

  def __str__(self):
    return 'suppose ' + str(self.label) + ': ' + str(self.premise) + '{' + str(self.body) + '}'

  def debruijnize(self, bindings):
    if self.premise:
      self.premise.debruijnize(bindings)
    new_bindings = [self.label] + bindings
    self.body.debruijnize(new_bindings)
  
@dataclass
class AllIntro(Proof):
  vars: List[Tuple[str,Type]]
  body: Proof

  def __str__(self):
    return 'arbitrary ' + ",".join([x + ":" + str(t) for (x,t) in self.vars]) \
        + '; ' + str(self.body)

  def debruijnize(self, bindings):
    new_bindings = [x for (x,t) in self.vars] + bindings
    self.body.debruijnize(new_bindings)
  
@dataclass
class AllElim(Proof):
  univ: Proof
  args: List[Term]

  def __str__(self):
    return str(self.univ) + '[' + ','.join([str(arg) for arg in self.args]) + ']'

  def debruijnize(self, bindings):
    self.univ.debruijnize(bindings)
    for arg in self.args:
      arg.debruijnize(bindings)
  
@dataclass
class PTuple(Proof):
  args: List[Proof]

  def __str__(self):
    return ', '.join([str(arg) for arg in self.args])

  def debruijnize(self, bindings):
    for arg in self.args:
      arg.debruijnize(bindings)
  
@dataclass
class PTrue(Proof):
  def __str__(self):
    return '.'
  def debruijnize(self, bindings):
    pass
  
@dataclass
class PReflexive(Proof):
  def __str__(self):
    return 'reflexive'
  def debruijnize(self, bindings):
    pass

@dataclass
class PHole(Proof):
  def __str__(self):
      return '?'
  def debruijnize(self, bindings):
    pass
  
@dataclass
class PSymmetric(Proof):
  body: Proof
  def __str__(self):
    return 'symmetric'
  def debruijnize(self, bindings):
    pass

@dataclass
class PTransitive(Proof):
  first: Proof
  second: Proof
  def __str__(self):
    return 'transitive'
  def debruijnize(self, bindings):
    self.first.debruijnize(bindings)
    self.second.debruijnize(bindings)

@dataclass
class PInjective(Proof):
  body: Proof
  def __str__(self):
    return 'injective'
  def debruijnize(self, bindings):
    self.body.debruijnize(bindings)
  
@dataclass
class IndCase(AST):
  pattern: Pattern
  body: Proof

  def __str__(self):
    return 'case ' + str(self.pattern) + '{' + str(self.body) + '}'

  def debruijnize(self, bindings):
    new_bindings = ['IH','EQ'] + list(self.pattern.parameters) + bindings 
    self.body.debruijnize(new_bindings)
  
@dataclass
class Induction(Proof):
  typ: Type
  cases: List[IndCase]

  def __str__(self):
    return 'induction ' + str(self.typ) + '\n' \
      + '\n'.join([str(c) for c in self.cases])
  
  def debruijnize(self, bindings):
    for c in self.cases:
      c.debruijnize(bindings)
    
@dataclass
class SwitchProof(Proof):
  subject: Term
  cases: List[IndCase]

  def __str__(self):
      return 'switch ' + str(self.subject) \
        + '{' + '\n'.join([str(c) for c in self.cases]) + '}'
    
  def debruijnize(self, bindings):
    self.subject.debruijnize(bindings)
    for c in self.cases:
      c.debruijnize(bindings)
    
@dataclass
class RewriteGoal(Proof):
  equation: Proof
  body: Proof

  def __str__(self):
      return 'rewrite goal with ' + str(self.equation) \
        + ' then ' + str(self.body)

  def debruijnize(self, bindings):
    self.equation.debruijnize(bindings)
    self.body.debruijnize(bindings)
    
@dataclass
class RewriteFact(Proof):
  subject: Proof
  equation: Proof

  def __str__(self):
      return 'rewrite ' + str(self.subject) + ' with ' + str(self.equation)

  def debruijnize(self, bindings):
    self.subject.debruijnize(bindings)
    self.equation.debruijnize(bindings)
    
################ Statements ######################################
  
@dataclass
class Theorem(Statement):
  name: str
  what: Formula
  proof: Proof

  def __str__(self):
    return 'theorem ' + self.name + ': ' + str(self.what) + '\nbegin\n' \
        + str(self.proof) + '\nend\n'

  def __repr__(self):
    return str(self)

  def debruijnize(self, bindings):
    self.what.debruijnize(bindings)
    self.proof.debruijnize(bindings)
    return self.name
    
@dataclass
class Constructor(AST):
  name: str
  parameters: List[Type]

  def debruijnize(self, bindings):
    for ty in self.parameters:
      ty.debruijnize(bindings)
    
@dataclass
class Union(Statement):
  name: str
  type_params: List[str]
  alternatives: List[Constructor]

  def debruijnize(self, bindings):
    new_bindings = list(self.type_params) + [self.name] + bindings
    for alt in self.alternatives:
      alt.debruijnize(new_bindings)
    return self.name

@dataclass
class FunCase(AST):
  pattern: Pattern
  parameters: List[str]
  body: Term

  def __str__(self):
      return '(' + str(self.pattern) + ',' + ",".join(self.parameters) \
          + ') = ' + str(self.body)

  def __repr__(self):
      return str(self)

  def debruijnize(self, bindings):
    new_bindings = list(self.parameters) + list(self.pattern.parameters) \
      + bindings
    self.body.debruijnize(new_bindings)
    
@dataclass
class RecFun(Statement):
  name: str
  type_params: List[str]
  params: List[Type]
  returns: Type
  cases: List[FunCase]

  def debruijnize(self, bindings):
    new_bindings = list(self.type_params) + [self.name] + bindings
    for ty in self.params:
      ty.debruijnize(new_bindings)
    self.returns.debruijnize(new_bindings)
    for c in self.cases:
      c.debruijnize(new_bindings)
    return self.name
    
  def __str__(self):
    return self.name

  def __repr__(self):
    return str(self)

  def __eq__(self, other):
    return self.name == other.name

  def reduce(self, env):
    return self

  def substitute(self, sub):
    return self
    
@dataclass
class Define(Statement):
  name: str
  typ: Type
  body: Term

  def debruijnize(self, bindings):
    if self.typ:
      self.typ.debruijnize(bindings)
    self.body.debruijnize(bindings)
    return self.name
  
@dataclass
class Import(Statement):
  name: str
  
  def debruijnize(self, bindings):
    return None
  
def mkEqual(loc, arg1, arg2):
  return Call(loc, TVar(loc, '='), [arg1, arg2], True)

def split_equation(loc, equation):
  match equation:
    case Call(loc1, TVar(loc2, '='), [L, R], _):
      return (L, R)
    case _:
      error(loc, 'expected an equality, not ' + str(equation))

def mkZero(loc):
  return TVar(loc, 'zero')

def mkSuc(loc, arg):
  return Call(loc, TVar(loc, 'suc'), [arg], False)

def intToNat(loc, n):
  if n == 0:
    return mkZero(loc)
  else:
    return mkSuc(loc, intToNat(loc, n - 1))

def isNat(t):
  match t:
    case TVar(loc, 'zero'):
      return True
    case Call(loc, TVar(loc2, 'suc'), [arg], infix):
      return isNat(arg)
    case _:
      return False

def natToInt(t):
  match t:
    case TVar(loc, 'zero'):
      return 0
    case Call(loc, TVar(loc2, 'suc'), [arg], infix):
      return 1 + natToInt(arg)

  
