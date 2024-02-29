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
  def shift(self, cutoff, amount):
    return self

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
    return self.name + '@' + str(self.index)

  def __repr__(self):
    return str(self)

  def __eq__(self, other):
    if not isinstance(other, TypeName):
      return False
    return self.name == other.name and self.index == other.index

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

  def shift(self, cutoff, amount):
    if self.index >= cutoff:
      return TypeName(self.location, self.name, self.index + amount)
    else:
      return self
    
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

  def shift(self, cutoff, amount):
    return self
  
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

  def shift(self, cutoff, amount):
    return self
  
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

  def shift(self, cutoff, amount):
    return self
  
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
      n = len(self.type_params)
      new_sub = {k:v.shift(0, n) for (k,v) in sub.items() }
      return FunctionType(self.location, self.type_params,
                          [pt.substitute(new_sub) for pt in self.param_types],
                          self.return_type.substitute(new_sub))
    
  def debruijnize(self, bindings):
    new_bindings = list(reversed(self.type_params)) + bindings
    for p in self.param_types:
      p.debruijnize(new_bindings)
    self.return_type.debruijnize(new_bindings)

  def shift(self, cutoff, amount):
    n = len(self.type_params)
    return FunctionType(self.location, self.type_params,
                        [ty.shift(cutoff + n, amount) for ty in self.param_types],
                        self.return_type.shift(cutoff + n, amount))
    
@dataclass
class TypeInst(Type):
  name: str
  arg_types: List[Type]
  index: int = -1

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
    return TypeInst(self.location, self.name,
                    [ty.substitute(sub) for ty in self.arg_types])

  def debruijnize(self, bindings):
    if self.name not in bindings:
      error(self.location, "debruijnize, can't find " + self.name)
    self.index = bindings.index(self.name)
    for ty in self.arg_types:
      ty.debruijnize(bindings)

  def shift(self, cutoff, amount):
    return TypeInst(self.location, self.name,
                    [ty.shift(cutoff, amount) for ty in self.arg_types])
    
# This is the type of a constructor such as 'empty' of a generic union
# when we do not yet know the type arguments.
@dataclass
class GenericType(Type):
  name: str
  index: int
  # TODO: add deBruijn index
  
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

  def shift(self, cutoff, amount):
    return self
  
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

  def shift(self, cutoff, amount):
    return Conditional(self.location,
                       self.cond.shift(cutoff, amount),
                       self.thn.shift(cutoff, amount),
                       self.els.shift(cutoff, amount))

    
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

  def shift(self, cutoff):
    return TAnnote(self.location,
                   self.subject.shift(cutoff, amount),
                   self.typ.shift(cutoff, amount))
    
@dataclass
class TVar(Term):
  name: str
  index: int = -1

  def __eq__(self, other):
      if not isinstance(other, TVar):
          return False
      ret = self.name == other.name and self.index == other.index
      return ret
  
  def __str__(self):
      if False and self.name == 'zero':
        return '0'
      else:
        return self.name + '@' + str(self.index)

  def __repr__(self):
      return str(self)
    
  def reduce(self, env):
      res = env.get(self.location, self.name, self.index)
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

  def shift(self, cutoff, amount):
    if self.index >= cutoff:
      return TVar(self.location, self.name, self.index + amount)
    else:
      return self
    
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

  def shift(self, cutoff, amount):
    return self

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
      return Closure(self.location, self.vars, self.body, env)

  def substitute(self, sub):
      n = len(self.vars)
      new_sub = {k: v.shift(0, n) for (k,v) in sub.items()}
      return Lambda(self.location, self.vars, self.body.substitute(new_sub))

  def debruijnize(self, bindings):
    new_bindings = list(reversed(self.vars)) + bindings
    self.body.debruijnize(new_bindings)

  def shift(self, cutoff, amount):
    n = len(self.vars)
    return Lambda(self.location, self.vars, self.body.shift(cutoff + n, amount))

@dataclass
class Closure(Term):
  vars: List[str]
  body: Term
  env: Any
  
  def __str__(self):
    return "[closure" + ",".join([v for v in self.vars]) + "{" + str(self.body) + "}]"

  def __repr__(self):
    return str(self)

  def __eq__(self, other):
      if not isinstance(other, Closure):
          return False
      return self.body == other.body

  def reduce(self, env):
      return self

  def substitute(self, sub):
      n = len(self.vars)
      new_sub = {k: v.shift(0, n) for (k,v) in sub.items()}
      return Closure(self.location, self.vars, self.body.substitute(new_sub))

  def shift(self, cutoff, amount):
    n = len(self.vars)
    return Closure(self.location, self.vars,
                   self.body.shift(cutoff + n, amount),
                   {k: v.shift(cutoff + n, amount) \
                    for (k,v) in self.env.items()})
  
    
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
      eq_rands = all([arg1 == arg2 for arg1,arg2 in zip(self.args, other.args)])
      return eq_rators and eq_rands

  def reduce(self, env):
      fun = self.rator.reduce(env)
      args = [arg.reduce(env) for arg in self.args]
      #print('*** reduce call to ' + str(fun))
      match fun:
        case Closure(loc, vars, body, clos_env):
          new_env = clos_env.extend_all(zip(vars, args))
          ret = body.reduce(new_env)
        case RecFunClosure(loc, name, typarams, params, returns, cases, clos_env):
          first_arg = args[0]
          rest_args = args[1:]
          for fun_case in cases:
              subst = {}
              if is_match(fun_case.pattern, first_arg, subst):
                  new_env = clos_env.extend_all(subst.items())
                  new_env = new_env.extend_all(zip(fun_case.parameters, rest_args))
                  ret = fun_case.body.reduce(new_env)
                  return ret
          ret = Call(self.location, fun, args, self.infix)
        case _:
          ret = Call(self.location, fun, args, self.infix)
      return ret

  def substitute(self, sub):
    return Call(self.location, self.rator.substitute(sub),
                [arg.substitute(sub) for arg in self.args],
                self.infix)

  def shift(self, cutoff, amount):
    return Call(self.location, self.rator.shift(cutoff, amount),
                [arg.shift(cutoff, amount) for arg in self.args],
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
      n = len(self.pattern.parameters)
      new_env = {k: v.shift(0, n) for (k,v) in env.items()}
      return SwitchCase(self.location,
                        PatternCons(self.pattern.location,
                                    self.pattern.constructor,
                                    self.pattern.parameters),
                        self.body.reduce(env))
    
  def substitute(self, sub):
      n = len(self.pattern.parameters)
      new_sub = {k: v.shift(0, n) for (k,v) in sub.items()}
      return SwitchCase(self.location,
                        PatternCons(self.pattern.location,
                                    self.pattern.constructor,
                                    self.pattern.parameters),
                        self.body.substitute(new_sub))

  def shift(self, cutoff, amount):
    n = len(self.pattern.parameters)
    return SwitchCase(self.location,
                      PatternCons(self.pattern.location,
                                  self.pattern.constructor,
                                  self.pattern.parameters),
                      self.body.shift(cutoff + n, amount))
    
  def debruijnize(self, bindings):
    new_bindings = list(reversed(self.pattern.parameters)) + bindings
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
          subst = {}
          if is_match(c.pattern, new_subject, subst):
            new_env = env.extend_all(subst.items())
            return c.body.reduce(new_env)
      new_cases = [c.reduce(env) for c in self.cases]
      return Switch(self.location, new_subject, new_cases)
  
  def substitute(self, sub):
      return Switch(self.location,
                    self.subject.substitute(sub),
                    [c.substitute(sub) for c in self.cases])

  def shift(self, cutoff, amount):
    return Switch(self.location, self.subject.shift(cutoff, amount),
                  [c.shift(cutoff, amount) for c in self.cases])
    
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
    return TermInst(self.location,
                    self.subject.substitute(sub),
                    [ty.substitute(sub) for ty in self.type_args])

  def shift(self, cutoff, amount):
    return TermInst(self.location, self.subject.shift(cutoff, amount),
                    [ty.shift(cutoff, amount) for ty in self.type_args])
   
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

  def shift(self, cutoff, amount):
    return TLet(self.location, self.var,
                self.rhs.shift(cutoff, amount),
                self.body.shift(cutoff + 1, amount))
    
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
  def shift(self, cutoff, amount):
    return self
  
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
  def shift(self, cutoff, amount):
    return And(self.location, [arg.shift(cutoff, amount) for arg in self.args])
  
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
  def shift(self, cutoff, amount):
    return Or(self.location, [arg.shift(cutoff, amount) for arg in self.args])

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
  def shift(self, cutoff, amount):
    return IfThen(self.location, self.premise.shift(cutoff, amount),
                  self.conclusion.shift(cutoff, amount))
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
    n = len(self.vars)
    new_sub = {k: v.shift(0, n) for (k,v) in sub.items()}
    return All(self.location, self.vars, self.body.substitute(new_sub))

  def shift(self, cutoff, amount):
    n = len(self.vars)
    return All(self.location, self.vars, self.body.shift(cutoff + n, amount))
    
  def debruijnize(self, bindings):
    new_bindings = [x for (x,t) in reversed(self.vars)] + bindings
    self.body.debruijnize(new_bindings)
    
  
@dataclass
class Some(Formula):
  vars: list[Tuple[str,Type]]
  body: Formula

  def substitute(self, sub):
    n = len(self.vars)
    new_sub = {k: v.shift(0, n) for (k,v) in sub.items()}
    return Some(self.location, self.vars, self.body.substitute(new_sub))
  
  def debruijnize(self, bindings):
    new_bindings = [x for (x,t) in reversed(self.vars)] + bindings
    self.body.debruijnize(new_bindings)

  def shift(self, cutoff, amount):
    n = len(self.vars)
    return Some(self.location, self.vars, self.body.shift(cutoff + n, amount))
    
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
    new_bindings = [] + bindings
    for (x,t) in self.vars:
      t.debruijnize(new_bindings)
      new_bindings.insert(0, x)
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
    return 'symmetric ' + str(self.body)
  def debruijnize(self, bindings):
    self.body.debruijnize(bindings)

@dataclass
class PTransitive(Proof):
  first: Proof
  second: Proof
  def __str__(self):
    return 'transitive ' + str(self.first) + ' ' + str(self.second)
  def debruijnize(self, bindings):
    self.first.debruijnize(bindings)
    self.second.debruijnize(bindings)

@dataclass
class PInjective(Proof):
  body: Proof
  def __str__(self):
    return 'injective ' + str(self.body)
  def debruijnize(self, bindings):
    self.body.debruijnize(bindings)
  
@dataclass
class IndCase(AST):
  pattern: Pattern
  body: Proof

  def __str__(self):
    return 'case ' + str(self.pattern) + '{' + str(self.body) + '}'

  def debruijnize(self, bindings):
    new_bindings = list(reversed(self.pattern.parameters)) + ['IH'] + bindings 
    self.body.debruijnize(new_bindings)
  
@dataclass
class Induction(Proof):
  typ: Type
  cases: List[IndCase]

  def __str__(self):
    return 'induction ' + str(self.typ) + '\n' \
      + '\n'.join([str(c) for c in self.cases])
  
  def debruijnize(self, bindings):
    self.typ.debruijnize(bindings)
    for c in self.cases:
      c.debruijnize(bindings)
    
@dataclass
class SwitchProofCase(AST):
  pattern: Pattern
  body: Proof

  def __str__(self):
    return 'case ' + str(self.pattern) + '{' + str(self.body) + '}'

  def debruijnize(self, bindings):
    new_bindings = list(reversed(self.pattern.parameters)) + ['EQ'] + bindings 
    self.body.debruijnize(new_bindings)
    
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

  def debruijnize(self, env):
    self.what.debruijnize(env)
    self.proof.debruijnize(env)
    return env.declare_proof_var(self.name, self.what)
    
@dataclass
class Constructor(AST):
  name: str
  parameters: List[Type]

  def debruijnize(self, bindings):
    for ty in self.parameters:
      ty.debruijnize(bindings)

  def shift(self, cutoff, amount):
    return Constructor(self.location, self.name,
                       [ty.shift(cutoff, amount) for ty in self.parameters])

  def __str__(self):
    return self.name + '(' + ','.join([str(ty) for ty in self.parameters]) + ');'
      
@dataclass
class Union(Statement):
  name: str
  type_params: List[str]
  alternatives: List[Constructor]

  def debruijnize(self, env):
    env = env.declare_type(self.name)
#    new_bindings = list(reversed(self.type_params)) + [self.name] + bindings
    for con in self.alternatives:
      con.debruijnize(env)
      env = env.declare_term_var(con.name, None)
    return env

  def shift(self, cutoff, amount):
    # Don't treat the Union name itself as a binder here,
    # it's more of a global variable. -Jeremy
    n = len(self.type_params)
    return Union(self.location, self.name, self.type_params,
                 [c.shift(cutoff + n, amount) for c in self.alternatives])

  def __str__(self):
    return 'union ' + self.name + '<' + ','.join(self.type_params) + '> {' \
      + ' '.join([str(c) for c in self.alternatives]) + '}'
  
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
    new_bindings = list(reversed(self.parameters)) \
      + list(reversed(self.pattern.parameters)) \
      + bindings
    self.body.debruijnize(new_bindings)
    
@dataclass
class RecFun(Statement):
  name: str
  type_params: List[str]
  params: List[Type]
  returns: Type
  cases: List[FunCase]

  def shift(self, cutoff, amount):
    return self
  
  def debruijnize(self, bindings):
    new_bindings = list(reversed(self.type_params)) + [self.name] + bindings
    for ty in self.params:
      ty.debruijnize(new_bindings)
    self.returns.debruijnize(new_bindings)
    for c in self.cases:
      c.debruijnize(new_bindings)
    return self.name
    
  def __str__(self):
    return 'function ' + self.name + '<' + ','.join(self.type_params) + '>' \
      + '(' + ','.join([str(ty) for ty in self.params]) + ')' \
      + ' -> ' + str(self.returns) + '{\n' \
      + '\n'.join([str(c) for c in self.cases]) \
      + '\n}'

  def __repr__(self):
    return str(self)

  def __eq__(self, other):
    if not isinstance(other, RecFun):
      return False
    return self.name == other.name

  def reduce(self, env):
    clos = RecFunClosure(self.location, self.name, self.type_params,
                         self.params, self.returns, self.cases, None)
    clos.env = env.extend(self.name, clos)
    return clos

  def substitute(self, sub):
    return self

@dataclass
class RecFunClosure(Statement):
  name: str
  type_params: List[str]
  params: List[Type]
  returns: Type
  cases: List[FunCase]
  env: Any

  def shift(self, cutoff, amount):
    return self
  
  def __str__(self):
    return '[recfun ' + self.name + ']'
  # + '<' + ','.join(self.type_params) + '>' \
  #     + '(' + ','.join([str(ty) for ty in self.params]) + ')' \
  #     + ' -> ' + str(self.returns) + '{\n' \
  #     + '\n'.join([str(c) for c in self.cases]) \
  #     + '\n}'

  def __repr__(self):
    return str(self)

  def __eq__(self, other):
    if not isinstance(other, RecFunClosure):
      return False
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

  # see 
  def debruijnize(self, env):
    return env
  
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

  
