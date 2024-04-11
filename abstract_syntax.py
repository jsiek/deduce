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

def base_name(name):
    ls = name.split('.')
    return ls[0]
  
@dataclass
class AST:
    location: Meta

@dataclass
class Term(AST):
  def shift_proof_vars(self, cutoff, amount):
    return self

@dataclass
class Formula(AST):
  def shift_proof_vars(self, cutoff, amount):
    return self

@dataclass
class Proof(AST):
  pass

@dataclass
class Statement(AST):
    pass

@dataclass
class Type(AST):
  def shift_term_vars(self, cutoff, amount):
    return self
  def shift_proof_vars(self, cutoff, amount):
    return self

################ Types ######################################

# @dataclass
# class TypeName(Type):
#   name: str
#   index: int = -1

#   def copy(self):
#     return TypeName(self.location, self.name, self.index)
  
#   def __str__(self):
#     return self.name + '$'

#   def __repr__(self):
#     return str(self)

#   def __eq__(self, other):
#     if not isinstance(other, TypeName):
#       return False
#     return self.name == other.name

#   def free_vars(self):
#     return set([self.name])

#   def substitute(self, sub):
#     if self.name in sub.keys():
#       return sub[self.name]
#     else:
#       return self

#   def uniquify(self, env):
#     if self.name not in env.keys():
#       error(self.location, "uniquify: could not find " + self.name \
#             + '\nin ' + str(env))
#     self.name = env[self.name]
    
#   def debruijnize(self, env):
#     self.index = env.index_of_type_var(self.name)

#   def shift_type_vars(self, cutoff, amount):
#     if self.index >= cutoff:
#       return TypeName(self.location, self.name, self.index + amount)
#     else:
#       return self
    
@dataclass
class IntType(Type):
    
  def copy(self):
    return IntType(self.location)
  
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

  def uniquify(self, env):
    pass
  
  def debruijnize(self, env):
    pass

  def shift_type_vars(self, cutoff, amount):
    return self
  
@dataclass
class BoolType(Type):
  def copy(self):
    return BoolType(self.location)
  
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

  def uniquify(self, env):
    pass
  
  def debruijnize(self, env):
    pass

  def shift_type_vars(self, cutoff, amount):
    return self
  
@dataclass
class TypeType(Type):
  def copy(self):
    return TypeType(self.location)
  
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

  def uniquify(self, env):
    pass
  
  def debruijnize(self, env):
    pass

  def shift_type_vars(self, cutoff, amount):
    return self
  
@dataclass
class FunctionType(Type):
  type_params: List[str]
  param_types: List[Type]
  return_type: Type

  def copy(self):
    return FunctionType(self.location,
                        [p for p in self.type_params],
                        [ty.copy() for ty in self.param_types],
                        self.return_type.copy())

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
      new_sub = {k:v.shift_type_vars(0, n) for (k,v) in sub.items() }
      return FunctionType(self.location, self.type_params,
                          [pt.substitute(new_sub) for pt in self.param_types],
                          self.return_type.substitute(new_sub))
    
  def uniquify(self, env):
    body_env = {x:y for (x,y) in env.items()}
    new_type_params = [generate_name(t) for t in self.type_params]
    for (old,new) in zip(self.type_params, new_type_params):
      body_env[old] = new
    self.type_params = new_type_params
    for p in self.param_types:
      p.uniquify(body_env)
    self.return_type.uniquify(body_env)
    
  def debruijnize(self, env):
    body_env = env.declare_type_vars(self.location, self.type_params)
    for p in self.param_types:
      p.debruijnize(body_env)
    self.return_type.debruijnize(body_env)

  def shift_type_vars(self, cutoff, amount):
    n = len(self.type_params)
    return FunctionType(self.location, self.type_params,
                        [ty.shift_type_vars(cutoff + n, amount) for ty in self.param_types],
                        self.return_type.shift_type_vars(cutoff + n, amount))
    
@dataclass
class TypeInst(Type):
  typ: Type
  arg_types: List[Type]

  def copy(self):
    return TypeInst(self.location,
                    self.typ.copy(),
                    [ty.copy() for ty in self.arg_types])
  
  def __str__(self):
    return str(self.typ) + \
      '<' + ','.join([str(arg) for arg in self.arg_types]) + '>'

  def __repr__(self):
    return str(self)

  def __eq__(self, other):
    match other:
      case TypeInst(l, typ, arg_types):
        return self.typ == typ and \
          all([t1 == t2 for (t1, t2) in zip(self.arg_types, arg_types)])
      case GenericUnknownInst(loc, typ):
        return self.typ == typ
      case _:
        return False

  def free_vars(self):
    return set().union(*[at.free_vars() for at in self.arg_types])

  def substitute(self, sub):
    return TypeInst(self.location, self.typ.substitute(sub),
                    [ty.substitute(sub) for ty in self.arg_types])

  def uniquify(self, env):
    self.typ.uniquify(env)
    for ty in self.arg_types:
      ty.uniquify(env)
  
  def debruijnize(self, env):
    self.typ.debruijnize(env)
    for ty in self.arg_types:
      ty.debruijnize(bindings)

  def shift_type_vars(self, cutoff, amount):
    return TypeInst(self.location,
                    self.typ.shift_type_vars(cutoff, amount),
                    [ty.shift_type_vars(cutoff, amount) for ty in self.arg_types])
    
# This is the type of a constructor such as 'empty' of a generic union
# when we do not yet know the type arguments.
@dataclass
class GenericUnknownInst(Type):
  typ: Type

  def copy(self):
    return GenericUnknownInst(self.location, self.typ.copy())
  
  def __str__(self):
    return str(self.typ) + '<?>'

  def __eq__(self, other):
    match other:
      case TypeInst(l, typ, arg_types):
        return self.typ == typ
      case GenericUnknownInst(l, typ):
        return self.typ == typ
      case _:
        return False

  def free_vars(self):
    return set()

  def substitute(self, sub):
    return self

  def uniquify(self, env):
    self.typ.uniquify(env)
  
  def debruijnize(self, env):
    self.typ.debruijnize(env)

  def shift_type_vars(self, cutoff, amount):
    return GenericUnknownInst(self.location,
                              self.typ.shift_type_vars(cutoff, amount))
  
################ Patterns ######################################

@dataclass
class Pattern(AST):
    pass

@dataclass
class PatternBool(Pattern):
  value : bool

  def __str__(self):
      return "true" if self.value else "false"

  def __repr__(self):
      return str(self)

  def uniquify(self, env):
    pass

  def bindings(self):
    return []

  def set_bindings(self, new_bindings):
    pass
  
@dataclass
class PatternCons(Pattern):
  constructor : Term
  parameters : List[str]

  def bindings(self):
    return self.parameters

  def set_bindings(self, params):
    self.parameters = params
  
  def copy(self):
    return PatternCons(self.location,
                       self.constructor.copy(),
                       [p for p in self.parameters])
  
  def __str__(self):
      return str(self.constructor) + '(' + ",".join(self.parameters) + ')'

  def __repr__(self):
      return str(self)

  def debruijnize(self, env):
    self.constructor.debruijnize(env)

  def uniquify(self, env):
    self.constructor.uniquify(env)
    
  def shift_type_vars(self, cutoff, amount):
    return PatternCons(self.location,
                       self.constructor.shift_type_vars(cutoff, amount),
                       self.parameters)
    
  def shift_term_vars(self, cutoff, amount):
    return PatternCons(self.location,
                       self.constructor.shift_term_vars(cutoff, amount),
                       self.parameters)

    
################ Terms ######################################

@dataclass
class Generic(Term):
  type_params: List[str]
  body: Term

  def copy(self):
    return Generic(self.location,
                   [T for T in self.type_params],
                   self.body.copy())
  
  def __str__(self):
    return "generic " + ",".join(self.type_params) + "{" + str(self.body) + "}"

  def __repr__(self):
    return str(self)

  def __eq__(self, other):
      if not isinstance(other, Generic):
          return False
      ren = {x: Var(self.location, y) for (x,y) in zip(self.type_params, other.type_params) }
      new_body = self.body.substitute(ren)
      return new_body == other.body

  def reduce(self, env):
      return self.body.reduce(env)

  def substitute(self, sub):
      n = len(self.type_params)
      new_sub = {k: v.shift_term_vars(0, n) for (k,v) in sub.items()}
      return Generic(self.location, self.type_params, self.body.substitute(new_sub))

  def debruijnize(self, env):
    body_env = env.declare_type_vars(self.location,
                                     [(x,None) for x in self.type_params])
    self.body.debruijnize(body_env)

  def uniquify(self, env):
    body_env = {x:y for (x,y) in env.items()}
    new_type_params = [generate_name(x) for x in self.type_params]
    for (old,new) in zip(self.type_params, new_type_params):
      body_env[old] = new
    self.type_params = new_type_params
    self.body.uniquify(body_env)
    
  def shift_type_vars(self, cutoff, amount):
    n = len(self.type_params)
    return Generic(self.location, self.type_params,
                  self.body.shift_type_vars(cutoff, amount))

  def shift_term_vars(self, cutoff, amount):
    return Lambda(self.location, self.type_params, self.body.shift_term_vars(cutoff, amount))
  

  
@dataclass
class Conditional(Term):
  cond: Term
  thn: Term
  els: Term

  def copy(self):
    return Conditional(self.location,
                       self.cond.copy(),
                       self.thn.copy(), self.els.copy())
  
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
  
  def debruijnize(self, env):
    self.cond.debruijnize(env)
    self.thn.debruijnize(env)
    self.els.debruijnize(env)

  def uniquify(self, env):
    self.cond.uniquify(env)
    self.thn.uniquify(env)
    self.els.uniquify(env)
    
  def shift_type_vars(self, cutoff, amount):
    return Conditional(self.location,
                       self.cond.shift_type_vars(cutoff, amount),
                       self.thn.shift_type_vars(cutoff, amount),
                       self.els.shift_type_vars(cutoff, amount))

  def shift_term_vars(self, cutoff, amount):
    return Conditional(self.location,
                       self.cond.shift_term_vars(cutoff, amount),
                       self.thn.shift_term_vars(cutoff, amount),
                       self.els.shift_term_vars(cutoff, amount))
  
    
@dataclass
class TAnnote(Term):
  subject: Term
  typ: Type

  def copy(self):
    return TAnnote(self.location,
                   self.subject.copy(),
                   self.typ.copy())
  
  def __str__(self):
      return str(self.subject) + ':' + str(self.typ)
    
  def __repr__(self):
      return str(self)
    
  def reduce(self, env):
    return self.subject.reduce(env)
  
  def substitute(self, sub):
    return TAnnote(self.location, self.subject.substitute(sub),
                   self.typ.substitute(sub))
  
  def debruijnize(self, env):
    self.subject.debruijnize(env)
    self.typ.debruijnize(env)

  def uniquify(self, env):
    self.subject.uniquify(env)
    self.typ.uniquify(env)
    
  def shift_type_vars(self, cutoff):
    return TAnnote(self.location,
                   self.subject.shift_type_vars(cutoff, amount),
                   self.typ.shift_type_vars(cutoff, amount))

  def shift_term_vars(self, cutoff):
    return TAnnote(self.location,
                   self.subject.shift_term_vars(cutoff, amount),
                   self.typ.shift_term_vars(cutoff, amount))
  
@dataclass
class Var(AST):
  name: str
  index: int = -1

  def free_vars(self):
    return set([self.name])
  
  def copy(self):
    return Var(self.location, self.name, self.index)
  
  def __eq__(self, other):
      if isinstance(other, DefinedValue):
        return self == other.body
      if not isinstance(other, Var):
          return False
      return self.name == other.name 
  
  def __str__(self):
      if base_name(self.name) == 'zero':
        return '0'
      else:
        return base_name(self.name)

  def __repr__(self):
      return str(self)
    
  def reduce(self, env):
      res = env.get_value_of_term_var(self)
      if res:
          return res.reduce(env)
      else:
          return self
  
  def substitute(self, sub):
      if self.name in sub:
          return sub[self.name]
      else:
          return self
        
  def debruijnize(self, env):
    self.index = env.index_of_term_var(self.name)

  def uniquify(self, env):
    #print('uniquify var ' + str(self))
    #print(str(env))
    if self.name not in env.keys():
      error(self.location, "uniquify: could not find " + self.name \
            + '\nin ' + str(env))
    self.name = env[self.name]
    #print('finished uniquify var ' + str(self))
    
  def shift_type_vars(self, cutoff, amount):
    return self
  
  def shift_term_vars(self, cutoff, amount):
    if self.index >= cutoff:
      return Var(self.location, self.name, self.index + amount)
    else:
      return self
    
@dataclass
class Int(Term):
  value: int

  def copy(self):
    return Int(self.location, self.value)
  
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

  def uniquify(self, env):
    pass
  
  def debruijnize(self, env):
    pass

  def shift_type_vars(self, cutoff, amount):
    return self
  
  def shift_term_vars(self, cutoff, amount):
    return self

@dataclass
class Lambda(Term):
  vars: List[str]
  body: Term

  def copy(self):
    return Lambda(self.location,
                  [v for v in self.vars],
                  self.body.copy())
  
  def __str__(self):
    return "λ" + ",".join(self.vars) + "{" + str(self.body) + "}"

  def __repr__(self):
    return str(self)

  def __eq__(self, other):
      if not isinstance(other, Lambda):
          return False
      ren = {x: Var(self.location, y) for (x,y) in zip(self.vars, other.vars) }
      new_body = self.body.substitute(ren)
      return new_body == other.body

  def reduce(self, env):
      return Closure(self.location, self.vars, self.body, env)

  def substitute(self, sub):
      n = len(self.vars)
      new_sub = {k: v.shift_term_vars(0, n) for (k,v) in sub.items()}
      return Lambda(self.location, self.vars, self.body.substitute(new_sub))

  def debruijnize(self, env):
    body_env = env.declare_term_vars(self.location,
                                     [(x,None) for x in self.vars])
    self.body.debruijnize(body_env)

  def uniquify(self, env):
    #print('uniquify Lambda ' + str(self))
    body_env = {x:y for (x,y) in env.items()}
    new_vars = [generate_name(x) for x in self.vars]
    for (old,new) in zip(self.vars, new_vars):
      body_env[old] = new
    self.vars = new_vars
    #print('body_env ' + str(body_env))
    self.body.uniquify(body_env)
    
  def shift_type_vars(self, cutoff, amount):
    n = len(self.vars)
    return Lambda(self.location, self.vars,
                  self.body.shift_type_vars(cutoff, amount))

  def shift_term_vars(self, cutoff, amount):
    n = len(self.vars)
    return Lambda(self.location, self.vars, self.body.shift_term_vars(cutoff + n, amount))
  
@dataclass
class Closure(Term):
  vars: List[str]
  body: Term
  env: Any
  
  def __str__(self):
    return "closure " + ",".join([v for v in self.vars]) + "{" + str(self.body) + "}"

  def __repr__(self):
    return str(self)

  def __eq__(self, other):
      if not isinstance(other, Closure):
          return False
      sub = {y: Var(self.location, x) for (x,y) in zip(self.vars, other.vars)}
      return self.body == other.body.substitute(sub)

  def reduce(self, env):
      return self

  def substitute(self, sub):
      n = len(self.vars)
      new_sub = {k: v.shift_term_vars(0, n) for (k,v) in sub.items()}
      return Closure(self.location, self.vars, self.body.substitute(new_sub))

  def shift_type_vars(self, cutoff, amount):
    return Closure(self.location, self.vars,
                   self.body.shift_type_vars(cutoff, amount),
                   self.env.shift_type_vars(cutoff, amount))

  def shift_term_vars(self, cutoff, amount):
    n = len(self.vars)
    return Closure(self.location, self.vars,
                   self.body.shift_term_vars(cutoff + n, amount),
                   self.env.shift_term_vars(cutoff + n, amount))
  
@dataclass
class DefinedValue(Term):
  name: str
  body: Term

  def __str__(self):
    #return "{|" + self.name + " := " + str(self.body) + "|}"
    return base_name(self.name)

  def __repr__(self):
    return str(self)

  def __eq__(self, other):
    if not isinstance(other, DefinedValue):
      return self.body == other
    return self.name == other.name

  def reduce(self, env):
    if self in get_reduce_only():
      return self.body.reduce(env)
    else:
      return self

  def substitute(self, sub):
    return DefinedValue(self.location, self.name, self.body.substitute(sub))
    
def is_match(pattern, arg, subst):
    ret = False
    match (pattern, arg):
      case (PatternCons(loc1, constr, []),
            Var(loc2, name, index)):
        ret = constr == arg
      case (PatternCons(loc1, constr, params),
            Call(loc2, Var(loc3, name, index), args, infix)):
        if constr == Var(loc3, name, index) and len(params) == len(args):
            for (k,v) in zip(params, args):
                subst[k] = v
            ret = True
        else:
            ret = False
      case _:
        ret = False
    return ret

reduce_only = []

def set_reduce_only(defs):
  global reduce_only
  reduce_only = defs

def get_reduce_only():
  global reduce_only
  return reduce_only
  
@dataclass
class Call(Term):
  rator: Term
  args: list[Term]
  infix: bool

  def copy(self):
    return Call(self.location,
                self.rator.copy(),
                [arg.copy() for arg in self.args],
                self.infix)
  
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
    match fun:
      # case DefinedValue(loc, name, val):
      #   if fun in get_reduce_only():
      #     ret = Call(self.location, val, args, self.infix).reduce(env)
      #   else:
      #     ret = Call(self.location, fun, args, self.infix)
      case Closure(loc, vars, body, clos_env):
        #print('*** applying function ' + str(fun) + '\nto ' + str(args))
        body_env = clos_env.define_term_vars(loc, zip(vars, args))
        #print('*** body ' + str(body_env))
        ret = body.reduce(body_env)
        #print('*** call result: ' + str(ret))
      case RecFunClosure(loc, name, typarams, params, returns, cases, clos_env):
        if fun in get_reduce_only(): # len(get_reduce_only()) == 0 or 
          #print('*** applying function ' + str(fun) + '\nto ' + str(args))
          first_arg = args[0]
          rest_args = args[1:]
          for fun_case in cases:
              subst = {}
              if is_match(fun_case.pattern, first_arg, subst):
                  #print('*** match subst ' + str(subst))
                  body_env = clos_env.define_term_vars(loc, subst.items())
                  body_env = body_env.define_term_vars(loc, zip(fun_case.parameters, rest_args))
                  #print('*** body ' + str(body_env))
                  ret = fun_case.body.reduce(body_env)
                  #print('*** ret ' + str(ret))
                  num_bindings = len(fun_case.pattern.parameters) + len(fun_case.parameters)
                  #result = ret.shift_term_vars(0, - num_bindings)
                  result = ret
                  #print('*** call result: ' + str(result))
                  return result
        ret = Call(self.location, fun, args, self.infix)
      case _:
        ret = Call(self.location, fun, args, self.infix)
    return ret

  def substitute(self, sub):
    return Call(self.location, self.rator.substitute(sub),
                [arg.substitute(sub) for arg in self.args],
                self.infix)

  def shift_type_vars(self, cutoff, amount):
    return Call(self.location, self.rator.shift_type_vars(cutoff, amount),
                [arg.shift_type_vars(cutoff, amount) for arg in self.args],
                self.infix)

  def shift_term_vars(self, cutoff, amount):
    return Call(self.location, self.rator.shift_term_vars(cutoff, amount),
                [arg.shift_term_vars(cutoff, amount) for arg in self.args],
                self.infix)
  
  def debruijnize(self, env):
    self.rator.debruijnize(env)
    for arg in self.args:
      arg.debruijnize(env)

  def uniquify(self, env):
    #print('uniquify call ' + str(self))
    #print(str(env))
    self.rator.uniquify(env)
    for arg in self.args:
      arg.uniquify(env)
    #print('finished uniquify call ' + str(self))
      
@dataclass
class SwitchCase(AST):
  pattern: Pattern
  body: Term
  
  def copy(self):
    return SwitchCase(self.location,
                      self.pattern.copy(),
                      self.body.copy())
  
  def __str__(self):
      return 'case ' + str(self.pattern) + '{' + str(self.body) + '}'

  def __repr__(self):
      return str(self)

  def reduce(self, env):
      n = len(self.pattern.parameters)
      return SwitchCase(self.location,
                        PatternCons(self.pattern.location,
                                    self.pattern.constructor,
                                    self.pattern.parameters),
                        self.body.reduce(env))
    
  def substitute(self, sub):
      n = len(self.pattern.parameters)
      new_sub = {k: v.shift_term_vars(0, n) for (k,v) in sub.items()}
      return SwitchCase(self.location,
                        self.pattern,
                        self.body.substitute(new_sub))

  def shift_type_vars(self, cutoff, amount):
    return SwitchCase(self.location,
                      self.pattern.shift_type_vars(cutoff, amount),
                      self.body.shift_type_vars(cutoff, amount))

  def shift_type_vars(self, cutoff, amount):
    return SwitchCase(self.location,
                      self.pattern.shift_type_vars(cutoff, amount),
                      self.body.shift_type_vars(cutoff, amount))

  def shift_term_vars(self, cutoff, amount):
    n = len(self.pattern.parameters)
    return SwitchCase(self.location,
                      self.pattern.shift_term_vars(cutoff + n, amount),
                      self.body.shift_term_vars(cutoff + n, amount))
  
  def debruijnize(self, env):
    body_env.declare_term_vars([(x,None) for x in self.pattern.parameters])
    self.body.debruijnize(body_env)

  def uniquify(self, env):
    self.pattern.uniquify(env)
    body_env = {x:y for (x,y) in env.items()}
    new_params = [generate_name(x) for x in self.pattern.parameters]
    for (old,new) in zip(self.pattern.parameters, new_params):
      body_env[old] = new
    self.pattern.parameters = new_params
    self.body.uniquify(body_env)
    
  def __eq__(self, other):
    if not isinstance(other, SwitchCase):
      return False
    return self.pattern.constructor == other.pattern.constructor \
      and self.body == other.body
    
@dataclass
class Switch(Term):
  subject: Term
  cases: List[SwitchCase]

  def copy(self):
    return Switch(self.location,
                  self.subject.copy(),
                  [c.copy() for c in self.cases])
  
  def __str__(self):
      return 'switch ' + str(self.subject) + ' { ' \
          + ' '.join([str(c) for c in self.cases]) \
          + ' }'

  def __repr__(self):
      return str(self)
  
  def reduce(self, env):
      new_subject = self.subject.reduce(env)
      for c in self.cases:
          subst = {}
          if is_match(c.pattern, new_subject, subst):
            new_env = env.define_term_vars(self.location, subst.items())
            return c.body.reduce(new_env)
      new_cases = [c.reduce(env) for c in self.cases]
      return Switch(self.location, new_subject, new_cases)
  
  def substitute(self, sub):
      return Switch(self.location,
                    self.subject.substitute(sub),
                    [c.substitute(sub) for c in self.cases])

  def shift_type_vars(self, cutoff, amount):
    return Switch(self.location, self.subject.shift_type_vars(cutoff, amount),
                  [c.shift_type_vars(cutoff, amount) for c in self.cases])

  def shift_term_vars(self, cutoff, amount):
    return Switch(self.location, self.subject.shift_term_vars(cutoff, amount),
                  [c.shift_term_vars(cutoff, amount) for c in self.cases])
  
  def debruijnize(self, env):
    self.subject.debruijnize(env)
    for c in self.cases:
      c.debruijnize(env)

  def uniquify(self, env):
    self.subject.uniquify(env)
    for c in self.cases:
      c.uniquify(env)
      
  def __eq__(self, other):
    if not isinstance(other, Switch):
      return False
    eq_subject = self.subject == other.subject
    eq_cases = all([c1 == c2 for (c1,c2) in zip(self.cases, other.cases)])
    return eq_subject and eq_cases

@dataclass
class TermInst(Term):
  subject: Term
  type_args: List[Type]

  def copy(self):
    return TermInst(self.location,
                    self.subject.copy(),
                    [ty.copy() for ty in self.type_args])
  
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

  def shift_type_vars(self, cutoff, amount):
    return TermInst(self.location, self.subject.shift_type_vars(cutoff, amount),
                    [ty.shift_type_vars(cutoff, amount) for ty in self.type_args])

  def shift_term_vars(self, cutoff, amount):
    return TermInst(self.location, self.subject.shift_term_vars(cutoff, amount),
                    [ty.shift_term_vars(cutoff, amount) for ty in self.type_args])
  
  def debruijnize(self, env):
    self.subject.debruijnize(env)
    for ty in self.type_args:
      ty.debruijnize(env)

  def uniquify(self, env):
    self.subject.uniquify(env)
    for ty in self.type_args:
      ty.uniquify(env)
      
  
@dataclass
class TLet(Term):
  var: str
  rhs: Term
  body: Term

  def reduce(self, env):
    rhs = self.rhs.reduce(env)
    body_env = env.define_term_var(self.location, self.var, None, rhs)
    return self.body.reduce(body_env)
    
  def copy(self):
    return TLet(self.location, self.var, self.rhs.copy(), self.body.copy())
  
  def debruijnize(self, env):
    self.rhs.debruijnize(env)
    body_env = env.declare_term_var(self.location, self.var, None)
    self.body.debruijnize(body_env)

  def uniquify(self, env):
    self.rhs.uniquify(env)
    body_env = {x:y for (x,y) in env.items()}
    new_var = generate_name(self.var)
    body_env[self.var] = new_var
    self.var = new_var
    self.body.uniquify(body_env)
    
  def shift_type_vars(self, cutoff, amount):
    return TLet(self.location, self.var,
                self.rhs.shift_type_vars(cutoff, amount),
                self.body.shift_type_vars(cutoff, amount))

  def shift_term_vars(self, cutoff, amount):
    return TLet(self.location, self.var,
                self.rhs.shift_term_vars(cutoff, amount),
                self.body.shift_term_vars(cutoff + 1, amount))
  
################ Formulas ######################################
  
@dataclass
class Bool(Formula):
  value: bool
  
  def copy(self):
    return Bool(self.location, self.value)
  
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
  def debruijnize(self, env):
    pass
  def uniquify(self, env):
    pass
  def shift_type_vars(self, cutoff, amount):
    return self
  def shift_term_vars(self, cutoff, amount):
    return self
  
@dataclass
class And(Formula):
  args: list[Formula]

  def copy(self):
    return And(self.location, [arg.copy() for arg in self.args])
  
  def __str__(self):
    return ' and '.join(['(' + str(arg) + ')' for arg in self.args])
  def __repr__(self):
    return str(self)
  def __eq__(self, other):
    if not isinstance(other, And):
      return False
    return all([arg1 == arg2 for arg1,arg2 in zip(self.args, other.args)])
  def reduce(self, env):
    return And(self.location, [arg.reduce(env) for arg in self.args])
  def substitute(self, sub):
    return And(self.location, [arg.substitute(sub) for arg in self.args])
  def debruijnize(self, env):
    for arg in self.args:
      arg.debruijnize(env)
  def uniquify(self, env):
    for arg in self.args:
      arg.uniquify(env)
  def shift_type_vars(self, cutoff, amount):
    return And(self.location, [arg.shift_type_vars(cutoff, amount) for arg in self.args])
  def shift_term_vars(self, cutoff, amount):
    return And(self.location, [arg.shift_term_vars(cutoff, amount) for arg in self.args])
  
@dataclass
class Or(Formula):
  args: list[Formula]
  def copy(self):
    return Or(self.location, [arg.copy() for arg in self.args])
  def __str__(self):
    return ' or '.join([str(arg) for arg in self.args])
  def __eq__(self, other):
    if not isinstance(other, Or):
      return False
    return all([arg1 == arg2 for arg1,arg2 in zip(self.args, other.args)])
  def reduce(self, env):
    return Or(self.location, [arg.reduce(env) for arg in self.args])
  def substitute(self, sub):
    return Or(self.location, [arg.substitute(sub) for arg in self.args])
  def debruijnize(self, env):
    for arg in self.args:
      arg.debruijnize(env)
  def uniquify(self, env):
    for arg in self.args:
      arg.uniquify(env)
  def shift_type_vars(self, cutoff, amount):
    return Or(self.location, [arg.shift_type_vars(cutoff, amount) for arg in self.args])
  def shift_term_vars(self, cutoff, amount):
    return Or(self.location, [arg.shift_term_vars(cutoff, amount) for arg in self.args])

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
  def copy(self):
    return IfThen(self.location, self.premise.copy(), self.conclusion.copy())
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
  def shift_type_vars(self, cutoff, amount):
    return IfThen(self.location, self.premise.shift_type_vars(cutoff, amount),
                  self.conclusion.shift_type_vars(cutoff, amount))
  def shift_term_vars(self, cutoff, amount):
    return IfThen(self.location, self.premise.shift_term_vars(cutoff, amount),
                  self.conclusion.shift_term_vars(cutoff, amount))
  def debruijnize(self, env):
    self.premise.debruijnize(env)
    self.conclusion.debruijnize(env)
  def uniquify(self, env):
    self.premise.uniquify(env)
    self.conclusion.uniquify(env)

    
@dataclass
class All(Formula):
  vars: list[Tuple[str,Type]]
  body: Formula

  def copy(self):
    return All(self.location,
               [(x, t.copy()) for (x,t) in self.vars],
               self.body.copy())
  
  def __str__(self):
    return 'all ' + ",".join([base_name(v) + ":" + str(t) for (v,t) in self.vars]) \
        + '. ' + str(self.body)

  def reduce(self, env):
    n = len(self.vars)
    return All(self.location, [(x, ty.reduce(env)) for (x,ty) in self.vars], self.body.reduce(env))

  def substitute(self, sub):
    n = len(self.vars)
    #new_sub = {k: v.shift_term_vars(0, n) for (k,v) in sub.items()}
    return All(self.location,
               [(x, ty.substitute(sub)) for (x,ty) in self.vars],
               self.body.substitute(sub))
  
  def __eq__(self, other):
    if not isinstance(other, All):
      return False
    sub = {y: Var(self.location, x) for ((x,tx),(y,ty))in zip(self.vars, other.vars)}
    return self.body == other.body.substitute(sub)

  def shift_type_vars(self, cutoff, amount):
    return All(self.location, self.vars, self.body.shift_type_vars(cutoff, amount))

  def shift_term_vars(self, cutoff, amount):
    n = len(self.vars)
    return All(self.location, self.vars, self.body.shift_term_vars(cutoff + n, amount))
  
  def debruijnize(self, env):
    body_env = env.declare_term_vars(self.vars)
    self.body.debruijnize(body_env)

  def uniquify(self, env):
    body_env = {x:y for (x,y) in env.items()}
    new_vars = []
    for (x,ty) in self.vars:
      t = ty.copy()
      t.uniquify(body_env)
      new_x = generate_name(x)
      new_vars.append( (new_x,t) )
      body_env[x] = new_x
    self.vars = new_vars
    self.body.uniquify(body_env)
    
@dataclass
class Some(Formula):
  vars: list[Tuple[str,Type]]
  body: Formula

  def copy(self):
    return Some(self.location,
               [(x,ty.copy()) for (x,ty) in self.vars],
               self.body.copy())
  
  def __str__(self):
    return 'some ' + ",".join([base_name(v) + ":" + str(t) for (v,t) in self.vars]) \
        + '. ' + str(self.body)
  
  def reduce(self, env):
    n = len(self.vars)
    return Some(self.location, [(x, ty.reduce(env)) for (x,ty) in self.vars], self.body.reduce(env))
  
  def substitute(self, sub):
    n = len(self.vars)
    new_sub = {k: v.shift_term_vars(0, n) for (k,v) in sub.items()}
    return Some(self.location,
                [(x,ty.substitute(sub)) for (x,ty) in self.vars],
                self.body.substitute(new_sub))
  
  def debruijnize(self, env):
    body_env = env.declare_term_vars(self.vars)
    self.body.debruijnize(body_env)

  def uniquify(self, env):
    body_env = {x:y for (x,y) in env.items()}
    new_vars = []
    for (x,ty) in self.vars:
      t = ty.copy()
      t.uniquify(body_env)
      new_x = generate_name(x)
      new_vars.append( (new_x,t) )
      body_env[x] = new_x
    self.vars = new_vars
    self.body.uniquify(body_env)
    
  def shift_type_vars(self, cutoff, amount):
    return Some(self.location, self.vars, self.body.shift_type_vars(cutoff, amount))

  def shift_term_vars(self, cutoff, amount):
    n = len(self.vars)
    return Some(self.location, self.vars,
                self.body.shift_term_vars(cutoff + n, amount))

  def __eq__(self, other):
    if not isinstance(other, Some):
      return False
    sub = {y: Var(self.location, x) for ((x,tx),(y,ty))in zip(self.vars, other.vars)}
    return self.body == other.body.substitute(sub)
  
################ Proofs ######################################
  
@dataclass
class PVar(Proof):
  name: str
  index: int = -1
  
  def copy(self):
    return PVar(self.location, self.name, self.index)
  
  def __eq__(self, other):
    if not isinstance(other, PVar):
      return False
    return self.name == other.name
  
  def __str__(self):
      return self.name

  def debruijnize(self, env):
    self.index = env.index_of_proof_var(self.name)

  def uniquify(self, env):
    self.name = env[self.name]
    
@dataclass
class PLet(Proof):
  label: str
  proved: Formula
  because: Proof
  body: Proof

  def __str__(self):
      return self.label + ': ' + str(self.proved) + ' by ' \
        + str(self.because) + '; ' + str(self.body)

  def debruijnize(self, env):
    self.proved.debruijnize(env)
    self.because.debruijnize(env)
    body_env = env.declare_proof_var(self.location, self.label, self.proved)
    self.body.debruijnize(body_env)

  def uniquify(self, env):
    self.proved.uniquify(env)
    self.because.uniquify(env)
    body_env = {x:y for (x,y) in env.items()}
    new_label = generate_name(self.label)
    body_env[self.label] = new_label
    self.label = new_label
    self.body.uniquify(body_env)
    
    
@dataclass
class PAnnot(Proof):
  claim: Formula
  reason: Proof

  def __str__(self):
      return 'have ' + str(self.claim) + ' by ' + str(self.reason)

  def debruijnize(self, env):
    self.claim.debruijnize(env)
    self.reason.debruijnize(env)

  def uniquify(self, env):
    #print('uniquify ' + str(self))
    self.claim.uniquify(env)
    self.reason.uniquify(env)
    
@dataclass
class Cases(Proof):
  subject: Proof
  cases: List[Tuple[str,Proof]]

  def debruijnize(self, env):
    self.subject.debruijnize(env)
    for c in self.cases:
      c.debruijnize(env)

  def uniquify(self, env):
    self.subject.uniquify(env)
    for c in self.cases:
      c.uniquify(env)
      
@dataclass
class ModusPonens(Proof):
  implication: Proof
  arg: Proof

  def __str__(self):
      return 'apply ' + str(self.implication) + ' with ' + str(self.arg)

  def debruijnize(self, env):
    self.implication.debruijnize(env)
    self.arg.debruijnize(env)

  def uniquify(self, env):
    self.implication.uniquify(env)
    self.arg.uniquify(env)
    
@dataclass
class ImpIntro(Proof):
  label: str
  premise: Formula
  body: Proof

  def __str__(self):
    return 'suppose ' + str(self.label) + ': ' + str(self.premise) + '{' + str(self.body) + '}'

  def debruijnize(self, env):
    if self.premise:
      self.premise.debruijnize(env)
    body_env = env.declare_proof_var(self.location, self.label, self.premise)
    self.body.debruijnize(body_env)

  def uniquify(self, env):
    if self.premise:
      self.premise.uniquify(env)
    body_env = copy_dict(env)
    new_label = generate_name(self.label)
    body_env[self.label] = new_label
    self.label = new_label
    self.body.uniquify(body_env)
    
@dataclass
class AllIntro(Proof):
  vars: List[Tuple[str,Type]]
  body: Proof

  def __str__(self):
    return 'arbitrary ' + ",".join([x + ":" + str(t) for (x,t) in self.vars]) \
        + '; ' + str(self.body)

  def debruijnize(self, env):
    body_env = env.declare_term_vars(self.vars)
    self.body.debruijnize(body_env)

  def uniquify(self, env):
    body_env = copy_dict(env)
    new_vars = []
    for (x,ty) in self.vars:
      t = ty.copy()
      t.uniquify(body_env)
      new_x = generate_name(x)
      new_vars.append( (new_x,t) )
      body_env[x] = new_x
    self.vars = new_vars
    self.body.uniquify(body_env)
    
@dataclass
class AllElim(Proof):
  univ: Proof
  args: List[Term]

  def __str__(self):
    return str(self.univ) + '[' + ','.join([str(arg) for arg in self.args]) + ']'

  def debruijnize(self, env):
    self.univ.debruijnize(env)
    for arg in self.args:
      arg.debruijnize(env)

  def uniquify(self, env):
    self.univ.uniquify(env)
    for arg in self.args:
      arg.uniquify(env)
      
@dataclass
class SomeIntro(Proof):
  witnesses: List[Term]
  body: Proof

  def __str__(self):
    return 'choose ' + ",".join([str(t) for t in self.witnesses]) \
        + '; ' + str(self.body)
  
  def uniquify(self, env):
    for t in self.witnesses:
      t.uniquify(env)
    self.body.uniquify(env)

@dataclass
class SomeElim(Proof):
  witnesses: List[str]
  label: str
  some: Proof
  body: Proof

  def __str__(self):
    return 'obtain ' + ",".join(self.witnesses) \
      + ' with ' + self.label \
      + ' from ' + str(self.some) \
      + '; ' + str(self.body)
  
  def uniquify(self, env):
    self.some.uniquify(env)
    body_env = copy_dict(env)
    new_witnesses = []
    for x in self.witnesses:
      new_x = generate_name(x)
      new_witnesses.append( new_x )
      body_env[x] = new_x
    new_label = generate_name(self.label)
    body_env[self.label] = new_label
    self.witnesses = new_witnesses
    self.label = new_label
    self.body.uniquify(body_env)
    
@dataclass
class PTuple(Proof):
  args: List[Proof]

  def __str__(self):
    return ', '.join([str(arg) for arg in self.args])

  def debruijnize(self, env):
    for arg in self.args:
      arg.debruijnize(env)

  def uniquify(self, env):
    for arg in self.args:
      arg.uniquify(env)

@dataclass
class PAndElim(Proof):
  which: int
  subject: Proof

  def __str__(self):
    return 'conjunct ' + str(self.which) + ' of ' + str(self.subject)

  def debruijnize(self, env):
    self.subject.debruijnize(env)

  def uniquify(self, env):
    self.subject.uniquify(env)
      
@dataclass
class PTrue(Proof):
  def __str__(self):
    return '.'
  def debruijnize(self, env):
    pass
  def uniquify(self, env):
    pass
  
@dataclass
class PReflexive(Proof):
  def __str__(self):
    return 'reflexive'
  def debruijnize(self, env):
    pass
  def uniquify(self, env):
    pass

@dataclass
class PHole(Proof):
  def __str__(self):
      return '?'
  def debruijnize(self, env):
    pass
  def uniquify(self, env):
    pass
  
@dataclass
class PSymmetric(Proof):
  body: Proof
  def __str__(self):
    return 'symmetric ' + str(self.body)
  def debruijnize(self, env):
    self.body.debruijnize(env)
  def uniquify(self, env):
    self.body.uniquify(env)

@dataclass
class PTransitive(Proof):
  first: Proof
  second: Proof
  def __str__(self):
    return 'transitive ' + str(self.first) + ' ' + str(self.second)
  def debruijnize(self, env):
    self.first.debruijnize(env)
    self.second.debruijnize(env)
  def uniquify(self, env):
    self.first.uniquify(env)
    self.second.uniquify(env)

@dataclass
class PInjective(Proof):
  constr: Type
  body: Proof
  def __str__(self):
    return 'injective ' + str(self.constr) + ' ' + str(self.body)
  def debruijnize(self, env):
    self.constr.debruijnize(env)
    self.body.debruijnize(env)
  def uniquify(self, env):
    self.constr.uniquify(env)
    self.body.uniquify(env)
  
@dataclass
class IndCase(AST):
  pattern: Pattern
  body: Proof

  def __str__(self):
    return 'case ' + str(self.pattern) + '{' + str(self.body) + '}'

  def debruijnize(self, env):
    body_env = env.declare_proof_var(self.location, 'IH', None)
    body_env = body_env.declare_term_vars([(x,None) for x in self.pattern.parameters])
    self.body.debruijnize(body_env)

  def uniquify(self, env):
    body_env = copy_dict(env)
    body_env['IH'] = 'IH'  # TODO: introduce explicit binders for IH
    new_params = [generate_name(x) for x in self.pattern.parameters]
    for (old,new) in zip(self.pattern.parameters, new_params):
      body_env[old] = new
    self.pattern.parameters = new_params
    self.pattern.uniquify(env)
    self.body.uniquify(body_env)
    
@dataclass
class Induction(Proof):
  typ: Type
  cases: List[IndCase]

  def __str__(self):
    return 'induction ' + str(self.typ) + '\n' \
      + '\n'.join([str(c) for c in self.cases])
  
  def debruijnize(self, env):
    self.typ.debruijnize(env)
    for c in self.cases:
      c.debruijnize(env)

  def uniquify(self, env):
    self.typ.uniquify(env)
    for c in self.cases:
      c.uniquify(env)
      
@dataclass
class SwitchProofCase(AST):
  pattern: Pattern
  body: Proof

  def __str__(self):
    return 'case ' + str(self.pattern) + '{' + str(self.body) + '}'

  def debruijnize(self, env):
    body_env = body_env.declare_term_vars([(x,None) for x in self.pattern.parameters])
    self.body.debruijnize(body_env)

  def uniquify(self, env):
    self.pattern.uniquify(env)
    body_env = copy_dict(env)
    new_params = [generate_name(x) for x in self.pattern.bindings()]
    for (old,new) in zip(self.pattern.bindings(), new_params):
      body_env[old] = new
    self.pattern.set_bindings(new_params)
    body_env['EQ'] = 'EQ'
    self.body.uniquify(body_env)
    
@dataclass
class SwitchProof(Proof):
  subject: Term
  cases: List[IndCase]

  def __str__(self):
      return 'switch ' + str(self.subject) \
        + '{' + '\n'.join([str(c) for c in self.cases]) + '}'
    
  def debruijnize(self, env):
    self.subject.debruijnize(env)
    for c in self.cases:
      c.debruijnize(env)

  def uniquify(self, env):
    self.subject.uniquify(env)
    for c in self.cases:
      c.uniquify(env)
      
@dataclass
class ApplyDefsGoal(Proof):
  definitions: List[Term]
  body: Proof

  def __str__(self):
      return 'apply ' + ', '.join([str(d) for d in self.definitions]) \
        + ' in goal; ' + str(self.body)

  def debruijnize(self, env):
    for d in self.definitions:
      d.debruijnize(env)
    self.body.debruijnize(env)

  def uniquify(self, env):
    for d in self.definitions:
      d.uniquify(env)
    self.body.uniquify(env)

@dataclass
class ApplyDefsFact(Proof):
  definitions: List[Term]
  subject: Proof

  def __str__(self):
      return 'apply ' + ', '.join([str(d) for d in self.definitions]) \
        + ' in ' + str(self.subject)

  def debruijnize(self, env):
    for d in self.definitions:
      d.debruijnize(env)
    self.subject.debruijnize(env)

  def uniquify(self, env):
    for d in self.definitions:
      d.uniquify(env)
    self.subject.uniquify(env)
    
@dataclass
class RewriteGoal(Proof):
  equation: Proof
  body: Proof

  def __str__(self):
      return 'rewrite goal with ' + str(self.equation) \
        + ' then ' + str(self.body)

  def debruijnize(self, env):
    self.equation.debruijnize(env)
    self.body.debruijnize(env)

  def uniquify(self, env):
    self.equation.uniquify(env)
    self.body.uniquify(env)
    
@dataclass
class RewriteFact(Proof):
  subject: Proof
  equation: Proof

  def __str__(self):
      return 'rewrite ' + str(self.subject) + ' with ' + str(self.equation)

  def debruijnize(self, env):
    self.subject.debruijnize(env)
    self.equation.debruijnize(env)

  def uniquify(self, env):
    self.subject.uniquify(env)
    self.equation.uniquify(env)
    
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
    return env.declare_proof_var(self.location, self.name, self.what)

  def uniquify(self, env):
    self.what.uniquify(env)
    self.proof.uniquify(env)
    new_name = generate_name(self.name)
    env[self.name] = new_name
    self.name = new_name
  
@dataclass
class Constructor(AST):
  name: str
  parameters: List[Type]

  def debruijnize(self, env):
    for ty in self.parameters:
      ty.debruijnize(env)

  def uniquify(self, env):
    for ty in self.parameters:
      ty.uniquify(env)
      
  def shift_type_vars(self, cutoff, amount):
    return Constructor(self.location, self.name,
                       [ty.shift_type_vars(cutoff, amount) for ty in self.parameters])

  def shift_term_vars(self, cutoff, amount):
    return Constructor(self.location, self.name,
                       [ty.shift_term_vars(cutoff, amount) for ty in self.parameters])
  
  def __str__(self):
    return self.name + '(' + ','.join([str(ty) for ty in self.parameters]) + ');'
      
@dataclass
class Union(Statement):
  name: str
  type_params: List[str]
  alternatives: List[Constructor]

  def reduce(self, env):
    return self
  
  def debruijnize(self, env):
    env = env.declare_type(self.location, self.name)
    body_env = env.declare_type_vars(self.location, self.type_params)
    for con in self.alternatives:
      con.debruijnize(body_env)
      env = env.declare_term_var(con.location, con.name, None)
    return env

  def uniquify(self, env):
    new_name = generate_name(self.name)
    env[self.name] = new_name
    self.name = new_name
    body_env = copy_dict(env)
    new_type_params = [generate_name(t) for t in self.type_params]
    for (old,new) in zip(self.type_params, new_type_params):
      body_env[old] = new
    self.type_params = new_type_params
    for con in self.alternatives:
      con.uniquify(body_env)
      new_con_name = generate_name(con.name)
      env[con.name] = new_con_name
      con.name = new_con_name
  
  def shift_type_vars(self, cutoff, amount):
    # Don't treat the Union name itself as a binder here,
    # it's more of a global variable. -Jeremy
    n = len(self.type_params)
    return Union(self.location, self.name, self.type_params,
                 [c.shift_type_vars(cutoff + n, amount) for c in self.alternatives])

  def shift_term_vars(self, cutoff, amount):
    return Union(self.location, self.name, self.type_params,
                 [c.shift_term_vars(cutoff, amount) for c in self.alternatives])
  
  def __str__(self):
    return base_name(self.name)
  
    # return 'union ' + self.name + '<' + ','.join(self.type_params) + '> {' \
    #   + ' '.join([str(c) for c in self.alternatives]) + '}'
  
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

  def debruijnize(self, env):
    self.pattern.debruijnize(env)
    body_env = env.declare_term_vars(self.location,
                                     [(x,None) for x in self.pattern.parameters])
    body_env = body_env.declare_term_vars(self.location,
                                          [(x,None) for x in self.parameters])
    self.body.debruijnize(body_env)

  def uniquify(self, env):
    self.pattern.uniquify(env)
    body_env = copy_dict(env)
    
    new_pat_params = [generate_name(x) for x in self.pattern.parameters]
    for (old,new) in zip(self.pattern.parameters, new_pat_params):
      body_env[old] = new
    self.pattern.parameters = new_pat_params

    new_params = [generate_name(x) for x in self.parameters]
    for (old,new) in zip(self.parameters, new_params):
      body_env[old] = new
    self.parameters = new_params

    self.body.uniquify(body_env)
    
  def shift_term_vars(self, cutoff, amount):
    n = len(self.pattern.parameters) + len(self.parameters)
    return FunCase(self.location, self.pattern.shift_term_vars(cutoff, amount),
                   self.parameters, self.body.shift_term_vars(cutoff + n, amount))
    
@dataclass
class RecFun(Statement):
  name: str
  type_params: List[str]
  params: List[Type]
  returns: Type
  cases: List[FunCase]

  def shift_type_vars(self, cutoff, amount):
    n = len(self.type_params)
    return RecFun(self.location, self.name, self.type_params,
                  [ty.shift_type_vars(cutoff + n, amount) for ty in self.params],
                  self.returns.shift_type_vars(cutoff + n, amount),
                  self.casts.shift_type_vars(cutoff + n, amount))

  def shift_term_vars(self, cutoff, amount):
    return RecFun(self.location, self.name, self.type_params,
                  self.params,
                  self.returns,
                  self.casts.shift_term_vars(cutoff + 1, amount))
                  
  def debruijnize(self, env):
    env = env.declare_term_var(self.location, self.name, None)
    body_env = env.declare_type_vars(self.location, self.type_params)
    for ty in self.params:
      ty.debruijnize(body_env)
    self.returns.debruijnize(body_env)
    for c in self.cases:
      c.debruijnize(body_env)
    return env

  def uniquify(self, env):
    new_name = generate_name(self.name)
    env[self.name] = new_name
    self.name = new_name
    
    body_env = copy_dict(env)
    new_type_params = [generate_name(t) for t in self.type_params]
    for (old,new) in zip(self.type_params, new_type_params):
      body_env[old] = new
    self.type_params = new_type_params
    
    for ty in self.params:
      ty.uniquify(body_env)
    self.returns.uniquify(body_env)
    for c in self.cases:
      c.uniquify(body_env)
  
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
    clos.env = env.define_term_var(self.location, self.name, None, clos)
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

  def shift_type_vars(self, cutoff, amount):
    n = len(self.type_params)
    return RecFunClosure(self.location, self.name, self.type_params,
                         [ty.shift_type_vars(cutoff + n, amount) for ty in self.params],
                         self.returns.shift_type_vars(cutoff + n, amount),
                         [case.shift_type_vars(cutoff + n, amount) for case in self.cases],
                         env) # cycles!?!?!?

  def shift_term_vars(self, cutoff, amount):
    return RecFunClosure(self.location, self.name, self.type_params,
                         self.params,
                         self.returns,
                         [case.shift_term_vars(cutoff, amount) for case in self.cases],
                         self.env) # cycles!?!?!

  def shift_proof_vars(self, cutoff, amount):
    return self
    
  def __str__(self):
    return base_name(self.name)
  
    # return '[' + self.name \
    #    + '<' + ','.join(self.type_params) + '>' \
    #    + '(' + ','.join([str(ty) for ty in self.params]) + ')' \
    #    + ' -> ' + str(self.returns) + '{' \
    #    + ' '.join([str(c) for c in self.cases]) \
    #    + '}' + ']'

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

  def debruijnize(self, env):
    if self.typ:
      self.typ.debruijnize(env)
    self.body.debruijnize(env)
    env = env.declare_term_var(self.location, self.name, self.typ)
    return env

  def uniquify(self, env):
    if self.typ:
      self.typ.uniquify(env)
    self.body.uniquify(env)
    new_name = generate_name(self.name)
    env[self.name] = new_name
    self.name = new_name
  
  def shift_type_vars(self, cutoff, amount):
    return Define(self.location, self.name,
                  self.typ.shift_type_vars(cutoff, amount),
                  self.body.shift_type_vars(cutoff, amount))

  def shift_term_vars(self, cutoff, amount):
    return Define(self.location, self.name,
                  self.typ.shift_term_vars(cutoff, amount),
                  self.body.shift_term_vars(cutoff, amount))
  
debruijnized_modules = set()

@dataclass
class Import(Statement):
  name: str
  ast: AST = None
  
  def debruijnize(self, env):
    if self.name not in debruijnized_modules:
      debruijnized_modules.add(self.name)
    filename = self.name + ".pf"
    file = open(filename, 'r')
    src = file.read()
    file.close()
    old_filename = get_filename()
    set_filename(filename)
    ast = parse(src, trace=False)
    set_filename(old_filename)
    for s in ast:
      env = s.debruijnize(env)
    return env

  def uniquify(self, env):
    if self.name not in debruijnized_modules:
      debruijnized_modules.add(self.name)
    filename = self.name + ".pf"
    file = open(filename, 'r')
    src = file.read()
    file.close()
    from parser import get_filename, set_filename, parse
    old_filename = get_filename()
    set_filename(filename)
    self.ast = parse(src, trace=False)
    set_filename(old_filename)
    for s in self.ast:
      s.uniquify(env)
    return env
  
  def shift_type_vars(self, cutoff, amount):
    return self

  def shift_term_vars(self, cutoff, amount):
    return self
  
def mkEqual(loc, arg1, arg2):
  return Call(loc, Var(loc, '='), [arg1, arg2], True)

def split_equation(loc, equation):
  match equation:
    case Call(loc1, Var(loc2, '='), [L, R], _):
      return (L, R)
    case _:
      error(loc, 'expected an equality, not ' + str(equation))

def mkZero(loc):
  return Var(loc, 'zero')

def mkSuc(loc, arg):
  return Call(loc, Var(loc, 'suc'), [arg], False)

def intToNat(loc, n):
  if n == 0:
    return mkZero(loc)
  else:
    return mkSuc(loc, intToNat(loc, n - 1))

def isNat(t):
  match t:
    case Var(loc, name) if base_name(name) == 'zero':
      return True
    case Call(loc, Var(loc2, name), [arg], infix) if base_name(name) == 'suc':
      return isNat(arg)
    case _:
      return False

def natToInt(t):
  match t:
    case Var(loc, name) if base_name(name) == 'zero':
      return 0
    case Call(loc, Var(loc2, name), [arg], infix) if base_name(name) == 'suc':
      return 1 + natToInt(arg)

  
