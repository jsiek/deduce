from dataclasses import dataclass
from lark.tree import Meta
from typing import Any, Tuple, List
from error import error, set_verbose, get_verbose
import os

infix_precedence = {'+': 6, '-': 6, '*': 7, '/': 7, '%': 7,
                    '=': 1, '<': 1, '≤': 1, '≥': 1, '>': 1, 'and': 2, 'or': 3,
                    '++': 6, '⨄': 6}
prefix_precedence = {'-': 5, 'not': 4}

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

import_directories = ["."]
  
def get_import_directories():
  global import_directories
  return import_directories

def add_import_directory(dir):
  global import_directories
  import_directories.append(dir)

@dataclass
class AST:
    location: Meta

@dataclass
class Type(AST):
  pass

@dataclass
class Term(AST):
  typeof: Type

@dataclass
class Formula(Term):
  pass

@dataclass
class Proof(AST):
  pass

@dataclass
class Statement(AST):
    pass

################ Types ######################################

@dataclass
class IntType(Type):
    
  def copy(self):
    return IntType(self.location)
  
  def __str__(self):
    return 'int'

  # def __repr__(self):
  #   return str(self)

  def __eq__(self, other):
    return isinstance(other, IntType)

  def free_vars(self):
    return set()

  def substitute(self, sub):
    return self

  def uniquify(self, env):
    pass
  
@dataclass
class BoolType(Type):
  def copy(self):
    return BoolType(self.location)
  
  def __str__(self):
    return 'bool'

  # def __repr__(self):
  #   return str(self)

  def __eq__(self, other):
    return isinstance(other, BoolType)

  def free_vars(self):
    return set()

  def substitute(self, sub):
    return self

  def uniquify(self, env):
    pass
  
  def reduce(self, env):
    return self
  
@dataclass
class TypeType(Type):
  def copy(self):
    return TypeType(self.location)
  
  def __str__(self):
    return 'type'

  def __eq__(self, other):
    return isinstance(other, TypeType)

  def free_vars(self):
    return set()

  def substitute(self, sub):
    return self

  def uniquify(self, env):
    pass
  
  def reduce(self, env):
    return self
  
@dataclass
class OverloadType(Type):
  types: List[Tuple[str,Type]]

  def __str__(self):
    return '(' + ' & '.join([x + ': ' + str(ty) for (x,ty) in self.types]) + ')'

  def __eq__(self, other):
    match other:
      case OverloadType(l2, types2):
        ret = True
        for ((x,t1), (y,t2)) in zip(self.types, types2):
          ret = ret and t1 == t2
        return ret
      case _:
        return False

  def free_vars(self):
    fvs = [t.free_vars() for (x,t) in self.types]
    return set().union(*fvs)

  def substitute(self, sub):
      return OverloadType(self.location, [(x, t.substitute(sub)) for (x,t) in self.types])

    
  def uniquify(self, env):
    for (x,t) in self.types:
      t.uniquify(env)
    
  def reduce(self, env):
    return OverloadType(self.location, [(x, ty.reduce(env)) for (x,ty) in self.types])
      
    
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
      prefix = '<' + ','.join([base_name(x) for x in self.type_params]) + '> '
    else:
      prefix = ''
    return '(' + prefix + 'fn ' + ', '.join([str(ty) for ty in self.param_types]) \
      + ' -> ' + str(self.return_type) + ')'

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
      new_sub = {k:v for (k,v) in sub.items() }
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
    
  def reduce(self, env):
    return FunctionType(self.location, self.type_params,
                        [ty.reduce(env) for ty in self.param_types],
                        self.return_type.reduce(env))
    
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

  def __eq__(self, other):
    match other:
      case TypeInst(l, typ, arg_types):
        return self.typ == typ and \
          all([t1 == t2 for (t1, t2) in zip(self.arg_types, arg_types)])
      # case GenericUnknownInst(loc, typ):
      #   return self.typ == typ
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

  def reduce(self, env):
    return TypeInst(self.location,
                    self.typ.reduce(env),
                    [ty.reduce(env) for ty in self.arg_types])
      
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
      # case TypeInst(l, typ, arg_types):
      #   return self.typ == typ
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
  
  
################ Patterns ######################################

@dataclass
class Pattern(AST):
    pass

@dataclass
class PatternBool(Pattern):
  value : bool

  def __str__(self):
      return "true" if self.value else "false"

  # def __repr__(self):
  #     return str(self)

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
      if len(self.parameters) > 0:
        return str(self.constructor) \
          + '(' + ",".join([base_name(p) for p in self.parameters]) + ')'
      else:
        return str(self.constructor)

  # def __repr__(self):
  #     return str(self)

  def uniquify(self, env):
    self.constructor.uniquify(env)
    
    
################ Terms ######################################

@dataclass
class Generic(Term):
  type_params: List[str]
  body: Term

  def copy(self):
    return Generic(self.location, self.typeof,
                   [T for T in self.type_params],
                   self.body.copy())
  
  def __str__(self):
    return "generic " + ",".join([base_name(t) for t in self.type_params]) \
      + "{" + str(self.body) + "}"

  # def __repr__(self):
  #   return str(self)

  def __eq__(self, other):
      if not isinstance(other, Generic):
          return False
      ren = {x: Var(self.location, None, y) \
             for (x,y) in zip(self.type_params, other.type_params) }
      new_body = self.body.substitute(ren)
      return new_body == other.body

  def reduce(self, env):
      return Generic(self.location, self.typeof, self.type_params,
                     self.body.reduce(env))

  def substitute(self, sub):
      n = len(self.type_params)
      new_sub = {k: v for (k,v) in sub.items()}
      return Generic(self.location, self.typeof, self.type_params, self.body.substitute(new_sub))

  def uniquify(self, env):
    body_env = {x:y for (x,y) in env.items()}
    new_type_params = [generate_name(x) for x in self.type_params]
    for (old,new) in zip(self.type_params, new_type_params):
      body_env[old] = new
    self.type_params = new_type_params
    self.body.uniquify(body_env)
    
  
@dataclass
class Conditional(Term):
  cond: Term
  thn: Term
  els: Term

  def copy(self):
    return Conditional(self.location, self.typeof,
                       self.cond.copy(),
                       self.thn.copy(), self.els.copy())
  
  def __str__(self):
      return '(if ' + str(self.cond) \
        + ' then ' + str(self.thn) \
        + ' else ' + str(self.els) + ')'
    
  def __eq__(self, other):
    if not isinstance(other, Conditional):
      return False
    return self.cond == other.cond and self.thn == other.thn and self.els == other.els
    
  def reduce(self, env):
     cond = self.cond.reduce(env)
     thn = self.thn.reduce(env)
     els = self.els.reduce(env)
     match cond:
       case Bool(l1, tyof, True):
         return thn
       case Bool(l1, tyof, False):
         return els
       case _:
         return Conditional(self.location, self.typeof, cond, thn, els)
  
  def substitute(self, sub):
    return Conditional(self.location, self.typeof, self.cond.substitute(sub),
                       self.thn.substitute(sub), self.els.substitute(sub))
  
  def uniquify(self, env):
    self.cond.uniquify(env)
    self.thn.uniquify(env)
    self.els.uniquify(env)

    
@dataclass
class TAnnote(Term):
  subject: Term
  typ: Type

  def copy(self):
    return TAnnote(self.location, self.typeof, self.subject.copy(),
                   self.typ.copy())
  
  def __str__(self):
      return str(self.subject) + ':' + str(self.typ)
    
  def reduce(self, env):
    return self.subject.reduce(env)
  
  def substitute(self, sub):
    return TAnnote(self.location, self.typeof, self.subject.substitute(sub),
                   self.typ.substitute(sub))
  
  def uniquify(self, env):
    self.subject.uniquify(env)
    self.typ.uniquify(env)
    
  
@dataclass
class Var(Term):
  name: str

  def free_vars(self):
    return set([self.name])
  
  def copy(self):
    return Var(self.location, self.typeof, self.name)
  
  def __eq__(self, other):
      if isinstance(other, RecFun):
        return self.name == other.name
      if not isinstance(other, Var):
        return False
      return self.name == other.name 
  
  def __str__(self):
      if base_name(self.name) == 'zero':
        return '0'
      elif get_verbose():
        return self.name
      else:
        return base_name(self.name)

  def reduce(self, env):
      if get_reduce_all() or (self in get_reduce_only()):
        res = env.get_value_of_term_var(self)
        if res:
          if get_verbose():
            print('\t var ' + self.name + ' ===> ' + str(res))
          return res.reduce(env)
        else:
            return self
      else:
        return self
  
  def substitute(self, sub):
      if self.name in sub:
          return sub[self.name]
      else:
          return self
        
  def uniquify(self, env):
    if self.name not in env.keys():
      error(self.location, "undefined variable " + self.name + "\t(uniquify)")
    self.name = env[self.name]
    
@dataclass
class Int(Term):
  value: int

  def copy(self):
    return Int(self.location, self.typeof, self.value)
  
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
  

@dataclass
class Lambda(Term):
  vars: List[str]
  body: Term

  def copy(self):
    return Lambda(self.location, self.typeof,
                 [v for v in self.vars],
                 self.body.copy())
  
  def __str__(self):
    return "λ" + ",".join([base_name(x) for x in self.vars]) \
      + "{" + str(self.body) + "}"

  def __eq__(self, other):
      if not isinstance(other, Lambda):
          return False
      ren = {x: Var(self.location, None, y) \
             for (x,y) in zip(self.vars, other.vars) }
      new_body = self.body.substitute(ren)
      return new_body == other.body

  def reduce(self, env):
    return Lambda(self.location, self.typeof, self.vars, self.body.reduce(env))

  def substitute(self, sub):
      n = len(self.vars)
      return Lambda(self.location, self.typeof, self.vars,
                    self.body.substitute(sub))

  def uniquify(self, env):
    body_env = {x:y for (x,y) in env.items()}
    new_vars = [generate_name(x) for x in self.vars]
    for (old,new) in zip(self.vars, new_vars):
      body_env[old] = new
    self.vars = new_vars
    self.body.uniquify(body_env)
    
def is_match(pattern, arg, subst):
    ret = False
    match pattern:
      case PatternCons(loc1, constr, []):
        match arg:
          case Var(loc2, ty2, name):
            ret = constr == arg
          case TermInst(loc3, tyof, Var(loc2, ty2, name), tyargs):
            ret = constr == Var(loc2, ty2, name)
          case _:
            ret = False
        
      case PatternCons(loc1, constr, params):
        match arg:
          case Call(loc2, cty, rator, args, infix):
            match rator:
              case Var(loc3, ty3, name):
                if constr == Var(loc3, ty3, name) and len(params) == len(args):
                    for (k,v) in zip(params, args):
                        subst[k] = v
                    ret = True
                else:
                    ret = False
              case TermInst(loc4, tyof, Var(loc3, ty3, name), tyargs):
                if constr == Var(loc3, ty3, name) and len(params) == len(args):
                    for (k,v) in zip(params, args):
                        subst[k] = v
                    ret = True
                else:
                    ret = False
              case _:
                ret = False
          case _:
            ret = False
      case _:
        ret = False
    if get_verbose():
      print('is_match(' + str(pattern) + ', ' + str(arg) + ') = ' + str(ret))
    return ret

# The variables that should be reduced.
reduce_only = []

def set_reduce_only(defs):
  global reduce_only
  reduce_only = defs

def get_reduce_only():
  global reduce_only
  return reduce_only

reduce_all = False

def get_reduce_all():
  global reduce_all
  return reduce_all

def set_reduce_all(b):
  global reduce_all
  reduce_all = b

def is_operator(trm):
  match trm:
    case Var(loc, tyof, name):
      return base_name(name) in infix_precedence.keys() \
          or base_name(name) in prefix_precedence.keys()
    case RecFun(loc, name, typarams, params, returns, cases):
      return base_name(name) in infix_precedence.keys() \
          or base_name(name) in prefix_precedence.keys()
    case TermInst(loc, tyof, subject, tyargs, inferred):
      return is_operator(subject)
    case _:
      return False

def operator_name(trm):
  match trm:
    case Var(loc, tyof, name):
      return base_name(name)
    case RecFun(loc, name, typarams, params, returns, cases):
      return base_name(name)
    case TermInst(loc, tyof, subject, tyargs):
      return operator_name(subject)
    case _:
      raise Exception('operator_name, unexpected term ' + str(trm))
    
def precedence(trm):
  match trm:
    case Call(loc1, tyof, rator, args, infix) if is_operator(rator):
      op_name = operator_name(rator)
      if len(args) == 2:
        return infix_precedence.get(op_name, None)
      elif len(args) == 1:
        return prefix_precedence.get(op_name, None)
      else:
        return None
    case _:
      return None

def op_arg_str(trm, arg):
  if precedence(trm) != None and precedence(arg) != None:
    if precedence(arg) <= precedence(trm):
      return "(" + str(arg) + ")"
  return str(arg)
    
@dataclass
class Call(Term):
  rator: Term
  args: list[Term]
  infix: bool

  def copy(self):
    ret = Call(self.location, self.typeof,
                self.rator.copy(),
                [arg.copy() for arg in self.args],
                self.infix)
    if hasattr(self, 'type_args'):
      ret.type_args = self.type_args
    return ret
  
  def __str__(self):
    if self.infix:
      return op_arg_str(self, self.args[0]) + " " + str(self.rator) \
        + " " + op_arg_str(self, self.args[1])
    elif isNat(self):
      return str(natToInt(self))
    else:
      return str(self.rator) + "(" + ", ".join([str(arg) for arg in self.args]) + ")"

  def __eq__(self, other):
      if not isinstance(other, Call):
          return False
      eq_rators = self.rator == other.rator
      eq_rands = all([arg1 == arg2 for arg1,arg2 in zip(self.args, other.args)])
      return eq_rators and eq_rands

  def reduce(self, env):
    fun = self.rator.reduce(env)
    args = [arg.reduce(env) for arg in self.args]
    if get_verbose():
      print('reduce call ' + str(self))
    if get_verbose():
      print('rator => ' + str(fun))    
    if get_verbose():
      print('args => ' + ', '.join([str(arg) for arg in args]))
    ret = None
    match fun:
      case Var(loc, ty, '='):
        if args[0] == args[1]:
          ret = Bool(loc, BoolType(loc), True)
        elif constructor_conflict(args[0], args[1], env):
          ret = Bool(loc, BoolType(loc), False)
        else:
          ret = Call(self.location, self.typeof, fun, args, self.infix)
      case Lambda(loc, ty, vars, body):
        subst = {k: v for (k,v) in zip(vars, args)}
        body_env = env
        new_body = body.substitute(subst)
        old_defs = get_reduce_only()
        set_reduce_only(old_defs + [Var(loc, None, x) for x in vars])
        ret = new_body.reduce(body_env)
        set_reduce_only(old_defs)
      case TermInst(loc, tyof, RecFun(loc2, name, typarams, params, returns, cases), type_args):
        if get_verbose():
          print('call to instantiated generic recursive function')
        first_arg = args[0]
        rest_args = args[1:]
        for fun_case in cases:
            subst = {}
            if is_match(fun_case.pattern, first_arg, subst):
                body_env = env
                for (x,ty) in zip(typarams, type_args):
                  subst[x] = ty
                for (k,v) in zip(fun_case.parameters, rest_args):
                  subst[k] = v
                # print('calling ' + name)
                # print('call site ' + str(self))
                # print('fun_case.body = ' + str(fun_case.body))
                # print('subst = ' + ', '.join([k + ': ' + str(v) for (k,v) in subst.items()]))
                new_fun_case_body = fun_case.body.substitute(subst)
                #print('new_fun_case_body = ' + str(new_fun_case_body))
                old_defs = get_reduce_only()
                reduce_defs = [x for x in old_defs]
                if Var(loc, None, name) in reduce_defs:
                  reduce_defs.remove(Var(loc, None, name))
                else:
                  pass
                reduce_defs += [Var(loc, None, x) \
                                for x in fun_case.pattern.parameters \
                                + fun_case.parameters]
                set_reduce_only(reduce_defs)
                ret = new_fun_case_body.reduce(body_env)
                set_reduce_only(old_defs)
                result = ret
                return result
            else:
              pass
        ret = Call(self.location, self.typeof, fun, args, self.infix)
      
      case RecFun(loc, name, [], params, returns, cases):
        if get_verbose():
          print('call to recursive function')
        first_arg = args[0]
        rest_args = args[1:]
        for fun_case in cases:
            subst = {}
            if is_match(fun_case.pattern, first_arg, subst):
                body_env = env
                for (k,v) in zip(fun_case.parameters, rest_args):
                  subst[k] = v
                new_fun_case_body = fun_case.body.substitute(subst)
                old_defs = get_reduce_only()
                reduce_defs = [x for x in old_defs]
                if Var(loc, None, name) in reduce_defs:
                  reduce_defs.remove(Var(loc, None, name))
                else:
                  pass
                reduce_defs += [Var(loc, None, x) \
                                for x in fun_case.pattern.parameters \
                                + fun_case.parameters]
                set_reduce_only(reduce_defs)
                ret = new_fun_case_body.reduce(body_env)
                set_reduce_only(old_defs)
                result = ret
                return result
            else:
              pass
        ret = Call(self.location, self.typeof, fun, args, self.infix)

      case Generic(loc2, tyof, typarams, body):
        error(self.location, 'in reduction, call to generic ' + str(self))
      case _:
        if get_verbose():
          print('not reducing call because neutral function: ' + str(fun))
        ret = Call(self.location, self.typeof, fun, args, self.infix)
        if hasattr(self, 'type_args'):
          ret.type_args = self.type_args
    return ret

  def substitute(self, sub):
    ret = Call(self.location, self.typeof, self.rator.substitute(sub),
                [arg.substitute(sub) for arg in self.args],
                self.infix)
    if hasattr(self, 'type_args'):
      ret.type_args = self.type_args
    return ret

  def uniquify(self, env):
    self.rator.uniquify(env)
    for arg in self.args:
      arg.uniquify(env)

      
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

  # def __repr__(self):
  #     return str(self)

  def reduce(self, env):
      n = len(self.pattern.parameters)
      return SwitchCase(self.location,
                        PatternCons(self.pattern.location,
                                    self.pattern.constructor,
                                    self.pattern.parameters),
                        self.body.reduce(env))
    
  def substitute(self, sub):
      n = len(self.pattern.parameters)
      new_sub = {k: v for (k,v) in sub.items()}
      return SwitchCase(self.location,
                        self.pattern,
                        self.body.substitute(new_sub))

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
    return Switch(self.location, self.typeof,
                  self.subject.copy(),
                  [c.copy() for c in self.cases])
  
  def __str__(self):
      return 'switch ' + str(self.subject) + ' { ' \
          + ' '.join([str(c) for c in self.cases]) \
          + ' }'

  # def __repr__(self):
  #     return str(self)
  
  def reduce(self, env):
      new_subject = self.subject.reduce(env)
      for c in self.cases:
          subst = {}
          if is_match(c.pattern, new_subject, subst):
            if get_verbose():
              print('switch, matched ' + str(c.pattern) + ' and ' \
                    + str(new_subject))
            new_body = c.body.substitute(subst)
            new_env = env
            old_defs = get_reduce_only()
            set_reduce_only(old_defs + [Var(self.location, None, x) \
                                        for x in subst.keys()])
            ret = new_body.reduce(new_env)
            set_reduce_only(old_defs)
            return ret
      ret = Switch(self.location, self.typeof, new_subject, self.cases)
      return ret
  
  def substitute(self, sub):
      return Switch(self.location, self.typeof,
                    self.subject.substitute(sub),
                    [c.substitute(sub) for c in self.cases])

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
  inferred : bool = True

  def __eq__(self, other):
    if isinstance(other, RecFun):
      return self.subject == other
    elif isinstance(other, TermInst):
      return self.subject == other.subject \
        and all([t1 == t2 for (t1,t2) in zip(self.type_args, other.type_args)])
    else:
      return False
  
  def copy(self):
    return TermInst(self.location, self.typeof,
                    self.subject.copy(),
                    [ty.copy() for ty in self.type_args],
                    self.inferred)
  
  def __str__(self):
    if self.inferred:
      return str(self.subject)
    else:
      return '@' + str(self.subject) + '<' + ','.join([str(ty) for ty in self.type_args]) + '>'

  def reduce(self, env):
    subject_red = self.subject.reduce(env)
    match subject_red:
      case Generic(loc2, tyof, typarams, body):
        sub = {x:t for (x,t) in zip(typarams, self.type_args)}
        return body.substitute(sub)
      case _:
        return TermInst(self.location, self.typeof, subject_red, self.type_args, self.inferred)
    
  def substitute(self, sub):
    return TermInst(self.location, self.typeof,
                    self.subject.substitute(sub),
                    [ty.substitute(sub) for ty in self.type_args],
                    self.inferred)

  def uniquify(self, env):
    self.subject.uniquify(env)
    for ty in self.type_args:
      ty.uniquify(env)
      
  
@dataclass
class TLet(Term):
  var: str
  rhs: Term
  body: Term

  def __str__(self):
    return 'define ' + base_name(self.var) + ' = ' + str(self.rhs) \
      + '\n\t' + str(self.body)
  # def __repr__(self):
  #   return str(self)
  
  def reduce(self, env):
    new_body = self.body.substitute({self.var: self.rhs})
    return new_body.reduce(env)
    
  def copy(self):
    return TLet(self.location, self.typeof, self.var,
                self.rhs.copy(), self.body.copy())
  
  def uniquify(self, env):
    self.rhs.uniquify(env)
    body_env = {x:y for (x,y) in env.items()}
    new_var = generate_name(self.var)
    body_env[self.var] = new_var
    self.var = new_var
    self.body.uniquify(body_env)
    
  def substitute(self, sub):
    new_rhs = self.rhs.substitute(sub)
    new_body = self.body.substitute(sub)
    return TLet(self.location, self.typeof, self.var, new_rhs, new_body)

################ Formulas ######################################
  
@dataclass
class Hole(Formula):
  
  def __str__(self):
      return '?'
    
  def uniquify(self, env):
    pass

  def reduce(self, env):
    return self
    
@dataclass
class Bool(Formula):
  value: bool
  
  def copy(self):
    return Bool(self.location, self.typeof, self.value)
  
  def __eq__(self, other):
      if not isinstance(other, Bool):
          return False
      return self.value == other.value
  def __str__(self):
    return 'true' if self.value else 'false'
  # def __repr__(self):
  #   return str(self)
  def reduce(self, env):
    return self
  def substitute(self, sub):
    return self
  def uniquify(self, env):
    pass

def list_of_and(arg):
  match arg:
    case And(loc, tyof, args):
      return args
    case _:
      return [arg]
    
def flatten_and(args):
  lol = [list_of_and(arg) for arg in args]
  ret = sum(lol, [])
  return ret

@dataclass
class And(Formula):
  args: list[Formula]

  def copy(self):
    return And(self.location, self.typeof, [arg.copy() for arg in self.args])
  
  def __str__(self):
    return '(' + ' and '.join([str(arg) for arg in self.args]) + ')'

  def __eq__(self, other):
    if not isinstance(other, And):
      return False
    return all([arg1 == arg2 for arg1,arg2 in zip(self.args, other.args)])
  
  def reduce(self, env):
    #new_args = [arg.reduce(env) for arg in self.args]
    new_args = flatten_and([arg.reduce(env) for arg in self.args])
    newer_args = []
    for arg in new_args:
      match arg:
        case Bool(loc, ty, val):
          if val:  # true: throw this away
            pass
          else:    # false: the whole thing is false
            return arg
        case _:
          newer_args.append(arg)
    if len(newer_args) == 0:
      return Bool(self.location, BoolType(self.location), True)
    elif len(newer_args) == 1:
      return newer_args[0]
    else:
      return And(self.location, self.typeof, newer_args)
  
  def substitute(self, sub):
    return And(self.location,
               self.typeof,
               [arg.substitute(sub) for arg in self.args])
  
  def uniquify(self, env):
    for arg in self.args:
      arg.uniquify(env)

def list_of_or(arg):
  match arg:
    case Or(loc, tyof, args):
      return args
    case _:
      return [arg]

def flatten_or(args):
  lol = [list_of_or(arg) for arg in args]
  ret = sum(lol, [])
  return ret
    
@dataclass
class Or(Formula):
  args: list[Formula]
  def copy(self):
    return Or(self.location, self.typeof, [arg.copy() for arg in self.args])
  
  def __str__(self):
    return '(' + ' or '.join([str(arg) for arg in self.args]) + ')'
  
  def __eq__(self, other):
    if not isinstance(other, Or):
      return False
    return all([arg1 == arg2 for arg1,arg2 in zip(self.args, other.args)])
  
  def reduce(self, env):
    new_args = flatten_or([arg.reduce(env) for arg in self.args])
    newer_args = []
    for arg in new_args:
      match arg:
        case Bool(loc, ty, val):
          if val:  # true: the whole thing is true
            return arg 
          else:    # false: throw this away
            pass
        case _:
          newer_args.append(arg)
    if len(newer_args) == 0:
      return Bool(self.location, False)
    elif len(newer_args) == 1:
      return newer_args[0]
    else:
      return Or(self.location, self.typeof, newer_args)
  
  def substitute(self, sub):
    return Or(self.location,
              self.typeof,
              [arg.substitute(sub) for arg in self.args])
  
  def uniquify(self, env):
    for arg in self.args:
      arg.uniquify(env)

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
    return IfThen(self.location, self.typeof, self.premise.copy(), self.conclusion.copy())
  
  def __str__(self):
    match self.conclusion:
      case Bool(loc, tyof, False):
        return 'not (' + str(self.premise) + ')'
      case _:
        return '(if ' + str(self.premise) \
          + ' then ' + str(self.conclusion) + ')'

  def __eq__(self, other):
    if not isinstance(other, IfThen):
      return False
    return self.premise == other.premise and self.conclusion == other.conclusion
  
  def reduce(self, env):
    prem = self.premise.reduce(env)
    conc = self.conclusion.reduce(env)
    if prem == conc:
      return Bool(self.location, BoolType(self.location), True)
    match prem:
      case Bool(loc, tyof, True):
        return self.conclusion
      case Bool(loc, tyof, False):
        return Bool(loc, tyof, True)
      case _:
        match conc:
          case Bool(loc, tyof, True):
            return Bool(self.location, tyof, True)
          case _:
            return IfThen(self.location, self.typeof, prem, conc)

  def substitute(self, sub):
    return IfThen(self.location,
                  self.typeof,
                  self.premise.substitute(sub),
                  self.conclusion.substitute(sub))
  
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
    return '(all ' + ", ".join([base_name(v) + ":" + str(t) for (v,t) in self.vars]) \
        + '. ' + str(self.body) + ')'

  def reduce(self, env):
    n = len(self.vars)
    new_body = self.body.reduce(env)
    match new_body:
      case Bool(_, b):
        return new_body
      case _:
        return All(self.location,
                   self.typeof,
                   [(x, ty.reduce(env)) for (x,ty) in self.vars],
                   new_body)

  def substitute(self, sub):
    n = len(self.vars)
    return All(self.location,
               self.typeof,
               [(x, ty.substitute(sub)) for (x,ty) in self.vars],
               self.body.substitute(sub))
  
  def __eq__(self, other):
    if not isinstance(other, All):
      return False
    sub = {y: Var(self.location, None, x) \
           for ((x,tx),(y,ty)) in zip(self.vars, other.vars)}
    return self.body == other.body.substitute(sub)

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
    return Some(self.location,
                self.typeof,
                [(x, ty.reduce(env)) for (x,ty) in self.vars],
                self.body.reduce(env))
  
  def substitute(self, sub):
    n = len(self.vars)
    new_sub = {k: v for (k,v) in sub.items()}
    return Some(self.location,
                self.typeof,
                [(x, ty.substitute(sub)) for (x,ty) in self.vars],
                self.body.substitute(new_sub))
  
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
    
  def __eq__(self, other):
    if not isinstance(other, Some):
      return False
    if all([tx == ty for ((x,tx),(y,ty))in zip(self.vars, other.vars)]):
      sub = {y: Var(self.location, None, x) \
             for ((x,tx),(y,ty)) in zip(self.vars, other.vars)}
      return self.body == other.body.substitute(sub)
    else:
      return False
  
################ Proofs ######################################
  
@dataclass
class PVar(Proof):
  name: str
  
  def copy(self):
    return PVar(self.location, self.name)
  
  def __eq__(self, other):
    if not isinstance(other, PVar):
      return False
    return self.name == other.name
  
  def __str__(self):
      return base_name(self.name)

  def uniquify(self, env):
    if self.name not in env.keys():
      error(self.location, "undefined proof variable " + self.name)
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

  def uniquify(self, env):
    self.proved.uniquify(env)
    self.because.uniquify(env)
    body_env = {x:y for (x,y) in env.items()}
    new_label = generate_name(self.label)
    body_env[self.label] = new_label
    self.label = new_label
    self.body.uniquify(body_env)

@dataclass
class PTLetNew(Proof):
  var: str
  rhs : Term
  body: Proof

  def __str__(self):
      return 'define_ ' + self.var + ' = ' + str(self.rhs) + '\n' \
         + str(self.body)

  def uniquify(self, env):
    self.rhs.uniquify(env)
    body_env = {x:y for (x,y) in env.items()}
    new_var = generate_name(self.var)
    body_env[self.var] = new_var
    self.var = new_var
    self.body.uniquify(body_env)
    
@dataclass
class PTerm(Proof):
  term: Term
  because: Proof
  body: Proof

  def __str__(self):
      return 'term ' + str(self.term) + ' by ' \
        + str(self.because) + '; ' + str(self.body)

  def uniquify(self, env):
    self.term.uniquify(env)
    self.because.uniquify(env)
    self.body.uniquify(env)
    
    
@dataclass
class PAnnot(Proof):
  claim: Formula
  reason: Proof

  def __str__(self):
      return 'conclude ' + str(self.claim) + ' by ' + str(self.reason)

  def uniquify(self, env):
    self.claim.uniquify(env)
    self.reason.uniquify(env)

@dataclass
class SufficesDefRewrite(Proof):
  claim: Formula
  definitions: List[Term]
  equations: List[Proof]
  body: Proof

  def __str__(self):
    return 'suffices ' + str(self.claim) + '\n' \
      + '\twith definition {' + ', '.join([str(d) for d in self.definitions]) + '}\n' \
      + '\trewrite ' + '|'.join([str(eqn) for eqn in self.equations])
  
  def uniquify(self, env):
    self.claim.uniquify(env)
    for d in self.definitions:
      d.uniquify(env)
    for eqn in self.equations:
      eqn.uniquify(env)
    self.body.uniquify(env)

@dataclass
class Suffices(Proof):
  claim: Formula
  reason: Proof
  body: Proof

  def __str__(self):
    return 'suffices ' + str(self.claim) + '   by ' + str(self.reason) + '\n' + str(self.body)

  def uniquify(self, env):
    self.claim.uniquify(env)
    self.reason.uniquify(env)
    self.body.uniquify(env)
  
@dataclass
class Cases(Proof):
  subject: Proof
  cases: List[Tuple[str,Formula,Proof]]

  def uniquify(self, env):
    self.subject.uniquify(env)
    i = 0
    new_cases = []
    while i != len(self.cases):
      body_env = {x:y for (x,y) in env.items()}
      label = self.cases[i][0]
      formula = self.cases[i][1]
      proof = self.cases[i][2]
      if formula:
        formula.uniquify(env)
      new_label = generate_name(label)
      body_env[label] = new_label
      proof.uniquify(body_env)
      new_cases.append((new_label, formula, proof))
      i += 1
    self.cases = new_cases
      
@dataclass
class ModusPonens(Proof):
  implication: Proof
  arg: Proof

  def __str__(self):
      return 'apply ' + str(self.implication) + ' with ' + str(self.arg)

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
class AllElimTypes(Proof):
  univ: Proof
  args: List[Type]

  def __str__(self):
    return str(self.univ) + '<' + ','.join([str(arg) for arg in self.args]) + '>'

  def uniquify(self, env):
    self.univ.uniquify(env)
    for arg in self.args:
      arg.uniquify(env)
      
@dataclass
class AllElim(Proof):
  univ: Proof
  args: List[Term]

  def __str__(self):
    return str(self.univ) + '[' + ','.join([str(arg) for arg in self.args]) + ']'

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
  prop: Formula
  some: Proof
  body: Proof

  def __str__(self):
    return 'obtain ' + ",".join(self.witnesses) \
      + ' where ' + self.label \
      + (' : ' + str(self.prop) if self.prop else '') \
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
    if self.prop:
      self.prop.uniquify(body_env)
    self.body.uniquify(body_env)
    
@dataclass
class PTuple(Proof):
  args: List[Proof]

  def __str__(self):
    return ', '.join([str(arg) for arg in self.args])

  def uniquify(self, env):
    for arg in self.args:
      arg.uniquify(env)

@dataclass
class PAndElim(Proof):
  which: int
  subject: Proof

  def __str__(self):
    return 'conjunct ' + str(self.which) + ' of ' + str(self.subject)

  def uniquify(self, env):
    self.subject.uniquify(env)
      
@dataclass
class PTrue(Proof):
  
  def __str__(self):
    return '.'
  
  def uniquify(self, env):
    pass
  
@dataclass
class PReflexive(Proof):
  
  def __str__(self):
    return 'reflexive'
  
  def uniquify(self, env):
    pass

@dataclass
class PHole(Proof):
  
  def __str__(self):
      return '?'
    
  def uniquify(self, env):
    pass

@dataclass
class PSorry(Proof):
  
  def __str__(self):
      return 'sorry'
    
  def uniquify(self, env):
    pass
  
@dataclass
class PSymmetric(Proof):
  body: Proof
  
  def __str__(self):
    return 'symmetric ' + str(self.body)
  
  def uniquify(self, env):
    self.body.uniquify(env)

@dataclass
class PTransitive(Proof):
  first: Proof
  second: Proof
  def __str__(self):
    return 'transitive ' + str(self.first) + ' ' + str(self.second)

  def uniquify(self, env):
    self.first.uniquify(env)
    self.second.uniquify(env)

@dataclass
class PInjective(Proof):
  constr: Type
  body: Proof
  
  def __str__(self):
    return 'injective ' + str(self.constr) + ' ' + str(self.body)

  def uniquify(self, env):
    self.constr.uniquify(env)
    self.body.uniquify(env)

@dataclass
class PExtensionality(Proof):
  body: Proof
  
  def __str__(self):
    return 'extensionality;\n' + str(self.body)

  def uniquify(self, env):
    self.body.uniquify(env)
    
@dataclass
class IndCase(AST):
  pattern: Pattern
  induction_hypotheses: list[Tuple[str,Formula]]
  body: Proof

  def __str__(self):
    return 'case ' + str(self.pattern) \
      + ' assume ' + ', '.join([x + ': ' + str(f) for (x,f) in self.induction_hypotheses]) \
      + '{' + str(self.body) + '}'

  def uniquify(self, env):
    body_env = copy_dict(env)

    new_params = [generate_name(x) for x in self.pattern.parameters]
    for (old,new) in zip(self.pattern.parameters, new_params):
      body_env[old] = new
      
    new_hyps = [(generate_name(x),f) for (x,f) in self.induction_hypotheses]
    for ((old,old_frm),(new,new_frm)) in zip(self.induction_hypotheses, new_hyps):
      body_env[old] = new
    for (x,f) in new_hyps:
      if f:
        f.uniquify(body_env)
      
    self.pattern.parameters = new_params
    self.pattern.uniquify(env)
    self.induction_hypotheses = new_hyps
    self.body.uniquify(body_env)
    
@dataclass
class Induction(Proof):
  typ: Type
  cases: List[IndCase]

  def __str__(self):
    return 'induction ' + str(self.typ) + '\n' \
      + '\n'.join([str(c) for c in self.cases])
  
  def uniquify(self, env):
    self.typ.uniquify(env)
    for c in self.cases:
      c.uniquify(env)
      
@dataclass
class SwitchProofCase(AST):
  pattern: Pattern
  assumptions: list[Tuple[str,Formula]]
  body: Proof

  def __str__(self):
    return 'case ' + str(self.pattern) + '{' + str(self.body) + '}'

  def uniquify(self, env):
    self.pattern.uniquify(env)
    body_env = copy_dict(env)
    
    new_params = [generate_name(x) for x in self.pattern.bindings()]
    for (old,new) in zip(self.pattern.bindings(), new_params):
      body_env[old] = new

    new_assumptions = [(generate_name(x),f) for (x,f) in self.assumptions]
    for (x,f) in new_assumptions:
      if f:
        f.uniquify(body_env)
    for ((old,old_frm),(new,new_frm)) in zip(self.assumptions, new_assumptions):
      body_env[old] = new

    self.pattern.set_bindings(new_params)
    self.assumptions = new_assumptions
    self.body.uniquify(body_env)
    
@dataclass
class SwitchProof(Proof):
  subject: Term
  cases: List[IndCase]

  def __str__(self):
      return 'switch ' + str(self.subject) \
        + '{' + '\n'.join([str(c) for c in self.cases]) + '}'
    
  def uniquify(self, env):
    self.subject.uniquify(env)
    for c in self.cases:
      c.uniquify(env)
      
@dataclass
class ApplyDefs(Proof):
  definitions: List[Term]

  def __str__(self):
      return 'definition {' + ', '.join([str(d) for d in self.definitions]) + '}'

  def uniquify(self, env):
    for d in self.definitions:
      d.uniquify(env)

@dataclass
class ApplyDefsGoal(Proof):
  definitions: List[Term]
  body: Proof

  def __str__(self):
      return 'definition {' + ', '.join([str(d) for d in self.definitions]) \
        + '}' + str(self.body)

  def uniquify(self, env):
    for d in self.definitions:
      d.uniquify(env)
    self.body.uniquify(env)

@dataclass
class ApplyDefsFact(Proof):
  definitions: List[Term]
  subject: Proof

  def __str__(self):
      return 'definition ' + ', '.join([str(d) for d in self.definitions]) \
        + ' in ' + str(self.subject)

  def uniquify(self, env):
    for d in self.definitions:
      d.uniquify(env)
    self.subject.uniquify(env)

@dataclass
class EnableDefs(Proof):
  definitions: List[Term]
  subject: Proof

  def __str__(self):
      return 'enable ' + ', '.join([str(d) for d in self.definitions]) \
        + ';\n' + str(self.subject)

  def uniquify(self, env):
    for d in self.definitions:
      d.uniquify(env)
    self.subject.uniquify(env)
    
@dataclass
class Rewrite(Proof):
  equations: List[Proof]

  def __str__(self):
      return 'rewrite ' + '|'.join([str(eqn) for eqn in self.equations])

  def uniquify(self, env):
    for eqn in self.equations:
      eqn.uniquify(env)
    
@dataclass
class RewriteGoal(Proof):
  equations: List[Proof]
  body: Proof

  def __str__(self):
      return 'rewrite ' + '|'.join([str(eqn) for eqn in self.equations]) \
        + '\n' + str(self.body)

  def uniquify(self, env):
    for eqn in self.equations:
      eqn.uniquify(env)
    self.body.uniquify(env)
    
@dataclass
class RewriteFact(Proof):
  subject: Proof
  equations: List[Proof]

  def __str__(self):
      return 'rewrite ' + ','.join([str(eqn) for eqn in self.equations]) \
        + ' in ' + str(self.subject)

  def uniquify(self, env):
    for eqn in self.equations:
      eqn.uniquify(env)
    self.subject.uniquify(env)
    
################ Statements ######################################
  
@dataclass
class Theorem(Statement):
  name: str
  what: Formula
  proof: Proof

  def __str__(self):
    return 'theorem ' + self.name + ': ' + str(self.what) + '\nbegin\n' \
        + str(self.proof) + '\nend\n'

  # def __repr__(self):
  #   return str(self)

  def uniquify(self, env):
    self.what.uniquify(env)
    self.proof.uniquify(env)
    new_name = generate_name(self.name)
    env[self.name] = new_name
    self.name = new_name

  def uniquify_body(self, env):
    pass
  
@dataclass
class Constructor(AST):
  name: str
  parameters: List[Type]

  def uniquify(self, env):
    for ty in self.parameters:
      ty.uniquify(env)
      
  def __str__(self):
    if len(self.parameters) > 0:
      return base_name(self.name) + '(' + ','.join([str(ty) for ty in self.parameters]) + ')'
    else:
      return base_name(self.name)
      
@dataclass
class Union(Statement):
  name: str
  type_params: List[str]
  alternatives: List[Constructor]

  def reduce(self, env):
    return self
  
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
      if con.name not in env.keys():
        new_con_name = generate_name(con.name)
        env[con.name] = new_con_name
      else:
        new_con_name = env[con.name]
      con.name = new_con_name

  def uniquify_body(self, env):
    pass
  
  def substitute(self, sub):
    return self
      
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

  # def __repr__(self):
  #     return str(self)

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
    
    
@dataclass
class RecFun(Statement):
  name: str
  type_params: List[str]
  params: List[Type]
  returns: Type
  cases: List[FunCase]

  def uniquify(self, env):
    if self.name not in env.keys():
      new_name = generate_name(self.name)
      env[self.name] = new_name
    else:
      new_name = env[self.name]
    self.name = new_name
    
    body_env = copy_dict(env)
    new_type_params = [generate_name(t) for t in self.type_params]
    for (old,new) in zip(self.type_params, new_type_params):
      body_env[old] = new
    self.old_type_params = self.type_params
    self.type_params = new_type_params
    
    for ty in self.params:
      ty.uniquify(body_env)
    self.returns.uniquify(body_env)

  def uniquify_body(self, env):
    body_env = copy_dict(env)
    for (old,new) in zip(self.old_type_params, self.type_params):
      body_env[old] = new
    
    for c in self.cases:
      c.uniquify(body_env)

    
  def __str__(self):
    return base_name(self.name)
    
  def to_string(self):
    return 'function ' + self.name + '<' + ','.join(self.type_params) + '>' \
      + '(' + ','.join([str(ty) for ty in self.params]) + ')' \
      + ' -> ' + str(self.returns) + '{\n' \
      + '\n'.join([str(c) for c in self.cases]) \
      + '\n}'

  def __eq__(self, other):
    if isinstance(other, Var):
      return self.name == other.name
    elif isinstance(other, TermInst):
      return self == other.subject
    elif isinstance(other, RecFun):
      return self.name == other.name
    else:
      return False
  
  def reduce(self, env):
    return self

  def substitute(self, sub):
    return self
  
@dataclass
class Define(Statement):
  name: str
  typ: Type
  body: Term

  def __str__(self):
    return 'define ' + self.name \
      + (' : ' + str(self.typ) if self.typ else '') \
      + ' = ' + str(self.body)
  
  def uniquify(self, env):
    if self.typ:
      self.typ.uniquify(env)
    self.body.uniquify(env)
    if self.name not in env.keys():
      new_name = generate_name(self.name)
      env[self.name] = new_name
    else:
      new_name = env[self.name]
    self.name = new_name
  
  def uniquify_body(self, env):
    pass

uniquified_modules = {}
  
@dataclass
class Assert(Statement):
  formula : Term

  def __str__(self):
    return 'assert ' + str(self.formula)

  def uniquify(self, env):
    pass
  
  def uniquify_body(self, env):
    self.formula.uniquify(env)

@dataclass
class Print(Statement):
  term : Term

  def __str__(self):
    return 'print ' + str(self.term)

  def uniquify(self, env):
    pass
  
  def uniquify_body(self, env):
    self.term.uniquify(env)

def find_file(loc, name):
  for dir in get_import_directories():
    filename = dir + "/" + name + ".pf"
    if os.path.isfile(filename):
      return filename
  error(loc, 'could not find a file for import: ' + name)
    
@dataclass
class Import(Statement):
  name: str
  ast: AST = None

  def __str__(self):
    return 'import ' + self.name
  
  def uniquify(self, env):
    global uniquified_modules
    if self.name in uniquified_modules.keys():
      self.ast = uniquified_modules[self.name]
      return env
    else:
      filename = find_file(self.location, self.name)
      file = open(filename, 'r')
      src = file.read()
      file.close()
      from parser import get_filename, set_filename, parse
      old_filename = get_filename()
      set_filename(filename)
      self.ast = parse(src, trace=False)
      uniquified_modules[self.name] = self.ast
      set_filename(old_filename)
      for s in self.ast:
        s.uniquify(env)
      for s in self.ast:
        s.uniquify_body(env)
      return env
  
  def uniquify_body(self, env):
    pass
  
def mkEqual(loc, arg1, arg2):
  ret = Call(loc, None, Var(loc, None, '='), [arg1, arg2], True)
  return ret

def split_equation(loc, equation):
  match equation:
    case Call(loc1, tyof, Var(loc2, tyof2, '='), [L, R], _):
      return (L, R)
    case _:
      error(loc, 'expected an equality, not ' + str(equation))

def is_equation(formula):
  match formula:
    case Call(loc1, tyof, Var(loc2, tyof2, '='), [L, R], _):
      return True
    case _:
      return False

def make_boolean_equation(formula):
  match formula:
    case IfThen(loc, tyof, frm, Bool(_, _, False)):
      return mkEqual(loc, frm,
                     Bool(formula.location, None, False))
    case _:
      return mkEqual(formula.location, formula,
                     Bool(formula.location, None, True))
      
def mkZero(loc):
  return Var(loc, None, 'zero')

def mkSuc(loc, arg):
  return Call(loc, None, Var(loc, None, 'suc'), [arg], False)

def intToNat(loc, n):
  if n == 0:
    return mkZero(loc)
  else:
    return mkSuc(loc, intToNat(loc, n - 1))

def isNat(t):
  match t:
    case Var(loc, tyof, name) if base_name(name) == 'zero':
      return True
    case Call(loc, tyof1, Var(loc2, tyof2, name), [arg], infix) if base_name(name) == 'suc':
      return isNat(arg)
    case _:
      return False

def natToInt(t):
  match t:
    case Var(loc, tyof, name) if base_name(name) == 'zero':
      return 0
    case Call(loc, tyof1, Var(loc2, tyof2, name), [arg], infix) if base_name(name) == 'suc':
      return 1 + natToInt(arg)

def is_constructor(constr_name, env):
  for (name,binding) in env.dict.items():
    if isinstance(binding, TypeBinding):
      match binding.defn:
        case Union(loc2, name, typarams, alts):
          for constr in alts:
            if constr.name == constr_name:
              return True
        case _:
          continue
  return False

def constructor_conflict(term1, term2, env):
  match (term1, term2):
    case (Call(loc1, tyof1, Var(_, tyof2, n1), rands1),
          Call(loc2, tyof3, Var(_, tyof4, n2), rands2)):
      if is_constructor(n1, env) and is_constructor(n2, env):
        if n1 != n2:
          return True
        else:
          return any([constructor_conflict(rand1, rand2, env) \
                      for (rand1, rand2) in zip(rands1, rands2)])
    case (Call(loc1, tyof1, Var(_, tyof2, n1), rands1), Var(_, tyof3, n2)):
      if is_constructor(n1, env) and is_constructor(n2, env) and n1 != n2:
        return True
    case (Var(_, tyof1, n1), Var(_, tyof2, n2)):
      if is_constructor(n1, env) and is_constructor(n2, env) and n1 != n2:
        return True
    case (Var(_, tyof1, n1), Call(loc2, tyof2, Var(_, tyof3, n2), rands2)):
      if is_constructor(n1, env) and is_constructor(n2, env) and n1 != n2:
        return True
    case (Bool(_, tyof1, True), Bool(_, tyof2, False)):
      return True
    case (Bool(_, tyof1, False), Bool(_, tyof2, True)):
      return True
  return False
    
@dataclass
class Binding(AST):
  pass

@dataclass
class TypeBinding(Binding):
  defn : AST = None
  
  def __str__(self):
    return str(self.defn)
  
@dataclass
class TermBinding(Binding):
  typ : Type
  defn : Term = None
  
  def __str__(self):
    return str(self.typ) + ' = ' + str(self.defn)

@dataclass
class ProofBinding(Binding):
  formula : Formula
  local : bool
  
  def __str__(self):
    return str(self.formula)
  
class Env:
  def __init__(self, env = None):
    if env:
      self.dict = copy_dict(env)
    else:
      self.dict = {}

  def __str__(self):
    return ',\n'.join(['\t' + k + ': ' + str(v) \
                       for (k,v) in reversed(self.dict.items())])

  def proofs_str(self):
    return ',\n'.join(['\t' + base_name(k) + ': ' + str(v) \
                       for (k,v) in reversed(self.dict.items()) \
                       if isinstance(v,ProofBinding) and v.local])
  
  def declare_type(self, loc, name):
    new_env = Env(self.dict)
    new_env.dict[name] = TypeBinding(loc)
    return new_env

  def declare_type_vars(self, loc, type_vars):
    new_env = self
    for x in type_vars:
      new_env = new_env.declare_type(loc, x)
    return new_env
  
  def define_type(self, loc, name, defn):
    if defn == None:
      error(loc, 'None not allowed in define_type')
    new_env = Env(self.dict)
    new_env.dict[name] = TypeBinding(loc, defn)
    return new_env
  
  def declare_term_var(self, loc, name, typ):
    if typ == None:
      error(loc, 'None not allowed in declare_term_var')
    new_env = Env(self.dict)
    new_env.dict[name] = TermBinding(loc, typ)
    return new_env

  def declare_term_vars(self, loc, xty_pairs):
    new_env = self
    for (x,ty) in xty_pairs:
      new_env = new_env.declare_term_var(loc, x, ty)
    return new_env
  
  def define_term_var(self, loc, name, typ, val):
    if typ == None:
      error(loc, 'None not allowed as type in define_term_var')
    if val == None:
      error(loc, 'None not allowed as value in define_term_var')
    new_env = Env(self.dict)
    new_env.dict[name] = TermBinding(loc, typ, val)
    return new_env

  def define_term_vars(self, loc, xv_pairs):
    new_env = self
    for (x,v) in xv_pairs:
      new_env = new_env.define_term_var(loc, x, None, v)
    return new_env
  
  def declare_proof_var(self, loc, name, frm):
    new_env = Env(self.dict)
    new_env.dict[name] = ProofBinding(loc, frm, False)
    return new_env

  def declare_local_proof_var(self, loc, name, frm):
    new_env = Env(self.dict)
    new_env.dict[name] = ProofBinding(loc, frm, True)
    return new_env
  
  def _def_of_type_var(self, curr, name):
    if name in curr.keys():
      return curr[name].defn
    else:
      raise Exception('variable not in env: ' + name)
  
  def _type_of_term_var(self, curr, name):
    if name in curr.keys():
      binding = curr[name]
      if isinstance(binding, TermBinding):
        return binding.typ
      elif isinstance(binding, TypeBinding):
        return TypeType(None)
      else:
        raise Exception('expected a term or type variable, not ' + name)
    else:
      return None

  def _value_of_term_var(self, curr, name):
    if name in curr.keys():
      return curr[name].defn
    else:
      return None
  
  def _formula_of_proof_var(self, curr, name):
    if name in curr.keys():
      if isinstance(curr[name], ProofBinding):
        return curr[name].formula
      else:
        raise Exception('expected a proof variable but instead got ' + base_name(name))
    else:
      return None
    
  def type_var_is_defined(self, tyname):
    match tyname:
      case Var(loc, tyof, name):
        return name in self.dict.keys()
      case _:
        raise Exception('expected a type name, not ' + str(tyname))

  def term_var_is_defined(self, tvar):
    match tvar:
      case Var(loc, tyof, name):
        if self._type_of_term_var(self.dict, name):
          return True
        else:
          return False
      case _:
        raise Exceptiona('expected a term variable, not ' + str(tvar))
        
  def proof_var_is_defined(self, pvar):
    match pvar:
      case PVar(loc, name):
        if self._formula_of_proof_var(self.dict, name):
          return True
        else:
          return False
      case _:
        raise Exception('expected proof var, not ' + str(pvar))
    
  def get_def_of_type_var(self, var):
    match var:
      case Var(loc, tyof, name):
        return self._def_of_type_var(self.dict, name)
      case _:
        raise Exception('get_def_of_type_var: unexpected ' + str(var))
      
  def get_formula_of_proof_var(self, pvar):
    match pvar:
      case PVar(loc, name):
        return self._formula_of_proof_var(self.dict, name)
      case _:
        raise Exception('get_formula_of_proof_var: expected PVar, not ' + str(pvar))
          
  def get_type_of_term_var(self, tvar):
    match tvar:
      case Var(loc, tyof, name):
        return self._type_of_term_var(self.dict, name)

  def get_value_of_term_var(self, tvar):
    match tvar:
      case Var(loc, tyof, name):
        return self._value_of_term_var(self.dict, name)

