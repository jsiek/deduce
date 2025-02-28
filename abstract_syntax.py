from dataclasses import dataclass, field
from lark.tree import Meta
from typing import Tuple, List, Optional, Set, Self
from error import error, warning, set_verbose, get_verbose, get_unique_names, VerboseLevel
from pathlib import Path
from edit_distance import edit_distance
from math import ceil
import os

infix_precedence = {'+': 6, '-': 6, '⊝': 6, '*': 7, '/': 7, '%': 7,
                    '=': 1, '<': 1, '≤': 1, '≥': 1, '>': 1, 'and': 2, 'or': 3,
                    '++': 6, '⨄': 6, '∈':1, '∪':6, '∩':6, '⊆': 1, '⇔': 2, '∘': 7}
prefix_precedence = {'-': 8, 'not': 4}

############ AST Base Classes ###########

@dataclass
class AST:
    location: Meta


@dataclass
class Type(AST):

  def copy(self) -> Self:
    error(self.location, 'copy not implemented')
    return self

  def free_vars(self) -> Set[str]:
    error(self.location, 'free_vars not implemented')
    return set()

  def substitute(self, sub) -> Self:
    error(self.location, 'substitute not implemented')

  def uniquify(self, env) -> None:
    error(self.location, 'uniquify not implemented')

  def reduce(self, env) -> Self:
    error(self.location, 'reduce not implemented')


@dataclass
class Term(AST):
  typeof: Optional[Type]

  def copy(self) -> Self:
    error(self.location, 'copy not implemented')
    return self

  def uniquify(self, env) -> None:
    error(self.location, 'uniquify not implemented')

  def substitute(self, sub) -> Self:
    error(self.location, 'substitute not implemented')

  def reduce(self, env) -> Self:
    error(self.location, 'reduce not implemented')

  def pretty_print(self, indent: int, afterNewline=False) -> str:
      if afterNewline:
          return indent*' ' + str(self)
      else:
          return str(self)

@dataclass
class Formula(Term):
  pass

@dataclass
class Proof(AST):
    
  def pretty_print(self, indent: int) -> str:
      return str(self)

@dataclass
class Statement(AST):
    
  def pretty_print(self, indent: int) -> str:
      return str(self)

################ Miscellaneous Functions #####################

def copy_dict(d):
  return {k: v for k, v in d.items()}


def maybe_str(o: Optional[str], default='') -> str:
  return str(o) if o is not None else default

def maybe_pretty_print(o: Optional[str], indent, default='') -> str:
  return o.pretty_print(indent) if o is not None else default

name_id = 0


def generate_name(name: str) -> str:
  global name_id
  ls = name.split('.')
  new_id = name_id
  name_id += 1
  return ls[0] + '.' + str(new_id)


def base_name(name: str) -> str:
  ls = name.split('.')
  return ls[0]


import_directories = set()


def init_import_directories():
  import_directories.add(".")
  lib_config_path = Path(os.path.expanduser("~/.config/deduce/libraries"))
  if lib_config_path.exists() and lib_config_path.is_file():
    with open(lib_config_path, 'r') as lib_config_file:
      for line in lib_config_file:
        import_directories.add(line.strip())


def get_import_directories():
  global import_directories
  if (get_verbose()):
    print("import directories: ", import_directories)
  return import_directories


def add_import_directory(dir):
  global import_directories
  import_directories.add(dir)


recursive_descent = True


def get_recursive_descent():
  global recursive_descent
  return recursive_descent


def set_recursive_descent(b):
  global recursive_descent
  recursive_descent = b


def type_names(loc, names: List[str]):
  index = 0
  result = []
  for n in reversed(names):
    result.insert(0, Var(loc, None, n, []))
    index += 1
  return result


def type_match(loc, tyvars, param_ty, arg_ty, matching):
  if get_verbose():
    print("type_match(" + str(param_ty) + "," + str(arg_ty) + ")")
    print("\tin  " + ', '.join([str(x) for x in tyvars]))
    print("\twith " + str(matching))
  match (param_ty, arg_ty):
    case (Var(l1, t1, n1, rs1), Var(l2, t2, n2, rs2)) if n1 == n2:
      pass
    case (Var(l1, t1, name, rs1), _) if param_ty in tyvars:
      if name in matching.keys():
        type_match(loc, tyvars, matching[name], arg_ty, matching)
      else:
        if get_verbose():
          print('matching ' + name + ' := ' + str(arg_ty))
        matching[name] = arg_ty
    case (FunctionType(l1, tv1, pts1, rt1), FunctionType(l2, tv2, pts2, rt2)) \
      if len(tv1) == len(tv2) and len(pts1) == len(pts2):
      for (pt1, pt2) in zip(pts1, pts2):
        type_match(loc, tyvars, pt1, pt2, matching)
      type_match(loc, tyvars, rt1, rt2, matching)
    case (TypeInst(l1, n1, args1), TypeInst(l2, n2, args2)):
      if n1 != n2 or len(args1) != len(args2):
        error(loc, str(arg_ty) + " does not match " + str(param_ty))
      for (arg1, arg2) in zip(args1, args2):
        type_match(loc, tyvars, arg1, arg2, matching)
    # How to handle GenericUnknownInst?
    case (TypeInst(l1, n1, args1), GenericUnknownInst(l2, n2)):
      if n1 != n2:
        error(loc, str(arg_ty) + " does not match " + str(param_ty))
    case _:
      if param_ty != arg_ty:
        error(loc, str(arg_ty) + " does not match " + str(param_ty))


def is_associative(loc, opname, typ, env):
  # print('is_associative? ' + str(opname) + ' for ' + str(typ))
  for (typarams, ty) in env.get_assoc_types(opname):
    type_params = type_names(loc, typarams)
    matching = {}
    try:
      type_match(loc, type_params, ty, typ, matching)
      # print('\tyes')
      return True
    except Exception as e:
      pass
  # print('\tno')
  return False


def rator_name(rator):
  match rator:
    case Var(l, t, n, rs):
      if len(rs) > 0:
        return rs[0]
      else:
        return n
    case RecFun(loc, name, typarams, params, returns, cases):
      return name
    case Lambda(loc, ty, vars, body):
      return 'no_name'
    case TermInst(loc3, tyof, arg2, tyargs):
      return rator_name(arg2)
    case Generic(loc2, tyof, typarams, body):
      # return rator_name(body)
      return 'no_name'
    case _:
      # raise Exception('rator_name: unhandled ' + repr(rator))
      return 'no_name'


def flatten_assoc(op_name, trm):
  match trm:
    case Call(loc2, tyof, rator, args) if rator_name(rator) == op_name:
      return sum([flatten_assoc(op_name, arg) for arg in args], [])
    case _:
      return [trm]


def flatten_assoc_list(op_name, args):
  return sum([flatten_assoc(op_name, arg) for arg in args], [])


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

  def free_vars(self) -> Set[str]:
    return set()

  def substitute(self, sub) -> Type:
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
    return '(' + ' & '.join([base_name(x) + ': ' + str(ty) for (x,ty) in self.types]) + ')'

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
      typarams = '<' + ','.join([(x if get_verbose() else base_name(x)) for x in self.type_params]) + '> '
    else:
      typarams = ''
    return '(' + 'fn ' + typarams + ', '.join([str(ty) for ty in self.param_types]) \
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
      overwrite(body_env, old, new, self.location)        
    self.type_params = new_type_params
    for p in self.param_types:
      p.uniquify(body_env)
    self.return_type.uniquify(body_env)
    
  def reduce(self, env):
    return FunctionType(self.location, self.type_params,
                        [ty.reduce(env) for ty in self.param_types],
                        self.return_type.reduce(env))
    
@dataclass
class ArrayType(Type):
  elt_type: Type
  
  def copy(self):
    return ArrayType(self.location, self.elt_type.copy())

  def __str__(self):
    return '[' + str(self.elt_type) + ']'

  def __eq__(self, other):
    match other:
      case ArrayType(loc, elt_type):
        return self.elt_type == elt_type
      case _:
        return False

  def free_vars(self):
    return self.elt_type.free_vars()

  def substitute(self, sub):
    return ArrayType(self.location, self.elt_type.substitute(sub))

  def uniquify(self, env):
    self.elt_type.uniquify(env)

  def reduce(self, env):
    return ArrayType(self.location, self.elt_type.reduce(env))
      
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
  constructor : Term         # typically a Var
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
          + '(' + ', '.join([base_name(p) for p in self.parameters]) + ')'
      else:
        return str(self.constructor)

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
    return "generic " + ",".join([(t if get_verbose() else base_name(t)) for t in self.type_params]) \
      + " { " + str(self.body) + " }"

  def pretty_print(self, indent, afterNewline=False):    
    return (indent*' ' if afterNewline else '') \
        + 'generic ' + ', '.join([(t if get_verbose() else base_name(t)) for t in self.type_params]) \
      + ' {\n' + self.body.pretty_print(indent+2, True) + '\n' \
      + indent*' ' + '}'

  def __eq__(self, other):
      if not isinstance(other, Generic):
          return False
      ren = {x: Var(self.location, None, y, [y]) \
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
      overwrite(body_env, old, new, self.location)
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

  def pretty_print(self, indent, afterNewline=False):
      return ('' if afterNewline else '\n') + indent*' ' + 'if ' + str(self.cond) + ' then\n' \
          + self.thn.pretty_print(indent+2, True) + '\n'\
          + indent*' ' + 'else\n' \
          + self.els.pretty_print(indent+2, True)
  
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

  def __eq__(self, other):
    return self.subject == other
    
  
@dataclass
class Var(Term):
  # name is established upon creation in the parser, 
  # then updated during type checking
  name: str

  # filled in during uniquify, list because of overloading
  resolved_names: list[str] = field(default_factory=list)

  def get_name(self):
    if len(self.resolved_names) > 0:
      return self.resolved_names[0]
    else:
      return self.name
  
  def free_vars(self):
    return {self.name}
  
  def copy(self):
    return Var(self.location, self.typeof, self.name, self.resolved_names)
  
  def __eq__(self, other):
      if isinstance(other, RecFun):
        result = self.name == other.name
      elif isinstance(other, TermInst):
        result = self == other.subject
      elif not isinstance(other, Var):
        result = False
      else:
        result = self.name == other.name
      return result
  
  def __str__(self):
      if isinstance(self.resolved_names, str):
        error(self.location,
              'resolved_names is a string but should be a list: ' \
              + self.resolved_names)
      
      if base_name(self.name) == 'zero' and not get_unique_names() and not get_verbose():
        return '0'
      elif base_name(self.name) == 'empty' and not get_unique_names() and not get_verbose():
          return '[]'
      # elif get_verbose():
      #   return self.name + '{' + ','.join(self.resolved_names) + '}'
      elif get_unique_names():
        if self.typeof == None:
          return self.name
        else:
          return self.name
      else:
        if is_operator(self):
          return 'operator ' + base_name(self.name)
        else:
          return base_name(self.name)

  def operator_str(self):
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
          trm = sub[self.name]
          if not isinstance(trm, RecFun):
            add_reduced_def(self.name)
          return trm
      else:
          return self
        
  def uniquify(self, env):
    if self.name not in env.keys():
      if get_verbose():
        env_str = '\nenvironment: ' + ', '.join(env.keys())
      else:
        env_str = ''

      import_advice = ''

      if self.name == "suc" or self.name == "zero":
        import_advice = "\n\tAdd `import Nat` to supply a definition."
      elif self.name == "empty" or self.name == "node":
        import_advice = "\n\tAdd `import List` to supply a definition."

      close_matches = []
      for var in env.keys():
        if edit_distance(self.name, var) <= ceil(len(self.name) / 5):
          close_matches.append(var)
      if len(close_matches) > 0:
        mispell_advice = '\n\tdid you intend: ' + ', '.join(close_matches) + '\n'
      else:
        mispell_advice = ''
      error(self.location, 'undefined variable: ' + self.name \
            + mispell_advice + import_advice + '' + env_str)
    self.resolved_names = env[self.name]
    
@dataclass
class Int(Term):
  value: int

  def copy(self):
    return Int(self.location, self.typeof, self.value)
  
  def __eq__(self, other):
      if isinstance(other, TermInst):
        return self == other.subject
      elif not isinstance(other, Int):
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
  vars: List[Tuple[str,Type]]
  body: Term

  def copy(self):
    return Lambda(self.location, self.typeof,
                 self.vars,
                 self.body.copy())
  
  def __str__(self):
    if get_verbose():
      params = self.vars
    else:
      params = [(base_name(x), t)for (x,t) in self.vars]
    return "fun " + ",".join([x + ':' + str(t) if t else x\
                              for (x,t) in params]) \
           + " { " + str(self.body) + " }"

  def pretty_print(self, indent, afterNewline=False):
    params = [(base_name(x), t)for (x,t) in self.vars]
    return (indent*' ' if afterNewline else '') \
        + "fun " + ', '.join([x + ':' + str(t) if t else x\
                            for (x,t) in params]) \
        + " {\n" + self.body.pretty_print(indent+2, True) + '\n'\
        + indent*' ' + '}'

  def __eq__(self, other):
      if not isinstance(other, Lambda):
          return False
      ren = {x: Var(self.location, t2, y) \
             for ((x,t1),(y,t2)) in zip(self.vars, other.vars) }
      new_body = self.body.substitute(ren)
      return new_body == other.body

  def reduce(self, env):
    return Lambda(self.location, self.typeof, self.vars, self.body.reduce(env))

  def substitute(self, sub):
      n = len(self.vars)
      new_vars = [(x, t.substitute(sub) if t else None) for (x,t) in self.vars]
      return Lambda(self.location, self.typeof, new_vars,
                    self.body.substitute(sub))

  def uniquify(self, env):
    body_env = {x:y for (x,y) in env.items()}
    for (x,t) in self.vars:
      if t:
        t.uniquify(env)
    new_vars = [(generate_name(x),t) for (x,t) in self.vars]
    for ((old,t1),(new,t2)) in zip(self.vars, new_vars):
      overwrite(body_env, old, new, self.location)
    self.vars = new_vars
    self.body.uniquify(body_env)
    
def is_match(pattern, arg, subst):
    ret = False
    match pattern:
      case PatternBool(loc1, value):
        match arg:
          case Bool(loc2, tyof, arg_value):
            ret = arg_value == value
          case Var(loc2, ty2, name, rs2):
            ret = False
          case _:
            error(loc1, 'Boolean pattern expected boolean argument, not\n\t' \
                  + str(arg))
      case PatternCons(loc1, constr, []):
        match arg:
          case Var(loc2, ty2, name, rs2):
            ret = constr == arg
          case TermInst(loc3, tyof, arg2, tyargs):
            ret = is_match(pattern, arg2, subst)
          case _:
            ret = False
        
      case PatternCons(loc1, constr, params):
        match arg:
          case Call(loc2, cty, rator, args):
            match rator:
              case Var(loc3, ty3, name, rs):
                if constr == Var(loc3, ty3, name, rs) and len(params) == len(args):
                    for (k,v) in zip(params, args):
                        subst[k] = v
                        if isinstance(v, TermInst):
                          v.inferred = False
                    ret = True
                else:
                    ret = False
              case TermInst(loc4, tyof, Var(loc3, ty3, name, rs), tyargs):
                if constr == Var(loc3, ty3, name, rs) and len(params) == len(args):
                    for (k,v) in zip(params, args):
                        subst[k] = v
                        if isinstance(v, TermInst):
                          v.inferred = False
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

# Definitions that were reduced.
reduced_defs = set()

def reset_reduced_defs():
  global reduced_defs
  reduced_defs = set()

def get_reduced_defs():
  global reduced_defs
  return reduced_defs

def add_reduced_def(df):
  global reduced_defs
  reduced_defs.add(df)

def complete_name(name):
    if base_name(name) in infix_precedence.keys() \
       or base_name(name) in prefix_precedence.keys():
        return 'operator ' + base_name(name)
    else:
        return base_name(name)
    
  
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
      if get_unique_names():
        return name
      else:
        return base_name(name)
    case RecFun(loc, name, typarams, params, returns, cases):
      return base_name(name)
    case TermInst(loc, tyof, subject, tyargs):
      return operator_name(subject)
    case _:
      raise Exception('operator_name, unexpected term ' + str(trm))

def is_infix_operator(trm):
  return is_operator(trm) and operator_name(trm) in infix_precedence.keys()

def is_prefix_operator(trm):
  return is_operator(trm) and operator_name(trm) in prefix_precedence.keys()

def precedence(trm):
  match trm:
    case Call(loc1, tyof, rator, args) if is_operator(rator):
      op_name = operator_name(rator)
      if len(args) >= 2:
        return infix_precedence.get(op_name, None)
      elif len(args) == 1:
        return prefix_precedence.get(op_name, None)
      else:
        return None
    case _:
      return None

def left_child(parent, child):
  match parent:
    case Call(loc1, tyof, rator, [left, right]):
      return child is left
    case _:
      return False
    
def op_arg_str(trm, arg):
  if precedence(trm) is not None and precedence(arg) is not None:
    if precedence(arg) < precedence(trm):
      return "(" + str(arg) + ")"
    elif precedence(arg) == precedence(trm): # and left_child(trm, arg):
      return "(" + str(arg) + ")"
  return str(arg)

def do_function_call(loc, name, type_params, type_args,
                     params, args, body, subst, env, return_type):
  body_env = env
  if False and len(params) != len(args):
    error(loc, 'in function call ' + base_name(name) \
          + '(' + ', '.join([str(a) for a in args]) + ')\n' \
          + '\tnumber of parameters: ' + str(len(params)) + '\n' \
          + '\tdoes not match number of arguments')
  for (x,ty) in zip(type_params, type_args):
    subst[x] = ty
  for (k,v) in zip(params, args):
    subst[k] = v
  for (k,v) in subst.items():
    if isinstance(v, TermInst):
      v.inferred = False
  new_fun_case_body = body.substitute(subst)
  old_defs = get_reduce_only()
  reduce_defs = [x for x in old_defs]
  if Var(loc, None, name, []) in reduce_defs:
    reduce_defs.remove(Var(loc, None, name, []))
  else:
    pass
  reduce_defs += [Var(loc, None, x, [x]) for x in params]
  # Revisit the following -Jeremy  
  # reduce_defs += [Var(loc, None, x, []) \
  #                 for x in fun_case.pattern.parameters \
  #                 + fun_case.parameters]
  set_reduce_only(reduce_defs)

  # Reduce the body of the function
  ret = new_fun_case_body.reduce(body_env)
  
  set_reduce_only(old_defs)
  add_reduced_def(name)
  if get_verbose():
    print('\tcall to ' + name + ' returns ' + str(ret))
  return explicit_term_inst(ret)


@dataclass
class Call(Term):
  rator: Term
  args: list[Term]

  def copy(self):
    ret = Call(self.location, self.typeof,
                self.rator.copy(),
                [arg.copy() for arg in self.args])
    if hasattr(self, 'type_args'):
      ret.type_args = self.type_args
    return ret

  def __str__(self):
    if is_infix_operator(self.rator) and len(self.args) >= 2:
      op_str = ' ' + operator_name(self.rator) + ' '
      return op_str.join([op_arg_str(self, arg) for arg in self.args])
    elif is_prefix_operator(self.rator) and len(self.args) == 1:
      return operator_name(self.rator) + " " + op_arg_str(self, self.args[0])
    elif isNat(self): # and not get_verbose():
      return str(natToInt(self))
    elif isDeduceInt(self):
      return deduceIntToInt(self)
    elif isNodeList(self):
      return '[' + nodeListToString(self)[:-2] + ']'
    elif isEmptySet(self) and not get_verbose():
      return '∅'
    else:
      return str(self.rator) + "(" \
        + ", ".join([str(arg) for arg in self.args])\
        + ")"

  def __eq__(self, other):
      if isinstance(other, TermInst):
        return self == other.subject
      if not isinstance(other, Call):
        return False
      if len(self.args) != len(other.args):
        return False
      eq_rators = self.rator == other.rator
      eq_rands = all([arg1 == arg2 for arg1,arg2 in zip(self.args, other.args)])
      result = eq_rators and eq_rands
      #print(str(self) + ' =? ' + str(other) + ' = ' + str(result))
      return result

  def reduce(self, env):
    if get_verbose():
      print('{{{{{{{{{{{{{{{{{{{{{{{{{{')
      print('reduce call ' + str(self))
    fun = self.rator.reduce(env)
    is_assoc = is_associative(self.location, rator_name(self.rator),
                              self.typeof, env)
    if is_assoc:
      flat_args = flatten_assoc_list(rator_name(self.rator), self.args)
    else:
      flat_args = self.args
    args = [arg.reduce(env) for arg in flat_args]
    if get_verbose():
      print('rator => ' + str(fun))
      print('is_associative? ' + str(is_assoc))
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
          ret = Call(self.location, self.typeof, fun, args)
      case Var(loc, ty, name, rs) if is_assoc:
        if get_verbose():
          print('rator is associative Var')
        ret = Call(self.location, self.typeof, fun,
                   flatten_assoc_list(rator_name(self.rator), args))
        if hasattr(self, 'type_args'):
          ret.type_args = self.type_args
      case Lambda(loc, ty, vars, body):
        if get_verbose():
          print('rator is Lambda')
        assert len(vars) == len(args)
        subst = {k: v for ((k,t),v) in zip(vars, args)}
        for (k,v) in subst.items():
          if isinstance(v, TermInst):
            v.inferred = False
        body_env = env
        new_body = body.substitute(subst)
        old_defs = get_reduce_only()
        set_reduce_only(old_defs + [Var(loc, t, x, []) for (x,t) in vars])
        ret = new_body.reduce(body_env)
        set_reduce_only(old_defs)
      case TermInst(loc, tyof,
                    RecFun(loc2, name, typarams, params, returns, cases),
                    type_args):
        return self.do_recursive_call(loc, name, fun, typarams, type_args,
                                      params, args, returns, cases, is_assoc,
                                      env) 
      case RecFun(loc, name, [], params, returns, cases):
        return self.do_recursive_call(loc, name, fun, [], [], params, args,
                                      returns, cases, is_assoc, env)
      case Generic(loc2, tyof, typarams, body):
        error(self.location, 'in reduction, call to generic\n\t' + str(self))
      case _:
        if get_verbose():
          print('not reducing call because neutral function: ' + str(fun))
        ret = Call(self.location, self.typeof, fun, args)
        if hasattr(self, 'type_args'):
          ret.type_args = self.type_args
    if get_verbose():
      print('call ' + str(self) + '\n\treturns ' + str(ret))
      print('}}}}}}}}}}}}}}}}}}}}}}}}}}')
    return ret

  def do_recursive_call(self, loc, name, fun, type_params, type_args, params, args,
                        returns, cases, is_assoc, env):
    if get_verbose():
      print('call to recursive function: ' + str(fun))
      print('\targs: ' + ', '.join([str(a) for a in args]))

    if is_assoc and len(args) > len(params):
      return self.reduce_associative(loc, name, fun, type_params, type_args,
                                     params, args, cases, env, returns)

    if len(args) == len(params):
      first_arg = args[0]
      rest_args = args[1:]
      for fun_case in cases:
          subst = {}
          if is_match(fun_case.pattern, first_arg, subst):
              return do_function_call(loc, name, type_params, type_args,
                                      fun_case.parameters, rest_args,
                                      fun_case.body, subst, env, returns)
    if is_assoc:
      if get_verbose():
        print('not reducing recursive call to associative ' + str(fun))
      return Call(self.location, self.typeof, fun,
                 flatten_assoc_list(rator_name(fun), args))
    else:
      if get_verbose():
        print('not reducing recursive call to ' + str(fun))
      return Call(self.location, self.typeof, fun, args)
  
  def reduce_associative(self, loc, name, fun, type_params, type_args,
                         params, args, cases, env, returns):
    if get_verbose():
      print('<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<')
      print('begin associative operator ' + str(fun))
      print('\targs: ' + ', '.join([str(a) for a in args]))
      print('\tparams: ' + ', '.join([str(p) for p in params]))

    old_reduce_only = get_reduce_only()
    reduce_only = [x for x in old_reduce_only]
    new_args = []
    worklist = args
    while len(worklist) > 1:
      if get_verbose():
        print('worklist: ' + ', '.join([str(a) for a in worklist]))
        print('new_args: ' + ', '.join([str(a) for a in new_args]))
      first_arg = worklist[0]; worklist = worklist[1:]
      #print('first_arg: ' + str(first_arg))
      did_call = False
      for fun_case in cases:
          subst = {}
          if is_match(fun_case.pattern, first_arg, subst):
              rest_args = worklist[:len(fun_case.parameters)]
              result = do_function_call(loc, name, type_params, type_args,
                                        fun_case.parameters, rest_args,
                                        fun_case.body, subst, env, returns)
              if get_verbose():
                print('call result: ' + str(result))
              worklist = [result] + worklist[len(fun_case.parameters):]
              did_call = True
              rator_var = Var(loc, None, name, [])
              if rator_var in reduce_only:
                reduce_only.remove(rator_var)
              set_reduce_only(reduce_only)
              break
      if not did_call:
        new_args.append(first_arg)
      if did_call and not get_reduce_all():
        break
      if get_verbose():
        print('-----------------------------')
    set_reduce_only(old_reduce_only)
    if get_verbose():
      print('end associative operator ' + str(fun))
      print('>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>')


    new_args += worklist
    flat_results = flatten_assoc_list(rator_name(self.rator), new_args)
    if get_verbose():
      print('}}}}}}}}}}}}}}}}}}}}}}}}}}')
    if len(flat_results) == 1:
      return explicit_term_inst(flat_results[0])
    else:
      return Call(self.location, self.typeof,
                  Var(loc, FunctionType(loc, [], params, returns),
                      name, [name]),
                  flat_results)
  
  def substitute(self, sub):
    ret = Call(self.location, self.typeof, self.rator.substitute(sub),
                [arg.substitute(sub) for arg in self.args])
    if hasattr(self, 'type_args'):
      ret.type_args = self.type_args
    return ret

  def uniquify(self, env):
    if False and get_verbose():
      print("uniquify call: " + str(self))
    self.rator.uniquify(env)
    for arg in self.args:
      arg.uniquify(env)
    if False and get_verbose():
      print("uniquify call result: " + str(self))

      
@dataclass
class SwitchCase(AST):
  pattern: Pattern
  body: Term
  
  def copy(self):
    return SwitchCase(self.location,
                      self.pattern.copy(),
                      self.body.copy())
  
  def __str__(self):
      return 'case ' + str(self.pattern) + ' { ' + str(self.body) + ' }'

  def pretty_print(self, indent):
      return indent*' ' + 'case ' + str(self.pattern) + ' {\n' \
          + (indent+2)*' ' + str(self.body) + '\n'\
          + indent*' ' + '}'
  
  def reduce(self, env):
      n = len(self.pattern.parameters)
      return SwitchCase(self.location,
                        PatternCons(self.pattern.location,
                                    self.pattern.constructor,
                                    self.pattern.parameters),
                        self.body.reduce(env))
    
  def substitute(self, sub):
      new_sub = {k: v for (k,v) in sub.items()}
      return SwitchCase(self.location,
                        self.pattern,
                        self.body.substitute(new_sub))

  def uniquify(self, env):
    self.pattern.uniquify(env)
    body_env = {x:y for (x,y) in env.items()}
    match self.pattern:
      case PatternBool(loc, value):
        pass
      case PatternCons(loc, constr, params):
        new_params = [generate_name(x) for x in params]
        for (old,new) in zip(params, new_params):
          overwrite(body_env, old, new, self.location)
        self.pattern.parameters = new_params
    self.body.uniquify(body_env)
    
  def __eq__(self, other):
    if not isinstance(other, SwitchCase):
      return False
    match self.pattern, other.pattern:
      case PatternBool(loc1, value1), PatternBool(loc2, value2):
        return value1 == value2 and self.body == other.body
      case PatternCons(loc1, constr1, params1), PatternCons(loc2, constr2, params2):
        alpha_rename = {x: Var(self.location, None, y) \
                        for (x,y) in zip(params1, params2) }
        new_body = self.body.substitute(alpha_rename)
        return constr1 == constr2 \
          and new_body == other.body
      case _:
        return False
    
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

  def pretty_print(self, indent, afterNewline=False):
      return ('' if afterNewline else '\n') + indent*' '+ 'switch ' + str(self.subject) + ' {\n' \
          + '\n'.join([c.pretty_print(indent+2) for c in self.cases]) + '\n'\
          + indent*' ' + '}'
  
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
            set_reduce_only(old_defs + [Var(self.location, None, x, []) \
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
      return self.subject == other
  
  def copy(self):
    return TermInst(self.location, self.typeof,
                    self.subject.copy(),
                    [ty.copy() for ty in self.type_args],
                    self.inferred)
  
  def __str__(self):
    if self.inferred and not get_verbose():
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
        return TermInst(self.location, self.typeof, subject_red,
                        self.type_args, self.inferred)
    
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
class Array(Term):
  elements: List[Term]
  
  def __eq__(self, other):
    if isinstance(other, Array):
      return all([elt == other_elt for (elt, other_elt) in zip(self.elements,
                                                               other.elements)])
    else:
      return False
  
  def copy(self):
    return Array(self.location, [elt.copy() for elt in self.elements])
  
  def __str__(self):
    return 'array(' + ', '.join([str(elt) for elt in self.elements]) + ')'

  def reduce(self, env):
    return Array(self.location, self.typeof,
                 [elt.reduce(env) for elt in self.elements])
    
  def substitute(self, sub):
    return Array(self.location, self.typeof,
                 [elt.substitute(sub) for elt in self.elements])
                    
  def uniquify(self, env):
    for elt in self.elements:
      elt.uniquify(env)
  
@dataclass
class MakeArray(Term):
  subject: Term

  def __eq__(self, other):
    if isinstance(other, MakeArray):
      return self.subject == other.subject
    else:
      return False
  
  def copy(self):
    return MakeArray(self.location, self.typeof,
                     self.subject.copy())
  
  def __str__(self):
    return 'array(' + str(self.subject) + ')'

  def reduce(self, env):
    subject_red = self.subject.reduce(env)
    if isNodeList(subject_red):
      elements = nodeListToList(subject_red)
      return Array(self.location, self.typeof, elements)
    else:
      return MakeArray(self.location, self.typeof, self.subject.reduce(env))
    
  def substitute(self, sub):
    return MakeArray(self.location, self.typeof,
                    self.subject.substitute(sub))

  def uniquify(self, env):
    self.subject.uniquify(env)

@dataclass
class ArrayGet(Term):
  subject: Term
  position: Term

  def __eq__(self, other):
    if isinstance(other, ArrayGet):
      return self.subject == other.subject \
        and self.position == other.position
    else:
      return False
  
  def copy(self):
    return ArrayGet(self.location, self.typeof,
                    self.subject.copy(), self.position.copy())
  
  def __str__(self):
    return str(self.subject) + '[' + str(self.position) + ']'

  def reduce(self, env):
    subject_red = self.subject.reduce(env)
    position_red = self.position.reduce(env)
    match subject_red:
      case Array(loc2, _, elements):
        if isNat(position_red):
          index = natToInt(position_red)
          if 0 <= index and index < len(elements):
            return elements[index].reduce(env)
          # Don't signal an error for out-of-bounds! -Jeremy
    return ArrayGet(self.location, self.typeof, subject_red, position_red)
    
  def substitute(self, sub):
    return ArrayGet(self.location, self.typeof,
                    self.subject.substitute(sub),
                    self.position.substitute(sub))

  def uniquify(self, env):
    self.subject.uniquify(env)
    self.position.uniquify(env)
      
@dataclass
class TLet(Term):
  var: str
  rhs: Term
  body: Term

  def __str__(self):
    return 'define ' + base_name(self.var) + ' = ' + str(self.rhs) + ';' \
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
    overwrite(body_env, self.var, new_var, self.location)
    self.var = new_var
    self.body.uniquify(body_env)
    
  def substitute(self, sub):
    new_rhs = self.rhs.substitute(sub)
    new_body = self.body.substitute(sub)
    return TLet(self.location, self.typeof, self.var, new_rhs, new_body)

@dataclass
class Hole(Term):
  
  def __str__(self):
      return '?'
    
  def uniquify(self, env):
    pass

  def reduce(self, env):
    return self

  def copy(self):
    return Hole(self.location, self.typeof)

  def substitute(self, sub):
    return self

@dataclass
class Omitted(Term):
  
  def __str__(self):
      return '--'
    
  def uniquify(self, env):
    pass

  def reduce(self, env):
    return self

  def copy(self):
    return Omitted(self.location, self.typeof)

  def substitute(self, sub):
    return self
  
@dataclass
class Mark(Term):
  subject: Term

  def __eq__(self, other):
    if isinstance(other, Mark):
      return self.subject == other.subject
    else:
      return self.subject == other
  
  def copy(self):
    return self.subject.copy()
    # return Mark(self.location, self.typeof,
    #             self.subject.copy())
  
  def __str__(self):
    return '#' + str(self.subject) + '#'

  def reduce(self, env):
    subject_red = self.subject.reduce(env)
    return Mark(self.location, self.typeof, subject_red)
    
  def substitute(self, sub):
    return Mark(self.location, self.typeof,
                self.subject.substitute(sub))

  def uniquify(self, env):
    self.subject.uniquify(env)

################ Formulas ######################################
  
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
    ret_args = []
    skip = False
    for i in range(len(self.args) - 1):
      if skip: 
        skip = False
        continue
      match self.args[i]:
        case IfThen(loc, tyof, prem, conc):
          if (self.args[i + 1]) == IfThen(loc, tyof, conc, prem):
            iff = Call(self.location, None, Var(self.location, None, '⇔', ['⇔']),
                       [prem,conc])
            iff_str = '(' + op_arg_str(iff, prem) + ' ⇔ ' + op_arg_str(iff, conc) +')'
            ret_args.append(iff_str)
            skip = True
            continue
      ret_args.append(self.args[i])
    
    if not skip:
      ret_args.append(self.args[-1])

    if len(ret_args) == 1:
      return str(ret_args[0])

    return '(' + ' and '.join([str(arg) for arg in ret_args]) + ')'

  def __eq__(self, other):
    if not isinstance(other, And):
      return False
    if len(self.args) != len(other.args):
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
    if len(self.args) != len(other.args):
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
      return Bool(self.location, BoolType(self.location), False)
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
    return IfThen(self.location, self.typeof, self.premise.copy(),
                  self.conclusion.copy())
  
  def __str__(self):
    match self.conclusion:
      case Bool(loc, tyof, False):
        return str(Call(self.location, self.typeof,
                        Var(self.location, None, 'not'),
                        [self.premise]))
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
      if get_verbose():
         print('reduce if, prem == conc')
      ret = Bool(self.location, BoolType(self.location), True)
    else:
      match prem:
        case Bool(loc, tyof, True):
          if get_verbose():
            print('reduce if, prem == True')
          ret = self.conclusion
        case Bool(loc, tyof, False):
          if get_verbose():
            print('reduce if, prem == False')
          ret = Bool(loc, tyof, True)
        case _:
          match conc:
            case Bool(loc, tyof, True):
              if get_verbose():
                print('reduce if, conc == True')
              ret = Bool(self.location, tyof, True)
            case _:
              ret = IfThen(self.location, self.typeof, prem, conc)
    if get_verbose():
      print('reduce ' + str(self) + '\n\t==> ' + str(ret))
    return ret
  
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
  var: Tuple[str,Type]
  # Position (s, e), where 
  #  e : The number of vars in the block
  #  s : The variable's index in the list, starting from the last var
  pos: Tuple[int, int]
  body: Formula

  def copy(self):
    x, t = self.var
    return All(self.location, self.typeof, (x, t.copy()), self.pos, self.body.copy())
  
  def __str__(self):
    v, t = self.var
    if not get_verbose():
      v = base_name(v)

    (s, e) = self.pos

    result = ''
    if s + 1 == e:
      result += "(all "
    result += f"{v}:{str(t)}"
    if s == 0:
      result += ". "
    else:
      result += ", "

    result += f"{str(self.body)}"

    if s + 1 == e: 
      result += ")"

    return result

  def reduce(self, env):
    new_body = self.body.reduce(env)
    match new_body:
      case Bool(loc, tyof, b):
        if get_verbose():
          print('reduce ' + str(self) + '\n\t==> ' + str(new_body))
        return new_body
      case _:
        x, ty = self.var
        return All(self.location,
                   self.typeof,
                   (x, ty.reduce(env)),
                   self.pos,
                   new_body)

  def substitute(self, sub):
    x, ty = self.var
    return All(self.location,
               self.typeof,
               (x, ty.substitute(sub)),
               self.pos,
               self.body.substitute(sub))
  
  def __eq__(self, other):
    if not isinstance(other, All):
      return False
    x, tx = self.var
    y, ty = other.var
    sub = { y: Var(self.location, None, x, [x]) }
    result = self.body == other.body.substitute(sub)
    return result

  def uniquify(self, env):
    body_env = {x:y for (x,y) in env.items()}
    (x,ty) = self.var
    t = ty.copy()
    t.uniquify(body_env)
    new_x = generate_name(x)
    overwrite(body_env, x, new_x, self.location)
    self.var = (new_x,t)
    self.body.uniquify(body_env)
    
@dataclass
class Some(Formula):
  vars: list[Tuple[str,Type]]
  body: Formula

  def copy(self):
    return Some(self.location,
                self.typeof,
               [(x,ty.copy()) for (x,ty) in self.vars],
               self.body.copy())
  
  def __str__(self):
      return 'some ' + ",".join([(v if get_verbose() else base_name(v)) + ":" + str(t) \
                                 for (v,t) in self.vars]) \
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
      overwrite(body_env, x, new_x, self.location)
    self.vars = new_vars
    self.body.uniquify(body_env)
    
  def __eq__(self, other):
    if not isinstance(other, Some):
      return False
    if all([tx == ty for ((x,tx),(y,ty))in zip(self.vars, other.vars)]):
      sub = {y: Var(self.location, None, x, [x]) \
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

  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
      return base_name(self.name)

  def uniquify(self, env):
    if self.name not in env.keys():
      env_str = ('\n' + ', '.join(env.keys())) if get_verbose() else ''
      error(self.location, "undefined proof variable " + self.name + env_str)
    if isinstance(env[self.name], list):
      self.name = env[self.name][0]
    else:
      error(self.location, "proof variable not bound to list " + self.name)
    
@dataclass
class PLet(Proof):
  label: str
  proved: Formula
  because: Proof
  body: Proof

  def pretty_print(self, indent):
      return indent*' ' + 'have ' + base_name(self.label) + ': ' + str(self.proved) + ' by {\n' \
          + self.because.pretty_print(indent+2) + '\n' \
          + indent*' ' + '}\n' \
          + maybe_pretty_print(self.body, indent)
  
  def __str__(self):
      return 'have ' + base_name(self.label) + ': ' + str(self.proved) \
        + ' by ' + str(self.because) + (' ' + str(self.body) if self.body else '')

  def uniquify(self, env):
    self.proved.uniquify(env)
    self.because.uniquify(env)
    body_env = {x:y for (x,y) in env.items()}
    new_label = generate_name(self.label)
    overwrite(body_env, self.label, new_label, self.location)
    self.label = new_label
    self.body.uniquify(body_env)

@dataclass
class PTLetNew(Proof):
  var: str
  rhs : Term
  body: Proof

  def pretty_print(self, indent):
      return indent*' ' + 'define ' + base_name(self.var) + ' = ' + str(self.rhs) + '\n' \
          + self.body.pretty_print(indent)
  
  def __str__(self):
      return 'define ' + base_name(self.var) + ' = ' + str(self.rhs) + '\n' \
         + str(self.body)

  def uniquify(self, env):
    self.rhs.uniquify(env)
    body_env = {x:y for (x,y) in env.items()}
    new_var = generate_name(self.var)
    overwrite(body_env, self.var, new_var, self.location)
    self.var = new_var
    self.body.uniquify(body_env)
    
    
@dataclass
class PRecall(Proof):
  facts: List[Formula]
  
  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
      return 'recall ' + ', '.join([str(f) for f in self.facts])

  def uniquify(self, env):
    for fact in self.facts:
      fact.uniquify(env)

  
@dataclass
class PAnnot(Proof):
  claim: Formula
  reason: Proof

  def pretty_print(self, indent):
      return indent*' ' + 'conclude ' + str(self.claim) + ' by {\n' \
          + self.reason.pretty_print(indent+2) + '\n' \
          + indent*' ' + '}\n'
  
  def __str__(self):
      return 'conclude ' + str(self.claim) + ' by ' + str(self.reason)

  def uniquify(self, env):
    self.claim.uniquify(env)
    self.reason.uniquify(env)

@dataclass
class Suffices(Proof):
  claim: Formula
  reason: Proof
  body: Proof

  def pretty_print(self, indent):
      return indent*' ' + 'suffices ' + str(self.claim) + '  by {\n' \
          + self.reason.pretty_print(indent+2) + '\n' \
          + maybe_pretty_print(self.body, indent)
  
  def __str__(self):
    return 'suffices ' + str(self.claim) + '  by ' + str(self.reason) + '\n' + maybe_str(self.body)

  def uniquify(self, env):
    self.claim.uniquify(env)
    self.reason.uniquify(env)
    self.body.uniquify(env)
  
@dataclass
class Cases(Proof):
  subject: Proof
  cases: List[Tuple[str,Formula,Proof]]

  def pretty_print(self, indent):
      cases_str = ''
      for (label, frm, body) in cases:
          cases_str += indent*' ' + 'case ' + base_name(label) + ' : ' + str(frm) + '{\n' \
              + body.pretty_print(indent+2) + '\n' \
              + indent*' ' + '}'
      return '\n'.join(cases_str) + '\n'
      
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
      overwrite(body_env, label, new_label, self.location)
      proof.uniquify(body_env)
      new_cases.append((new_label, formula, proof))
      i += 1
    self.cases = new_cases
      
@dataclass
class ModusPonens(Proof):
  implication: Proof
  arg: Proof

  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
      return 'apply ' + str(self.implication) + ' to ' + str(self.arg)

  def uniquify(self, env):
    self.implication.uniquify(env)
    self.arg.uniquify(env)
    
@dataclass
class ImpIntro(Proof):
  label: str
  premise: Formula
  body: Proof

  def pretty_print(self, indent):
    return indent*' ' + 'assume ' + str(self.label) + \
      (': ' + str(self.premise) if self.premise else '') + '\n'\
      + maybe_pretty_print(self.body, indent)
  
  def __str__(self):
    return 'assume ' + str(self.label) + \
      (': ' + str(self.premise) if self.premise else '') + \
      ('{' + str(self.body) + '}' if self.body else '')

  def uniquify(self, env):
    if self.premise:
      self.premise.uniquify(env)
    body_env = copy_dict(env)
    new_label = generate_name(self.label)
    overwrite(body_env, self.label, new_label, self.location)
    self.label = new_label
    self.body.uniquify(body_env)
    
@dataclass
class AllIntro(Proof):
  var: Tuple[str,Type]
  # Position (s, e), where 
  #  e : The number of vars in the all intro list
  #  s : The variable's index in the list, starting from the last var
  pos: Tuple[int, int]
  body: Proof

  def arbitrary_str(self):
    s, e = self.pos
    x, t = self.var
    res = ''
    if s + 1 == e:
      res += 'arbitrary '
    res += f"{x} : {str(t)}"
    if s == 0:
      res += ";"
    else:
      res += ","
    return res

  def pretty_print(self, indent):
      return indent*' ' + self.arbitrary_str() + '\n' \
          + maybe_pretty_print(self.body, indent)
  
  def __str__(self):
    return self.arbitrary_str() + maybe_str(self.body)

  def uniquify(self, env):
    body_env = copy_dict(env)
    x, ty = self.var
    new_t = ty.copy()
    new_t.uniquify(body_env)
    new_x = generate_name(x)
    overwrite(body_env, x, new_x, self.location)
    self.var = (new_x, new_t)
    self.body.uniquify(body_env)

  def set_body(self, new_body):
    if self.body:
      self.body.set_body(new_body)
    else:
      self.body = new_body
    
@dataclass
class AllElimTypes(Proof):
  univ: Proof
  arg: Type
  # Position (s, e), where 
  #  e : The number of vars in the block
  #  s : The variable's index in the list, starting from the first var
  pos: Tuple[int, int]

  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
    print(self.pos)
    s, e = self.pos
    res = str(self.univ)
    if s == 0:
      res += f"<{self.arg}"
    else:
      res += f", {self.arg}"

    if s + 1 == e:
      res += ">"

    return res

  def uniquify(self, env):
    self.univ.uniquify(env)
    self.arg.uniquify(env)
      
@dataclass
class AllElim(Proof):
  univ: Proof
  arg: Term
  # Position (s, e), where 
  #  e : The number of vars in the list
  #  s : The variable's index in the list, starting from the first var
  pos: Tuple[int, int]

  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
    s, e = self.pos
    res = str(self.univ)
    if s == 0:
      res += f"[{self.arg}"
    else:
      res += f", {self.arg}"

    if s + 1 == e:
      res += "]"

    return res

  def uniquify(self, env):
    self.univ.uniquify(env)
    self.arg.uniquify(env)
      
@dataclass
class SomeIntro(Proof):
  witnesses: List[Term]
  body: Proof

  def pretty_print(self, indent):
    return indent*' ' + 'choose ' + ",".join([str(t) for t in self.witnesses]) + '\n' \
        + maybe_pretty_print(self.body, indent)
  
  def __str__(self):
    return 'choose ' + ",".join([str(t) for t in self.witnesses]) \
        + '; ' + maybe_str(self.body)
  
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
  
  def pretty_print(self, indent):
    return indent*' ' + 'obtain ' + ",".join(self.witnesses) \
      + ' where ' + self.label \
      + (' : ' + str(self.prop) if self.prop else '') \
      + ' from ' + str(self.some)  + '\n'\
      + maybe_pretty_print(self.body, indent)

  def __str__(self):
    return 'obtain ' + ",".join(self.witnesses) \
      + ' where ' + self.label \
      + (' : ' + str(self.prop) if self.prop else '') \
      + ' from ' + str(self.some) \
      + '; ' + maybe_str(self.body)
  
  def uniquify(self, env):
    self.some.uniquify(env)
    body_env = copy_dict(env)
    new_witnesses = []
    for x in self.witnesses:
      new_x = generate_name(x)
      new_witnesses.append( new_x )
      overwrite(body_env, x, new_x, self.location)
    new_label = generate_name(self.label)
    overwrite(body_env, self.label, new_label, self.location)
    self.witnesses = new_witnesses
    self.label = new_label
    if self.prop:
      self.prop.uniquify(body_env)
    self.body.uniquify(body_env)
    
@dataclass
class PTuple(Proof):
  args: List[Proof]

  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
    return ', '.join([str(arg) for arg in self.args])

  def uniquify(self, env):
    for arg in self.args:
      arg.uniquify(env)

def extract_tuple(pf):
    match pf:
      case PTuple(loc, pfs):
        return pfs
      case _:
       return [pf]
   
@dataclass
class PAndElim(Proof):
  which: int
  subject: Proof

  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
    return 'conjunct ' + str(self.which) + ' of ' + str(self.subject)

  def uniquify(self, env):
    self.subject.uniquify(env)
      
@dataclass
class PTrue(Proof):
  
  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
    return '.'
  
  def uniquify(self, env):
    pass
  
@dataclass
class PReflexive(Proof):
  
  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
    return 'reflexive'
  
  def uniquify(self, env):
    pass

@dataclass
class PHole(Proof):
  
  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
      return '?'
    
  def uniquify(self, env):
    pass

@dataclass
class PSorry(Proof):
  
  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
      return 'sorry'
    
  def uniquify(self, env):
    pass

@dataclass
class PHelpUse(Proof):
  proof : Proof
  
  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
      return 'help ' + str(self.proof)
    
  def uniquify(self, env):
    self.proof.uniquify(env)
  
@dataclass
class PSymmetric(Proof):
  body: Proof
  
  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
    return 'symmetric ' + str(self.body)
  
  def uniquify(self, env):
    self.body.uniquify(env)

@dataclass
class PTransitive(Proof):
  first: Proof
  second: Proof
  
  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
    return 'transitive ' + str(self.first) + ' ' + str(self.second)

  def uniquify(self, env):
    self.first.uniquify(env)
    self.second.uniquify(env)

@dataclass
class PInjective(Proof):
  constr: Type
  body: Proof
  
  def pretty_print(self, indent):
    return indent*' ' + 'injective ' + str(self.constr) + '\n' \
        + maybe_pretty_print(self.body, indent)
  
  def __str__(self):
    return 'injective ' + str(self.constr) + '; ' + maybe_str(self.body)

  def uniquify(self, env):
    self.constr.uniquify(env)
    self.body.uniquify(env)

@dataclass
class PExtensionality(Proof):
  body: Proof
  
  def pretty_print(self, indent):
    return indent*' ' + 'extensionality\n' \
        + maybe_pretty_print(self.body, indent)

  def __str__(self):
    return 'extensionality\n' + maybe_str(self.body)

  def uniquify(self, env):
    self.body.uniquify(env)
    
@dataclass
class IndCase(AST):
  pattern: Pattern
  induction_hypotheses: list[Tuple[str,Formula]]
  body: Proof

  def pretty_print(self, indent):
    return indent*' ' + 'case ' + str(self.pattern) \
      + ' assume ' + ', '.join([x + ': ' + str(f) for (x,f) in self.induction_hypotheses]) \
      + '{\n' \
      + self.body.pretty_print(indent+2) \
      + indent*' ' + '}\n'
      
  def __str__(self):
    return 'case ' + str(self.pattern) \
      + ' assume ' + ', '.join([x + ': ' + str(f) for (x,f) in self.induction_hypotheses]) \
      + '{' + str(self.body) + '}'

  def uniquify(self, env):
    body_env = copy_dict(env)

    new_params = [generate_name(x) for x in self.pattern.parameters]
    for (old,new) in zip(self.pattern.parameters, new_params):
      overwrite(body_env, old, new, self.location)

    new_hyps = [(generate_name(x),f) for (x,f) in self.induction_hypotheses]
    for ((old,old_frm),(new,new_frm)) in zip(self.induction_hypotheses, new_hyps):
      overwrite(body_env, old, new, self.location)
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

  def pretty_print(self, indent):
    return indent*' ' + 'induction ' + str(self.typ) + '\n' \
      + '\n'.join([c.pretty_print(indent) for c in self.cases])

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

  def pretty_print(self, indent):
    return indent*' ' + 'case ' + str(self.pattern) + '{\n' \
        + self.body.pretty_print(indent+2) \
        + indent*' ' + '}\n'

  def __str__(self):
    return 'case ' + str(self.pattern) + '{' + str(self.body) + '}'

  def uniquify(self, env):
    self.pattern.uniquify(env)
    body_env = copy_dict(env)
    
    new_params = [generate_name(x) for x in self.pattern.bindings()]
    for (old,new) in zip(self.pattern.bindings(), new_params):
      overwrite(body_env, old, new, self.location)

    new_assumptions = [(generate_name(x),f) for (x,f) in self.assumptions]
    for (x,f) in new_assumptions:
      if f:
        f.uniquify(body_env)
    for ((old,old_frm),(new,new_frm)) in zip(self.assumptions, new_assumptions):
      overwrite(body_env, old, new, self.location)

    self.pattern.set_bindings(new_params)
    self.assumptions = new_assumptions
    self.body.uniquify(body_env)
    
@dataclass
class SwitchProof(Proof):
  subject: Term
  cases: List[SwitchProofCase]

  def pretty_print(self, indent):
      return indent*' ' + 'switch ' + str(self.subject) + '{\n' \
          + '\n'.join([c.pretty_print(indent+2) for c in self.cases]) \
          + indent*' ' + '}\n'
      
  def __str__(self):
      return 'switch ' + str(self.subject) \
        + '{' + '\n'.join([str(c) for c in self.cases]) + '}'
    
  def uniquify(self, env):
    self.subject.uniquify(env)
    for c in self.cases:
      c.uniquify(env)
      
@dataclass
class EvaluateGoal(Proof):

  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
    return 'evaluate'

  def uniquify(self, env):
    pass

@dataclass
class EvaluateFact(Proof):
  subject: Proof

  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
    return 'evaluate ' + str(self.subject)

  def uniquify(self, env):
    self.subject.uniquify(env)
  
@dataclass
class ApplyDefs(Proof):
  definitions: List[Term]

  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
      return 'definition ' + ' | '.join([str(d) for d in self.definitions])

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
      return 'definition ' + ' | '.join([str(d) for d in self.definitions]) \
        + ' in ' + str(self.subject)

  def uniquify(self, env):
    for d in self.definitions:
      d.uniquify(env)
    self.subject.uniquify(env)

@dataclass
class EnableDefs(Proof):
  definitions: List[Term]
  body: Proof

  def __str__(self):
      return 'enable { ' + ', '.join([str(d) for d in self.definitions]) \
        + ' };' + maybe_str(self.body)

  def uniquify(self, env):
    for d in self.definitions:
      d.uniquify(env)
    self.body.uniquify(env)
    
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

## Updates the environment with a name, creating overloads
def extend(env, name, new_name, loc):
  if name in env['no overload']:
    ty = env['no overload'][name]
    error(loc, f"Cannot overload {ty} names. {name} is already defined as a {ty}")

  if name in env.keys():
    env[name].append(new_name)
  else:
    env[name] = [new_name]

## Overwrites a value in the environment, with a warning
def overwrite(env, name, new_name, loc):
  if name in env['no overload']:
    ty = env['no overload'][name]
    error(loc, f"Cannot overload {ty} names. {name} is already defined as a {ty}")

  if base_name(name) != "_" and name in env.keys():
    warning(loc, f"WARNING: {name} is already defined")
  env[name] = [new_name]
      
@dataclass
class Theorem(Statement):
  name: str
  what: Formula
  proof: Proof
  isLemma: bool

  def __str__(self):
    return ('lemma ' if self.isLemma else 'theorem ') \
      + self.name + ': ' + str(self.what) \
      + '\nproof\n' + self.proof.pretty_print(2) + '\nend\n'

  def uniquify(self, env):
    if self.name in env.keys():
      error(self.location, "theorem names may not be overloaded")
    self.what.uniquify(env)
    self.proof.uniquify(env)
    new_name = generate_name(self.name)
    overwrite(env, self.name, new_name, self.location)
    env['no overload'][self.name] = 'theorem'
    self.name = new_name
    
  def collect_exports(self, export_env):
    if not self.isLemma:
      export_env[base_name(self.name)] = [self.name]
    
@dataclass
class Constructor(AST):
  name: str
  parameters: List[Type]

  def pretty_print(self, indent):
      return indent*' ' + str(self)
  
  def uniquify(self, env, body_env):
    for ty in self.parameters:
      ty.uniquify(body_env)

    new_name = generate_name(self.name)
    extend(env, self.name, new_name, self.location)
    self.name = new_name
      
  def __str__(self):
    if get_verbose():
      name = self.name
    else:
      name = base_name(self.name)
    if len(self.parameters) > 0:
      return name + '(' + ', '.join([str(ty) for ty in self.parameters]) + ')'
    else:
      return name
  
      
@dataclass
class Union(Statement):
  name: str
  type_params: List[str]
  alternatives: List[Constructor]
  isPrivate: bool

  def reduce(self, env):
    return self
  
  def uniquify(self, env):
    if self.name in env.keys():
      error(self.location, "union names may not be overloaded")
    new_name = generate_name(self.name)
    env[self.name] = [new_name]
    env['no overload'][self.name] = 'union'
    self.name = new_name
    
    body_env = copy_dict(env)
    new_type_params = [generate_name(t) for t in self.type_params]
    for (old,new) in zip(self.type_params, new_type_params):
      extend(body_env, old, new, self.location)
    self.type_params = new_type_params
    
    for con in self.alternatives:
      con.uniquify(env, body_env)

  def collect_exports(self, export_env):
    if self.isPrivate:
      return
    export_env[base_name(self.name)] = [self.name]
    for con in self.alternatives:
      extend(export_env, base_name(con.name), con.name, self.location)
    
  def substitute(self, sub):
    return self
      
  def pretty_print(self, indent):
      return indent*' ' + 'union ' + base_name(self.name) \
          + ('<' + ','.join([base_name(t) for t in self.type_params]) + '>' if len(self.type_params) > 0 \
             else '') + ' {\n' \
        + '\n'.join([c.pretty_print(indent+2) for c in self.alternatives]) + '\n'\
        + indent*' ' + '}\n'
  
  def __str__(self):
    if get_verbose():
      return 'union ' + self.name + '<' + ','.join(self.type_params) + '> {' \
        + ' '.join([str(c) for c in self.alternatives]) + '}'
    else:
      return base_name(self.name)
  
  
@dataclass
class FunCase(AST):
  rator: Term
  pattern: Pattern
  parameters: List[str]
  body: Term

  def pretty_print(self, indent):
      return indent*' ' + str(self.rator) + '(' + str(self.pattern) \
          + (', ' + ', '.join([base_name(p) for p in self.parameters]) if len(self.parameters) > 0 else '') \
          + ') = ' + self.body.pretty_print(indent+2)
  
  def __str__(self):
      return str(self.rator) + '(' + str(self.pattern) + ',' + ",".join(self.parameters) \
          + ') = ' + str(self.body)

  def uniquify(self, env):
    self.rator.uniquify(env)
    self.pattern.uniquify(env)
    body_env = copy_dict(env)

    match self.pattern:
      case PatternCons(loc, cons, parameters):
        new_pat_params = [generate_name(x) for x in parameters]
        for (old,new) in zip(parameters, new_pat_params):
          overwrite(body_env, old, new, self.location)
        self.pattern.parameters = new_pat_params
      case PatternBool(loc, b):
        pass

    new_params = [generate_name(x) for x in self.parameters]
    for (old,new) in zip(self.parameters, new_params):
      overwrite(body_env, old, new, self.location)
    self.parameters = new_params

    self.body.uniquify(body_env)
    
    
@dataclass
class RecFun(Statement):
  name: str
  type_params: List[str]
  params: List[Type]
  returns: Type
  cases: List[FunCase]
  isPrivate: bool

  def uniquify(self, env):
    new_name = generate_name(self.name)
    extend(env, self.name, new_name, self.location)
    self.name = new_name
    
    body_env = copy_dict(env)
    new_type_params = [generate_name(t) for t in self.type_params]
    for (old,new) in zip(self.type_params, new_type_params):
      extend(body_env, old, new, self.location)
    self.old_type_params = self.type_params
    self.type_params = new_type_params
    
    for ty in self.params:
      ty.uniquify(body_env)
    self.returns.uniquify(body_env)

    for c in self.cases:
      c.uniquify(body_env)
    
  def collect_exports(self, export_env):
    if self.isPrivate:
      return
    extend(export_env, base_name(self.name), self.name, self.location)

  def __str__(self):
    if get_verbose():
      return self.to_string()
    else:
      return self.name if get_unique_names() else base_name(self.name)
    
  def to_string(self):
    return 'recursive ' + self.name + '<' + ','.join(self.type_params) + '>' \
      + '(' + ','.join([str(ty) for ty in self.params]) + ')' \
      + ' -> ' + str(self.returns) + '{\n' \
      + '\n'.join([str(c) for c in self.cases]) \
      + '\n}'

  def pretty_print(self, indent):
    return indent*' ' + 'recursive ' + complete_name(self.name) \
        + ('<' + ','.join([base_name(t) for t in self.type_params]) + '>' if len(self.type_params) > 0 \
           else '') \
      + '(' + ','.join([str(ty) for ty in self.params]) + ')' \
      + ' -> ' + str(self.returns) + '{\n' \
      + '\n'.join([c.pretty_print(indent+2) for c in self.cases]) + '\n' \
      + '}\n'

  def __eq__(self, other):
    if isinstance(other, Var):
      result = self.name == other.name
      #print(str(self) + ' =? ' + str(other) + ' = ' + str(result))
      return result
    elif isinstance(other, TermInst):
      return self == other.subject
    elif isinstance(other, RecFun):
      result = self.name == other.name
      #print(str(self) + ' =? ' + str(other) + ' = ' + str(result))
      return result
    else:
      return False
  
  def reduce(self, env):
    return self

  def substitute(self, sub):
    return self

def pretty_print_function(name, type_params, params, body):
    return 'fun ' + complete_name(name) \
        + ('<' + ', '.join([base_name(t) for t in type_params]) + '>' \
           if len(type_params) > 0 else '') \
        + '(' + ', '.join([x + ':' + str(t) if t else x \
                           for (x,t) in params]) + ')' \
        + " {\n" + body.pretty_print(2, True) + "\n}\n"

@dataclass
class Define(Statement):
  name: str
  typ: Type
  body: Term
  isPrivate: bool

  def __str__(self):
    if isinstance(self.body, Lambda):
        params = [(base_name(x), t) for (x,t) in self.body.vars]
        return pretty_print_function(self.name,[],params, self.body.body)
    elif isinstance(self.body, Generic) \
         and isinstance(self.body.body, Lambda):
        typarams = self.body.type_params
        params = [(base_name(x), t) for (x,t) in self.body.body.vars]
        return pretty_print_function(self.name, typarams, params,
                                     self.body.body.body)
    else:
        return 'define ' + complete_name(self.name) \
            + (' : ' + str(self.typ) if self.typ else '') \
            + ' = ' + self.body.pretty_print(4, False) + '\n'
  
  def uniquify(self, env):
    if self.typ:
      self.typ.uniquify(env)
    self.body.uniquify(env)

    new_name = generate_name(self.name)
    extend(env, self.name, new_name, self.location)
    self.name = new_name

  def collect_exports(self, export_env):
    if self.isPrivate:
      return
    extend(export_env, base_name(self.name), self.name, self.location)
    
uniquified_modules = {}

def get_uniquified_modules():
  global uniquified_modules
  return uniquified_modules

def add_uniquified_module(module_name, ast):
  global uniquified_modules
  uniquified_modules[module_name] = ast


@dataclass
class Assert(Statement):
  formula : Term

  def __str__(self):
    return 'assert ' + str(self.formula)

  def uniquify(self, env):
    self.formula.uniquify(env)
  
  def collect_exports(self, export_env):
    pass
    
@dataclass
class Print(Statement):
  term : Term

  def __str__(self):
    return 'print ' + str(self.term)

  def uniquify(self, env):
    self.term.uniquify(env)
  
  def collect_exports(self, export_env):
    pass

  
def find_file(loc, name):
  for dir in get_import_directories():
    filename = os.path.join(dir, name + ".pf")
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
    if get_verbose():
      print('uniquify import ' + self.name)
    old_verbose = get_verbose()
    if get_verbose() == VerboseLevel.CURR_ONLY:
      set_verbose(VerboseLevel.NONE)

    global uniquified_modules
    if self.name in uniquified_modules.keys():
      self.ast = uniquified_modules[self.name]
    else:
      filename = find_file(self.location, self.name)
      file = open(filename, 'r', encoding="utf-8")
      src = file.read()
      file.close()
      if get_recursive_descent():
        from rec_desc_parser import get_filename, set_filename, parse
      else:
        from parser import get_filename, set_filename, parse
      old_filename = get_filename()
      set_filename(filename)
      self.ast = parse(src, trace=False)
      uniquified_modules[self.name] = self.ast
      set_filename(old_filename)
      uniquify_deduce(self.ast)
      
    for stmt in self.ast:
      stmt.collect_exports(env)
    set_verbose(old_verbose)
    if get_verbose():
      print('\tuniquify finished import ' + self.name)

  def collect_exports(self, export_env):
    pass

@dataclass
class Associative(Statement):
  type_params: List[str]
  op: Term
  typeof: Type

  def __str__(self):
    return 'associative ' + str(self.op) \
      + ('<' + ','.join(self.type_params) + '>' if len(self.type_params) > 0 else '') \
      + ' ' + str(self.typeof)

  def uniquify(self, env):
    self.op.uniquify(env)
    body_env = {x:y for (x,y) in env.items()}
    new_type_params = [generate_name(x) for x in self.type_params]
    for (old,new) in zip(self.type_params, new_type_params):
      overwrite(body_env, old, new, self.location)
    self.type_params = new_type_params
    self.typeof.uniquify(body_env)

  def collect_exports(self, export_env):
    opname = self.op.resolved_names[0]
    full_name = '__associative_' + opname
    base = base_name(opname)
    full_base_name = '__associative_' + base
    export_env[full_base_name] = [full_name]

# ---------------------
# Auxiliary Functions
  
def mkEqual(loc, arg1, arg2):
  ret = Call(loc, None, Var(loc, None, '=', []), [arg1, arg2])
  return ret

def split_equation(loc, equation):
  match equation:
    case Call(loc1, tyof, Var(loc2, tyof2, '=', rs2), [L, R]):
      return (L, R)
    case All(loc1, tyof, var, pos, body):
      return split_equation(loc, body)
    case _:
      error(loc, 'expected an equality, not ' + str(equation))

def equation_vars(formula):
  match formula:
    case Call(loc1, tyof, Var(loc2, tyof2, '=', rs2), [L, R]):
      return []
    case All(loc1, tyof, var, pos, body):
      x, t = var
      v = Var(loc1, None, x, [])
      v.typeof = t
      return [v] + equation_vars(body)
    case _:
      raise Exception('equation_vars unhandled ' + str(formula))
      
def is_equation(formula):
  match formula:
    case Call(loc1, tyof, Var(loc2, tyof2, '=', rs2), [L, R]):
      return True
    case All(loc1, tyof, var, pos, body):
      return is_equation(body)
    case _:
      return False

def mkZero(loc):
  return Var(loc, None, 'zero', [])

def mkSuc(loc, arg):
  return Call(loc, None, Var(loc, None, 'suc', []), [arg])

def intToNat(loc, n):
  if n == 0:
    return mkZero(loc)
  else:
    return mkSuc(loc, intToNat(loc, n - 1))

def isNat(t):
  match t:
    case Var(loc, tyof, name, rs) if base_name(name) == 'zero':
      return True
    case Call(loc, tyof1, Var(loc2, tyof2, name, rs), [arg]) \
      if base_name(name) == 'suc':
      return isNat(arg)
    case _:
      return False

def natToInt(t):
  match t:
    case Var(loc, tyof, name, rs) if base_name(name) == 'zero':
      return 0
    case Call(loc, tyof1, Var(loc2, tyof2, name, rs), [arg]) \
      if base_name(name) == 'suc':
      return 1 + natToInt(arg)

def mkPos(loc, arg):
  return Call(loc, None, Var(loc, None, 'pos', []), [arg])

def mkNeg(loc, arg):
  return Call(loc, None, Var(loc, None, 'negsuc', []), [arg])

def intToDeduceInt(loc, n, sign):
  if sign == 'PLUS':
    return mkPos(loc, intToNat(loc, n))
  else:
    return mkNeg(loc, intToNat(loc, n - 1))

def isDeduceInt(t):
  match t:
    case Call(loc, tyof1, Var(loc2, tyof2, name), [arg]) if base_name(name) == 'pos':
      return isNat(arg)
    case Call(loc, tyof1, Var(loc2, tyof2, name), [arg]) if base_name(name) == 'negsuc':
      return isNat(arg)
    case _:
      return False
  

def deduceIntToInt(t):
  match t:
    case Call(loc, tyof1, Var(loc2, tyof2, name), [arg]) if base_name(name) == 'pos':
      return '+' + str(natToInt(arg))
    case Call(loc, tyof1, Var(loc2, tyof2, name), [arg]) if base_name(name) == 'negsuc':
      return '-' + str(1 + natToInt(arg))

def is_constructor(constr_name, env):
  for (name,binding) in env.dict.items():
    if isinstance(binding, TypeBinding):
      match binding.defn:
        case Union(loc2, name, typarams, alts, isPrivate):
          for constr in alts:
            if constr.name == constr_name:
              return True
        case _:
          continue
  return False

def is_constr_term(term, env):
  match term:
    case Var(loc, ty, n, rs):
      return is_constructor(n, env)
    case TermInst(loc, ty, body):
      return is_constr_term(body, env)
    case _:
      return False

def constr_name(term):
  match term:
    case Var(loc, ty, n, rs):
      return n
    case TermInst(loc, ty, body):
      return constr_name(body)
    case _:
      raise Exception('constr_name unhandled ' + str(term))
    
def constructor_conflict(term1, term2, env):
  match (term1, term2):
    case (Call(loc1, tyof1, rator1, rands1),
          Call(loc2, tyof3, rator2, rands2)) if is_constr_term(rator1, env) and is_constr_term(rator2, env):
     if constr_name(rator1) != constr_name(rator2):
       return True
     else:
       return any([constructor_conflict(rand1, rand2, env) \
                   for (rand1, rand2) in zip(rands1, rands2)])
    case (Call(loc1, tyof1, rator1, rands1), term2) if is_constr_term(rator1, env) and is_constr_term(term2, env):
      if constr_name(rator1) != constr_name(term2):
        return True
    case (term1, term2) if is_constr_term(term1, env) and is_constr_term(term2, env):
      if constr_name(term1) != constr_name(term2):
        return True
    case (term1, Call(loc2, tyof2, rator2, rands2)) if is_constr_term(term1, env) and is_constr_term(rator2, env):
      if constr_name(term1) != constr_name(rator2):
        return True
    case (Bool(_, tyof1, True), Bool(_, tyof2, False)):
      return True
    case (Bool(_, tyof1, False), Bool(_, tyof2, True)):
      return True
  return False

def isNodeList(t):
  match t:
    case TermInst(loc2, tyof2, Var(loc3, tyof3, name, rs1), tyargs, inferred) \
      if base_name(name) == 'empty':
        return True
    case Call(loc, tyof1, TermInst(loc2, tyof2, Var(loc3, tyof3, name, rs3), tyargs, inferred),
              [arg, ls]) if base_name(name) == 'node':
        return isNodeList(ls)
    case _:
      return False
    
def nodeListToList(t):
  match t:
    case TermInst(loc2, tyof2, Var(loc3, tyof3, name, rs), tyargs, inferred) \
      if base_name(name) == 'empty':
        return []
    case Call(loc, tyof1, TermInst(loc2, tyof2, Var(loc3, tyof3, name, rs),
                                   tyargs, inferred),
              [arg, ls]) if base_name(name) == 'node':
      return [arg] + nodeListToList(ls)
    
def nodeListToString(t):
  match t:
    case TermInst(loc2, tyof2, Var(loc3, tyof3, name, rs), tyargs, inferred) \
      if base_name(name) == 'empty':
        return ''
    case Call(loc, tyof1, TermInst(loc2, tyof2, Var(loc3, tyof3, name, rs),
                                   tyargs, inferred),
              [arg, ls]) if base_name(name) == 'node':
      return str(arg) + ', ' + nodeListToString(ls)

def mkEmpty(loc):
  return Var(loc, None, 'empty', [])

def mkNode(loc, arg, ls):
  return Call(loc, None, Var(loc, None, 'node', []), [arg, ls])

def listToNodeList(loc, lst):
  if len(lst) == 0:
    return mkEmpty(loc)
  else:
    return mkNode(loc, lst[0], listToNodeList(loc, lst[1:]))

def isEmptySet(t):
  match t:
    case Call(loc2, tyof2, fun,
              [Lambda(loc3, tyof3, vars, Bool(loc4, tyof4, False))]) \
              if base_name(rator_name(fun)) == 'char_fun':
      return True
    case _:
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
  local : bool = False
  
  def __str__(self):
    return str(self.typ) + (' = ' + str(self.defn) if self.defn else '')

@dataclass
class ProofBinding(Binding):
  formula : Formula
  local : bool
  
  def __str__(self):
    return str(self.formula)

def type_params_str(type_params):
  if len(type_params) > 0:
    return '<' + ','.join(type_params) + '>'
  else:
    return ''
  
@dataclass
class AssociativeBinding(Binding):
  opname: str
  types: List[Tuple[List[str], Type]]

  def __str__(self):
    return 'associative ' + self.opname \
      + ' ' + ', '.join(type_params_str(type_params) + str(t) \
                        for (type_params, t) in self.types)
        
class Env:
  def __init__(self, env = None):
    if env:
      self.dict = copy_dict(env)
    else:
      self.dict = {}

  def __str__(self):
    return ',\n'.join(['\t' + k + ': ' + str(v) \
                       for (k,v) in reversed(self.dict.items())])

  def __contains__(self, item):
    return item in self.dict.keys()
    
  def proofs_str(self):
    return ',\n'.join(['\t' + base_name(k) + ': ' + str(v) \
                       for (k,v) in reversed(self.dict.items()) \
                       if isinstance(v,ProofBinding) and (v.local or get_verbose() == VerboseLevel.FULL)])

  def term_vars_str(self):
    return ',\n'.join(['\t' + base_name(k) + ': ' + str(v.typ) \
                       for (k,v) in reversed(self.dict.items()) \
                       if isinstance(v,TermBinding) and v.local])
  
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
  
  def declare_term_var(self, loc, name, typ, local = False):
    if typ == None:
      error(loc, 'None not allowed as type of variable in declare_term_var')
    new_env = Env(self.dict)
    new_env.dict[name] = TermBinding(loc, typ)
    new_env.dict[name].local = local
    return new_env

  def declare_assoc(self, loc, opname, typarams, typ):
    new_env = Env(self.dict)
    full_name = '__associative_' + opname
    if full_name in new_env:
      old = new_env.dict[full_name]
      new_env.dict[full_name] = AssociativeBinding(loc, opname, [(typarams, typ)] + old.types)
    else:
      new_env.dict[full_name] = AssociativeBinding(loc, opname, [(typarams, typ)])
    return new_env
  
  def declare_term_vars(self, loc, xty_pairs, local = False):
    new_env = self
    for (x,ty) in xty_pairs:
      new_env = new_env.declare_term_var(loc, x, ty, local)
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
        raise Exception('expected a term or type variable, not ' + base_name(name))
    else:
      return None

  def _value_of_term_var(self, curr, name):
    if name in curr.keys():
      return curr[name].defn
    else:
      return None
  
  def _formula_of_proof_var(self, curr, name):
    if name in curr.keys():
      match curr[name]:
        case ProofBinding(loc, formula):
          return formula
        case TermBinding(loc, FunctionType()):
          raise Exception('expected a proof but instead got term `' + base_name(name) + '`.'\
                        + '\nPerhaps you meant `definition ' + base_name(name) + '`?')
        case TermBinding():
          raise Exception('expected a proof but instead got term `' + base_name(name) + '`.'\
                        + '\nPerhaps you meant `recall ' + base_name(name) + '`?')
        case TypeBinding():
          raise Exception('expected a proof but instead got type ' + base_name(name))
        case _:
          raise Exception('expected a proof but instead got ' + base_name(name))
    else:
      return None
    
  def type_var_is_defined(self, tyname):
    match tyname:
      case Var(loc, tyof, name, resolved_names):
        if len(resolved_names) == 1:
          return resolved_names[0] in self.dict.keys()
        else:
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
        raise Exception('expected a term variable, not ' + str(tvar))
        
  def proof_var_is_defined(self, pvar):
    match pvar:
      case PVar(loc, name):
        if self._formula_of_proof_var(self.dict, name):
          return True
        else:
          return False
      case _:
        raise Exception('expected proof var, not ' + str(pvar))

  def get_assoc_types(self, opname):
    full_name = '__associative_' + opname
    if full_name in self.dict.keys():
      return self.dict['__associative_' + opname].types
    else:
      return []
      
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
      case Var(loc, tyof, name, resolved_names):
        if isinstance(resolved_names, str):
          error(loc, 'resolved_names is a string but should be a list: ' + str(tvar))
        overloads = [(x, self._type_of_term_var(self.dict, x)) for x in resolved_names]
        if len(overloads) > 1:
          ret = OverloadType(loc, overloads)
        elif len(overloads) == 1:
          ret = overloads[0][1]
        else:
          ret = self._type_of_term_var(self.dict, name)
        if get_verbose():
          print('get_type_of_term_var(' + name + ') = ' + str(ret))
        return ret

  def get_value_of_term_var(self, tvar):
    match tvar:
      case Var(loc, tyof, name):
        return self._value_of_term_var(self.dict, name)

  def local_proofs(self):
    return [b.formula for (name, b) in self.dict.items() \
            if isinstance(b, ProofBinding) and b.local]

  def proofs(self):
    return [b.formula for (name, b) in self.dict.items() \
            if isinstance(b, ProofBinding)]
  
def print_theorems(filename, ast):
  fullpath = Path(filename)
  theorem_filename = fullpath.with_suffix('.thm')
  to_print = []
  for s in ast:
    if isinstance(s, Theorem) and not s.isLemma:
      to_print.append(base_name(s.name) + ': ' + str(s.what) + '\n')
    elif hasattr(s, 'isPrivate') and not s.isPrivate:
      to_print.append(s.pretty_print(0))
  
  if len(to_print) == 0:
    return
  
  with open(theorem_filename, 'w', encoding='utf-8') as theorem_file:
    print('This file was automatically generated by Deduce.', file=theorem_file)
    print('This file summarizes the theorems proved in the file:\n\t' + filename, file=theorem_file)
    print('', file=theorem_file)
    for line in to_print:
      print(line, file=theorem_file)

############# Marks for controlling rewriting and definitions #########################

default_mark_LHS = True

def set_default_mark_LHS(b):
  global default_mark_LHS
  default_mark_LHS = b
  
def get_default_mark_LHS():
  global default_mark_LHS
  return default_mark_LHS

@dataclass
class MarkException(BaseException):
    subject: Term

def count_marks(formula):
  match formula:
    case Mark(loc2, tyof, subject):
      return 1 + count_marks(subject)
    case TermInst(loc2, tyof, subject, tyargs, inferred):
      return count_marks(subject)
    case Var(loc2, tyof, name):
      return 0
    case Bool(loc2, tyof, val):
      return 0
    case And(loc2, tyof, args):
      return sum([count_marks(arg) for arg in args])
    case Or(loc2, tyof, args):
      return sum([count_marks(arg) for arg in args])
    case IfThen(loc2, tyof, prem, conc):
      return count_marks(prem) + count_marks(conc)
    case All(loc2, tyof, var, _, frm2):
      return count_marks(frm2)
    case Some(loc2, tyof, vars, frm2):
      return count_marks(frm2)
    case Call(loc2, tyof, rator, args):
      return count_marks(rator) + sum([count_marks(arg) for arg in args])
    case Switch(loc2, tyof, subject, cases):
      return count_marks(subject) + sum([count_marks(c) for c in cases])
    case SwitchCase(loc2, pat, body):
      return count_marks(body)
    case RecFun(loc, name, typarams, params, returns, cases):
      return 0
    case Conditional(loc2, tyof, cond, thn, els):
      return count_marks(cond) + count_marks(thn) + count_marks(els)
    case Lambda(loc2, tyof, vars, body):
      return count_marks(body)
    case Generic(loc2, tyof, typarams, body):
      return count_marks(body)
    case TAnnote(loc2, tyof, subject, typ):
      return count_marks(subject)
    case TLet(loc2, tyof, var, rhs, body):
      return count_marks(rhs) + count_marks(body)
    case Hole(loc2, tyof):
      return 0
    case Omitted(loc2, tyof):
      return 0
    case ArrayGet(loc, tyof, arr, ind):
      return count_marks(arr) + count_marks(ind)
    case _:
      error(formula.location, 'in count_marks function, unhandled ' + str(formula))

def find_mark(formula):
  match formula:
    case Mark(loc2, tyof, subject):
      raise MarkException(subject)
    case TermInst(loc2, tyof, subject, tyargs, inferred):
      find_mark(subject)
    case Var(loc2, tyof, name):
      pass
    case Bool(loc2, tyof, val):
      pass
    case And(loc2, tyof, args):
      for arg in args:
          find_mark(arg)
    case Or(loc2, tyof, args):
      for arg in args:
          find_mark(arg)
    case IfThen(loc2, tyof, prem, conc):
      find_mark(prem)
      find_mark(conc)
    case All(loc2, tyof, var, pos, frm2):
      find_mark(frm2)
    case Some(loc2, tyof, vars, frm2):
      find_mark(frm2)
    case Call(loc2, tyof, rator, args):
      find_mark(rator)
      for arg in args:
          find_mark(arg)
    case Switch(loc2, tyof, subject, cases):
      find_mark(subject)
      for c in cases:
          find_mark(c)
    case SwitchCase(loc2, pat, body):
      find_mark(body)
    case RecFun(loc, name, typarams, params, returns, cases):
      pass
    case Conditional(loc2, tyof, cond, thn, els):
      find_mark(cond)
      find_mark(thn)
      find_mark(els)
    case Lambda(loc2, tyof, vars, body):
      find_mark(body)
    case Generic(loc2, tyof, typarams, body):
      find_mark(body)
    case TAnnote(loc2, tyof, subject, typ):
      find_mark(subject)
    case TLet(loc2, tyof, var, rhs, body):
      find_mark(rhs)
      find_mark(body)
    case Hole(loc2, tyof):
      pass
    case ArrayGet(loc2, tyof, arr, ind):
      find_mark(arr)
      find_mark(ind)
    case _:
      error(formula.location, 'in find_mark function, unhandled ' + str(formula))

def replace_mark(formula, replacement):
  match formula:
    case Mark(loc2, tyof, subject):
      return replacement
    case TermInst(loc2, tyof, subject, tyargs, inferred):
      return TermInst(loc2, tyof, replace_mark(subject, replacement), tyargs, inferred)
    case Var(loc2, tyof, name):
      return formula
    case Bool(loc2, tyof, val):
      return formula
    case And(loc2, tyof, args):
      return And(loc2, tyof, [replace_mark(arg, replacement) for arg in args])
    case Or(loc2, tyof, args):
      return Or(loc2, tyof, [replace_mark(arg, replacement) for arg in args])
    case IfThen(loc2, tyof, prem, conc):
      return IfThen(loc2, tyof, replace_mark(prem, replacement),
                    replace_mark(conc, replacement))
    case All(loc2, tyof, var, pos, frm2):
      return All(loc2, tyof, var, pos, replace_mark(frm2, replacement))
    case Some(loc2, tyof, vars, frm2):
      return Some(loc2, tyof, vars, replace_mark(frm2, replacement))
    case Call(loc2, tyof, rator, args):
      return Call(loc2, tyof, replace_mark(rator, replacement),
                  [replace_mark(arg, replacement) for arg in args])
    case Switch(loc2, tyof, subject, cases):
      return Switch(loc2, tyof, replace_mark(subject, replacement),
                    [replace_mark(c, replacement) for c in cases])
    case SwitchCase(loc2, pat, body):
      return SwitchCase(loc2, pat, replace_mark(body, replacement))
    case RecFun(loc, name, typarams, params, returns, cases):
      return formula
    case Conditional(loc2, tyof, cond, thn, els):
      return Conditional(loc2, tyof, replace_mark(cond, replacement),
                         replace_mark(thn, replacement),
                         replace_mark(els, replacement))
    case Lambda(loc2, tyof, vars, body):
      return Lambda(loc2, tyof, vars, replace_mark(body, replacement))
    case Generic(loc2, tyof, typarams, body):
      return Generic(loc2, tyof, typarams, replace_mark(body, replacement))
    case TAnnote(loc2, tyof, subject, typ):
      return TAnnote(loc2, tyof, replace_mark(subject, replacement))
    case TLet(loc2, tyof, var, rhs, body):
      return TLet(loc2, tyof, var, replace_mark(rhs, replacement),
                  replace_mark(body, replacement))
    case Hole(loc2, tyof):
      return formula
    case ArrayGet(loc2, tyof, arr, ind):
      return ArrayGet(loc2, tyof, replace_mark(arr, replacement), replace_mark(ind, replacement))
    case _:
      error(formula.location, 'in replace_mark function, unhandled ' + str(formula))

def remove_mark(formula):
  num_marks = count_marks(formula)
  if num_marks == 0:
      return formula
  else:
        try:
            find_mark(formula)
            loc = formula.location if hasattr(formula, 'location') else None
            error(loc, 'in remove_mark, find_mark failed on formula:\n\t' + str(formula))
        except MarkException as ex:
            return replace_mark(formula, ex.subject)
      
def extract_and(frm):
    match frm:
      case And(loc, tyof, args):
        return args
      case _:
       return [frm]

def extract_or(frm):
    match frm:
      case Or(loc, tyof, args):
        return args
      case _:
       return [frm]

def uniquify_deduce(ast):
  env = {}
  env['≠'] = ['≠']
  env['='] = ['=']
  # Using a space in the name to not collide with deduce identifiers
  env['no overload'] = {}
  for stmt in ast:
    stmt.uniquify(env)

def make_switch_for(meta, defs, subject, cases):
  new_cases = [SwitchProofCase(c.location, c.pattern, c.assumptions,
                               ApplyDefsGoal(meta, [Var(meta, None, t, []) for t in defs],
                                             c.body)) \
               for c in cases]
  return SwitchProof(meta, subject, new_cases)

def explicit_term_inst(term):
  match term:
    case TermInst(loc2, tyof, subject, tyargs, inferred):
      return TermInst(loc2, tyof, subject, tyargs, False)
    case Switch(loc2, tyof, subject, cases):
      return Switch(loc2, tyof, explicit_term_inst(subject),
                    [explicit_term_inst(c) for c in cases])
    case SwitchCase(loc2, pat, body):
      return SwitchCase(loc2, pat, explicit_term_inst(body))
    case Lambda(loc2, tyof, vars, body):
      return Lambda(loc2, tyof, vars, explicit_term_inst(body))
    case Mark(loc2, tyof, subject):
      return Mark(loc2, tyof, explicit_term_inst(subject))
    case Conditional(loc2, tyof, cond, thn, els):
      return Conditional(loc2, tyof, explicit_term_inst(cond),
                         explicit_term_inst(thn),
                         explicit_term_inst(els))
    case Generic(loc2, tyof, typarams, body):
      return Generic(loc2, tyof, typarams, explicit_term_inst(body))
    case TLet(loc2, tyof, var, rhs, body):
      return TLet(loc2, tyof, var, rhs,
                  explicit_term_inst(body))
    case _:
      return term
