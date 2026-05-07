from dataclasses import dataclass, field
from lark.tree import Meta
from typing import Tuple, List, Optional, Set, Self
from error import error, warning, static_error, match_failed, MatchFailed
from flags import *
from pathlib import Path
from edit_distance import edit_distance
from math import ceil
import os

infix_precedence = {'+': 6, '-': 6, '∸': 6, '⊝': 6, '*': 7, '/': 7, '%': 7,
                    '=': 1, '<': 1, '≤': 1, '≥': 1, '>': 1, 'and': 2, 'or': 3,
                    '≲': 1, '≈': 1,
                    '++': 6, '⨄': 6, '∈':1, '∪':6, '∩':6, '⊆': 1, '⇔': 2,
                    '∘': 7, '^' : 8}
prefix_precedence = {'-': 9, 'not': 4}
recursion_depth = 0

def name2str(s):
    if get_unique_names():
        return s
    else:
        return base_name(s)

# current_module is used during uniquify and collect_exports
current_module = 'none'

def get_current_module():
    global current_module
    return current_module

def set_current_module(name):
    global current_module
    current_module = name

# Back-pointers from a predicate's uniquified name to its Predicate AST
# node. Populated during Predicate.uniquify and read by the proof checker
# when desugaring `rule induction`. Persisted across check_deduce
# invocations because uniquify happens once per file.
_predicate_decls_by_unique_name = {}

def get_predicate_decl(unique_name):
  return _predicate_decls_by_unique_name.get(unique_name)

############ AST Base Classes ###########

@dataclass
class AST:
  location: Meta

  def copy(self) -> Self:
    error(self.location, 'copy not implemented for \n\t' + repr(self))
    return self

@dataclass
class Type(AST):

  def free_vars(self) -> Set[str]:
    error(self.location, 'free_vars not implemented')
    return set()

  def substitute(self, sub) -> Self:
    error(self.location, 'substitute not implemented')

  def uniquify(self, env) -> Self:
    error(self.location, 'uniquify not implemented')

  def reduce(self, env) -> Self:
    error(self.location, 'reduce not implemented')


@dataclass
class Term(AST):
  typeof: Optional[Type]

  def copy(self) -> Self:
    error(self.location, 'copy not implemented')
    return self

  def uniquify(self, env) -> Self:
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
    
  def key(self) -> str:
      return str(self)
    
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

def type_names(loc, names: List[str]):
  index = 0
  result = []
  for n in reversed(names):
    result.insert(0, ResolvedVar(loc, None, n))
    index += 1
  return result


def type_match(loc, tyvars, param_ty, arg_ty, matching):
  if get_verbose():
    print("type_match(" + str(param_ty) + "," + str(arg_ty) + ")")
    print("\tin  " + ', '.join([str(x) for x in tyvars]))
    print("\twith " + str(matching))
  # `param_ty` may be a tyvar reference encoded as either an
  # OverloadedVar (if it came straight from uniquify) or a ResolvedVar
  # (if a prior narrowing has already occurred). `get_name()` gives us
  # the canonical identifier in both cases.
  param_is_var = isinstance(param_ty, VarRef)
  arg_is_var = isinstance(arg_ty, VarRef)
  if param_is_var and param_ty in tyvars:
    tyvar_name = param_ty.get_name()
    if tyvar_name in matching.keys():
      if matching[tyvar_name] == arg_ty:
        return
      else:
        type_match(loc, tyvars, matching[tyvar_name], arg_ty, matching)
    else:
      if get_verbose():
        print('matching ' + tyvar_name + ' := ' + str(arg_ty))
      matching[tyvar_name] = arg_ty
    return
  if param_is_var and arg_is_var \
     and param_ty.get_name() == arg_ty.get_name():
    return
  match (param_ty, arg_ty):
    case (FunctionType(l1, tv1, pts1, rt1), FunctionType(l2, tv2, pts2, rt2)) \
      if len(tv1) == len(tv2) and len(pts1) == len(pts2):
      for (pt1, pt2) in zip(pts1, pts2):
        type_match(loc, tyvars, pt1, pt2, matching)
      type_match(loc, tyvars, rt1, rt2, matching)
    case (TypeInst(l1, n1, args1), TypeInst(l2, n2, args2)):
      if n1 != n2 or len(args1) != len(args2):
        match_failed(loc, str(arg_ty) + " does not match " + str(param_ty))
      for (arg1, arg2) in zip(args1, args2):
        type_match(loc, tyvars, arg1, arg2, matching)
    # How to handle GenericUnknownInst?
    case (TypeInst(l1, n1, args1), GenericUnknownInst(l2, n2)):
      if n1 != n2:
        match_failed(loc, str(arg_ty) + " does not match " + str(param_ty))
    case _:
      if param_ty != arg_ty:
        match_failed(loc, str(arg_ty) + " does not match " + str(param_ty))


def is_associative(loc, opname, typ, env):
  #print('is_associative? ' + str(opname) + ' for ' + str(typ))
  for (typarams, ty) in env.get_assoc_types(opname):
    type_params = type_names(loc, typarams)
    matching = {}
    try:
      #print('type_params = ' + ', '.join([str(t) for t in type_params]))
      #print(str(ty) + ' =? ' + str(typ))
      type_match(loc, type_params, ty, typ, matching)
      #print('\tyes')
      return True
    except Exception as e:
      pass
  #print('\tno')
  return False


def rator_name(rator):
  if isinstance(rator, VarRef):
    return rator.get_name()
  match rator:
    case RecFun(loc, name, typarams, params, returns, cases):
      return name
    case GenRecFun(loc, name, typarams, params, returns, measure, measure_ty, body, terminates):
      return name
    case Lambda(loc, ty, vars, body):
      return 'no_name'
    case TermInst(loc3, tyof, arg2, tyargs):
      return rator_name(arg2)
    case Generic(loc2, tyof, typarams, body):
      return 'no_name'
    case _:
      return 'no_name'


def flatten_assoc(op_name, trm):
  match trm:
    case Call(loc2, tyof, rator, args) if rator_name(rator) == op_name:
      return sum([flatten_assoc(op_name, arg) for arg in args], [])
    case _:
      return [trm]


def flatten_assoc_list(op_name, args):
  return sum([flatten_assoc(op_name, arg) for arg in args], [])


@dataclass(kw_only=True)
class Declaration(AST):
  visibility:str = 'public'

  def key(self):
      if is_operator_name(self.name):
          return 'operator ' + name2str(self.name)
      else:
          return name2str(self.name)

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
    return self

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
    return self

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
    return self

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
    return OverloadType(self.location,
                        [(x, t.uniquify(env)) for (x,t) in self.types])

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
    new_param_types = [p.uniquify(body_env) for p in self.param_types]
    new_return_type = self.return_type.uniquify(body_env)
    return FunctionType(self.location, new_type_params,
                        new_param_types, new_return_type)

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
    return ArrayType(self.location, self.elt_type.uniquify(env))

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
    return TypeInst(self.location,
                    self.typ.uniquify(env),
                    [ty.uniquify(env) for ty in self.arg_types])

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
    return GenericUnknownInst(self.location, self.typ.uniquify(env))

def get_type_name(ty):
  if isinstance(ty, VarRef):
    return ty
  match ty:
    case TypeInst(l1, ty, type_args):
      return get_type_name(ty)
    case _:
      raise Exception('unhandled case in get_type_name: ' + repr(ty))
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
    return self

  def bindings(self):
    return []

  def with_bindings(self, new_bindings):
    return self

  def reduce(self, env):
      return self

@dataclass
class PatternCons(Pattern):
  constructor : Term         # typically a Var
  parameters : List[str]

  def bindings(self):
    return self.parameters

  def with_bindings(self, params):
    return PatternCons(self.location, self.constructor, params)

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
    return PatternCons(self.location, self.constructor.uniquify(env),
                       [p for p in self.parameters])

  def reduce(self, env):
    return self

@dataclass
class PatternTerm(Pattern):
  term: Term
  parameters: list[str]

  def bindings(self):
    return self.parameters

  def with_bindings(self, params):
    return PatternTerm(self.location, self.term, params)

  def copy(self):
    return PatternTerm(self.location, self.term.copy(), [x for x in self.parameters])

  def __str__(self):
    return str(self.term)

  def uniquify(self, env):
    return PatternTerm(self.location, self.term.uniquify(env),
                       [p for p in self.parameters])

  def reduce(self, env):
    return self
    
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
      ren = {x: ResolvedVar(self.location, None, y) \
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
    return Generic(self.location, self.typeof, new_type_params,
                   self.body.uniquify(body_env))


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
     if get_reduce_all():   # Does this work? Need to test!
         match cond:
           case Bool(l1, tyof, True):
             return self.thn.reduce(env)
           case Bool(l1, tyof, False):
             return self.els.reduce(env)
           case _:
             return Conditional(self.location, self.typeof, cond, self.thn, self.els)
     else:
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
    return Conditional(self.location, self.typeof,
                       self.cond.uniquify(env),
                       self.thn.uniquify(env),
                       self.els.uniquify(env))


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
    return TAnnote(self.location, self.typeof,
                   self.subject.uniquify(env),
                   self.typ.uniquify(env))

  def __eq__(self, other):
    return self.subject == other
    
  
@dataclass
class VarRef(Term):
  # Abstract base for variable references. Concrete subclasses are
  # `Var` (post-parse, holds a source identifier) and `OverloadedVar`
  # (post-uniquify, holds uniquified candidate names). Code that wants
  # to operate on either variant should `isinstance(node, VarRef)` and
  # call `get_name()` rather than reach for a `name` field — the two
  # subclasses store names differently on purpose.
  def get_name(self) -> str:
    error(self.location, 'get_name not implemented on VarRef base')

  def free_vars(self):
    return {self.get_name()}

  def operator_str(self):
    return name2str(self.get_name())


@dataclass
class Var(VarRef):
  # A source-level variable reference, before name resolution.
  # `name` is the identifier as written by the user. After uniquify
  # this node is replaced by `OverloadedVar`, which carries the
  # uniquified candidate names and is what the rest of the pipeline
  # operates on.
  name: str

  def get_name(self):
    return self.name

  def copy(self):
    return Var(self.location, self.typeof, self.name)

  def __eq__(self, other):
      if isinstance(other, OverloadedVar):
        # Pre- and post-uniquify references are not interchangeable.
        return False
      elif isinstance(other, RecFun):
        result = self.name == other.name
      elif isinstance(other, GenRecFun):
        result = self.name == other.name
      elif isinstance(other, TermInst):
        result = self == other.subject
      elif not isinstance(other, Var):
        result = False
      else:
        result = self.name == other.name
      return result

  def __str__(self):
      if base_name(self.name) == 'empty' and not get_unique_names() and not get_verbose():
          return '[]'
      elif get_unique_names():
        return name2str(self.name) + '{}'
      elif is_var_operator(self):
        return 'operator ' + name2str(self.name)
      else:
        return name2str(self.name)

  def reduce(self, env):
      # Pre-uniquify Vars don't appear in the runtime environment, so
      # they reduce to themselves. The post-uniquify form is
      # `OverloadedVar`, which has its own reduce.
      return self

  def substitute(self, sub):
      if self.name in sub:
          trm = sub[self.name]
          if not isinstance(trm, RecFun) and not isinstance(trm, GenRecFun):
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

      if self.name == "suc" or self.name == "zero" or self.name == "lit":
        import_advice = "\n\tAdd `import Nat` to use natural numbers."
      elif self.name == "empty" or self.name == "node":
        import_advice = "\n\tAdd `import List` to use lists."
      elif self.name == "bzero" or self.name == "dub_inc" or self.name == "inc_dub" or self.name == "fromNat":
        import_advice = "\n\tAdd `import UInt` to use unsigned integers."
      if import_advice != '':
          static_error(self.location, import_advice)

      close_matches = []
      for var in env.keys():
        if edit_distance(self.name, var) <= ceil(len(self.name) / 5):
          close_matches.append(var)
      if len(close_matches) > 0:
        mispell_advice = '\n\tdid you intend: ' + ', '.join(close_matches) + '\n'
      else:
        mispell_advice = ''
      static_error(self.location, 'undefined variable: ' + self.name \
                   + mispell_advice + '' + env_str)

    return OverloadedVar(self.location, self.typeof, env[self.name])


@dataclass
class OverloadedVar(VarRef):
  # A variable reference after uniquify. `resolved_names` is the
  # non-empty list of uniquified candidate names this reference could
  # resolve to. The canonical chosen name is `resolved_names[0]`;
  # overload resolution during type checking narrows the list to
  # length 1. There is *no* source-name field on this class — recover
  # it via `base_name(self.get_name())` when you need to display it.
  resolved_names: list[str]

  def __post_init__(self):
    if len(self.resolved_names) == 0:
      error(self.location,
            'OverloadedVar must have at least one resolved name')

  @property
  def name(self):
    # Derived, read-only. Always equal to the canonical chosen name.
    # Exposed so ``.name`` access works uniformly with `Var`, but
    # there is no `name` field that could drift out of sync with
    # `resolved_names`.
    return self.resolved_names[0]

  def get_name(self):
    return self.resolved_names[0]

  def copy(self):
    return OverloadedVar(self.location, self.typeof,
                       list(self.resolved_names))

  def __eq__(self, other):
    if isinstance(other, OverloadedVar):
      return self.resolved_names[0] == other.resolved_names[0]
    elif isinstance(other, ResolvedVar):
      # Symmetric with ResolvedVar.__eq__ (see comment there).
      return self.resolved_names[0] == other.name
    elif isinstance(other, RecFun):
      return self.resolved_names[0] == other.name
    elif isinstance(other, GenRecFun):
      return self.resolved_names[0] == other.name
    elif isinstance(other, TermInst):
      return self == other.subject
    elif isinstance(other, Var):
      # Pre- and post-uniquify references are not interchangeable.
      return False
    else:
      return False

  def __str__(self):
    chosen = self.resolved_names[0]
    if base_name(chosen) == 'empty' and not get_unique_names() and not get_verbose():
      return '[]'
    elif get_unique_names():
      return name2str(chosen) + '{' + ','.join(self.resolved_names) + '}'
    elif is_var_operator(self):
      return 'operator ' + name2str(chosen)
    else:
      return name2str(chosen)

  def reduce(self, env):
    if get_reduce_all() or (self in get_reduce_only()):
      chosen = self.resolved_names[0]
      if get_dont_reduce_opaque() and chosen in env.dict.keys():
        binding = env.dict[chosen]
        if binding.visibility == 'opaque' \
           and binding.module != env.get_current_module():
            return self

      res = env.get_value_of_term_var(self)
      if res:
        if get_verbose():
          print('\t var ' + chosen + ' ===> ' + str(res))
        if isinstance(res, Union):
          return self
        return res.reduce(env)
      else:
        return self
    else:
      return self

  def substitute(self, sub):
    chosen = self.resolved_names[0]
    if chosen in sub:
      trm = sub[chosen]
      if not isinstance(trm, RecFun) and not isinstance(trm, GenRecFun):
        add_reduced_def(chosen)
      return trm
    else:
      return self

  def uniquify(self, env):
    # Already uniquified — re-uniquify is a no-op (we'd hit this if
    # uniquify_deduce were ever called twice on the same AST).
    return self

  def resolve_to(self, chosen_name, ty=None):
    """Transition this OverloadedVar into a ResolvedVar bound to a
    single chosen name. Used by type-check overload resolution and
    by `check_constr_pattern` once the constructor for a pattern
    has been determined. The returned `ResolvedVar` is a different
    class — pattern matches and isinstance checks distinguish it
    from the still-overloaded form, which is the whole point of
    the split."""
    return ResolvedVar(self.location, ty if ty is not None else self.typeof,
                       chosen_name)


@dataclass
class ResolvedVar(VarRef):
  # A variable reference after overload resolution. `name` is the
  # single uniquified name this reference is bound to. There is no
  # candidate list — that's the OverloadedVar state. Once a Var has
  # become a ResolvedVar, no further name-narrowing is possible: the
  # only transitions are substitution / reduction, which produce a
  # different node entirely.
  name: str

  def get_name(self):
    return self.name

  def copy(self):
    return ResolvedVar(self.location, self.typeof, self.name)

  def __eq__(self, other):
    if isinstance(other, ResolvedVar):
      return self.name == other.name
    elif isinstance(other, OverloadedVar):
      # A resolved name matches an overloaded reference iff it's
      # the chosen candidate. Comparing across the boundary lets
      # post-typecheck code keep working with code that hasn't yet
      # narrowed (e.g. equality reduction in mixed sub-ASTs).
      return self.name == other.resolved_names[0]
    elif isinstance(other, RecFun):
      return self.name == other.name
    elif isinstance(other, GenRecFun):
      return self.name == other.name
    elif isinstance(other, TermInst):
      return self == other.subject
    elif isinstance(other, Var):
      # Pre- and post-uniquify references are not interchangeable.
      return False
    else:
      return False

  def __str__(self):
    if base_name(self.name) == 'empty' and not get_unique_names() and not get_verbose():
      return '[]'
    elif get_unique_names():
      return name2str(self.name) + '{' + self.name + '}'
    elif is_var_operator(self):
      return 'operator ' + name2str(self.name)
    else:
      return name2str(self.name)

  def reduce(self, env):
    if get_reduce_all() or (self in get_reduce_only()):
      if get_dont_reduce_opaque() and self.name in env.dict.keys():
        binding = env.dict[self.name]
        if binding.visibility == 'opaque' \
           and binding.module != env.get_current_module():
            return self

      res = env.get_value_of_term_var(self)
      if res:
        if get_verbose():
          print('\t var ' + self.name + ' ===> ' + str(res))
        if isinstance(res, Union):
          return self
        return res.reduce(env)
      else:
        return self
    else:
      return self

  def substitute(self, sub):
    if self.name in sub:
      trm = sub[self.name]
      if not isinstance(trm, RecFun) and not isinstance(trm, GenRecFun):
        add_reduced_def(self.name)
      return trm
    else:
      return self

  def uniquify(self, env):
    # Already uniquified.
    return self


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
    return self


@dataclass
class Lambda(Term):
  vars: List[Tuple[str,Type]]
  body: Term

  def copy(self):
    return Lambda(self.location, self.typeof,
                 self.vars,
                 self.body.copy())
  
  def __str__(self):
    if get_unique_names():
      params = self.vars
    else:
      params = [(base_name(x), t) for (x,t) in self.vars]
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
      # ResolvedVar so the substituted bodies compare equal to the
      # uniquified-name references already in `other.body`.
      ren = {x: ResolvedVar(self.location, t2, y) \
             for ((x,t1),(y,t2)) in zip(self.vars, other.vars) }
      new_body = self.body.substitute(ren)
      return new_body == other.body

  def reduce(self, env):
    if get_eval_all():
      ret = Lambda(self.location, self.typeof, self.vars, self.body)
      ret.env = self.env if hasattr(self, 'env') else env
      return ret
    else:
      return Lambda(self.location, self.typeof, self.vars, self.body.reduce(env))

  def substitute(self, sub):
      n = len(self.vars)
      new_vars = [(x, t.substitute(sub) if t else None) for (x,t) in self.vars]
      return Lambda(self.location, self.typeof, new_vars,
                    self.body.substitute(sub))

  def uniquify(self, env):
    body_env = {x:y for (x,y) in env.items()}
    new_var_types = [t.uniquify(env) if t else None for (x,t) in self.vars]
    new_vars = [(generate_name(x), nt) \
                for ((x,_), nt) in zip(self.vars, new_var_types)]
    for ((old,_), (new,_)) in zip(self.vars, new_vars):
      overwrite(body_env, old, new, self.location)
    new_body = self.body.uniquify(body_env)
    return Lambda(self.location, self.typeof, new_vars, new_body)

def is_match(pattern, arg, subst):
    ret = False
    match pattern:
      case PatternBool(loc1, value):
        match arg:
          case Bool(loc2, tyof, arg_value):
            ret = arg_value == value
          case _ if isinstance(arg, VarRef):
            ret = False
          case _:
            error(loc1, 'Boolean pattern expected boolean argument, not\n\t' \
                  + str(arg))
      case PatternCons(loc1, constr, []):
        if isinstance(arg, VarRef):
          ret = constr == arg
        else:
          match arg:
            case TermInst(loc3, tyof, arg2, tyargs):
              ret = is_match(pattern, arg2, subst)
            case _:
              ret = False

      case PatternCons(loc1, constr, params):
        match arg:
          case Call(loc2, cty, rator, args):
            # `rator` may be a (possibly term-instantiated) VarRef.
            inner = rator
            if isinstance(inner, TermInst):
              inner = inner.subject
            if isinstance(inner, VarRef) \
               and constr == inner and len(params) == len(args):
              for (k, v) in zip(params, args):
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

dont_reduce_opaque = False

def get_dont_reduce_opaque():
  global dont_reduce_opaque
  return dont_reduce_opaque

def set_dont_reduce_opaque(b):
  global dont_reduce_opaque
  dont_reduce_opaque = b

eval_all = False

def get_eval_all():
  # return False
  global eval_all
  return eval_all

def set_eval_all(b):
  global eval_all
  eval_all = b

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
        return name2str(name)
    
def is_operator_name(name):
    return base_name(name) in infix_precedence.keys() \
        or base_name(name) in prefix_precedence.keys()
    
    
def is_var_operator(trm):
  # `Var.__str__` / `OverloadedVar.__str__` use this without recursing
  # through `is_operator`, which would loop on TermInst(Var(...)).
  return isinstance(trm, VarRef) and is_operator_name(trm.get_name())

def is_operator(trm):
  if isinstance(trm, VarRef):
    return is_operator_name(trm.get_name())
  match trm:
    case RecFun(loc, name, typarams, params, returns, cases):
      return is_operator_name(name)
    case GenRecFun(loc, name, typarams, params, returns, measure, measure_ty, body, terminates):
      return is_operator_name(name)
    case TermInst(loc, tyof, subject, tyargs, inferred):
      return is_operator(subject)
    case _:
      return False

def operator_name(trm):
  if isinstance(trm, VarRef):
    nm = trm.get_name()
    return nm if get_unique_names() else base_name(nm)
  match trm:
    case RecFun(loc, name, typarams, params, returns, cases):
      return base_name(name)
    case GenRecFun(loc, name, typarams, params, returns, measure, measure_ty, body, terminates):
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
  fast_call = False
  if get_eval_all() and len(args) == 2  and isNat(args[0]) and isNat(args[1]):
    op = base_name(name)
    x = natToInt(args[0])
    y = natToInt(args[1])
    # This is a really hack-y fix
    sname = getSuc(args[0])
    sname = sname if sname else getSuc(args[1])
    zname = getZero(args[0])
    ty = return_type
    ret = None
    if op == '+':
      ret = intToNat(loc, x + y, sname=sname, zname=zname, ty=ty)
    elif op == '-':
      ret = intToNat(loc, x - y, sname=sname, zname=zname, ty=ty)
    elif op == '/':
      ret = intToNat(loc, x // y, sname=sname, zname=zname, ty=ty)
    elif op == '*':
      ret = intToNat(loc, x * y, sname=sname, zname=zname, ty=ty)
    elif op == '^':
      ret = intToNat(loc, x ** y, sname=sname, zname=zname, ty=ty)
    if ret: 
      if get_verbose():
        print(f"Doing fast arithmetic on call {x} {op} {y}.")
      ret.typeof = return_type
      fast_call = True

  if not fast_call:    
    body_env = env
    if False and len(params) != len(args):
      error(loc, 'in function call ' + name2str(name) \
            + '(' + ', '.join([str(a) for a in args]) + ')\n' \
            + '\tnumber of parameters: ' + str(len(params)) + '\n' \
            + '\tdoes not match number of arguments')
    for (x,ty) in zip(type_params, type_args):
      subst[x] = ty
    for (k,v) in zip(params, args):
      subst[k] = v

    for k, v in subst.items():
      if isinstance(v, TermInst):
        v.inferred = False

    if get_reduce_all() and get_eval_all():
      if get_verbose():
        print("Fast evaluate", body)
      for k, v in subst.items():
        if k in type_params:
          env = env.define_type(loc, k, v)
        else:
          env = env.define_term_var(loc, k, v.typeof, v)

      ret = body.reduce(env)
    else:
      new_fun_case_body = body.substitute(subst)
      old_defs = get_reduce_only()
      reduce_defs = [x for x in old_defs]
      if ResolvedVar(loc, None, name) in reduce_defs:
        reduce_defs.remove(ResolvedVar(loc, None, name))
      else:
        pass
      reduce_defs += [ResolvedVar(loc, None, x) for x in params]
      # Revisit the following -Jeremy  
      # reduce_defs += [ResolvedVar(loc, None, x) \
      #                 for x in fun_case.pattern.parameters \
      #                 + fun_case.parameters]
      set_reduce_only(reduce_defs)

      # Reduce the body of the function
      ret = new_fun_case_body.reduce(body_env)

      set_reduce_only(old_defs)

  add_reduced_def(name)
  if get_verbose():
    print('\tcall to ' + name + ' returns ' + str(ret))

  if env.get_tracing(name):
    global recursion_depth
    print('<' * recursion_depth, str(ret))
    recursion_depth -= 1

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
    elif isDeduceInt(self):
      return deduceIntToInt(self)
    elif isLitNat(self): # and not get_verbose():
      return 'ℕ' + str(natToInt(self))
    # elif isNat(self): # and not get_verbose():
    #   return '`' + str(natToInt(self))
    elif isLitUInt(self): # and not get_verbose():
      return str(uintToInt(self))
    elif isUInt(self) and not get_verbose():
      return str(uintToInt(self))
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
    fun = self.rator.reduce(env)
    if get_eval_all():
      is_assoc = False
    else:
      is_assoc = is_associative(self.location, rator_name(self.rator),
                                self.typeof, env)
    if is_assoc:
      flat_args = flatten_assoc_list(rator_name(self.rator), self.args)
    else:
      flat_args = self.args
    args = [arg.reduce(env) for arg in flat_args]
    ret = None
    match fun:
      case Var(loc, ty, '=') | OverloadedVar(loc, ty, ['=']) | ResolvedVar(loc, ty, '='):
        if args[0] == args[1]:
          ret = Bool(loc, BoolType(loc), True)
        elif constructor_conflict(args[0], args[1], env):
          ret = Bool(loc, BoolType(loc), False)
        else:
          ret = Call(self.location, self.typeof, fun, args)
      case (OverloadedVar() | ResolvedVar()) if is_assoc:
        ret = Call(self.location, self.typeof, fun,
                   flatten_assoc_list(rator_name(self.rator), args))
        if hasattr(self, 'type_args'):
          ret.type_args = self.type_args
            
      case Lambda(loc, ty, vars, body):
        if hasattr(fun, 'env'):
          ret = self.do_call(loc, vars, body, args, fun.env)
        else:
          ret = self.do_call(loc, vars, body, args, env)
    
      case GenRecFun(loc, name, [], params, returns, measure, measure_ty,
                   body, terminates):
        if env.get_tracing(name):
          global recursion_depth
          recursion_depth += 1
          print('>' * recursion_depth, str(base_name(name)) + '(' + str(' '.join([str(x) for x in args]) + ')'))

        subst = {k: v for ((k,t),v) in zip(params, args)}
        ret = do_function_call(loc, name, [], [], [x for (x,t) in params], args,
                               body, subst, env, None)
    
      case TermInst(loc, tyof,
                    GenRecFun(loc2, name, typarams, params, returns,
                              measure, measure_ty, body, terminates),
                    type_args):
        subst = {k: v for ((k,t),v) in zip(params, args)}
        ret = do_function_call(loc, name, typarams, type_args, [x for (x,t) in params], args,
                               body, subst, env, None)
    
      case RecFun(loc, name, [], params, returns, cases):
        ret = self.do_recursive_call(loc, name, fun, [], [], params, args,
                                     returns, cases, is_assoc, env)
      case TermInst(loc, tyof,
                    RecFun(loc2, name, typarams, params, returns, cases),
                    type_args):
        ret = self.do_recursive_call(loc, name, fun, typarams, type_args,
                                     params, args, returns, cases, is_assoc,
                                     env)
      case Generic(loc2, tyof, typarams, body):
        error(self.location, 'in reduction, call to generic\n\t' + str(self))
      case _:
        # if get_verbose():
        #   print('not reducing call because neutral function: ' + str(fun))
        ret = Call(self.location, self.typeof, fun, args)
        if hasattr(self, 'type_args'):
          ret.type_args = self.type_args

    if not get_eval_all():
        ret = auto_rewrites(ret, env)
    
    # if get_verbose():
    #   print('call ' + str(self) + '\n\treturns ' + str(ret))
    #   print('}}}}}}}}}}}}}}}}}}}}}}}}}}')
    return ret

  def do_call(self, loc, vars, body, args, env):
    # because of associativity, args can be longer
    # if len(vars) != len(args):
    #     print("params: " + ', '.join([str(x) for (x,t) in vars]))
    #     print("args: " + ', '.join([str(p) for p in args]))
    #     error(loc, "param arg length mismatch: " + str(self))
    subst = {k: v for ((k,t),v) in zip(vars, args)}
    return do_function_call(loc, "anonymous", [], [], [], [], body, subst, env, None)

  def do_recursive_call(self, loc, name, fun, type_params, type_args, params, args,
                        returns, cases, is_assoc, env):
    if get_verbose():
      print('call to recursive function: ' + str(fun))
      print('\targs: ' + ', '.join([str(a) for a in args]))

    if env.get_tracing(name):
      global recursion_depth
      recursion_depth += 1
      print('>' * recursion_depth, str(base_name(name)) + '(' + str(' '.join([str(x) for x in args]) + ')'))

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
      # if get_verbose():
      #   print('worklist: ' + ', '.join([str(a) for a in worklist]))
      #   print('new_args: ' + ', '.join([str(a) for a in new_args]))
      first_arg = worklist[0]; worklist = worklist[1:]
      did_call = False
      for fun_case in cases:
          subst = {}
          if is_match(fun_case.pattern, first_arg, subst):
              rest_args = worklist[:len(fun_case.parameters)]
              result = do_function_call(loc, name, type_params, type_args,
                                        fun_case.parameters, rest_args,
                                        fun_case.body, subst, env, returns)
              # if get_verbose():
              #   print('call result: ' + str(result))
              worklist = [result] + worklist[len(fun_case.parameters):]
              did_call = True
              rator_var = ResolvedVar(loc, None, name)
              if rator_var in reduce_only:
                reduce_only.remove(rator_var)
              set_reduce_only(reduce_only)
              break
      if not did_call:
        new_args.append(first_arg)
      if did_call and not get_reduce_all():
        break
      # if get_verbose():
      #   print('-----------------------------')
    set_reduce_only(old_reduce_only)
    # if get_verbose():
    #   print('end associative operator ' + str(fun))
    #   print('>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>')


    new_args += worklist
    flat_results = flatten_assoc_list(rator_name(self.rator), new_args)
    # if get_verbose():
    #   print('}}}}}}}}}}}}}}}}}}}}}}}}}}')
    if len(flat_results) == 1:
      return explicit_term_inst(flat_results[0])
    else:
      return Call(self.location, self.typeof,
                  fun,
                  flat_results)
  
  def substitute(self, sub):
    ret = Call(self.location, self.typeof, self.rator.substitute(sub),
                [arg.substitute(sub) for arg in self.args])
    if hasattr(self, 'type_args'):
      ret.type_args = self.type_args
    return ret

  def uniquify(self, env):
    new_rator = self.rator.uniquify(env)
    new_args = [a.uniquify(env) for a in self.args]
    ret = Call(self.location, self.typeof, new_rator, new_args)
    if hasattr(self, 'type_args'):
      ret.type_args = self.type_args
    return ret


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
      return SwitchCase(self.location,
                        self.pattern.reduce(env),
                        self.body.reduce(env))
    
  def substitute(self, sub):
      new_sub = {k: v for (k,v) in sub.items()}
      return SwitchCase(self.location,
                        self.pattern,
                        self.body.substitute(new_sub))

  def uniquify(self, env):
    new_pat = self.pattern.uniquify(env)
    body_env = {x:y for (x,y) in env.items()}
    match new_pat:
      case PatternBool(loc, value):
        pass
      case PatternCons(loc, constr, params):
        new_params = [generate_name(x) for x in params]
        for (old,new) in zip(params, new_params):
          overwrite(body_env, old, new, self.location)
        new_pat = new_pat.with_bindings(new_params)
    new_body = self.body.uniquify(body_env)
    return SwitchCase(self.location, new_pat, new_body)

  def __eq__(self, other):
    if not isinstance(other, SwitchCase):
      return False
    match self.pattern, other.pattern:
      case PatternBool(loc1, value1), PatternBool(loc2, value2):
        return value1 == value2 and self.body == other.body
      case PatternCons(loc1, constr1, params1), PatternCons(loc2, constr2, params2):
        # Use ResolvedVar in the rename so substituted-in references
        # compare equal to the (already uniquified) ResolvedVars in
        # `other.body`. Picking Var here would break post-uniquify
        # equality across the two bodies.
        alpha_rename = {x: ResolvedVar(self.location, None, y) \
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
            if get_eval_all():
              for k, v in subst.items():
                env = env.define_term_var(self.location, k, v.typeof, v)
              ret = c.body.reduce(env)
            else:
              new_body = c.body.substitute(subst)
              new_env = env
              old_defs = get_reduce_only()
              set_reduce_only(old_defs + [ResolvedVar(self.location, None, x) \
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
    return Switch(self.location, self.typeof,
                  self.subject.uniquify(env),
                  [c.uniquify(env) for c in self.cases])

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
    type_args_red = [t.reduce(env) for t in self.type_args]
    match subject_red:
      case Generic(loc2, tyof, typarams, body):
        # sub = {x:t for (x,t) in zip(typarams, self.type_args)}
        sub = {x:t for (x,t) in zip(typarams, type_args_red)}
        return body.substitute(sub)
      case _:
        # return TermInst(self.location, self.typeof, subject_red,
        #                self.type_args, self.inferred)
        return TermInst(self.location, self.typeof, subject_red,
                        type_args_red, self.inferred)
    
  def substitute(self, sub):
    return TermInst(self.location, self.typeof,
                    self.subject.substitute(sub),
                    [ty.substitute(sub) for ty in self.type_args],
                    self.inferred)

  def uniquify(self, env):
    return TermInst(self.location, self.typeof,
                    self.subject.uniquify(env),
                    [ty.uniquify(env) for ty in self.type_args],
                    self.inferred)

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
    return Array(self.location, self.typeof,
                 [elt.uniquify(env) for elt in self.elements])

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
    return MakeArray(self.location, self.typeof, self.subject.uniquify(env))

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
        index = None
        if isNat(position_red):
          index = natToInt(position_red)
        elif isUInt(position_red):
          index = uintToInt(position_red)
        else:
            error(self.location, "array access expected number index, not " + str(position_red))
        if not (index is None):
          if 0 <= index and index < len(elements):
            return elements[index].reduce(env)
          # Don't signal an error for out-of-bounds! -Jeremy
    return ArrayGet(self.location, self.typeof, subject_red, position_red)
    
  def substitute(self, sub):
    return ArrayGet(self.location, self.typeof,
                    self.subject.substitute(sub),
                    self.position.substitute(sub))

  def uniquify(self, env):
    return ArrayGet(self.location, self.typeof,
                    self.subject.uniquify(env),
                    self.position.uniquify(env))

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

  def reduceLets(self, env):
    new_body = self.body.substitute({self.var: self.rhs})
    if isinstance(new_body, TLet):
      return new_body.reduceLets(env)
    else:
      return new_body

  def copy(self):
    return TLet(self.location, self.typeof, self.var,
                self.rhs.copy(), self.body.copy())
  
  def uniquify(self, env):
    new_rhs = self.rhs.uniquify(env)
    body_env = {x:y for (x,y) in env.items()}
    new_var = generate_name(self.var)
    overwrite(body_env, self.var, new_var, self.location)
    new_body = self.body.uniquify(body_env)
    return TLet(self.location, self.typeof, new_var, new_rhs, new_body)

  def substitute(self, sub):
    new_rhs = self.rhs.substitute(sub)
    new_body = self.body.substitute(sub)
    return TLet(self.location, self.typeof, self.var, new_rhs, new_body)

@dataclass
class Hole(Term):
  
  def __str__(self):
      return '?'

  def uniquify(self, env):
    return self

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
    return self

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
    return Mark(self.location, self.typeof, self.subject.uniquify(env))

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
    return self

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

def is_true(b):
  match b:
    case Bool(loc, ty, val):
        return val
    case _:
        return False

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
            iff = Call(self.location, None, ResolvedVar(self.location, None, '⇔'),
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
    return And(self.location, self.typeof,
               [a.uniquify(env) for a in self.args])

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
    return Or(self.location, self.typeof,
              [a.uniquify(env) for a in self.args])

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
    return IfThen(self.location, self.typeof,
                  self.premise.uniquify(env),
                  self.conclusion.uniquify(env))

@dataclass
class All(Formula):
  var: Tuple[str,Type]
  # Position (s, e), where 
  #  s : The variable's index in the list, starting from the last var
  #  e : The number of vars in the block
  pos: Tuple[int, int]
  body: Formula

  def copy(self):
    x, t = self.var
    return All(self.location, self.typeof, (x, t.copy()), self.pos, self.body.copy())
  
  def __str__(self):
    v, t = self.var
    v = name2str(v)

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
    sub = { y: ResolvedVar(self.location, None, x) }
    result = self.body == other.body.substitute(sub)
    return result

  def uniquify(self, env):
    body_env = {x:y for (x,y) in env.items()}
    (x, ty) = self.var
    new_t = ty.uniquify(body_env)
    new_x = generate_name(x)
    overwrite(body_env, x, new_x, self.location)
    new_body = self.body.uniquify(body_env)
    return All(self.location, self.typeof, (new_x, new_t),
               self.pos, new_body)

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
    new_body = self.body.reduce(env)
    match new_body:
      case Bool(loc2, tyof, True):
        return new_body
      case Bool(loc2, tyof, False):
        return new_body
      case _:
        return Some(self.location,
                    self.typeof,
                    [(x, ty.reduce(env)) for (x,ty) in self.vars],
                    new_body)
  
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
    for (x, ty) in self.vars:
      new_t = ty.uniquify(body_env)
      new_x = generate_name(x)
      new_vars.append((new_x, new_t))
      overwrite(body_env, x, new_x, self.location)
    new_body = self.body.uniquify(body_env)
    return Some(self.location, self.typeof, new_vars, new_body)

  def __eq__(self, other):
    if not isinstance(other, Some):
      return False
    if all([tx == ty for ((x,tx),(y,ty))in zip(self.vars, other.vars)]):
      sub = {y: ResolvedVar(self.location, None, x) \
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
      hits = find_private_lemma_definers(self.name)
      if hits:
        def fmt_hit(h):
          module, filename, line = h
          if filename is not None and line is not None:
            return "module " + module + " (" + filename + ":" + str(line) + ")"
          return "module " + module
        where = ', '.join(fmt_hit(h) for h in hits)
        msg = ("'" + self.name + "' is declared as a `lemma` in "
               + where + "; lemmas are module-private and not accessible"
               + " from other modules. To make it accessible here, change"
               + " `lemma` to `theorem` there.")
        error(self.location, msg)
      env_str = ('\n' + ', '.join(env.keys())) if get_verbose() else ''
      error(self.location, "undefined proof variable " + self.name + env_str)
    if not isinstance(env[self.name], list):
      error(self.location, "proof variable not bound to list " + self.name)
    return PVar(self.location, env[self.name][0])
    
@dataclass
class PLet(Proof):
  label: str
  proved: Formula
  because: Proof
  body: Proof

  def copy(self):
      return PLet(self.location, self.label, self.proved.copy(), self.because.copy(), self.body.copy())
  
  def pretty_print(self, indent):
      return indent*' ' + 'have ' + base_name(self.label) + ': ' + str(self.proved) + ' by {\n' \
          + self.because.pretty_print(indent+2) + '\n' \
          + indent*' ' + '}\n' \
          + maybe_pretty_print(self.body, indent)
  
  def __str__(self):
      return 'have ' + base_name(self.label) + ': ' + str(self.proved) \
        + ' by ' + str(self.because) + (' ' + str(self.body) if self.body else '')

  def uniquify(self, env):
    new_proved = self.proved.uniquify(env)
    new_because = self.because.uniquify(env)
    body_env = {x:y for (x,y) in env.items()}
    new_label = generate_name(self.label)
    overwrite(body_env, self.label, new_label, self.location)
    new_body = self.body.uniquify(body_env)
    return PLet(self.location, new_label, new_proved, new_because, new_body)

@dataclass
class PTLetNew(Proof):
  var: str
  rhs : Term
  body: Proof

  def copy(self):
      return PTLetNew(self.location, self.var, self.rhs.copy(), self.body.copy())
  
  def pretty_print(self, indent):
      return indent*' ' + 'define ' + base_name(self.var) + ' = ' + str(self.rhs) + '\n' \
          + self.body.pretty_print(indent)
  
  def __str__(self):
      return 'define ' + base_name(self.var) + ' = ' + str(self.rhs) + '\n' \
         + str(self.body)

  def uniquify(self, env):
    new_rhs = self.rhs.uniquify(env)
    body_env = {x:y for (x,y) in env.items()}
    new_var = generate_name(self.var)
    overwrite(body_env, self.var, new_var, self.location)
    new_body = self.body.uniquify(body_env)
    return PTLetNew(self.location, new_var, new_rhs, new_body)


@dataclass
class PRecall(Proof):
  facts: List[Formula]

  def copy(self):
      return PRecall(self.location, [fact.copy() for fact in self.facts])
  
  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
      return 'recall ' + ', '.join([str(f) for f in self.facts])

  def uniquify(self, env):
    return PRecall(self.location, [f.uniquify(env) for f in self.facts])


@dataclass
class PAnnot(Proof):
  claim: Formula
  body: Proof

  def copy(self):
      return PAnnot(self.location, self.claim.copy(), self.body.copy())
  
  def pretty_print(self, indent):
      return indent*' ' + 'conclude ' + str(self.claim) + ' by {\n' \
          + self.body.pretty_print(indent+2) + '\n' \
          + indent*' ' + '}\n'
  
  def __str__(self):
      return 'conclude ' + str(self.claim) + ' by ' + str(self.body)

  def uniquify(self, env):
    return PAnnot(self.location,
                  self.claim.uniquify(env),
                  self.body.uniquify(env))

@dataclass
class Suffices(Proof):
  claim: Formula
  reason: Proof
  body: Proof

  def copy(self):
      return Suffices(self.location, self.claim.copy(), self.reason.copy(), self.body.copy())
  
  def pretty_print(self, indent):
      return indent*' ' + 'suffices ' + str(self.claim) + '  by {\n' \
          + self.reason.pretty_print(indent+2) + '\n' \
          + maybe_pretty_print(self.body, indent)
  
  def __str__(self):
    return 'suffices ' + str(self.claim) + '  by ' + str(self.reason) + '\n' + maybe_str(self.body)

  def uniquify(self, env):
    return Suffices(self.location,
                    self.claim.uniquify(env),
                    self.reason.uniquify(env),
                    self.body.uniquify(env))

@dataclass
class Cases(Proof):
  subject: Proof
  cases: List[Tuple[str,Formula,Proof]]

  def copy(self):
      return Cases(self.location, self.subject.copy(), [(l, f.copy(), p.copy()) for (l,f,p) in self.cases])
  
  def pretty_print(self, indent):
      cases_str = ''
      for (label, frm, body) in self.cases:
          cases_str += indent*' ' + 'case ' + base_name(label) + ' : ' + str(frm) + '{\n' \
              + body.pretty_print(indent+2) + '\n' \
              + indent*' ' + '}'
      return '\n'.join(cases_str) + '\n'
      
  def uniquify(self, env):
    new_subject = self.subject.uniquify(env)
    new_cases = []
    for (label, formula, proof) in self.cases:
      body_env = {x:y for (x,y) in env.items()}
      new_formula = formula.uniquify(env) if formula else None
      new_label = generate_name(label)
      overwrite(body_env, label, new_label, self.location)
      new_proof = proof.uniquify(body_env)
      new_cases.append((new_label, new_formula, new_proof))
    return Cases(self.location, new_subject, new_cases)
      
@dataclass
class ModusPonens(Proof):
  implication: Proof
  arg: Proof

  def copy(self):
      return ModusPonens(self.location, self.implication.copy(), self.arg.copy())
  
  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
      return 'apply ' + str(self.implication) + ' to ' + str(self.arg)

  def uniquify(self, env):
    return ModusPonens(self.location,
                       self.implication.uniquify(env),
                       self.arg.uniquify(env))

@dataclass
class ImpIntro(Proof):
  label: str
  premise: Formula
  body: Proof

  def copy(self):
      return ImpIntro(self.location, self.label, self.premise.copy(), self.body.copy())
  
  def pretty_print(self, indent):
    return indent*' ' + 'assume ' + str(self.label) + \
      (': ' + str(self.premise) if self.premise else '') + '\n'\
      + maybe_pretty_print(self.body, indent)
  
  def __str__(self):
    return 'assume ' + str(self.label) + \
      (': ' + str(self.premise) if self.premise else '') + \
      ('{' + str(self.body) + '}' if self.body else '')

  def uniquify(self, env):
    new_premise = self.premise.uniquify(env) if self.premise else None
    body_env = copy_dict(env)
    new_label = generate_name(self.label)
    overwrite(body_env, self.label, new_label, self.location)
    new_body = self.body.uniquify(body_env)
    return ImpIntro(self.location, new_label, new_premise, new_body)

@dataclass
class AllIntro(Proof):
  var: Tuple[str,Type]
  # Position (s, e), where 
  #  e : The number of vars in the all intro list
  #  s : The variable's index in the list, starting from the last var
  pos: Tuple[int, int]
  body: Proof

  def copy(self):
      return AllIntro(self.location, (self.var[0], self.var[1].copy()), self.position, self.body.copy())
  
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
    new_t = ty.uniquify(body_env)
    new_x = generate_name(x)
    overwrite(body_env, x, new_x, self.location)
    new_body = self.body.uniquify(body_env)
    return AllIntro(self.location, (new_x, new_t), self.pos, new_body)

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

  def copy(self):
      return AllElimTypes(self.location, self.univ.copy(), self.arg, self.pos)
  
  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
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
    return AllElimTypes(self.location,
                        self.univ.uniquify(env),
                        self.arg.uniquify(env),
                        self.pos)

@dataclass
class AllElim(Proof):
  univ: Proof
  arg: Term
  # Position (s, e), where 
  #  e : The number of vars in the list
  #  s : The variable's index in the list, starting from the first var
  pos: Tuple[int, int]

  def copy(self):
      return AllElim(self.location, self.univ.copy(), self.arg.copy(), self.pos)
  
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
    return AllElim(self.location,
                   self.univ.uniquify(env),
                   self.arg.uniquify(env),
                   self.pos)

@dataclass
class SomeIntro(Proof):
  witnesses: List[Term]
  body: Proof

  def copy(self):
      return SomeIntro(self.location, [w.copy() for w in self.witnesses], self.body.copy())

  def pretty_print(self, indent):
    return indent*' ' + 'choose ' + ",".join([str(t) for t in self.witnesses]) + '\n' \
        + maybe_pretty_print(self.body, indent)
  
  def __str__(self):
    return 'choose ' + ",".join([str(t) for t in self.witnesses]) \
        + '; ' + maybe_str(self.body)
  
  def uniquify(self, env):
    return SomeIntro(self.location,
                     [w.uniquify(env) for w in self.witnesses],
                     self.body.uniquify(env))

@dataclass
class SomeElim(Proof):
  witnesses: List[str]
  label: str
  prop: Formula
  some: Proof
  body: Proof

  def copy(self):
      return SomeElim(self.location, self.witnesses, self.label,
                      self.prop.copy(), self.some.copy(), self.body.copy())
  
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
    new_some = self.some.uniquify(env)
    body_env = copy_dict(env)
    new_witnesses = []
    for x in self.witnesses:
      new_x = generate_name(x)
      new_witnesses.append(new_x)
      overwrite(body_env, x, new_x, self.location)
    new_label = generate_name(self.label)
    overwrite(body_env, self.label, new_label, self.location)
    new_prop = self.prop.uniquify(body_env) if self.prop else None
    new_body = self.body.uniquify(body_env)
    return SomeElim(self.location, new_witnesses, new_label,
                    new_prop, new_some, new_body)
    
@dataclass
class PTuple(Proof):
  args: List[Proof]

  def copy(self) -> Self:
      return PTuple(self.location, [arg.copy() for arg in self.args])
  
  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
    return ', '.join([str(arg) for arg in self.args])

  def uniquify(self, env):
    return PTuple(self.location, [a.uniquify(env) for a in self.args])

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

  def copy(self):
      return PAndElim(self.location, self.which, self.subject.copy())
  
  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
    return 'conjunct ' + str(self.which) + ' of ' + str(self.subject)

  def uniquify(self, env):
    return PAndElim(self.location, self.which, self.subject.uniquify(env))

@dataclass
class PTrue(Proof):

  def copy(self):
      return PTrue(self.location)
    
  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
    return '.'

  def uniquify(self, env):
    return self

@dataclass
class PReflexive(Proof):

  def copy(self):
      return PReflexive(self.location)
    
  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
    return 'reflexive'

  def uniquify(self, env):
    return self

@dataclass
class PHole(Proof):
  
  def copy(self):
      return PHole(self.location)
  
  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
      return '?'

  def uniquify(self, env):
    return self

@dataclass
class PSorry(Proof):
  
  def copy(self):
      return PSorry(self.location)
  
  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
      return 'sorry'

  def uniquify(self, env):
    return self

@dataclass
class PHelpUse(Proof):
  proof : Proof
  
  def copy(self):
      return PHelpUse(self.location, self.proof.copy())
  
  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
      return 'help ' + str(self.proof)

  def uniquify(self, env):
    return PHelpUse(self.location, self.proof.uniquify(env))

@dataclass
class PSymmetric(Proof):
  body: Proof

  def copy(self):
      return PSymmetric(self.location, self.body.copy())
  
  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
    return 'symmetric ' + str(self.body)

  def uniquify(self, env):
    return PSymmetric(self.location, self.body.uniquify(env))

@dataclass
class PTransitive(Proof):
  first: Proof
  second: Proof
  
  def copy(self):
      return PTransitive(self.location, self.first.copy(), self.second.copy())
  
  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
    return 'transitive ' + str(self.first) + ' ' + str(self.second)

  def uniquify(self, env):
    return PTransitive(self.location,
                       self.first.uniquify(env),
                       self.second.uniquify(env))

@dataclass
class PInjective(Proof):
  constr: Type
  body: Proof

  def copy(self):
      return PInjective(self.location, self.constr.copy(), self.body.copy())
  
  def pretty_print(self, indent):
    return indent*' ' + 'injective ' + str(self.constr) + '\n' \
        + maybe_pretty_print(self.body, indent)
  
  def __str__(self):
    return 'injective ' + str(self.constr) + '; ' + maybe_str(self.body)

  def uniquify(self, env):
    return PInjective(self.location,
                      self.constr.uniquify(env),
                      self.body.uniquify(env))

@dataclass
class PExtensionality(Proof):
  body: Proof

  def copy(self):
      return PExtensionality(self.location, self.body.copy())
  
  def pretty_print(self, indent):
    return indent*' ' + 'extensionality\n' \
        + maybe_pretty_print(self.body, indent)

  def __str__(self):
    return 'extensionality\n' + maybe_str(self.body)

  def uniquify(self, env):
    return PExtensionality(self.location, self.body.uniquify(env))

@dataclass
class IndCase(AST):
  pattern: Pattern
  induction_hypotheses: list[Tuple[str,Formula]]
  body: Proof

  def copy(self):
      return IndCase(self.location, self.pattern.copy(),
                     [(l,f.copy()) for (l,f) in self.induction_hypotheses],
                     self.body.copy())
  
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
    for (old, new) in zip(self.pattern.parameters, new_params):
      overwrite(body_env, old, new, self.location)

    new_hyp_labels = [generate_name(x) for (x, _) in self.induction_hypotheses]
    for ((old, _), new) in zip(self.induction_hypotheses, new_hyp_labels):
      overwrite(body_env, old, new, self.location)

    new_hyps = []
    for ((_, f), new_label) in zip(self.induction_hypotheses, new_hyp_labels):
      new_f = f.uniquify(body_env) if f else None
      new_hyps.append((new_label, new_f))

    new_pat = self.pattern.with_bindings(new_params).uniquify(body_env)
    new_body = self.body.uniquify(body_env)
    return IndCase(self.location, new_pat, new_hyps, new_body)

@dataclass
class Induction(Proof):
  typ: Type
  cases: List[IndCase]

  def copy(self):
      return Induction(self.location, self.typ.copy(), [c.copy() for c in self.cases])
  
  def pretty_print(self, indent):
    return indent*' ' + 'induction ' + str(self.typ) + '\n' \
      + '\n'.join([c.pretty_print(indent) for c in self.cases])

  def __str__(self):
    return 'induction ' + str(self.typ) + '\n' \
      + '\n'.join([str(c) for c in self.cases])
  
  def uniquify(self, env):
    return Induction(self.location,
                     self.typ.uniquify(env),
                     [c.uniquify(env) for c in self.cases])

@dataclass
class RuleInductionCase(AST):
  # `case <rule_name> { <proof> }` from a `rule induction` block.
  # The body is a complete proof of the rule's M-augmented conjunct of
  # `<pred>_rule_induction`'s `rules_hyp` (the user's `arbitrary` and
  # `assume` happen inside the body).
  rule_name: str
  body: Proof

  def copy(self):
    return RuleInductionCase(self.location, self.rule_name, self.body.copy())

  def pretty_print(self, indent):
    return indent*' ' + 'case ' + base_name(self.rule_name) + ' {\n' \
        + self.body.pretty_print(indent+2) + '\n' + indent*' ' + '}'

  def __str__(self):
    return 'case ' + base_name(self.rule_name) + ' { ' \
        + str(self.body) + ' }'

  def uniquify(self, env):
    # Resolve the rule name against the env so we can match against the
    # uniquified rule names later. Wrong names are reported with a
    # did-you-mean message.
    if self.rule_name not in env.keys():
      from edit_distance import edit_distance
      from math import ceil
      close = [v for v in env.keys()
               if edit_distance(self.rule_name, v)
                  <= ceil(len(self.rule_name) / 5)]
      hint = '\n\tdid you intend: ' + ', '.join(close) if close else ''
      error(self.location,
            "no such rule '" + self.rule_name + "'" + hint)
    resolved = env[self.rule_name]
    new_rule_name = self.rule_name
    if isinstance(resolved, list) and len(resolved) >= 1:
      new_rule_name = resolved[0]
    return RuleInductionCase(self.location, new_rule_name,
                             self.body.uniquify(env))

@dataclass
class RuleInduction(Proof):
  # `rule induction <pred> case <r1> { ... } ...`
  # Desugars to `apply <pred>_rule_induction[<motive>] to (<case_1>, ...,
  # <case_k>)`. The motive is inferred from the goal, which must have
  # the shape `all xs. if <pred>(xs) then Q(xs)`.
  hyp_name: str
  cases: list

  def copy(self):
    return RuleInduction(self.location, self.hyp_name,
                         [c.copy() for c in self.cases])

  def pretty_print(self, indent):
    return indent*' ' + 'rule induction ' + base_name(self.hyp_name) + '\n' \
        + '\n'.join([c.pretty_print(indent) for c in self.cases])

  def __str__(self):
    return 'rule induction ' + base_name(self.hyp_name) + ' ' \
        + ' '.join([str(c) for c in self.cases])

  def uniquify(self, env):
    if self.hyp_name not in env.keys():
      from edit_distance import edit_distance
      from math import ceil
      close = [v for v in env.keys()
               if edit_distance(self.hyp_name, v)
                  <= ceil(len(self.hyp_name) / 5)]
      hint = '\n\tdid you intend: ' + ', '.join(close) if close else ''
      error(self.location,
            "rule induction: no such predicate '"
            + self.hyp_name + "'" + hint)
    resolved = env[self.hyp_name]
    new_hyp_name = self.hyp_name
    if isinstance(resolved, list) and len(resolved) >= 1:
      new_hyp_name = resolved[0]
    return RuleInduction(self.location, new_hyp_name,
                         [c.uniquify(env) for c in self.cases])

@dataclass
class RuleInversion(Proof):
  # `rule inversion <pred> case <r1> { ... } ...`
  # Same shape as RuleInduction, but desugars to applying the
  # `<pred>_rule_inversion` theorem instead — the cases prove the
  # *non*-augmented rule conjuncts (no induction hypothesis).
  hyp_name: str
  cases: list

  def copy(self):
    return RuleInversion(self.location, self.hyp_name,
                         [c.copy() for c in self.cases])

  def pretty_print(self, indent):
    return indent*' ' + 'rule inversion ' + base_name(self.hyp_name) + '\n' \
        + '\n'.join([c.pretty_print(indent) for c in self.cases])

  def __str__(self):
    return 'rule inversion ' + base_name(self.hyp_name) + ' ' \
        + ' '.join([str(c) for c in self.cases])

  def uniquify(self, env):
    if self.hyp_name not in env.keys():
      from edit_distance import edit_distance
      from math import ceil
      close = [v for v in env.keys()
               if edit_distance(self.hyp_name, v)
                  <= ceil(len(self.hyp_name) / 5)]
      hint = '\n\tdid you intend: ' + ', '.join(close) if close else ''
      error(self.location,
            "rule inversion: no such predicate '"
            + self.hyp_name + "'" + hint)
    resolved = env[self.hyp_name]
    new_hyp_name = self.hyp_name
    if isinstance(resolved, list) and len(resolved) >= 1:
      new_hyp_name = resolved[0]
    return RuleInversion(self.location, new_hyp_name,
                         [c.uniquify(env) for c in self.cases])

@dataclass
class SwitchProofCase(AST):
  pattern: Pattern
  assumptions: list[Tuple[str,Formula]]
  body: Proof

  def copy(self):
      return SwitchProofCase(self.location, self.pattern.copy(),
                             [(l,f.copy()) for (l,f) in self.assumptions],
                             self.body.copy())
  
  def pretty_print(self, indent):
    return indent*' ' + 'case ' + str(self.pattern) + '{\n' \
        + self.body.pretty_print(indent+2) \
        + indent*' ' + '}\n'

  def __str__(self):
    return 'case ' + str(self.pattern) + '{' + str(self.body) + '}'

  def uniquify(self, env):
    body_env = copy_dict(env)

    new_params = [generate_name(x) for x in self.pattern.bindings()]
    for (old, new) in zip(self.pattern.bindings(), new_params):
      overwrite(body_env, old, new, self.location)

    new_assumption_labels = [generate_name(x) for (x, _) in self.assumptions]
    for ((old, _), new) in zip(self.assumptions, new_assumption_labels):
      overwrite(body_env, old, new, self.location)

    new_assumptions = []
    for ((_, f), new_label) in zip(self.assumptions, new_assumption_labels):
      new_f = f.uniquify(body_env) if f else None
      new_assumptions.append((new_label, new_f))

    new_pat = self.pattern.with_bindings(new_params).uniquify(body_env)
    new_body = self.body.uniquify(body_env)
    return SwitchProofCase(self.location, new_pat,
                           new_assumptions, new_body)

@dataclass
class SwitchProof(Proof):
  subject: Term
  cases: List[SwitchProofCase]
  
  def copy(self):
      return SwitchProof(self.location, self.subject.copy(),
                         [c.copy() for c in self.cases])
      
  def pretty_print(self, indent):
      return indent*' ' + 'switch ' + str(self.subject) + '{\n' \
          + '\n'.join([c.pretty_print(indent+2) for c in self.cases]) \
          + indent*' ' + '}\n'
      
  def __str__(self):
      return 'switch ' + str(self.subject) \
        + '{' + '\n'.join([str(c) for c in self.cases]) + '}'
    
  def uniquify(self, env):
    return SwitchProof(self.location,
                       self.subject.uniquify(env),
                       [c.uniquify(env) for c in self.cases])

@dataclass
class EvaluateGoal(Proof):

  def copy(self):
      return EvaluateGoal(self.location)

  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
    return 'evaluate'

  def uniquify(self, env):
    return self

@dataclass
class EvaluateFact(Proof):
  subject: Proof

  def copy(self):
      return EvaluateFact(self.location, self.subject.copy())
  
  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
    return 'evaluate in ' + str(self.subject)

  def uniquify(self, env):
    return EvaluateFact(self.location, self.subject.uniquify(env))

@dataclass
class SimplifyGoal(Proof):
  body: Proof
  givens: List[Proof]

  def copy(self):
      return SimplifyGoal(self.location, self.body.copy(),
                          [p.copy() for p in self.givens])
  
  def __str__(self):
      return 'simplify ' + ' | '.join([str(p) for p in self.givens]) + '\n' \
          + str(self.body)

  def uniquify(self, env):
    return SimplifyGoal(self.location,
                        self.body.uniquify(env),
                        [p.uniquify(env) for p in self.givens])


@dataclass
class SimplifyFact(Proof):
  subject: Proof
  givens: List[Proof]

  def copy(self):
      return SimplifyFact(self.location, self.subject.copy(),
                          [p.copy() for p in self.givens])
  
  def pretty_print(self, indent):
      return str(self)
  
  def __str__(self):
    return 'simplify ' \
        + ' | '.join([str(p) for p in self.givens]) \
        + ' in ' + str(self.subject)

  def uniquify(self, env):
    return SimplifyFact(self.location,
                        self.subject.uniquify(env),
                        [p.uniquify(env) for p in self.givens])

@dataclass
class ApplyDefsGoal(Proof):
  definitions: List[Term]
  body: Proof

  def copy(self):
      return ApplyDefsGoal(self.location, [d.copy() for d in self.definitions], self.body.copy())
  
  def __str__(self):
      return 'expand ' + ' | '.join([str(d) for d in self.definitions]) \
        + ' ' + str(self.body)

  def uniquify(self, env):
    return ApplyDefsGoal(self.location,
                         [d.uniquify(env) for d in self.definitions],
                         self.body.uniquify(env))

@dataclass
class ApplyDefsFact(Proof):
  definitions: List[Term]
  subject: Proof

  def copy(self):
      return ApplyDefsFact(self.location, [t.copy() for t in self.definitions],
                           self.subject.copy())
  
  def __str__(self):
      return 'expand ' + ' | '.join([str(d) for d in self.definitions]) \
        + ' in ' + str(self.subject)

  def uniquify(self, env):
    return ApplyDefsFact(self.location,
                         [d.uniquify(env) for d in self.definitions],
                         self.subject.uniquify(env))

@dataclass
class RewriteGoal(Proof):
  equations: List[Proof]
  body: Proof

  def copy(self):
      return RewriteGoal(self.location, [p.copy() for p in self.equations],
                         self.body.copy())
  
  def __str__(self):
      return 'replace ' + '|'.join([str(eqn) for eqn in self.equations]) \
        + '\n' + str(self.body)

  def uniquify(self, env):
    return RewriteGoal(self.location,
                       [e.uniquify(env) for e in self.equations],
                       self.body.uniquify(env))

@dataclass
class RewriteFact(Proof):
  subject: Proof
  equations: List[Proof]

  def copy(self):
      return RewriteFact(self.location,
                         self.subject.copy(),
                         [p.copy() for p in self.equations])
  
  def __str__(self):
      return 'replace ' + ','.join([str(eqn) for eqn in self.equations]) \
        + ' in ' + str(self.subject)

  def uniquify(self, env):
    return RewriteFact(self.location,
                       self.subject.uniquify(env),
                       [e.uniquify(env) for e in self.equations])

################ Statements ######################################

## Updates the environment with a name, creating overloads
def extend(env, name, new_name, loc):
  if name in env['no overload']:
    ty = env['no overload'][name]
    error(loc, f"Cannot overload {ty} names. {name} is already defined as a {ty}")

  if name in env.keys():
      if not new_name in env[name]:
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
class Postulate(Statement):
  name: str
  what: Formula

  def key(self):
      return self.name
  
  def __str__(self):
    return 'postulate ' + self.name + ': ' + str(self.what) + '\n\n'

  def uniquify(self, env):
    if self.name in env.keys():
      error(self.location, "theorem names may not be overloaded")
    new_what = self.what.uniquify(env)
    new_name = generate_name(self.name)
    overwrite(env, self.name, new_name, self.location)
    env['no overload'][self.name] = 'theorem'
    return Postulate(self.location, new_name, new_what)

  def collect_exports(self, export_env, importing_module):
    export_env[base_name(self.name)] = [self.name]

@dataclass
class Theorem(Statement):
  name: str
  what: Formula
  proof: Proof
  isLemma: bool = False   # TODO: remove this, use visibility

  def key(self):
      return self.name
  
  def __str__(self):
    return ('lemma ' if self.isLemma else 'theorem ') \
      + self.name + ': ' + str(self.what) \
      + '\nproof\n' + self.proof.pretty_print(2) + '\nend\n'

  def uniquify(self, env):
    if self.name in env.keys():
      error(self.location, "theorem names may not be overloaded: " + base_name(self.name))
    new_what = self.what.uniquify(env)
    new_proof = self.proof.uniquify(env)
    new_name = generate_name(self.name)
    overwrite(env, self.name, new_name, self.location)
    env['no overload'][self.name] = 'theorem'
    return Theorem(self.location, new_name, new_what, new_proof, self.isLemma)

  def collect_exports(self, export_env, importing_module):
    if importing_module == get_current_module() or not self.isLemma:
      export_env[base_name(self.name)] = [self.name]
    
@dataclass
class Constructor(AST):
  name: str
  parameters: List[Type]

  def pretty_print(self, indent):
      return indent*' ' + str(self)
  
  def uniquify(self, env, body_env):
    new_params = [ty.uniquify(body_env) for ty in self.parameters]
    new_name = generate_name(self.name)
    extend(env, self.name, new_name, self.location)
    return Constructor(self.location, new_name, new_params)

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
class Rule(AST):
  # An introduction rule of a `predicate` / `relation` declaration.
  # The formula is whatever the user wrote on the right of `name :`.
  # Validation (must be a quantified implication or a bare conclusion of
  # the form `pred(args)`) happens later, with diagnostics that quote
  # `original_keyword` and the rule's name.
  name: str
  formula: Formula

  def uniquify(self, env, body_env):
    new_formula = self.formula.uniquify(body_env)
    if self.name in env.keys():
      error(self.location,
            "rule names may not be overloaded: " + base_name(self.name))
    new_name = generate_name(self.name)
    overwrite(env, self.name, new_name, self.location)
    env['no overload'][self.name] = 'rule'
    return Rule(self.location, new_name, new_formula)

  def __str__(self):
    return base_name(self.name) + ' : ' + str(self.formula)

  def pretty_print(self, indent):
    return indent*' ' + base_name(self.name) + ' : ' + str(self.formula)


@dataclass
class Predicate(Declaration):
  # An inductively defined predicate or relation. `original_keyword` is
  # 'predicate' or 'relation' — kept on the AST so error messages echo the
  # form the user actually wrote.
  name: str
  type_params: List[str]
  signature: Type
  rules: List[Rule]
  original_keyword: str = 'predicate'

  def reduce(self, env):
    return self

  def substitute(self, sub):
    return self

  def uniquify(self, env):
    if self.name in env.keys():
      error(self.location,
            self.original_keyword + " names may not be overloaded: " \
            + base_name(self.name))
    new_name = generate_name(self.name)
    env[self.name] = [new_name]
    env['no overload'][self.name] = self.original_keyword
    base_pred = base_name(self.name)

    # Pre-register the synthesised `<pred>_rule_induction` theorem name so
    # user code referencing it gets resolved correctly during uniquify.
    # The translation pass in proof_checker.py reads `rule_induction_name`
    # off the AST and emits a Theorem with that exact uniquified name.
    rule_ind_base = base_pred + '_rule_induction'
    if rule_ind_base in env.keys():
      error(self.location,
            "name '" + rule_ind_base + "' is already defined; the "
            + self.original_keyword + " '" + base_pred
            + "' would auto-generate a theorem with that name")
    rule_ind_unique = generate_name(rule_ind_base)
    env[rule_ind_base] = [rule_ind_unique]
    env['no overload'][rule_ind_base] = 'theorem'
    # Same treatment for the inversion principle.
    rule_inv_base = base_pred + '_rule_inversion'
    if rule_inv_base in env.keys():
      error(self.location,
            "name '" + rule_inv_base + "' is already defined; the "
            + self.original_keyword + " '" + base_pred
            + "' would auto-generate a theorem with that name")
    rule_inv_unique = generate_name(rule_inv_base)
    env[rule_inv_base] = [rule_inv_unique]
    env['no overload'][rule_inv_base] = 'theorem'

    body_env = copy_dict(env)
    new_type_params = [generate_name(t) for t in self.type_params]
    for (old, new) in zip(self.type_params, new_type_params):
      extend(body_env, old, new, self.location)

    new_signature = self.signature.uniquify(body_env)
    new_rules = [rule.uniquify(env, body_env) for rule in self.rules]

    new_pred = Predicate(self.location, new_name, new_type_params,
                         new_signature, new_rules,
                         self.original_keyword,
                         visibility=self.visibility)
    new_pred.rule_induction_name = rule_ind_unique
    new_pred.rule_inversion_name = rule_inv_unique
    # Register a back-pointer keyed by the predicate's uniquified name so
    # the proof checker can recover this AST node (specifically
    # `rule_induction_name` / `rule_inversion_name` and the rule list)
    # when desugaring a `rule induction` / `rule inversion` proof.
    _predicate_decls_by_unique_name[new_name] = new_pred
    return new_pred

  def collect_exports(self, export_env, importing_module):
    if self.visibility == 'private' and importing_module != get_current_module():
      return
    export_env[base_name(self.name)] = [self.name]
    for rule in self.rules:
      extend(export_env, base_name(rule.name), rule.name, self.location)
    if hasattr(self, 'rule_induction_name'):
      extend(export_env, base_name(self.rule_induction_name),
             self.rule_induction_name, self.location)

  def __str__(self):
    if get_verbose():
      shown_name = self.name
    else:
      shown_name = base_name(self.name)
    header = self.original_keyword + ' ' + shown_name
    if self.type_params:
      header += '<' + ','.join([base_name(t) for t in self.type_params]) + '>'
    body = '\n'.join('  ' + str(r) for r in self.rules)
    return header + ' : ' + str(self.signature) + ' {\n' + body + '\n}'

  def pretty_print(self, indent):
    return indent*' ' + str(self)


@dataclass
class Union(Declaration):
  name: str
  type_params: List[str]
  alternatives: List[Constructor]

  def reduce(self, env):
    return self
  
  def uniquify(self, env):
    if self.name in env.keys():
      error(self.location, "union names may not be overloaded")
    new_name = generate_name(self.name)
    env[self.name] = [new_name]
    env['no overload'][self.name] = 'union'

    body_env = copy_dict(env)
    new_type_params = [generate_name(t) for t in self.type_params]
    for (old, new) in zip(self.type_params, new_type_params):
      extend(body_env, old, new, self.location)

    new_alts = [con.uniquify(env, body_env) for con in self.alternatives]
    return Union(self.location, new_name, new_type_params, new_alts,
                 visibility=self.visibility)

  def collect_exports(self, export_env, importing_module):
    if self.visibility == 'private' and importing_module != get_current_module():
      return
    export_env[base_name(self.name)] = [self.name]

    if not self.visibility == 'opaque' or (importing_module == get_current_module()):
      for con in self.alternatives:
        extend(export_env, base_name(con.name), con.name, self.location)
    
  def substitute(self, sub):
    return self
      
  def pretty_print(self, indent):
      header = 'union ' + base_name(self.name) \
          + ('<' + ','.join([base_name(t) for t in self.type_params]) + '>' if len(self.type_params) > 0 \
             else '')
      if self.visibility == 'opaque':
        ret = header + '\n'
      else:
        ret = header + ' {\n' \
                     + '\n'.join([c.pretty_print(indent+2) for c in self.alternatives]) + '\n'\
                     + indent*' ' + '}\n'
      
      return indent*' ' + ret
  
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

  def uniquify(self, env, fun_name):
    if self.rator.name != fun_name:
        error(self.rator.location, 'expected function name "' + fun_name + \
              '", not "' + str(self.rator.name) + '"')
    new_rator = self.rator.uniquify(env)
    new_pat = self.pattern.uniquify(env)
    body_env = copy_dict(env)

    match new_pat:
      case PatternCons(loc, cons, parameters):
        new_pat_params = [generate_name(x) for x in parameters]
        for (old, new) in zip(parameters, new_pat_params):
          overwrite(body_env, old, new, self.location)
        new_pat = new_pat.with_bindings(new_pat_params)
      case PatternBool(loc, b):
        pass

    new_params = [generate_name(x) for x in self.parameters]
    for (old, new) in zip(self.parameters, new_params):
      overwrite(body_env, old, new, self.location)

    new_body = self.body.uniquify(body_env)
    return FunCase(self.location, new_rator, new_pat, new_params, new_body)


@dataclass
class RecFun(Declaration):
  name: str
  type_params: List[str]
  params: List[Type]
  returns: Type
  cases: List[FunCase]

  def uniquify(self, env):
    old_name = self.name
    new_name = generate_name(self.name)
    extend(env, self.name, new_name, self.location)

    body_env = copy_dict(env)
    new_type_params = [generate_name(t) for t in self.type_params]
    for (old, new) in zip(self.type_params, new_type_params):
      extend(body_env, old, new, self.location)

    new_params = [ty.uniquify(body_env) for ty in self.params]
    new_returns = self.returns.uniquify(body_env)
    new_cases = [c.uniquify(body_env, old_name) for c in self.cases]

    new_recfun = RecFun(self.location, new_name, new_type_params,
                        new_params, new_returns, new_cases,
                        visibility=self.visibility)
    new_recfun.old_type_params = self.type_params
    return new_recfun
      
  def collect_exports(self, export_env, importing_module):
    if self.visibility == 'private' and importing_module != get_current_module():
      return
    extend(export_env, base_name(self.name), self.name, self.location)

  def __str__(self):
    if get_verbose():
      return '`' + name2str(self.name)
    else:
      return name2str(self.name)
    
  def to_string(self):
    return 'recursive ' + self.name + '<' + ','.join([name2str(t) for t in self.type_params]) + '>' \
      + '(' + ','.join([str(ty) for ty in self.params]) + ')' \
      + ' -> ' + str(self.returns) + '{\n' \
      + '\n'.join([str(c) for c in self.cases]) \
      + '\n}'

  def pretty_print(self, indent):
    header = complete_name(self.name) \
        + ('<' + ','.join([name2str(t) for t in self.type_params]) + '>' \
           if len(self.type_params) > 0 else '') \
      + '(' + ','.join([str(ty) for ty in self.params]) + ')' \
      + ' -> ' + str(self.returns)
    if self.visibility == 'opaque':
      ret = 'fun ' + header + '\n'
    else:
      ret = 'recursive ' + header + '{\n' \
      + '\n'.join([c.pretty_print(indent+2) for c in self.cases]) + '\n' \
      + '}\n'

    return indent*' ' + ret 

  def __eq__(self, other):
    if isinstance(other, ResolvedVar):
      return self.name == other.name
    elif isinstance(other, OverloadedVar):
      return self.name == other.resolved_names[0]
    elif isinstance(other, Var):
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

def pretty_print_function_header(name, type_params, params):
    return 'fun ' + complete_name(name) \
        + ('<' + ', '.join([base_name(t) for t in type_params]) + '>' \
           if len(type_params) > 0 else '') \
        + '(' + ', '.join([x + ':' + str(t) if t else x \
                           for (x,t) in params]) + ')\n'

def pretty_print_function(name, type_params, params, body):
    return 'fun ' + complete_name(name) \
        + ('<' + ', '.join([base_name(t) for t in type_params]) + '>' \
           if len(type_params) > 0 else '') \
        + '(' + ', '.join([x + ':' + str(t) if t else x \
                           for (x,t) in params]) + ')' \
        + " {\n" + body.pretty_print(2, True) + "\n}\n"

@dataclass
class GenRecFun(Declaration):
  name: str
  type_params: List[str]
  vars: List[Tuple[str,Type]]
  returns: Type
  measure: Term
  measure_ty: Type
  body: Term
  terminates: Proof

  def uniquify(self, env):
    new_name = generate_name(self.name)
    extend(env, self.name, new_name, self.location)

    body_env = copy_dict(env)
    terminates_env = copy_dict(env)
    new_type_params = [generate_name(t) for t in self.type_params]
    for (old, new) in zip(self.type_params, new_type_params):
      extend(body_env, old, new, self.location)
      extend(terminates_env, old, new, self.location)

    new_returns = self.returns.uniquify(body_env)

    new_var_types = [t.uniquify(body_env) if t else None
                     for (_, t) in self.vars]
    new_vars = [(generate_name(x), nt)
                for ((x, _), nt) in zip(self.vars, new_var_types)]
    for ((old, _), (new, _)) in zip(self.vars, new_vars):
      overwrite(body_env, old, new, self.location)

    new_measure = self.measure.uniquify(body_env)
    new_measure_ty = self.measure_ty.uniquify(env)
    new_terminates = self.terminates.uniquify(terminates_env)
    new_body = self.body.uniquify(body_env)

    new_recfun = GenRecFun(self.location, new_name, new_type_params,
                           new_vars, new_returns, new_measure,
                           new_measure_ty, new_body, new_terminates,
                           visibility=self.visibility)
    new_recfun.old_type_params = self.type_params
    return new_recfun
    
  def collect_exports(self, export_env, importing_module):
    if self.visibility == 'private' and (importing_module != get_current_module()):
      return
    extend(export_env, base_name(self.name), self.name, self.location)

  def __str__(self):
    if get_verbose():
      return self.to_string()
    else:
      return self.name if get_unique_names() else base_name(self.name)
    
  def to_string(self):
    return 'recfun ' + self.name + '<' + ','.join(self.type_params) + '>' \
        + '(' + ', '.join([x + ':' + str(t) if t else x\
                           for (x,t) in self.vars]) + ')' \
        + ' -> ' + str(self.returns) + '\n' \
        + '\tmeasure ' + str(self.measure) \
        + ' {\n' + str(self.body) + '\n}\n' \
        + 'terminates {\n' + str(self.terminates) + '\n}\n'

  def pretty_print(self, indent):
    header = complete_name(self.name) \
        + ('<' + ','.join([name2str(t) for t in self.type_params]) + '>' \
           if len(self.type_params) > 0 else '') \
      + '(' + ', '.join([base_name(x) + ':' + str(t) if t else x for (x,t) in self.vars])\
      + ') -> ' + str(self.returns) \
      + '\nmeasure\t' + str(self.measure) + ' '
    
    if self.visibility == 'opaque':
      ret = 'fun ' + header + '\n'
    else:
      ret = 'recfun ' + header + ' {' + self.body.pretty_print(indent+2) + '\n}\n'

    return indent*' ' + ret
      

  def __eq__(self, other):
    if isinstance(other, ResolvedVar):
      return self.name == other.name
    elif isinstance(other, OverloadedVar):
      return self.name == other.resolved_names[0]
    elif isinstance(other, Var):
      return self.name == other.name
    elif isinstance(other, TermInst):
      return self == other.subject
    elif isinstance(other, GenRecFun):
      return self.name == other.name
    else:
      return False
  
  def reduce(self, env):
    return self

  def substitute(self, sub):
    return self

@dataclass
class Define(Declaration):
  name: str
  typ: Type
  body: Term

  def str_header(self):
    if isinstance(self.body, Lambda):
        params = [(base_name(x), t) for (x,t) in self.body.vars]
        return pretty_print_function_header(self.name,[],params)
    elif isinstance(self.body, Generic) \
         and isinstance(self.body.body, Lambda):
        typarams = self.body.type_params
        params = [(base_name(x), t) for (x,t) in self.body.body.vars]
        return pretty_print_function_header(self.name, typarams, params)
    else:
        return 'define ' + complete_name(self.name) \
            + (' : ' + str(self.typ) if self.typ else '') + '\n'
  
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
    
  def pretty_print(self, indent):
      if self.visibility == 'opaque':
          return self.str_header()
      else:
          return str(self)
    
  def uniquify(self, env):
    new_typ = self.typ.uniquify(env) if self.typ else None
    new_body = self.body.uniquify(env)

    new_name = generate_name(self.name)
    extend(env, self.name, new_name, self.location)
    return Define(self.location, new_name, new_typ, new_body,
                  visibility=self.visibility)

  def collect_exports(self, export_env, importing_module):
    if self.visibility == 'private' and (importing_module != get_current_module()):
      return
    extend(export_env, base_name(self.name), self.name, self.location)

uniquified_modules = {}

def get_uniquified_modules():
  global uniquified_modules
  return uniquified_modules

def add_uniquified_module(module_name, ast):
  global uniquified_modules
  uniquified_modules[module_name] = ast

def find_private_lemma_definers(name):
  """Return a list of (module, filename, line) tuples for every private
  `lemma` whose base name matches `name`. Used by `PVar.uniquify` to give
  a more specific error than "undefined proof variable" when a lookup
  fails because the matching definition was filtered out by
  `Theorem.collect_exports` (lemmas are module-private).

  The `module` field is the module declared by the file (one module can
  span several files — e.g., `lib/Nat.pf` and `lib/NatMult.pf` both
  declare `module Nat`); falls back to the import key for files with no
  `module` declaration. `filename` and `line` come from the `lemma`'s
  source location and may be `None` if the location is empty."""
  global uniquified_modules
  hits = []
  for import_key, ast in uniquified_modules.items():
    if ast is None:
      continue
    declared_module = None
    matching_loc = None
    for stmt in ast:
      if isinstance(stmt, Module) and declared_module is None:
        declared_module = stmt.name
      if isinstance(stmt, Theorem) and stmt.isLemma \
         and base_name(stmt.name) == name and matching_loc is None:
        matching_loc = stmt.location
    if matching_loc is not None:
      reported = declared_module if declared_module is not None else import_key
      filename = matching_loc.filename if not matching_loc.empty else None
      line = matching_loc.line if not matching_loc.empty else None
      hits.append((reported, filename, line))
  return hits


@dataclass
class Assert(Statement):
  formula : Term

  def __str__(self):
    return 'assert ' + str(self.formula)

  def uniquify(self, env):
    return Assert(self.location, self.formula.uniquify(env))

  def collect_exports(self, export_env, importing_module):
    pass

@dataclass
class Print(Statement):
  term : Term

  def __str__(self):
    return 'print ' + str(self.term)

  def uniquify(self, env):
    return Print(self.location, self.term.uniquify(env))

  def collect_exports(self, export_env, importing_module):
    pass


def find_file(loc, name):
  for dir in get_import_directories():
    filename = os.path.join(dir, name + ".pf")
    if os.path.isfile(filename):
      return filename
  error(loc, 'could not find a file for import: ' + name)

def greatest_lower_bound(vis1, vis2):
    if vis1 == 'public':
        return vis2
    elif vis1 == 'private' or vis1 == 'default':
        return 'private'
    else:
        raise Exception('in greatest_lower_bound: unknown visibility: ' + vis1)
  
@dataclass
class Import(Declaration):
  name: str
  ast: AST = None

  def __str__(self):
    return 'import ' + self.name

  def pretty_print(self, indent):
    return indent*' '  + str(self) + '\n'

  def uniquify(self, env):
    importing_module = get_current_module()
    set_current_module(self.name)
    if get_verbose():
      print('uniquify import ' + self.name + ' ==> ' + importing_module + '\n')
    old_verbose = get_verbose()
    if get_verbose() == VerboseLevel.CURR_ONLY:
      set_verbose(VerboseLevel.NONE)

    global uniquified_modules
    if self.name in uniquified_modules.keys():
      new_ast = uniquified_modules[self.name]
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
      parsed_ast = parse(src, trace=False)
      set_filename(old_filename)
      new_ast = uniquify_deduce(parsed_ast)
      uniquified_modules[self.name] = new_ast

    env['__module__' + self.name] = None
    if get_verbose():
        print('collecting exports from ' + self.name + ' for import to ' + importing_module + '\n')
    for stmt in new_ast:
      stmt.collect_exports(env, importing_module)
    set_verbose(old_verbose)
    if get_verbose():
      print('\tuniquify finished import ' + self.name)
    set_current_module(importing_module)
    return Import(self.location, self.name, new_ast,
                  visibility=self.visibility)

  def collect_exports(self, export_env, importing_module):
    module_name = '__module__' + self.name
    if self.visibility == 'public' and not (module_name in export_env.keys()):
      set_current_module(self.name)
      export_env[module_name] = None
      for stmt in self.ast:
        stmt.collect_exports(export_env, importing_module)
      set_current_module(importing_module)

@dataclass
class Auto(Statement):
  name: Term

  def key(self):
      return str(self.name)
  
  def __str__(self):
    return 'auto ' + str(self.name)

  def uniquify(self, env):
    return Auto(self.location, self.name.uniquify(env))

  def collect_exports(self, export_env, importing_module):
    pass

@dataclass
class Inductive(Statement):
  typ: Type 
  thm_name: Term

  def __str__(self):
    return 'inductive ' + str(self.typ) + ' by ' + str(self.thm_name)

  def uniquify(self, env):
    return Inductive(self.location,
                     self.typ.uniquify(env),
                     self.thm_name.uniquify(env))

  def collect_exports(self, export_env, importing_module):
    pass


@dataclass
class Module(Statement):
  name: str

  def pretty_print(self, indent):
      return indent*' ' + 'module ' + self.name + '\n'
  
  def uniquify(self, env):
      set_current_module(self.name)
      return Module(self.location, self.name)

  def collect_exports(self, export_env, importing_module):
      set_current_module(self.name)

@dataclass
class Export(Statement):
  name: str
  resolved_names: list[str] = field(default_factory=list)

  def pretty_print(self, indent):
      return indent*' ' + 'export ' + self.name + '\n'
  
  def uniquify(self, env):
      return Export(self.location, self.name, env[self.name])

  def collect_exports(self, export_env, importing_module):
      for x in self.resolved_names:
          extend(export_env, base_name(x), x, self.location)
      
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
    new_op = self.op.uniquify(env)
    body_env = {x:y for (x,y) in env.items()}
    new_type_params = [generate_name(x) for x in self.type_params]
    for (old, new) in zip(self.type_params, new_type_params):
      overwrite(body_env, old, new, self.location)
    new_typeof = self.typeof.uniquify(body_env)
    return Associative(self.location, new_type_params, new_op, new_typeof)

  def collect_exports(self, export_env, importing_module):
    opname = self.op.get_name()
    full_name = '__associative_' + opname
    base = base_name(opname)
    full_base_name = '__associative_' + base
    export_env[full_base_name] = [full_name]

@dataclass
class Trace(Statement):
  rec_fun: Var

  def __str__(self):
    return 'trace ' + str(self.rec_fun)

  def uniquify(self, env):
    return Trace(self.location, self.rec_fun.uniquify(env))

  def reduce(self, env):
    self.rec_fun.reduce(env)

# ---------------------
# Auxiliary Functions
  
def mkEqual(loc, arg1, arg2):
  ret = Call(loc, None, ResolvedVar(loc, None, '='), [arg1, arg2])
  return ret

def split_equation(loc, equation, env):
  if isinstance(equation, TLet):
    equation = equation.reduceLets(env)
    
  match equation:
    case Call(loc1, tyof, rator, [L, R]) if isinstance(rator, VarRef) and rator.get_name() == '=':
      return (L, R)
    case All(loc1, tyof, var, pos, body):
      return split_equation(loc, body, env)
    case _:
      error(loc, 'expected an equality, not ' + str(equation))

def equation_vars(formula):
  match formula:
    case Call(loc1, tyof, rator, [L, R]) if isinstance(rator, VarRef) and rator.get_name() == '=':
      return []
    case All(loc1, tyof, var, pos, body):
      x, t = var
      v = ResolvedVar(loc1, None, x)
      v.typeof = t
      return [v] + equation_vars(body)
    case _:
      raise Exception('equation_vars unhandled ' + str(formula))
      
def is_equation(formula):
  match formula:
    case Call(loc1, tyof, rator, [L, R]) if isinstance(rator, VarRef) and rator.get_name() == '=':
      return True
    case All(loc1, tyof, var, pos, body):
      return is_equation(body)
    case _:
      return False

def isUInt(t):
  match t:
    case (OverloadedVar(loc, tyof, [n, *_]) | ResolvedVar(loc, tyof, n)) if base_name(n) == 'bzero':
      return True
    case Call(loc, tyof1, (OverloadedVar(loc2, tyof2, [n, *_]) | ResolvedVar(loc2, tyof2, n)), [arg]) \
      if base_name(n) == 'inc_dub':
        return isUInt(arg)
    case Call(loc, tyof1, (OverloadedVar(loc2, tyof2, [n, *_]) | ResolvedVar(loc2, tyof2, n)), [arg]) \
      if base_name(n) == 'dub_inc':
        return isUInt(arg)
    case Call(loc, tyof1, (OverloadedVar(loc2, tyof2, [n, *_]) | ResolvedVar(loc2, tyof2, n)), [arg]) \
      if base_name(n) == 'fromNat':
        return isNat(arg)
    case _:
      return False

def isBZero(t):
  match t:
    case (OverloadedVar(loc, tyof, [n, *_]) | ResolvedVar(loc, tyof, n)) if base_name(n) == 'bzero':
      return True
    case _:
      return False
  
def isDubInc(t):
  match t:
    case Call(loc, tyof1, (OverloadedVar(loc2, tyof2, [n, *_]) | ResolvedVar(loc2, tyof2, n)), [arg]) \
      if base_name(n) == 'dub_inc':
        return True
    case _:
      return False
  
def isIncDub(t):
  match t:
    case Call(loc, tyof1, (OverloadedVar(loc2, tyof2, [n, *_]) | ResolvedVar(loc2, tyof2, n)), [arg]) \
      if base_name(n) == 'inc_dub':
        return True
    case _:
      return False

def get_arg(t):
  match t:
    case Call(loc, tyof1, rator, [arg]):
      return arg
    case _:
      raise Exception('get_arg')
  
def mkBZero(loc, zname='bzero', ty=None):
  return ResolvedVar(loc, ty, zname)

def mkIncDub(loc, arg, cname='inc_dub', ty=None):
  return Call(loc, ty, ResolvedVar(loc, None, cname), [arg])

def mkDubInc(loc, arg, cname='dub_inc', ty=None):
  return Call(loc, ty, ResolvedVar(loc, None, cname), [arg])

def uint_inc(loc, x):
    if isBZero(x):
        return mkIncDub(loc, x)
    elif isDubInc(x):
        return mkIncDub(loc, uint_inc(loc, get_arg(x)))
    elif isIncDub(x):
        return mkDubInc(loc, get_arg(x))
    else:
        error(loc, 'not a UInt constructor: ' + str(x))

# The parsers use this function to create unsigned integer literals.
def intToUInt(loc, n, bzero='bzero', dubinc='dub_inc',
              incdub='inc_dub', uint_ty=None):
    if n == 0:
        return mkBZero(loc, bzero, uint_ty)
    else:
        return uint_inc(loc, intToUInt(loc, n - 1, bzero, dubinc, incdub, uint_ty))
    
def mkZero(loc, zname='zero', ty=None):
  # Use OverloadedVar when the name is already uniquified (contains
  # '.'), otherwise a pre-uniquify Var. Fast-arithmetic call sites
  # in the type checker pass uniquified names extracted from the
  # existing AST; parser call sites pass the bare source name.
  if '.' in zname:
    return ResolvedVar(loc, ty, zname)
  return Var(loc, ty, zname)

def mkSuc(loc, arg, sname='suc', ty=None):
  if '.' in sname:
    rator = ResolvedVar(loc, None, sname)
  else:
    rator = Var(loc, None, sname)
  return Call(loc, ty, rator, [arg])

def intToNat(loc, n, zname='zero', sname='suc', ty=None):
  if n <= 0:
    return mkZero(loc, zname=zname, ty=ty)
  else:
    return mkSuc(loc, intToNat(loc, n - 1, zname=zname, sname=sname, ty=ty),
                 sname=sname, ty=ty)

def isNat(t):
  match t:
    case (OverloadedVar(loc, tyof, [n, *_]) | ResolvedVar(loc, tyof, n)) if base_name(n) == 'zero':
      return True
    case Call(loc, tyof1, (OverloadedVar(loc2, tyof2, [n, *_]) | ResolvedVar(loc2, tyof2, n)), [arg]) \
         if base_name(n) == 'suc':
      return isNat(arg)
    case Call(loc, tyof1, (OverloadedVar(loc2, tyof2, [n, *_]) | ResolvedVar(loc2, tyof2, n)), [arg]) \
         if base_name(n) == 'lit':
      return isNat(arg)
    case _:
      return False

def isLitNat(t):
  match t:
    case Call(loc, tyof1, (OverloadedVar(loc2, tyof2, [n, *_]) | ResolvedVar(loc2, tyof2, n)), [arg]) \
         if base_name(n) == 'lit':
      return isNat(arg)
    case _:
      return False

def isLitUInt(t):
  match t:
    case Call(loc, tyof1, (OverloadedVar(loc2, tyof2, [n, *_]) | ResolvedVar(loc2, tyof2, n)), [arg]) \
         if base_name(n) == 'fromNat':
      return isLitNat(arg)
    case _:
      return False
  
def isInt(t):
  match t:
    case Call(loc, tyof1, (OverloadedVar(loc2, tyof2, [n, *_]) | ResolvedVar(loc2, tyof2, n)), [arg]) \
      if base_name(n) == 'pos':
      return isUInt(arg)
    case Call(loc, tyof1, (OverloadedVar(loc2, tyof2, [n, *_]) | ResolvedVar(loc2, tyof2, n)), [arg]) \
      if base_name(n) == 'negsuc':
      return isUInt(arg)
    case _:
      return False
  
def getZero(t):
  match t:
    case (OverloadedVar(loc, tyof, [n, *_]) | ResolvedVar(loc, tyof, n)) if base_name(n) == 'zero':
      return n
    case Call(loc, tyof1, (OverloadedVar(loc2, tyof2, [n, *_]) | ResolvedVar(loc2, tyof2, n)), [arg]) \
      if base_name(n) == 'suc':
      return getZero(arg)
    case _:
      return False

def getSuc(t):
  match t:
    case (OverloadedVar(loc, tyof, [n, *_]) | ResolvedVar(loc, tyof, n)) if base_name(n) == 'zero':
      return False
    case Call(loc, tyof1, (OverloadedVar(loc2, tyof2, [n, *_]) | ResolvedVar(loc2, tyof2, n)), [arg]) \
      if base_name(n) == 'suc':
      return n
    case _:
      return False

def natToInt(t):
  match t:
    case (OverloadedVar(loc, tyof, [n, *_]) | ResolvedVar(loc, tyof, n)) if base_name(n) == 'zero':
      return 0
    case Call(loc, tyof1, (OverloadedVar(loc2, tyof2, [n, *_]) | ResolvedVar(loc2, tyof2, n)), [arg]) \
      if base_name(n) == 'suc':
      return 1 + natToInt(arg)
    case Call(loc, tyof1, (OverloadedVar(loc2, tyof2, [n, *_]) | ResolvedVar(loc2, tyof2, n)), [arg]) \
      if base_name(n) == 'lit':
      return natToInt(arg)
    case _:
      raise Exception('natToInt: not a Nat: ' + str(t))

def uintToInt(t):
  match t:
    case (OverloadedVar(loc, tyof, [n, *_]) | ResolvedVar(loc, tyof, n)) if base_name(n) == 'bzero':
      return 0
    case Call(loc, tyof1, (OverloadedVar(loc2, tyof2, [n, *_]) | ResolvedVar(loc2, tyof2, n)), [arg]) \
      if base_name(n) == 'dub_inc':
      return 2 * (1 + uintToInt(arg))
    case Call(loc, tyof1, (OverloadedVar(loc2, tyof2, [n, *_]) | ResolvedVar(loc2, tyof2, n)), [arg]) \
      if base_name(n) == 'inc_dub':
      return 1 + 2 * uintToInt(arg)
    case Call(loc, tyof1, (OverloadedVar(loc2, tyof2, [n, *_]) | ResolvedVar(loc2, tyof2, n)), [arg]) \
      if base_name(n) == 'fromNat':
      return natToInt(arg)
    case _:
      raise Exception('uintToInt: not a uint ' + str(t))

def mkUIntLit(loc, num):
    return Call(loc, None, Var(loc, None, 'fromNat'),
                [Call(loc, None, Var(loc, None, 'lit'),
                      [intToNat(loc, num)])])
  
def mkPos(loc, arg):
  return Call(loc, None, Var(loc, None, 'pos'), [arg])

def mkNeg(loc, arg):
  return Call(loc, None, Var(loc, None, 'negsuc'), [arg])

# The following is used in the parser.
def mkIntLit(loc, n, sign):
  if sign == 'PLUS':
    return mkPos(loc, mkUIntLit(loc, n))
  else:
    return mkNeg(loc, mkUIntLit(loc, n - 1))

def isDeduceInt(t):
  match t:
    case Call(loc, tyof1, (Var(loc2, tyof2, name) | OverloadedVar(loc2, tyof2, [name, *_]) | ResolvedVar(loc2, tyof2, name)), [arg]) if base_name(name) == 'pos':
      return isUInt(arg)
    case Call(loc, tyof1, (Var(loc2, tyof2, name) | OverloadedVar(loc2, tyof2, [name, *_]) | ResolvedVar(loc2, tyof2, name)), [arg]) if base_name(name) == 'negsuc':
      return isUInt(arg)
    case _:
      return False

def deduceIntToInt(t):
  match t:
    case Call(loc, tyof1, (Var(loc2, tyof2, name) | OverloadedVar(loc2, tyof2, [name, *_]) | ResolvedVar(loc2, tyof2, name)), [arg]) if base_name(name) == 'pos':
      return '+' + str(uintToInt(arg))
    case Call(loc, tyof1, (Var(loc2, tyof2, name) | OverloadedVar(loc2, tyof2, [name, *_]) | ResolvedVar(loc2, tyof2, name)), [arg]) if base_name(name) == 'negsuc':
      return '-' + str(1 + uintToInt(arg))
    case _:
      error(t.location, 'deduceIntToInt: expected an int, not ' + str(t))

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

def is_constr_term(term, env):
  if isinstance(term, VarRef):
    return is_constructor(term.get_name(), env)
  match term:
    case TermInst(loc, ty, body):
      return is_constr_term(body, env)
    case _:
      return False

def constr_name(term):
  if isinstance(term, VarRef):
    return term.get_name()
  match term:
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

def _is_named(node, base):
  if isinstance(node, OverloadedVar):
    return base_name(node.resolved_names[0]) == base
  if isinstance(node, ResolvedVar):
    return base_name(node.name) == base
  return False

def isNodeList(t):
  match t:
    case TermInst(loc2, tyof2, ctor, tyargs, inferred) if _is_named(ctor, 'empty'):
      return True
    case Call(loc, tyof1, TermInst(loc2, tyof2, ctor, tyargs, inferred),
              [arg, ls]) if _is_named(ctor, 'node'):
      return isNodeList(ls)
    case _:
      return False

def nodeListToList(t):
  match t:
    case TermInst(loc2, tyof2, ctor, tyargs, inferred) if _is_named(ctor, 'empty'):
      return []
    case Call(loc, tyof1, TermInst(loc2, tyof2, ctor, tyargs, inferred),
              [arg, ls]) if _is_named(ctor, 'node'):
      return [arg] + nodeListToList(ls)

def nodeListToString(t):
  match t:
    case TermInst(loc2, tyof2, ctor, tyargs, inferred) if _is_named(ctor, 'empty'):
      return ''
    case Call(loc, tyof1, TermInst(loc2, tyof2, ctor, tyargs, inferred),
              [arg, ls]) if _is_named(ctor, 'node'):
      return str(arg) + ', ' + nodeListToString(ls)

def mkEmpty(loc):
  return Var(loc, None, 'empty')

def mkNode(loc, arg, ls):
  return Call(loc, None, Var(loc, None, 'node'), [arg, ls])

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

@dataclass(kw_only=True)
class Binding(AST):
  module : str
  visibility : str = 'public'

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

@dataclass
class AutoEquationBinding(Binding):
  equations : List[Formula]
  
  def __str__(self):
    return ', '.join([str(e) for e in self.equations])


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

  # This is a hack. Not reliable. Added for GenRecFun.
  def base_to_unique(self, name):
    for k in self.dict.keys():
      if base_name(k) == name:
        return k
    return None

  def base_to_overloads(self, name):
    overloads = []
    for k in self.dict.keys():
      if base_name(k) == name:
        overloads.append(k)
    return overloads

  def __str__(self):
    return ',\n'.join(['\t' + name2str(k) + ': ' + str(v) \
                       for (k,v) in reversed(self.dict.items())])

  def __contains__(self, item):
    return item in self.dict.keys()
    
  def proofs_str(self):
    return ',\n'.join(['\t' + name2str(k) + ': ' + str(v) \
                       for (k,v) in reversed(self.dict.items()) \
                       if isinstance(v,ProofBinding) and (v.local or get_verbose() == VerboseLevel.FULL)])

  def term_vars_str(self):
    return ',\n'.join(['\t' + base_name(k) + ': ' + str(v.typ) \
                       for (k,v) in reversed(self.dict.items()) \
                       if isinstance(v,TermBinding) and v.local])
  
  def declare_type(self, loc, name, vis = 'public'):
    new_env = Env(self.dict)
    new_env.dict[name] = TypeBinding(loc, module=self.get_current_module(), visibility=vis)
    return new_env

  def declare_type_vars(self, loc, type_vars):
    new_env = self
    for x in type_vars:
      new_env = new_env.declare_type(loc, x)
    return new_env
  
  def define_type(self, loc, name, defn, visibility = 'public'):
    if defn == None:
      error(loc, 'None not allowed in define_type')
    new_env = Env(self.dict)
    new_env.dict[name] = TypeBinding(loc, defn, module=self.get_current_module(), visibility=visibility)
    return new_env
  
  def declare_term_var(self, loc, name, typ, local = False, visibility='public'):
    if typ == None:
      error(loc, 'None not allowed as type of variable in declare_term_var')
    new_env = Env(self.dict)
    new_env.dict[name] = TermBinding(loc, typ, module=self.get_current_module(), visibility=visibility)
    new_env.dict[name].local = local
    return new_env

  def declare_assoc(self, loc, opname, typarams, typ):
    #print('declaring assoc ' + opname + ' ' + str(typ))
    new_env = Env(self.dict)
    full_name = '__associative_' + opname
    if full_name in new_env:
      old = new_env.dict[full_name]
      new_env.dict[full_name] = AssociativeBinding(loc, opname, [(typarams, typ)] + old.types,
                                                   module=self.get_current_module())
    else:
      new_env.dict[full_name] = AssociativeBinding(loc, opname, [(typarams, typ)],
                                                   module=self.get_current_module())
    return new_env

  def declare_auto_rewrite(self, loc, equation):
    new_env = Env(self.dict)
    full_name = '__auto__'
    (lhs,rhs) = split_equation(loc, equation, new_env)
    head_lhs = term_head(lhs)
    #print('declare auto: ' + head_lhs + '\n\t' + str(equation))
    if full_name in self.dict:
        if head_lhs in new_env.dict[full_name].equations:
            new_env.dict[full_name].equations[head_lhs].append(equation)
        else:
            new_env.dict[full_name].equations[head_lhs] = [equation]
    else:
        new_equations = {}
        new_equations[head_lhs] = [equation]
        if 'no_name' not in new_equations:
            new_equations['no_name'] = []
        new_env.dict[full_name] = AutoEquationBinding(loc, new_equations,
                                                      module=self.get_current_module())
    return new_env

  def get_auto_rewrites(self, head):
    full_name = '__auto__'
    if full_name in self.dict.keys():
        if head in self.dict[full_name].equations:
            return self.dict[full_name].equations[head]
        else:
            return self.dict[full_name].equations['no_name']
    else:
      return []

  def declare_inductive(self, loc, ind_dict, thm):
    new_env = Env(self.dict)
    full_name = '__inductive__'
    typ = ind_dict["ind_ty"]
    ind_dict["thm"] = thm
    type_name = get_type_name(typ).name

    if full_name in new_env.dict:
      if type_name in new_env.dict[full_name]:
        pass
      else:
        new_env.dict[full_name][type_name] = ind_dict
      # Check for type, overwrite/ add to existing
      pass
    else:
      new_env.dict[full_name] = {}
      new_env.dict[full_name][type_name] = ind_dict
    
    return new_env

  def get_inductive(self, typ):
    full_name = '__inductive__'
    type_name = get_type_name(typ).name
    if full_name in self.dict:
      if type_name in self.dict[full_name]:
        return self.dict[full_name][type_name]

    return None

  def declare_term_vars(self, loc, xty_pairs, local = False):
    new_env = self
    for (x,ty) in xty_pairs:
      new_env = new_env.declare_term_var(loc, x, ty, local)
    return new_env
  
  def define_term_var(self, loc, name, typ, val, visibility='public'):
    if False and typ == None:
      error(loc, 'None not allowed as type in define_term_var')
    if val == None:
      error(loc, 'None not allowed as value in define_term_var')
    new_env = Env(self.dict)
    new_env.dict[name] = TermBinding(loc, typ, val, module=self.get_current_module(),
                                     visibility=visibility)
    return new_env

  def define_term_vars(self, loc, xv_pairs):
    new_env = self
    for (x,v) in xv_pairs:
      new_env = new_env.define_term_var(loc, x, None, v)
    return new_env
  
  def declare_proof_var(self, loc, name, frm):
    new_env = Env(self.dict)
    new_env.dict[name] = ProofBinding(loc, frm, False, module=self.get_current_module())
    return new_env

  def declare_local_proof_var(self, loc, name, frm):
    new_env = Env(self.dict)
    new_env.dict[name] = ProofBinding(loc, frm, True, module=self.get_current_module())
    return new_env

  def declare_module(self, module):
    new_env = Env(self.dict)
    new_env.dict['__current_module__'] = module
    return new_env
  
  def declare_tracing(self, function_name: str):
    new_env = Env(self.dict)
    if 'tracing' not in new_env.dict:
      new_env.dict['tracing'] = set()
    new_env.dict['tracing'].add(function_name)
    return new_env

  def get_current_module(self):
      return self.dict['__current_module__']
  
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

  def _term_var_defined(self, curr, name):
    if name in curr.keys():
      binding = curr[name]
      if isinstance(binding, TermBinding) or isinstance(binding, TypeBinding):
        return True
    return False

  def _value_of_term_var(self, curr, name):
    if name in curr.keys(): # the name '=' is not in the env
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
                        + '\nPerhaps you meant `expand ' + base_name(name) + '`?')
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
    if isinstance(tyname, VarRef):
      return tyname.get_name() in self.dict.keys()
    raise Exception('expected a type name, not ' + str(tyname))

  def term_var_is_defined(self, tvar):
    match tvar:
      case OverloadedVar(loc, tyof, resolved_names):
        return any([self._term_var_defined(self.dict, x) for x in resolved_names])
      case ResolvedVar(loc, tyof, name):
        return self._term_var_defined(self.dict, name)
      case Var(loc, tyof, name):
        return self._term_var_defined(self.dict, name)
        
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
    if isinstance(var, VarRef):
      return self._def_of_type_var(self.dict, var.get_name())
    raise Exception('get_def_of_type_var: unexpected ' + str(var))
      
  def get_formula_of_proof_var(self, pvar):
    match pvar:
      case PVar(loc, name):
        return self._formula_of_proof_var(self.dict, name)
      case _:
        raise Exception('get_formula_of_proof_var: expected PVar, not ' + str(pvar))
          
  def get_type_of_term_var(self, tvar):
    match tvar:
      case OverloadedVar(loc, tyof, resolved_names):
        looked_up = [(x, self._type_of_term_var(self.dict, x)) for x in resolved_names]
        # Drop candidates not in env (e.g., overloads from modules
        # that haven't been imported here).
        overloads = [(x, ty) for (x, ty) in looked_up if ty is not None]
        if len(overloads) == 0:
          return None
        if len(overloads) > 1:
          return OverloadType(loc, overloads)
        return overloads[0][1]
      case ResolvedVar(loc, tyof, name):
        return self._type_of_term_var(self.dict, name)
      case Var(loc, tyof, name):
        return self._type_of_term_var(self.dict, name)

  def get_value_of_term_var(self, tvar):
    if isinstance(tvar, VarRef):
      return self._value_of_term_var(self.dict, tvar.get_name())
      
  def get_tracing(self, function_name: str) -> bool:
    return 'tracing' in self.dict and function_name in self.dict['tracing']

  def local_proofs(self):
    return [b.formula for (name, b) in self.dict.items() \
            if isinstance(b, ProofBinding) and b.local]

  def proofs(self):
    return [b.formula for (name, b) in self.dict.items() \
            if isinstance(b, ProofBinding)]

collected_imports = set()

def collect_public(s, to_print):
    global collected_imports
    if isinstance(s, Theorem) and not s.isLemma:
      to_print.append(s)
    elif isinstance(s, Postulate):
      to_print.append(s)
    elif isinstance(s, Auto):
      to_print.append(s)
    elif isinstance(s, Import):
      if s.name in collected_imports:
          return
      collected_imports.add(s.name)
      if s.ast != None and s.visibility == 'public':
        for stmt in s.ast:
            collect_public(stmt, to_print)
    elif isinstance(s, Declaration) and not s.visibility == 'private':
      to_print.append(s)

def print_theorems_statement(s, f):
    if isinstance(s, Theorem) and not s.isLemma:
        print(base_name(s.name) + ': ' + str(s.what) + '\n', file=f)
    elif isinstance(s, Postulate):
      print(base_name(s.name) + ': ' + str(s.what) + '\n', file=f)
    elif isinstance(s, Auto):
      print('auto ' + str(s.name) + '\n', file=f)
    elif isinstance(s, Declaration) and not s.visibility == 'private':
      print(s.pretty_print(0), file=f)
      
def print_theorems(filename, ast):
  global collected_imports
  collected_imports = set()
  fullpath = Path(filename)
  theorem_filename = fullpath.with_suffix('.thm')
  to_print = []
  
  for s in ast:
    collect_public(s, to_print)
  
  if len(to_print) == 0:
    return
  
  with open(theorem_filename, 'w', encoding='utf-8') as theorem_file:
    print('This file was automatically generated by Deduce.', file=theorem_file)
    print('This file summarizes the theorems proved in the file:\n\t' + filename, file=theorem_file)
    print('', file=theorem_file)
    for s in sorted(to_print, key=lambda s: s.key()):
      print_theorems_statement(s, theorem_file)

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
    case Var() | OverloadedVar() | ResolvedVar():
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
    case GenRecFun(loc, name, typarams, params, returns, measure, measure_ty, body, trm):
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
    case Var() | OverloadedVar() | ResolvedVar():
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
    case Var() | OverloadedVar() | ResolvedVar():
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

# --------------------------------------------------------------------------
# AST sanity checks
#
# Phase invariants encoded by the class hierarchy:
#   - parser produces ``Var`` (source-name only)
#   - ``uniquify`` produces ``OverloadedVar`` (uniquified candidates)
#   - type checking narrows ``OverloadedVar`` to ``ResolvedVar`` (single
#     chosen name) where it can; genuinely-unresolved overloads stay
#     as multi-candidate ``OverloadedVar``
#
# These walkers verify the invariants by visiting every AST descendant
# of a top-level statement list. They're meant to run after each phase
# during development, and fail fast on stray pre-uniquify ``Var`` nodes
# left behind by helper functions that haven't been migrated to the
# new class hierarchy.
# --------------------------------------------------------------------------

def _walk_ast_descendants(roots):
  """Yield every AST descendant reachable from ``roots`` (a single
  node or an iterable). Memoized by ``id()`` so shared sub-ASTs
  (e.g. cached imported-module statements) aren't revisited."""
  from dataclasses import fields, is_dataclass
  seen = set()
  stack = []
  if isinstance(roots, list) or isinstance(roots, tuple):
    stack.extend(roots)
  else:
    stack.append(roots)
  while stack:
    node = stack.pop()
    nid = id(node)
    if nid in seen:
      continue
    seen.add(nid)
    yield node
    if isinstance(node, list) or isinstance(node, tuple):
      stack.extend(node)
      continue
    if isinstance(node, dict):
      stack.extend(node.values())
      continue
    if isinstance(node, AST) and is_dataclass(node):
      for f in fields(node):
        child = getattr(node, f.name, None)
        if child is None:
          continue
        # Skip strings explicitly — the bound-name lists in Lambda /
        # All / Some are str values that should not be walked.
        if isinstance(child, str):
          continue
        if isinstance(child, (int, bool)):
          continue
        stack.append(child)

def check_post_uniquify_invariants(ast_list):
  """Assert that the AST is in canonical post-uniquify shape: every
  variable reference is an ``OverloadedVar`` or ``ResolvedVar``; no
  pre-uniquify ``Var`` survives. ``ResolvedVar`` is allowed because
  some construction helpers (mkSuc/mkZero etc. for runtime
  arithmetic) already produce a fully-narrowed reference, and that's
  fine — it just means there's nothing for type-check to do.

  Raises ``Exception`` listing up to 20 offending nodes on failure."""
  bad = []
  for node in _walk_ast_descendants(ast_list):
    if type(node) is Var:
      bad.append((getattr(node, 'location', None), node.name))
  if bad:
    msgs = []
    for (loc, name) in bad[:20]:
      loc_str = ''
      try:
        if loc is not None and not getattr(loc, 'empty', True):
          loc_str = f'{loc.filename}:{loc.line}: '
      except Exception:
        pass
      msgs.append(f'  {loc_str}pre-uniquify Var({name!r})')
    suffix = f'\n  ... and {len(bad) - 20} more' if len(bad) > 20 else ''
    raise Exception(
      'Post-uniquify AST sanity check failed: pre-uniquify `Var` '
      'nodes still present.\n'
      'Each one is a leftover construction site that wasn\'t migrated '
      'to OverloadedVar/ResolvedVar.\n' + '\n'.join(msgs) + suffix)

def check_post_typecheck_invariants(ast_list):
  """Post-typecheck invariants. Hard error on any pre-uniquify ``Var``.
  Single-candidate ``OverloadedVar`` is currently a soft warning:
  the type checker doesn't visit proof bodies yet, so those leak
  OverloadedVars even when they aren't actually overloaded. The
  invariant will go strict once ``check_proof_of`` is refactored to
  rebuild proof ASTs (tracked separately).

  Multi-candidate ``OverloadedVar`` is permitted (genuine unresolved
  overload).
  """
  def loc_prefix(loc):
    try:
      if loc is not None and not getattr(loc, 'empty', True):
        return f'{loc.filename}:{loc.line}: '
    except Exception:
      pass
    return ''
  bad_var = []
  for node in _walk_ast_descendants(ast_list):
    if type(node) is Var:
      bad_var.append((getattr(node, 'location', None), node.name))
  if bad_var:
    msgs = [f'  {loc_prefix(loc)}pre-uniquify Var({name!r})'
            for (loc, name) in bad_var[:20]]
    raise Exception(
      'Post-typecheck AST sanity check failed: pre-uniquify `Var` '
      'nodes still present.\n' + '\n'.join(msgs))

def uniquify_deduce(ast):
  env = {}
  env['≠'] = ['≠']
  env['='] = ['=']
  # Using a space in the name to not collide with deduce identifiers
  env['no overload'] = {}
  result = [stmt.uniquify(env) for stmt in ast]
  check_post_uniquify_invariants(result)
  return result

def make_switch_for(meta, defs, subject, cases):
  new_cases = [SwitchProofCase(c.location, c.pattern, c.assumptions,
                               ApplyDefsGoal(meta, [ResolvedVar(meta, None, t) for t in defs],
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

      ret = Lambda(loc2, tyof, vars, explicit_term_inst(body))
      if hasattr(term, 'env'):
        ret.env = term.env
      return ret
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

num_rewrites = 0

def reset_num_rewrites():
    global num_rewrites
    num_rewrites = 0

def inc_rewrites():
    global num_rewrites
    num_rewrites = 1 + num_rewrites

def get_num_rewrites():
    global num_rewrites
    return num_rewrites

def rewrite_aux(loc, formula, equation, env, depth = -1):
  if depth == 0:
      return formula
  try:
    rhs = try_rewrite(loc, formula, equation, env)
    inc_rewrites()
    return rhs
  except MatchFailed as e:
    if get_verbose():
      print('\tno match')
    pass
  match formula:
    case TermInst(loc2, tyof, subject, tyargs, inferred):
      return TermInst(loc2, tyof, rewrite_aux(loc, subject, equation, env, depth - 1),
                      tyargs, inferred)
    case OverloadedVar() | ResolvedVar() | Var():
      return formula
    case Bool(loc2, tyof, val):
      return formula
    case And(loc2, tyof, args):
      return And(loc2, tyof, [rewrite_aux(loc, arg, equation, env, depth - 1) for arg in args])
    case Or(loc2, tyof, args):
      return Or(loc2, tyof, [rewrite_aux(loc, arg, equation, env, depth - 1) for arg in args])
    case IfThen(loc2, tyof, prem, conc):
      return IfThen(loc2, tyof, rewrite_aux(loc, prem, equation, env, depth - 1),
                    rewrite_aux(loc, conc, equation, env, depth - 1))
    case All(loc2, tyof, var, pos, frm2):
      return All(loc2, tyof, var, pos, rewrite_aux(loc, frm2, equation, env, depth - 1))
    case Some(loc2, tyof, vars, frm2):
      return Some(loc2, tyof, vars, rewrite_aux(loc, frm2, equation, env, depth - 1))
    case Call(loc2, tyof, rator, args):
      is_assoc = is_associative(loc2, rator_name(rator), formula.typeof, env)
      if get_verbose():
          print('is_assoc? ' + str(is_assoc))
      if is_assoc:
          # args = sum([flatten_assoc(rator_name(rator), arg) for arg in args], [])
          args = flatten_assoc_list(rator_name(rator), args)
      new_rator = rewrite_aux(loc, rator, equation, env, depth - 1)
      new_args = [rewrite_aux(loc, arg, equation, env, depth - 1) for arg in args]
      if False and get_verbose():
          print('while trying to rewrite ' + str(formula) + '\n\twith equation ' + str(equation))
          print('new_args: ' + ', '.join([str(arg) for arg in new_args]))
      (lhs,rhs) = split_equation(loc2, equation, env)
      arity = call_arity(lhs)
      if get_verbose():
          print('lhs = ' + str(lhs) + '\n\tarity: ' + str(arity)) 
      if is_assoc and len(new_args) > arity and arity > 1:
        # try to rewrite each arity-number of adjacent terms
        i = 0
        output_terms = []
        while i + arity <= len(new_args):
            call_args = new_args[i : i + arity]
            tmp = Call(loc2, tyof, new_rator, call_args)
            old_num_rewrites = get_num_rewrites()
            try:
               new_tmp = rewrite_aux(loc, tmp, equation, env, depth)
            except MatchFailed as e:
               new_tmp = tmp
            new_num_rewrites = get_num_rewrites()
            if new_num_rewrites == old_num_rewrites:
                if get_verbose():
                    print('replace using: ' + str(equation) \
                          + '\n\tdid not match: ' + str(tmp))
                output_terms.append(new_args[i])
                i = i + 1
            else:
                flat_tmp = flatten_assoc(rator_name(rator), new_tmp)
                if get_verbose():
                    print('rewrote: ' + str(tmp) + '\n\tinto: ' \
                          + ', '.join([str(a) for a in flat_tmp]))
                output_terms += flat_tmp
                i = i + arity
        if i < len(new_args):
            output_terms += new_args[i:]
        if len(output_terms) > 1:
            return Call(loc2, tyof, new_rator, output_terms)
        else:
            return output_terms[0]
      else: # not an associative rator
        call = Call(loc2, tyof, new_rator, new_args)
        if hasattr(formula, 'type_args'):
          call.type_args = formula.type_args
        return call
  
    case Switch(loc2, tyof, subject, cases):
      return Switch(loc2, tyof, rewrite_aux(loc, subject, equation, env, depth - 1),
                    [rewrite_aux(loc, c, equation, env, depth - 1) for c in cases])
    case SwitchCase(loc2, pat, body):
      return SwitchCase(loc2, pat, rewrite_aux(loc, body, equation, env, depth - 1))
    case RecFun(loc, name, typarams, params, returns, cases):
      return formula
    case Conditional(loc2, tyof, cond, thn, els):
      return Conditional(loc2, tyof, rewrite_aux(loc, cond, equation, env, depth - 1),
                         rewrite_aux(loc, thn, equation, env, depth - 1),
                         rewrite_aux(loc, els, equation, env, depth - 1))
    case Lambda(loc2, tyof, vars, body):
      return Lambda(loc2, tyof, vars, rewrite_aux(loc, body, equation, env, depth - 1))
  
    case Generic(loc2, tyof, typarams, body):
      return Generic(loc2, tyof, typarams, rewrite_aux(loc, body, equation, env, depth - 1))
  
    case TAnnote(loc2, tyof, subject, typ):
      return TAnnote(loc, tyof, rewrite_aux(loc, subject, equation, env, depth - 1), typ)

    case ArrayGet(loc2, tyof, arr, ind):
      return ArrayGet(loc, tyof, rewrite_aux(loc, arr, equation, env, depth - 1),
                      rewrite_aux(loc, ind, equation, env, depth - 1))
  
    case TLet(loc2, tyof, var, rhs, body):
      return TLet(loc2, tyof, var, rewrite_aux(loc, rhs, equation, env, depth - 1),
                  rewrite_aux(loc, body, equation, env, depth - 1))
  
    case Hole(loc2, tyof):
      return formula

    case Omitted(loc2, tyof):
      return formula
  
    case Mark(loc, tyof, subject):
      return Mark(loc, tyof, rewrite_aux(loc, subject, equation, env, depth - 1))
  
    case _:
      error(loc, 'internal error in rewrite function, unhandled ' + str(formula))

def try_rewrite(loc, formula, equation, env):
  (lhs, rhs) = split_equation(loc, equation, env)
  if False and get_verbose():
      print('try rewrite? ' + str(formula) + '\n\twith equation ' + str(equation))
  matching = {}
  eq_vars = equation_vars(equation)
  formula_match(loc, eq_vars, lhs, formula, matching, Env())
  # print('rewriting using: ' + str(equation) + '\n' \
  #       + '\t' + str(formula) \
  #       + '\t==> ' + str(rhs.substitute(matching)) + '\n')
  if False and get_verbose():
      print('\tmatched LHS, rewriting to the RHS: ' + str(rhs.substitute(matching)))
  return rhs.substitute(matching).reduce(env)

def formula_match(loc, vars, pattern_frm, frm, matching, env):
  if False and get_verbose():
    print("formula_match:\n\t" + str(pattern_frm) + "\n\t" + str(frm) + "\n")
    print("\tin  " + ','.join([str(x) for x in vars]))
    print("\twith " + ','.join([x + ' := ' + str(f) for (x,f) in matching.items()]))
  match (pattern_frm, frm):
    case (TermInst(loc1, tyof1, subject1, tyargs1, inferred1),
          TermInst(loc2, tyof2, subject2, tyargs2, inferred2)) \
          if len(tyargs1) == len(tyargs2):
      try:
        matching2 = dict(matching)
        for (t1,t2) in zip(tyargs1, tyargs2):
          formula_match(loc, vars, t1, t2, matching2, env)
        formula_match(loc, vars, subject1, subject2, matching2, env)
        matching.clear()
        matching.update(matching2)
      except MatchFailed as ex:
        formula_match(loc, vars, subject1, frm, matching, env)
        
    case (TermInst(loc2, tyof, subject, tyargs, inferred), _):
      formula_match(loc, vars, subject, frm, matching, env)
      
    case (_, TermInst(loc2, tyof, subject, tyargs, inferred)):
      formula_match(loc, vars, pattern_frm, subject, matching, env)
      
    case _ if isinstance(pattern_frm, VarRef) and isinstance(frm, VarRef) \
              and pattern_frm.get_name() == frm.get_name():
      pass
    case _ if isinstance(pattern_frm, VarRef) and pattern_frm in vars:
      tyvar_name = pattern_frm.get_name()
      if tyvar_name in matching.keys():
        formula_match(loc, vars, matching[tyvar_name], frm, matching, env)
      else:
        if get_verbose():
            print("formula_match, " + base_name(tyvar_name) + ' := ' + str(frm))
        matching[tyvar_name] = frm
        
    case (Call(loc2, tyof2, goal_rator, goal_rands),
          Call(loc3, tyof3, rator, rands)):
      if False and get_verbose():
          print("matching Call with Call\n\trator pattern: " + str(goal_rator) + '\n'\
                + '\trator formula: ' + str(rator))
      formula_match(loc, vars, goal_rator, rator, matching, env)
      if len(rands) >= len(goal_rands):
        while len(rands) > 0:
          # What is the following for? -Jeremy
          if len(goal_rands) == 1 and len(rands) > 1:
              rand = Call(loc3, tyof3, rator, rands)
              rands = []
          else:
              rand = rands[0]
              rands = rands[1:]
              
          goal_rand = goal_rands[0]
          goal_rands = goal_rands[1:]
            
          new_goal_rand = goal_rand.substitute(matching)
          formula_match(loc, vars, new_goal_rand, rand, matching, env)
          
      else:
        match_failed(loc, "formula: " + str(frm) + "\n" \
                     + "does not match expected formula: " + str(pattern_frm))
        
    case (And(loc2, tyof2, goal_args),
          And(loc3, tyof3, args)):
      for (goal_arg, arg) in zip(goal_args, args):
          new_goal_arg = goal_arg.substitute(matching)
          formula_match(loc, vars, new_goal_arg, arg, matching, env)
    case (Or(loc2, tyof2, goal_args),
          Or(loc3, tyof3, args)):
      for (goal_arg, arg) in zip(goal_args, args):
          new_goal_arg = goal_arg.substitute(matching)
          formula_match(loc, vars, new_goal_arg, arg, matching, env)
    case (IfThen(loc2, tyof2, goal_prem, goal_conc),
          IfThen(loc3, tyof3, prem, conc)):
      formula_match(loc, vars, goal_prem, prem, matching, env)
      new_goal_conc = goal_conc.substitute(matching)
      formula_match(loc, vars, new_goal_conc, conc, matching, env)
    # UNDER CONSTRUCTION
    case _:
      red_pattern = pattern_frm.reduce(env)
      red_frm = frm.reduce(env)
      if red_pattern != red_frm:
          match_failed(loc, "formula: " + str(red_frm) + "\n" \
                       + "does not match expected formula: " + str(red_pattern))

def call_arity(call):
    match call:
      case Call(loc2, tyof, rator, args):
        return len(args)
      case _:
        return 1 #raise Exception('call_arity: not a call ' + str(call))

def term_head(term):
    match term:
      case Call(loc, ty1, rator, args):
          return base_name(rator_name(rator)) # TODO: remove base_name -Jeremy
      case _:
          return 'no_name'
    
def auto_rewrites(term, env):
    orig_term = term
    # Iterate until we can't rewrite anymore (to a fixed point)
    while True:
        current = get_num_rewrites()
        # Grab all the equations that are applicable to the head constructor
        equations = env.get_auto_rewrites(term_head(term))
        # Rewrite using the first equation that matches 
        for eq in equations:
            current_eq = get_num_rewrites()
            term = rewrite_aux(term.location, term, eq, env, 1)
            if current_eq < get_num_rewrites():
               break
        if current == get_num_rewrites():
            break
    return term        
