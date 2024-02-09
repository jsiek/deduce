from dataclasses import dataclass
from lark.tree import Meta
from typing import Any, Tuple, List

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
  
  def __str__(self):
    return self.name

  def __repr__(self):
    return str(self)

  def __eq__(self, other):
    if not isinstance(other, TypeName):
      return False
    return self.name == other.name

@dataclass
class IntType(Type):
    
  def __str__(self):
    return 'int'

  def __repr__(self):
    return str(self)

  def __eq__(self, other):
    return isinstance(other, IntType)

@dataclass
class BoolType(Type):
  def __str__(self):
    return 'bool'

  def __repr__(self):
    return str(self)

  def __eq__(self, other):
    return isinstance(other, BoolType)

@dataclass
class TypeType(Type):
  def __str__(self):
    return 'type'

  def __repr__(self):
    return str(self)

  def __eq__(self, other):
    return isinstance(other, TypeType)
  
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
          ret = ret and type_equal(pt1, pt2)
        return ret and type_equal(self.return_type, rt2)
      case _:
        return False
      
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
class TAnnote(Term):
  subject: Term
  typ: Type

  def __str__(self):
      return str(self.subject) + ':' + str(self.typ)
    
  def __repr__(self):
      return str(self)
    
  def reduce(self, env):
    return self.subject.reduce(env)
  
  def substitute(self, env):
    return TAnnote(self.location, self.subject.substitute(env), self.typ)
  
  
@dataclass
class TVar(Term):
  name: str

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
      if self.name in env:
          return env[self.name]
      else:
          return self
  
  def substitute(self, env):
      if self.name in env.keys():
          return env[self.name]
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

  def substitute(self, env):
      return self
  
@dataclass
class PrimitiveCall(Term):
  op: str
  args: list[Term]

  def __str__(self):
    if self.op == 'equal':
        return str(self.args[0]) + " = " + str(self.args[1])
    elif self.op == 'add':
        return str(self.args[0]) + " + " + str(self.args[1])
    else:
      return "." + self.op + ".(" + ",".join([str(arg) for arg in self.args]) + ")"

  def __repr__(self):
    return str(self)

  def __eq__(self, other):
      if not isinstance(other, PrimitiveCall):
          return False
      return self.op == other.op \
          and all([arg1 == arg2 for arg1,arg2 in zip(self.args, other.args)])

  def reduce(self, env):
      new_args = [arg.reduce(env) for arg in self.args]
      ret = None
      if self.op == 'add':
          if all([isinstance(arg, Int) for arg in new_args]):
              ret = Int(self.location, new_args[0].value + new_args[1].value)
      if self.op == 'max':
          if all([isinstance(arg, Int) for arg in new_args]):
              ret = Int(self.location, max(new_args[0].value, new_args[1].value))

      if ret == None:
          ret = PrimitiveCall(self.location, self.op, new_args)
      return ret

  def substitute(self, env):
      return PrimitiveCall(self.location, self.op,
                           [arg.substitute(env) for arg in self.args])

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

  def substitute(self, env):
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
      # to do: alpha-equivalence
      if not isinstance(other, Lambda):
          return False
      return self.vars == other.vars and self.body == other.body

  def reduce(self, env):
      return self

  def substitute(self, env):
      new_env = copy_dict(env)
      # alpha rename the parameters
      new_vars = [generate_name(p) for p in self.vars]
      for (v,new_v) in zip(self.vars, new_vars):
          new_env[v] = TVar(self.location, new_v)
      return Lambda(new_vars, self.body.substitute(new_env), name)

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
      ret = self.rator == other.rator \
          and all([arg1 == arg2 for arg1,arg2 in zip(self.args, other.args)])
      return ret

  def reduce(self, env):
      fun = self.rator.reduce(env)
      args = [arg.reduce(env) for arg in self.args]
      match fun:
        case Lambda(loc, vars, body):
          new_env = copy_dict(env)
          for (x,arg) in zip(vars, args):
            new_env[x] = arg
          ret = body.reduce(new_env)
        case RecFun(loc, name, typarams, params, returns, cases):
          first_arg = args[0]
          rest_args = args[1:]
          for fun_case in cases:
              subst = {}
              if is_match(fun_case.pattern, first_arg, subst):
                  new_env = copy_dict(env)
                  for (k,v) in subst.items():
                      new_env[k] = v.reduce(env)
                  for (k,v) in zip(fun_case.parameters, rest_args):
                      new_env[k] = v.reduce(env)
                  return fun_case.body.reduce(new_env)
          ret = Call(self.location, fun, args, self.infix)
        case _:
          ret = Call(self.location, fun, args, self.infix)
      # print('reduce call ' + str(self) + ' to ' + str(ret))
      return ret

  def substitute(self, env):
      return Call(self.location, self.rator.substitute(env),
                  [arg.substitute(env) for arg in self.args],
                  self.infix)

@dataclass
class SwitchCase(AST):
  pattern: Pattern
  body: Term
  
  def __str__(self):
      return 'case ' + str(self.pattern) + '{' + str(self.body) + '}'

  def __repr__(self):
      return str(self)

  def substitute(self, env):
      new_env = copy_dict(env)
      # alpha rename the parameters
      new_params = [generate_name(x) for x in self.pattern.parameters]
      for x, new_x in zip(self.pattern.parameters, new_params):
          new_env[x] = TVar(self.location, new_x)
      return SwitchCase(self.location,
                        PatternCons(self.pattern.constructor, new_params),
                        self.body.substitute(new_env))
  
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
            new_env = copy_dict(env)
            for x,v in subst.items():
              new_env[x] = v
            return c.body.reduce(new_env)
      return Switch(self.location, new_subject, self.cases)
  
  def substitute(self, env):
      return Switch(self.location, self.subject.substitute(env),
                    [c.substitute(env) for c in self.cases])
  

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

    
################ Formulas ######################################
  
@dataclass
class Bool(Formula):
  value: bool
  def __eq__(self, other):
      return self.value == other.value
  def __str__(self):
    return str(self.value)
  def __repr__(self):
    return str(self)
  def reduce(self, env):
    return self
  def substitute(self, env):
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

@dataclass
class Or(Formula):
  args: list[Formula]
  def __str__(self):
    return ' or '.join([str(arg) for arg in self.args])
  def __eq__(self, other):
      return all([arg1 == arg2 for arg1,arg2 in zip(self.args, other.args)])
  def reduce(self, env):
    return Or(self.location, [arg.reduce(env) for arg in self.args])

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

@dataclass
class Some(Formula):
  vars: list[Tuple[str,Type]]
  body: Formula

################ Proofs ######################################
  
@dataclass
class PVar(Proof):
  name: str

  def __str__(self):
      return str(self.name)
  
@dataclass
class PLet(Proof):
  label: str
  proved: Formula
  because: Proof
  body: Proof

  def __str__(self):
      return self.label + ': ' + str(self.proved) + ' because ' + str(self.because) + '; ' + str(self.body)

@dataclass
class PAnnot(Proof):
  claim: Formula
  reason: Proof

  def __str__(self):
      return 'have ' + str(self.claim) + ' because ' + str(self.reason)
  
@dataclass
class Cases(Proof):
  subject: Proof
  cases: List[Tuple[str,Proof]]

@dataclass
class Apply(Proof):
  implication: Proof
  arg: Proof

  def __str__(self):
      return 'apply ' + str(self.implication) + ' with ' + str(self.arg)

@dataclass
class ImpIntro(Proof):
  label: str
  premise: Formula
  body: Proof

  def __str__(self):
    return 'suppose ' + str(self.label) + ': ' + str(self.premise) + '{' + str(self.body) + '}'

@dataclass
class AllIntro(Proof):
  vars: List[Tuple[str,Type]]
  body: Proof

  def __str__(self):
    return 'arbitrary ' + ",".join([x + ":" + str(t) for (x,t) in self.vars]) \
        + '; ' + str(self.body)

@dataclass
class AllElim(Proof):
  univ: Proof
  args: List[Term]

  def __str__(self):
    return str(self.univ) + '[' + ','.join([str(arg) for arg in self.args]) + ']'


@dataclass
class PTuple(Proof):
  args: List[Proof]

  def __str__(self):
    return ', '.join([str(arg) for arg in self.args])
  
@dataclass
class PTrue(Proof):
  def __str__(self):
      return '.'

@dataclass
class PReflexive(Proof):
  def __str__(self):
      return 'reflexive'

@dataclass
class PHole(Proof):
  def __str__(self):
      return '?'
  
@dataclass
class PSymmetric(Proof):
  body: Proof
  def __str__(self):
      return 'symmetric'

@dataclass
class PTransitive(Proof):
  first: Proof
  second: Proof
  def __str__(self):
      return 'transitive'

@dataclass
class PInjective(Proof):
  body: Proof
  def __str__(self):
      return 'injective'
  
@dataclass
class IndCase(AST):
  pattern: Pattern
  body: Proof
    
@dataclass
class Induction(Proof):
  typ: str
  cases: List[IndCase]

  def __str__(self):
      return 'induction'

@dataclass
class SwitchProof(Proof):
  subject: Term
  cases: List[IndCase]

  def __str__(self):
      return 'switch proof'
    
@dataclass
class RewriteGoal(Proof):
  equation: Proof
  body: Proof

  def __str__(self):
      return 'rewrite_goal'

@dataclass
class RewriteFact(Proof):
  subject: Proof
  equation: Proof

  def __str__(self):
      return 'rewrite_fact'

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
    
@dataclass
class Constructor(AST):
    name: str
    parameters: List[Type]
    
@dataclass
class Union(Statement):
    name: str
    type_params: List[str]
    alternatives: List[Constructor]

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
  
@dataclass
class RecFun(Statement):
    name: str
    type_params: List[str]
    params: List[Type]
    returns: Type
    cases: List[FunCase]

    def __str__(self):
      return self.name

    def __repr__(self):
      return str(self)

    def __eq__(self, other):
        return self.name == other.name

    def reduce(self, env):
        return self
    
@dataclass
class Define(Statement):
  name: str
  body: Term

@dataclass
class Import(Statement):
  name: str
  

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

  
