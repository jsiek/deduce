from error import error
from abstract_syntax import *

@dataclass
class Binding(AST):
  pass

@dataclass
class TypeBinding(Binding):
  defn : AST = None
  
  def __str__(self):
    return str(self.defn)
  
  def shift_type_vars(self, cutoff, amount):
    return TypeBinding(self.location,
                       self.defn.shift_type_vars(cutoff, amount))
  
  def shift_term_vars(self, cutoff, amount):
    return TypeBinding(self.location,
                       self.defn.shift_term_vars(cutoff, amount))
  
@dataclass
class TermBinding(Binding):
  typ : Type
  defn : Term = None
  
  def __str__(self):
    return str(self.typ) + ' = ' + str(self.defn)

  def shift_type_vars(self, cutoff, amount):
    return TermBinding(self.location,
                       self.typ.shift_type_vars(cutoff, amount),
                       self.defn.shift_type_vars(cutoff, amount))
  
  def shift_term_vars(self, cutoff, amount):
    if self.defn:
      new_defn = self.defn.shift_term_vars(cutoff, amount)
    else:
      new_defn = None
    return TermBinding(self.location,
                       self.typ.shift_term_vars(cutoff, amount),
                       new_defn)
  
@dataclass
class ProofBinding(Binding):
  formula : Formula
  
  def __str__(self):
    return str(self.formula)

  def shift_type_vars(self, cutoff, amount):
    return ProofBinding(self.location, self.formula.shift_type_vars(cutoff, amount))
  
  def shift_term_vars(self, cutoff, amount):
    return ProofBinding(self.location, self.formula.shift_term_vars(cutoff, amount))
  
class Env:
  def __init__(self, env = None):
    if env:
      self.dict = copy_dict(env)
    else:
      self.dict = {}

  def __str__(self):
    return ','.join([k + ': ' + str(v) for (k,v) in self.dict.items()])

  def __repr__(self):
    return repr(self.dict)
  
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
    new_env = Env(self.dict)
    new_env.dict[name] = TypeBinding(loc, defn)
    return new_env
  
  def declare_term_var(self, loc, name, typ):
    new_env = Env(self.dict)
    new_env.dict[name] = TermBinding(loc, typ)
    return new_env

  def declare_term_vars(self, loc, xty_pairs):
    new_env = self
    for (x,ty) in xty_pairs:
      new_env = new_env.declare_term_var(loc, x, ty)
    return new_env
  
  def define_term_var(self, loc, name, typ, val):
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
    new_env.dict[name] = ProofBinding(loc, frm)
    return new_env

  def _def_of_type_var(self, curr, name, index):
    if name in curr.keys():
      return curr[name].defn
    else:
      raise Exception('variable not in env: ' + name)
  
  def _type_of_term_var(self, curr, name, index):
    if name in curr.keys():
      return curr[name].typ
    else:
      return None

  def _value_of_term_var(self, curr, name, index):
    if name in curr.keys():
      return curr[name].defn
    else:
      return None
  
  def _formula_of_proof_var(self, curr, name, index):
    if name in curr.keys():
      return curr[name].formula
    else:
      return None
    
  def type_var_is_defined(self, tyname):
    match tyname:
      case TypeName(loc, name, index):
        return name in self.dict.keys()
      case _:
        raise Exception('expected a type name, not ' + str(tyname))

  def term_var_is_defined(self, tvar):
    match tvar:
      case TVar(loc, name, index):
        if self._type_of_term_var(self.dict, name, index):
          return True
        else:
          return False
      case _:
        raise Exceptiona('expected a term variable, not ' + str(tvar))
        
  def proof_var_is_defined(self, pvar):
    match pvar:
      case PVar(loc, name, index):
        if self._formula_of_proof_var(self.dict, name, index):
          return True
        else:
          return False
      case _:
        raise Exception('expected proof var, not ' + str(pvar))
    
  def get_def_of_type_var(self, var):
    match var:
      case TypeName(loc, name, index):
        return self._def_of_type_var(self.dict, name, index)
      case _:
        raise Exception('get_def_of_type_var: unexpected ' + str(var))
      
  def get_formula_of_proof_var(self, pvar):
    match pvar:
      case PVar(loc, name, index):
        return self._formula_of_proof_var(self.dict, name, index)
      case _:
        raise Exception('get_formula_of_proof_var: expected PVar, not ' + str(pvar))
          
  def get_type_of_term_var(self, tvar):
    match tvar:
      case TVar(loc, name, index):
        return self._type_of_term_var(self.dict, name, index)

  def get_value_of_term_var(self, tvar):
    match tvar:
      case TVar(loc, name, index):
        return self._value_of_term_var(self.dict, name, index)
