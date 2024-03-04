from error import error
from abstract_syntax import *
from alist import *

@dataclass
class Binding(AST):
  pass

@dataclass
class TypeBinding(Binding):
  defn : AST = None

@dataclass
class TermBinding(Binding):
  typ : Type
  defn : Term = None

@dataclass
class ProofBinding(Binding):
  formula : Formula

class Env:
  def __init__(self, alist = None):
    self.alist = alist

  def __str__(self):
    return 'env:  ' + str_of_alist(self.alist)

  def declare_type(self, loc, name):
    return Env(cons(cons(name, TypeBinding(loc)), self.alist))

  def declare_type_vars(self, loc, type_vars):
    new_env = self
    for x in type_vars:
      new_env = new_env.declare_type(loc, x)
    return new_env
  
  def define_type(self, loc, name, defn):
    return Env(cons(cons(name, TypeBinding(loc, defn)), self.alist))
  
  def declare_term_var(self, loc, name, typ):
    return Env(cons(cons(name, TermBinding(loc, typ)), self.alist))

  def declare_term_vars(self, loc, xty_pairs):
    new_env = self
    for (x,ty) in xty_pairs:
      new_env = new_env.declare_term_var(x, ty)
    return new_env
  
  def define_term_var(self, loc, name, typ, val):
    return Env(cons(cons(name, TermBinding(loc, typ, val)), self.alist))

  def declare_proof_var(self, loc, name, frm):
    return Env(cons(cons(name, ProofBinding(loc, typ)), self.alist))

  def _def_of_type_var(self, curr, name, index):
    if curr:
      if index == 0:
        assert name == curr[0][0]
        return curr[0][1].defn
      else:
        match curr[0][1]:
          case TypeBinding(loc, defn):
            return _def_of_type_var(curr[1], index - 1).shift_type_vars(0, 1)
          case TermBinding(loc, typ, defn):
            return _def_of_type_var(curr[1], index).shift_term_vars(0, 1)
          case ProofBinding(loc, frm):
            return _def_of_type_var(curr[1], index).shift_proof_vars(0, 1)
    else:
      return None
    
  def _type_of_term_var(self, curr, name, index):
    if curr:
      if index == 0:
        assert name == curr[0][0]
        return curr[0][1].typ
      else:
        match curr[0][1]:
          case TypeBinding(loc, defn):
            return _type_of_term_var(curr[1], index).shift_type_vars(0, 1)
          case TermBinding(loc, typ, defn):
            return _type_of_term_var(curr[1], index - 1).shift_term_vars(0, 1)
          case ProofBinding(loc, frm):
            return _type_of_term_var(curr[1], index).shift_proof_vars(0, 1)
    else:
      return None

  def _value_of_term_var(self, curr, name, index):
    if curr:
      if index == 0:
        assert name == curr[0][0]
        return curr[0][1].defn
      else:
        match curr[0][1]:
          case TypeBinding(loc, defn):
            return _value_of_term_var(curr[1], index).shift_type_vars(0, 1)
          case TermBinding(loc, typ, defn):
            return _value_of_term_var(curr[1], index - 1).shift_term_vars(0, 1)
          case ProofBinding(loc, frm):
            return _value_of_term_var(curr[1], index).shift_proof_vars(0, 1)
    else:
      return None
  
  def _formula_of_proof_var(self, curr, name, index):
    if curr:
      if index == 0:
        assert name == curr[0][0]
        return curr[0][1].formula
      else:
        match curr[0][1]:
          case TypeBinding(loc, defn):
            return _formula_of_proof_var(curr[1], index).shift_type_vars(0, 1)
          case TermBinding(loc, typ, defn):
            return _formula_of_proof_var(curr[1], index).shift_term_vars(0, 1)
          case ProofBinding(loc, frm):
            return _formula_of_proof_var(curr[1], index - 1).shift_proof_vars(0, 1)
    else:
      return None
    
  def type_var_is_defined(self, tyname):
    match tyname:
      case TypeName(loc, name, index):
        if self._def_of_type_var(self.alist, name, index)
          return True
        else:
          return False
      case _:
        print('expected a type name, not ' + str(tyname))
        exit(-1)

  def term_var_is_defined(self, tvar):
    match tvar:
      case TVar(loc, name, index):
        if self._type_of_term_var(self.alist, name, index)
          return True
        else:
          return False
      case _:
        print('expected a term variable, not ' + str(tvar))
        exit(-1)
        
  def proof_var_is_defined(self, pvar):
    match pvar:
      case PVar(loc, name, index):
        if self._formula_of_proof_var(self.alist, name, index):
          return True
        else:
          return False
      case _:
        print('expected proof var, not ' + str(pvar))
        exit(-1)
    
  def get_formula_of_proof_var(self, pvar):
    match pvar:
      case PVar(loc, name, index):
        return self._formula_of_proof_var(self.alist, name, index):
          
  def get_type_of_term_var(self, tvar):
    match tvar:
      case TVar(loc, name, index):
        return self._type_of_term_var(self.alist, name, index)

  def get_value_of_term_var(self, tvar):
    match tvar:
      case TVar(loc, name, index):
        return self._value_of_term_var(self.alist, name, index)

  def index_of_type_var(self, name):
    index = 0
    curr = self.alist
    while curr and curr[0][0] != name:
      match curr[0][1]:
        case TypeBinding(loc, defn):
          index += 1
        case TermBinding(loc, typ, defn):
          pass
        case ProofBinding(loc, frm):
          pass
      curr = curr[1]
    if curr:
      return index
    else:
      return None

  def index_of_term_var(self, name):
    index = 0
    curr = self.alist
    while curr and curr[0][0] != name:
      match curr[0][1]:
        case TypeBinding(loc, defn):
          pass
        case TermBinding(loc, typ, defn):
          index += 1
        case ProofBinding(loc, frm):
          pass
      curr = curr[1]
    if curr:
      return index
    else:
      return None

  def index_of_proof_var(self, name):
    index = 0
    curr = self.alist
    while curr and curr[0][0] != name:
      match curr[0][1]:
        case TypeBinding(loc, defn):
          pass
        case TermBinding(loc, typ, defn):
          pass
        case ProofBinding(loc, frm):
          index += 1
      curr = curr[1]
    if curr:
      return index
    else:
      return None

  
