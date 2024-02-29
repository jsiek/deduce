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

  def type_var_is_defined(self, tyname):
    if self.get_binding_of_type_var(tyname):
      return True
    else:
      return False
  
  def get_binding_of_type_var(self, tyname):
    match tyname:
      case TypeName(loc, name, index):
        curr = self.alist
        while curr and index != 0:
          match curr[0][1]:
            case TypeBinding(loc, defn):
              index -= 1
            case TermBinding(loc, typ, defn):
              pass
            case ProofBinding(loc, frm):
              pass
          curr = curr[1]
        if curr:
          if curr[0][0] == name:
            return curr[0][1]
          else:
            error(loc, 'index mismatch for ' + str(tyname) + '\nfound ' + str(curr[0]))
        else:
          return None
      case _:
        return None

  def term_var_is_defined(self, tyname):
    if self.get_binding_of_term_var(tyname):
      return True
    else:
      return False
      
  def get_binding_of_term_var(self, tvar):
    match tvar:
      case TVar(loc, name, index):
        curr = self.alist
        while curr and index != 0:
          match curr[0][1]:
            case TypeBinding(loc, defn):
              pass
            case TermBinding(loc, typ, defn):
              index -= 1
            case ProofBinding(loc, frm):
              pass
          curr = curr[1]
        if curr:
          if curr[0][0] == name:
            return curr[0][1]
          else:
            error(loc, 'index mismatch for ' + str(tvar) + '\nfound ' + str(curr[0]))
        else:
          return None
      case _:
        return None

  def proof_var_is_defined(self, tyname):
    if self.get_binding_of_proof_var(tyname):
      return True
    else:
      return False
    
  def get_binding_of_proof_var(self, pvar):
    match pvar:
      case PVar(loc, name, index):
        curr = self.alist
        while curr and index != 0:
          match curr[0][1]:
            case TypeBinding(loc, defn):
              pass
            case TermBinding(loc, typ, defn):
              pass
            case ProofBinding(loc, frm):
              index -= 1
          curr = curr[1]
        if curr:
          if curr[0][0] == name:
            return curr[0][1]
          else:
            error(loc, 'index mismatch for ' + str(pvar) + '\nfound ' + str(curr[0]))
        else:
          return None
      case _:
        return None

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

  
