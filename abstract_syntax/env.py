from __future__ import annotations

from .core import *
from .terms import *
from .proofs import *
from .declarations import *

@dataclass(kw_only=True)
class Binding(AST):
  module : str
  visibility : str = 'public'

@dataclass
class TypeBinding(Binding):
  defn : Optional[AST] = None

  def __str__(self) -> str:
    return str(self.defn)

@dataclass
class TermBinding(Binding):
  typ : Optional[Type]
  defn : Optional[Term | RecFun | GenRecFun | ViewRecFun] = None
  local : bool = False
  
  def __str__(self) -> str:
    return str(self.typ) + (' = ' + str(self.defn) if self.defn else '')

@dataclass
class ProofBinding(Binding):
  formula : Formula
  local : bool
  
  def __str__(self) -> str:
    return str(self.formula)

@dataclass
class AutoEquationBinding(Binding):
  equations : dict[str, list[Formula]]
  fallback_equations : list[Formula] = field(default_factory=list)
  
  def __str__(self) -> str:
    head_equations = [e for equations in self.equations.values() for e in equations]
    return ', '.join([str(e) for e in head_equations + self.fallback_equations])

@dataclass
class ViewBinding(Binding):
  view: ViewDecl

  def __str__(self) -> str:
    return str(self.view)


def type_params_str(type_params: Sequence[str]) -> str:
  if len(type_params) > 0:
    return '<' + ','.join(type_params) + '>'
  else:
    return ''
  
@dataclass
class AssociativeBinding(Binding):
  opname: str
  types: List[Tuple[List[str], Type]]

  def __str__(self) -> str:
    return 'associative ' + self.opname \
      + ' ' + ', '.join(type_params_str(type_params) + str(t) \
                        for (type_params, t) in self.types)

class Env:
  def __init__(self, env: Optional[dict[str, Any]] = None) -> None:
    if env:
      self.dict = copy_dict(env)
    else:
      self.dict = {}

  # This is a hack. Not reliable. Added for GenRecFun.
  def base_to_unique(self, name: str) -> str | None:
    for k in self.dict.keys():
      if base_name(k) == name:
        return k
    return None

  def base_to_overloads(self, name: str) -> list[str]:
    overloads = []
    for k in self.dict.keys():
      if base_name(k) == name:
        overloads.append(k)
    return overloads

  def __str__(self) -> str:
    return ',\n'.join(['\t' + name2str(k) + ': ' + str(v) \
                       for (k,v) in reversed(self.dict.items())])

  def __contains__(self, item: str) -> bool:
    return item in self.dict.keys()
    
  def proofs_str(self) -> str:
    return ',\n'.join(['\t' + name2str(k) + ': ' + str(v) \
                       for (k,v) in reversed(self.dict.items()) \
                       if isinstance(v,ProofBinding) and (v.local or get_verbose() == VerboseLevel.FULL)])

  def term_vars_str(self) -> str:
    return ',\n'.join(['\t' + base_name(k) + ': ' + str(v.typ) \
                       for (k,v) in reversed(self.dict.items()) \
                       if isinstance(v,TermBinding) and v.local])
  
  def declare_type(self, loc: Meta, name: str, vis: str = 'public') -> Env:
    new_env = Env(self.dict)
    new_env.dict[name] = TypeBinding(loc, module=self.get_current_module(), visibility=vis)
    return new_env

  def declare_type_vars(self, loc: Meta, type_vars: Sequence[str]) -> Env:
    new_env = self
    for x in type_vars:
      new_env = new_env.declare_type(loc, x)
    return new_env
  
  def define_type(self, loc: Meta, name: str, defn: AST,
                  visibility: str = 'public') -> Env:
    if defn == None:
      internal_error(loc, 'None not allowed in define_type')
    new_env = Env(self.dict)
    new_env.dict[name] = TypeBinding(loc, defn, module=self.get_current_module(), visibility=visibility)
    return new_env

  def declare_view(self, loc: Meta, view: ViewDecl,
                   visibility: str = 'public') -> Env:
    new_env = Env(self.dict)
    new_env.dict[view.name] = ViewBinding(loc, view,
                                          module=self.get_current_module(),
                                          visibility=visibility)
    return new_env
  
  def declare_term_var(self, loc: Meta, name: str, typ: Type,
                       local: bool = False, visibility: str = 'public') -> Env:
    if typ == None:
      internal_error(loc, 'None not allowed as type of variable in declare_term_var')
    new_env = Env(self.dict)
    new_env.dict[name] = TermBinding(loc, typ, module=self.get_current_module(), visibility=visibility)
    new_env.dict[name].local = local
    return new_env

  def declare_assoc(self, loc: Meta, opname: str, typarams: List[str],
                    typ: Type) -> Env:
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

  def declare_auto_rewrite(self, loc: Meta, equation: Formula) -> Env:
    new_env = Env(self.dict)
    full_name = '__auto__'
    (lhs,rhs) = split_equation(loc, equation, new_env)
    head_lhs = call_head_name(lhs)
    #print('declare auto: ' + head_lhs + '\n\t' + str(equation))
    if full_name in self.dict:
        old = cast(AutoEquationBinding, self.dict[full_name])
        new_equations = {head: [*equations]
                         for (head, equations) in old.equations.items()}
        new_fallback_equations = [*old.fallback_equations]
    else:
        new_equations = {}
        new_fallback_equations = []
    if head_lhs is None:
        new_fallback_equations.append(equation)
    else:
        new_equations.setdefault(head_lhs, []).append(equation)
    new_env.dict[full_name] = AutoEquationBinding(loc, new_equations,
                                                  new_fallback_equations,
                                                  module=self.get_current_module())
    return new_env

  def get_auto_rewrites(self, head: str | None) -> list[Formula]:
    full_name = '__auto__'
    if full_name in self.dict.keys():
        binding = cast(AutoEquationBinding, self.dict[full_name])
        if head is None:
            return binding.fallback_equations
        return binding.equations.get(head, binding.fallback_equations)
    else:
      return []

  def declare_inductive(self, loc: Meta, ind_dict: InductiveInfo,
                        thm: Proof | Term) -> Env:
    new_env = Env(self.dict)
    full_name = '__inductive__'
    typ = ind_dict["ind_ty"]
    ind_dict["thm"] = thm
    type_name = cast(VarRef, get_type_name(typ)).get_name()

    if full_name in new_env.dict:
      inductives = cast(dict[str, InductiveInfo], new_env.dict[full_name])
      if type_name in inductives:
        pass
      else:
        inductives[type_name] = ind_dict
      # Check for type, overwrite/ add to existing
      pass
    else:
      new_env.dict[full_name] = {}
      new_env.dict[full_name][type_name] = ind_dict
    
    return new_env

  def get_inductive(self, typ: Type) -> InductiveInfo | None:
    full_name = '__inductive__'
    type_name = cast(VarRef, get_type_name(typ)).get_name()
    if full_name in self.dict:
      inductives = cast(dict[str, InductiveInfo], self.dict[full_name])
      if type_name in inductives:
        return inductives[type_name]

    return None

  def declare_term_vars(self, loc: Meta,
                        xty_pairs: Iterable[tuple[str, Type]],
                        local: bool = False) -> Env:
    new_env = self
    for (x,ty) in xty_pairs:
      new_env = new_env.declare_term_var(loc, x, ty, local)
    return new_env
  
  def define_term_var(self, loc: Meta, name: str, typ: Type | None,
                      val: Term | RecFun | GenRecFun | ViewRecFun,
                      visibility: str = 'public') -> Env:
    if val == None:
      internal_error(loc, 'None not allowed as value in define_term_var')
    new_env = Env(self.dict)
    new_env.dict[name] = TermBinding(loc, cast(Type, typ), cast(Term, val),
                                     module=self.get_current_module(),
                                     visibility=visibility)
    return new_env

  def define_term_vars(self, loc: Meta,
                       xv_pairs: Iterable[tuple[str, Term]]) -> Env:
    new_env = self
    for (x,v) in xv_pairs:
      new_env = new_env.define_term_var(loc, x, None, v)
    return new_env
  
  def declare_proof_var(self, loc: Meta, name: str, frm: Formula) -> Env:
    new_env = Env(self.dict)
    new_env.dict[name] = ProofBinding(loc, frm, False, module=self.get_current_module())
    return new_env

  def declare_local_proof_var(self, loc: Meta, name: str,
                              frm: Formula) -> Env:
    new_env = Env(self.dict)
    new_env.dict[name] = ProofBinding(loc, frm, True, module=self.get_current_module())
    return new_env

  def declare_module(self, module: str) -> Env:
    new_env = Env(self.dict)
    new_env.dict['__current_module__'] = module
    return new_env
  
  def declare_tracing(self, function_name: str) -> Env:
    new_env = Env(self.dict)
    if 'tracing' not in new_env.dict:
      new_env.dict['tracing'] = set()
    new_env.dict['tracing'].add(function_name)
    return new_env

  def get_current_module(self) -> str:
      return cast(str, self.dict['__current_module__'])
  
  def _def_of_type_var(self, curr: dict[str, Any],
                       name: str) -> AST | None:
    if name in curr.keys():
      binding = curr[name]
      if isinstance(binding, ViewBinding):
        return binding.view.source
      return cast(AST | None, binding.defn)
    else:
      raise Exception('variable not in env: ' + name)
  

  def _type_of_term_var(self, curr: dict[str, object],
                        name: str) -> Type | None:
    if name in curr.keys():
      binding = curr[name]
      if isinstance(binding, TermBinding):
        return binding.typ
      elif isinstance(binding, TypeBinding):
        return TypeType(cast(Meta, None))
      elif isinstance(binding, ViewBinding):
        raise Exception('expected a term or type variable, not view ' + base_name(name))
      else:
        raise Exception('expected a term or type variable, not ' + base_name(name))
    else:
      return None

  def _term_var_defined(self, curr: dict[str, object], name: str) -> bool:
    if name in curr.keys():
      binding = curr[name]
      if isinstance(binding, TermBinding) or isinstance(binding, TypeBinding):
        return True
    return False

  def _value_of_term_var(self, curr: dict[str, Any], name: str) -> Term | RecFun | GenRecFun | None:
    if name in curr.keys(): # the name '=' is not in the env
      return cast(Term | RecFun | GenRecFun | None, curr[name].defn)
    else:
      return None
  
  def _formula_of_proof_var(self, curr: dict[str, object],
                            name: str) -> Formula | None:
    if name in curr.keys():
      match curr[name]:
        case ProofBinding(_, formula):
          return formula
        case TermBinding(_, FunctionType()):
          raise UserError('expected a proof but instead got term `' + base_name(name) + '`.'\
                        + '\nPerhaps you meant `expand ' + base_name(name) + '`?')
        case TermBinding():
          raise UserError('expected a proof but instead got term `' + base_name(name) + '`.'\
                        + '\nPerhaps you meant `recall ' + base_name(name) + '`?')
        case TypeBinding():
          raise UserError('expected a proof but instead got type ' + base_name(name))
        case _:
          raise UserError('expected a proof but instead got ' + base_name(name))
    else:
      return None
    
  def type_var_is_defined(self, tyname: VarRef) -> bool:
    if isinstance(tyname, VarRef):
      return tyname.get_name() in self.dict.keys()
    raise Exception('expected a type name, not ' + str(tyname))

  def term_var_is_defined(self, tvar: VarRef) -> bool:
    match tvar:
      case OverloadedVar(_, _, resolved_names):
        return any([self._term_var_defined(self.dict, x) for x in resolved_names])
      case ResolvedVar(_, _, name):
        return self._term_var_defined(self.dict, name)
      case Var(_, _, name):
        return self._term_var_defined(self.dict, name)
      case _:
        raise Exception('expected term var, not ' + str(tvar))
        
  def proof_var_is_defined(self, pvar: PVar) -> bool:
    match pvar:
      case PVar(_, name):
        if self._formula_of_proof_var(self.dict, name):
          return True
        else:
          return False
      case _:
        raise Exception('expected proof var, not ' + str(pvar))

  def get_assoc_types(self, opname: str) -> list[Tuple[List[str], Type]]:
    full_name = '__associative_' + opname
    if full_name in self.dict.keys():
      return cast(AssociativeBinding, self.dict[full_name]).types
    else:
      return []
      
  def get_def_of_type_var(self, var: VarRef) -> AST | None:
    if isinstance(var, VarRef):
      return self._def_of_type_var(self.dict, var.get_name())
    raise Exception('get_def_of_type_var: unexpected ' + str(var))

  def get_view(self, name: str | VarRef) -> ViewDecl | None:
    if isinstance(name, VarRef):
      name = name.get_name()
    if name in self.dict and isinstance(self.dict[name], ViewBinding):
      return cast(ViewBinding, self.dict[name]).view
    return None
      
  def get_formula_of_proof_var(self, pvar: PVar | Term) -> Formula:
    match pvar:
      case PVar(_, name):
        return cast(Formula, self._formula_of_proof_var(self.dict, name))
      case _:
        raise Exception('get_formula_of_proof_var: expected PVar, not ' + str(pvar))
          
  def get_type_of_term_var(self, tvar: Term) -> Type | None:
    match tvar:
      case OverloadedVar(loc, _, resolved_names):
        looked_up = [(x, self._type_of_term_var(self.dict, x)) for x in resolved_names]
        # Drop candidates not in env (e.g., overloads from modules
        # that haven't been imported here).
        overloads = [(x, ty) for (x, ty) in looked_up if ty is not None]
        if len(overloads) == 0:
          return None
        if len(overloads) > 1:
          return OverloadType(loc, overloads)
        return overloads[0][1]
      case ResolvedVar(loc, _, name):
        return self._type_of_term_var(self.dict, name)
      case Var(loc, _, name):
        return self._type_of_term_var(self.dict, name)
      case _:
        raise Exception('get_type_of_term_var: expected VarRef, not ' + str(tvar))

  def get_value_of_term_var(self, tvar: VarRef) -> Term | RecFun | GenRecFun | None:
    return self._value_of_term_var(self.dict, tvar.get_name())
      
  def get_tracing(self, function_name: str) -> bool:
    return 'tracing' in self.dict and function_name in self.dict['tracing']

  def local_proofs(self) -> list[Formula]:
    return [b.formula for (name, b) in self.dict.items() \
            if isinstance(b, ProofBinding) and b.local]

  def proofs(self) -> list[Formula]:
    return [b.formula for (name, b) in self.dict.items() \
            if isinstance(b, ProofBinding)]

