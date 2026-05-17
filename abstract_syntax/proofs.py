from __future__ import annotations

from typing import TYPE_CHECKING

from .core import *
from .terms import *

if TYPE_CHECKING:
    from .declarations import find_private_lemma_definers, overwrite

################ Proofs ######################################
  
@dataclass
class PVar(Proof):
  name: str

  def __eq__(self, other: object) -> bool:
    if not isinstance(other, PVar):
      return False
    return self.name == other.name

  def pretty_print(self, indent: int, afterNewline: bool = False) -> str:
      return str(self)
  
  def __str__(self) -> str:
      return base_name(self.name)

  def uniquify(self, env: dict[str, Any], ctx: UniquifyContext) -> PVar:
    if self.name not in env.keys():
      hits = find_private_lemma_definers(self.name)
      if hits:
        def fmt_hit(h: tuple[str, str | None, int | None]) -> str:
          module, filename, line = h
          if filename is not None and line is not None:
            return "module " + module + " (" + filename + ":" + str(line) + ")"
          return "module " + module
        where = ', '.join(fmt_hit(h) for h in hits)
        msg = ("'" + self.name + "' is declared as a `lemma` in "
               + where + "; lemmas are module-private and not accessible"
               + " from other modules. To make it accessible here, change"
               + " `lemma` to `theorem` there.")
        user_error(self.location, msg)
      env_str = ('\n' + ', '.join(env.keys())) if get_verbose() else ''
      user_error(self.location, "undefined proof variable " + self.name + env_str)
    if not isinstance(env[self.name], list):
      user_error(self.location, "proof variable not bound to list " + self.name)
    return PVar(self.location, env[self.name][0])
    
@dataclass
class PLet(Proof):
  label: str
  proved: Formula
  because: Proof
  body: Proof

  def pretty_print(self, indent: int, afterNewline: bool = False) -> str:
      return indent*' ' + 'have ' + base_name(self.label) + ': ' + str(self.proved) + ' by {\n' \
          + self.because.pretty_print(indent+2) + '\n' \
          + indent*' ' + '}\n' \
          + maybe_pretty_print(self.body, indent)
  
  def __str__(self) -> str:
      return 'have ' + base_name(self.label) + ': ' + str(self.proved) \
        + ' by ' + str(self.because) + (' ' + str(self.body) if self.body else '')

  def uniquify(self, env: dict[str, Any], ctx: UniquifyContext) -> PLet:
    new_proved = self.proved.uniquify(env, ctx)
    new_because = self.because.uniquify(env, ctx)
    body_env = {x:y for (x,y) in env.items()}
    new_label = generate_name(self.label, ctx)
    overwrite(body_env, self.label, new_label, self.location)
    new_body = self.body.uniquify(body_env, ctx)
    return PLet(self.location, new_label, new_proved, new_because, new_body)

@dataclass
class PTLetNew(Proof):
  var: str
  rhs : Term
  body: Proof

  def pretty_print(self, indent: int) -> str:
      return indent*' ' + 'define ' + base_name(self.var) + ' = ' + str(self.rhs) + '\n' \
          + self.body.pretty_print(indent)
  
  def __str__(self) -> str:
      return 'define ' + base_name(self.var) + ' = ' + str(self.rhs) + '\n' \
         + str(self.body)

  def uniquify(self, env: dict[str, Any], ctx: UniquifyContext) -> PTLetNew:
    new_rhs = self.rhs.uniquify(env, ctx)
    body_env = {x:y for (x,y) in env.items()}
    new_var = generate_name(self.var, ctx)
    overwrite(body_env, self.var, new_var, self.location)
    new_body = self.body.uniquify(body_env, ctx)
    return PTLetNew(self.location, new_var, new_rhs, new_body)


@dataclass
class PRecall(Proof):
  facts: List[Formula]

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self) -> str:
      return 'recall ' + ', '.join([str(f) for f in self.facts])


@dataclass
class PAnnot(Proof):
  claim: Formula
  body: Proof

  def pretty_print(self, indent: int) -> str:
      return indent*' ' + 'conclude ' + str(self.claim) + ' by {\n' \
          + self.body.pretty_print(indent+2) + '\n' \
          + indent*' ' + '}\n'

  def __str__(self) -> str:
      return 'conclude ' + str(self.claim) + ' by ' + str(self.body)

@dataclass
class Suffices(Proof):
  claim: Formula
  reason: Proof
  body: Proof

  def pretty_print(self, indent: int) -> str:
      return indent*' ' + 'suffices ' + str(self.claim) + '  by {\n' \
          + self.reason.pretty_print(indent+2) + '\n' \
          + maybe_pretty_print(self.body, indent)

  def __str__(self) -> str:
    return 'suffices ' + str(self.claim) + '  by ' + str(self.reason) + '\n' + maybe_str(self.body)

@dataclass
class Cases(Proof):
  subject: Proof
  cases: List[Tuple[str,Optional[Formula],Proof]]

  def pretty_print(self, indent: int) -> str:
      cases_str = ''
      for (label, frm, body) in self.cases:
          cases_str += indent*' ' + 'case ' + base_name(label) + ' : ' + str(frm) + '{\n' \
              + body.pretty_print(indent+2) + '\n' \
              + indent*' ' + '}'
      return '\n'.join(cases_str) + '\n'
      
  def uniquify(self, env: dict[str, Any], ctx: UniquifyContext) -> Cases:
    new_subject = self.subject.uniquify(env, ctx)
    new_cases = []
    for (label, formula, proof) in self.cases:
      body_env = {x:y for (x,y) in env.items()}
      new_formula = formula.uniquify(env, ctx) if formula else None
      new_label = generate_name(label, ctx)
      overwrite(body_env, label, new_label, self.location)
      new_proof = proof.uniquify(body_env, ctx)
      new_cases.append((new_label, new_formula, new_proof))
    return Cases(self.location, new_subject, new_cases)
      
@dataclass
class ModusPonens(Proof):
  implication: Proof
  arg: Proof

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self) -> str:
      return 'apply ' + str(self.implication) + ' to ' + str(self.arg)

@dataclass
class ImpIntro(Proof):
  label: str
  premise: Optional[Formula]
  body: Proof

  def pretty_print(self, indent: int) -> str:
    return indent*' ' + 'assume ' + str(self.label) + \
      (': ' + str(self.premise) if self.premise else '') + '\n'\
      + maybe_pretty_print(self.body, indent)
  
  def __str__(self) -> str:
    return 'assume ' + str(self.label) + \
      (': ' + str(self.premise) if self.premise else '') + \
      ('{' + str(self.body) + '}' if self.body else '')

  def uniquify(self, env: dict[str, Any], ctx: UniquifyContext) -> ImpIntro:
    new_premise = self.premise.uniquify(env, ctx) if self.premise else None
    body_env = copy_dict(env)
    new_label = generate_name(self.label, ctx)
    overwrite(body_env, self.label, new_label, self.location)
    new_body = self.body.uniquify(body_env, ctx)
    return ImpIntro(self.location, new_label, new_premise, new_body)

@dataclass
class AllIntro(Proof):
  var: Tuple[str,Type]
  # Position (s, e), where
  #  e : The number of vars in the all intro list
  #  s : The variable's index in the list, starting from the last var
  pos: Tuple[int, int]
  body: Proof

  def arbitrary_str(self) -> str:
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

  def pretty_print(self, indent: int) -> str:
      return indent*' ' + self.arbitrary_str() + '\n' \
          + maybe_pretty_print(self.body, indent)
  
  def __str__(self) -> str:
    return self.arbitrary_str() + maybe_str(self.body)

  def uniquify(self, env: dict[str, Any], ctx: UniquifyContext) -> AllIntro:
    body_env = copy_dict(env)
    x, ty = self.var
    new_t = ty.uniquify(body_env, ctx)
    new_x = generate_name(x, ctx)
    overwrite(body_env, x, new_x, self.location)
    new_body = self.body.uniquify(body_env, ctx)
    return AllIntro(self.location, (new_x, new_t), self.pos, new_body)

  def set_body(self, new_body: Proof) -> None:
    if self.body:
      cast(AllIntro, self.body).set_body(new_body)
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

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self) -> str:
    s, e = self.pos
    res = str(self.univ)
    if s == 0:
      res += f"<{self.arg}"
    else:
      res += f", {self.arg}"

    if s + 1 == e:
      res += ">"

    return res

@dataclass
class AllElim(Proof):
  univ: Proof
  arg: Term
  # Position (s, e), where
  #  e : The number of vars in the list
  #  s : The variable's index in the list, starting from the first var
  pos: Tuple[int, int]

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self) -> str:
    s, e = self.pos
    res = str(self.univ)
    if s == 0:
      res += f"[{self.arg}"
    else:
      res += f", {self.arg}"

    if s + 1 == e:
      res += "]"

    return res

@dataclass
class SomeIntro(Proof):
  witnesses: List[Term]
  body: Proof

  def pretty_print(self, indent: int) -> str:
    return indent*' ' + 'choose ' + ",".join([str(t) for t in self.witnesses]) + '\n' \
        + maybe_pretty_print(self.body, indent)

  def __str__(self) -> str:
    return 'choose ' + ",".join([str(t) for t in self.witnesses]) \
        + '; ' + maybe_str(self.body)

@dataclass
class SomeElim(Proof):
  witnesses: List[str]
  label: str
  prop: Optional[Formula]
  some: Proof
  body: Proof

  def pretty_print(self, indent: int) -> str:
    return indent*' ' + 'obtain ' + ",".join(self.witnesses) \
      + ' where ' + self.label \
      + (' : ' + str(self.prop) if self.prop else '') \
      + ' from ' + str(self.some)  + '\n'\
      + maybe_pretty_print(self.body, indent)

  def __str__(self) -> str:
    return 'obtain ' + ",".join(self.witnesses) \
      + ' where ' + self.label \
      + (' : ' + str(self.prop) if self.prop else '') \
      + ' from ' + str(self.some) \
      + '; ' + maybe_str(self.body)
  
  def uniquify(self, env: dict[str, Any], ctx: UniquifyContext) -> SomeElim:
    new_some = self.some.uniquify(env, ctx)
    body_env = copy_dict(env)
    new_witnesses = []
    for x in self.witnesses:
      new_x = generate_name(x, ctx)
      new_witnesses.append(new_x)
      overwrite(body_env, x, new_x, self.location)
    new_label = generate_name(self.label, ctx)
    overwrite(body_env, self.label, new_label, self.location)
    new_prop = self.prop.uniquify(body_env, ctx) if self.prop else None
    new_body = self.body.uniquify(body_env, ctx)
    return SomeElim(self.location, new_witnesses, new_label,
                    new_prop, new_some, new_body)
    
@dataclass
class PTuple(Proof):
  args: List[Proof]

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self) -> str:
    return ', '.join([str(arg) for arg in self.args])

def extract_tuple(pf: Proof) -> List[Proof]:
    match pf:
      case PTuple(_, pfs):
        return pfs
      case _:
       return [pf]
   
@dataclass
class PAndElim(Proof):
  which: int
  subject: Proof

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self) -> str:
    return 'conjunct ' + str(self.which) + ' of ' + str(self.subject)

@dataclass
class PTrue(Proof):

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self) -> str:
    return '.'

@dataclass
class PReflexive(Proof):

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self) -> str:
    return 'reflexive'

@dataclass
class PHole(Proof):

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self) -> str:
      return '?'

@dataclass
class PSorry(Proof):

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self) -> str:
      return 'sorry'

@dataclass
class PHelpUse(Proof):
  proof : Proof

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self) -> str:
      return 'help ' + str(self.proof)

@dataclass
class PSymmetric(Proof):
  body: Proof

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self) -> str:
    return 'symmetric ' + str(self.body)

@dataclass
class PTransitive(Proof):
  first: Proof
  second: Proof

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self) -> str:
    return 'transitive ' + str(self.first) + ' ' + str(self.second)

@dataclass
class PInjective(Proof):
  constr: Type
  body: Proof

  def pretty_print(self, indent: int) -> str:
    return indent*' ' + 'injective ' + str(self.constr) + '\n' \
        + maybe_pretty_print(self.body, indent)

  def __str__(self) -> str:
    return 'injective ' + str(self.constr) + '; ' + maybe_str(self.body)

@dataclass
class PExtensionality(Proof):
  body: Proof

  def pretty_print(self, indent: int) -> str:
    return indent*' ' + 'extensionality\n' \
        + maybe_pretty_print(self.body, indent)

  def __str__(self) -> str:
    return 'extensionality\n' + maybe_str(self.body)

@dataclass
class IndCase(AST):
  pattern: Pattern
  induction_hypotheses: list[Tuple[str,Formula]]
  body: Proof

  def pretty_print(self, indent: int) -> str:
    return indent*' ' + 'case ' + str(self.pattern) \
      + ' assume ' + ', '.join([x + ': ' + str(f) for (x,f) in self.induction_hypotheses]) \
      + '{\n' \
      + self.body.pretty_print(indent+2) \
      + indent*' ' + '}\n'
      
  def __str__(self) -> str:
    return 'case ' + str(self.pattern) \
      + ' assume ' + ', '.join([x + ': ' + str(f) for (x,f) in self.induction_hypotheses]) \
      + '{' + str(self.body) + '}'

  def uniquify(self, env: object, ctx: object) -> IndCase:
    env_map = cast(dict[str, Any], env)
    uniq_ctx = cast(UniquifyContext, ctx)
    body_env = copy_dict(env_map)
    pattern = cast(Any, self.pattern)

    new_params = [generate_name(x, uniq_ctx) for x in pattern.parameters]
    for (old, new) in zip(pattern.parameters, new_params):
      overwrite(body_env, old, new, self.location)

    new_hyp_labels = [generate_name(x, uniq_ctx) for (x, _) in self.induction_hypotheses]
    for ((old, _), new) in zip(self.induction_hypotheses, new_hyp_labels):
      overwrite(body_env, old, new, self.location)

    new_hyps: list[Tuple[str, Formula]] = []
    for ((_, f), new_label) in zip(self.induction_hypotheses, new_hyp_labels):
      new_f = f.uniquify(body_env, uniq_ctx) if f else None
      new_hyps.append((new_label, cast(Formula, new_f)))

    new_pat = pattern.with_bindings(new_params).uniquify(body_env, uniq_ctx)
    new_body = self.body.uniquify(body_env, uniq_ctx)
    return IndCase(self.location, new_pat, new_hyps, new_body)

@dataclass
class Induction(Proof):
  typ: Type
  cases: List[IndCase]

  def pretty_print(self, indent: int) -> str:
    return indent*' ' + 'induction ' + str(self.typ) + '\n' \
      + '\n'.join([c.pretty_print(indent) for c in self.cases])

  def __str__(self) -> str:
    return 'induction ' + str(self.typ) + '\n' \
      + '\n'.join([str(c) for c in self.cases])

@dataclass
class RuleInductionCase(AST):
  # `case <rule_name> { <proof> }` from a `rule induction` block.
  # The body is a complete proof of the rule's M-augmented conjunct of
  # `<pred>_rule_induction`'s `rules_hyp` (the user's `arbitrary` and
  # `assume` happen inside the body).
  rule_name: str
  body: Proof

  def pretty_print(self, indent: int) -> str:
    return indent*' ' + 'case ' + base_name(self.rule_name) + ' {\n' \
        + self.body.pretty_print(indent+2) + '\n' + indent*' ' + '}'

  def __str__(self) -> str:
    return 'case ' + base_name(self.rule_name) + ' { ' \
        + str(self.body) + ' }'

  def uniquify(self, env: object, ctx: object) -> RuleInductionCase:
    env_map = cast(dict[str, Any], env)
    uniq_ctx = cast(UniquifyContext, ctx)
    # Resolve the rule name against the env so we can match against the
    # uniquified rule names later. Wrong names are reported with a
    # did-you-mean message.
    if self.rule_name not in env_map.keys():
      from edit_distance import edit_distance
      from math import ceil
      close = [v for v in env_map.keys()
               if edit_distance(self.rule_name, v)
                  <= ceil(len(self.rule_name) / 5)]
      hint = '\n\tdid you intend: ' + ', '.join(close) if close else ''
      user_error(self.location,
                 "no such rule '" + self.rule_name + "'" + hint)
    resolved = env_map[self.rule_name]
    new_rule_name = self.rule_name
    if isinstance(resolved, list) and len(resolved) >= 1:
      new_rule_name = resolved[0]
    return RuleInductionCase(self.location, new_rule_name,
                             self.body.uniquify(env_map, uniq_ctx))

@dataclass
class RuleInduction(Proof):
  # `rule induction <pred> case <r1> { ... } ...`
  # Desugars to `apply <pred>_rule_induction[<motive>] to (<case_1>, ...,
  # <case_k>)`. The motive is inferred from the goal, which must have
  # the shape `all xs. if <pred>(xs) then Q(xs)`.
  hyp_name: str
  cases: List[RuleInductionCase]

  def pretty_print(self, indent: int) -> str:
    return indent*' ' + 'rule induction ' + base_name(self.hyp_name) + '\n' \
        + '\n'.join([c.pretty_print(indent) for c in self.cases])

  def __str__(self) -> str:
    return 'rule induction ' + base_name(self.hyp_name) + ' ' \
        + ' '.join([str(c) for c in self.cases])

  def uniquify(self, env: object, ctx: object) -> RuleInduction:
    env_map = cast(dict[str, Any], env)
    uniq_ctx = cast(UniquifyContext, ctx)
    if self.hyp_name not in env_map.keys():
      from edit_distance import edit_distance
      from math import ceil
      close = [v for v in env_map.keys()
               if edit_distance(self.hyp_name, v)
                  <= ceil(len(self.hyp_name) / 5)]
      hint = '\n\tdid you intend: ' + ', '.join(close) if close else ''
      user_error(self.location,
                 "rule induction: no such predicate '"
                 + self.hyp_name + "'" + hint)
    resolved = env_map[self.hyp_name]
    new_hyp_name = self.hyp_name
    if isinstance(resolved, list) and len(resolved) >= 1:
      new_hyp_name = resolved[0]
    return RuleInduction(self.location, new_hyp_name,
                         [c.uniquify(env_map, uniq_ctx) for c in self.cases])

@dataclass
class RuleInversion(Proof):
  # `rule inversion <pred> case <r1> { ... } ...`
  # Same shape as RuleInduction, but desugars to applying the
  # `<pred>_rule_inversion` theorem instead — the cases prove the
  # *non*-augmented rule conjuncts (no induction hypothesis).
  hyp_name: str
  cases: List[RuleInductionCase]

  def pretty_print(self, indent: int) -> str:
    return indent*' ' + 'rule inversion ' + base_name(self.hyp_name) + '\n' \
        + '\n'.join([c.pretty_print(indent) for c in self.cases])

  def __str__(self) -> str:
    return 'rule inversion ' + base_name(self.hyp_name) + ' ' \
        + ' '.join([str(c) for c in self.cases])

  def uniquify(self, env: object, ctx: object) -> RuleInversion:
    env_map = cast(dict[str, Any], env)
    uniq_ctx = cast(UniquifyContext, ctx)
    if self.hyp_name not in env_map.keys():
      from edit_distance import edit_distance
      from math import ceil
      close = [v for v in env_map.keys()
               if edit_distance(self.hyp_name, v)
                  <= ceil(len(self.hyp_name) / 5)]
      hint = '\n\tdid you intend: ' + ', '.join(close) if close else ''
      user_error(self.location,
                 "rule inversion: no such predicate '"
                 + self.hyp_name + "'" + hint)
    resolved = env_map[self.hyp_name]
    new_hyp_name = self.hyp_name
    if isinstance(resolved, list) and len(resolved) >= 1:
      new_hyp_name = resolved[0]
    return RuleInversion(self.location, new_hyp_name,
                         [c.uniquify(env_map, uniq_ctx) for c in self.cases])

@dataclass
class SwitchProofCase(AST):
  pattern: Pattern
  assumptions: list[Tuple[str,Formula]]
  body: Proof

  def pretty_print(self, indent: int) -> str:
    return indent*' ' + 'case ' + str(self.pattern) + '{\n' \
        + self.body.pretty_print(indent+2) \
        + indent*' ' + '}\n'

  def __str__(self) -> str:
    return 'case ' + str(self.pattern) + '{' + str(self.body) + '}'

  def uniquify(self, env: object, ctx: object) -> SwitchProofCase:
    env_map = cast(dict[str, Any], env)
    uniq_ctx = cast(UniquifyContext, ctx)
    body_env = copy_dict(env_map)
    pattern = cast(Any, self.pattern)

    new_params = [generate_name(x, uniq_ctx) for x in pattern.bindings()]
    for (old, new) in zip(pattern.bindings(), new_params):
      overwrite(body_env, old, new, self.location)

    new_assumption_labels = [generate_name(x, uniq_ctx) for (x, _) in self.assumptions]
    for ((old, _), new) in zip(self.assumptions, new_assumption_labels):
      overwrite(body_env, old, new, self.location)

    new_assumptions: list[Tuple[str, Formula]] = []
    for ((_, f), new_label) in zip(self.assumptions, new_assumption_labels):
      new_f = f.uniquify(body_env, uniq_ctx) if f else None
      new_assumptions.append((new_label, cast(Formula, new_f)))

    new_pat = pattern.with_bindings(new_params).uniquify(body_env, uniq_ctx)
    new_body = self.body.uniquify(body_env, uniq_ctx)
    return SwitchProofCase(self.location, new_pat,
                           new_assumptions, new_body)

@dataclass
class SwitchProof(Proof):
  subject: Term
  cases: List[SwitchProofCase]

  def pretty_print(self, indent: int) -> str:
      return indent*' ' + 'switch ' + str(self.subject) + '{\n' \
          + '\n'.join([c.pretty_print(indent+2) for c in self.cases]) \
          + indent*' ' + '}\n'

  def __str__(self) -> str:
      return 'switch ' + str(self.subject) \
        + '{' + '\n'.join([str(c) for c in self.cases]) + '}'

@dataclass
class EvaluateGoal(Proof):

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self) -> str:
    return 'evaluate'

@dataclass
class EvaluateFact(Proof):
  subject: Proof

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self) -> str:
    return 'evaluate in ' + str(self.subject)

@dataclass
class SimplifyGoal(Proof):
  body: Proof
  givens: List[Proof]

  def __str__(self) -> str:
      return 'simplify ' + ' | '.join([str(p) for p in self.givens]) + '\n' \
          + str(self.body)


@dataclass
class SimplifyFact(Proof):
  subject: Proof
  givens: List[Proof]

  def pretty_print(self, indent: int) -> str:
      return str(self)

  def __str__(self) -> str:
    return 'simplify ' \
        + ' | '.join([str(p) for p in self.givens]) \
        + ' in ' + str(self.subject)

@dataclass
class ApplyDefsGoal(Proof):
  definitions: List[Term]
  body: Proof

  def __str__(self) -> str:
      return 'expand ' + ' | '.join([str(d) for d in self.definitions]) \
        + ' ' + str(self.body)

@dataclass
class ApplyDefsFact(Proof):
  definitions: List[Term]
  subject: Proof

  def __str__(self) -> str:
      return 'expand ' + ' | '.join([str(d) for d in self.definitions]) \
        + ' in ' + str(self.subject)

@dataclass
class RewriteGoal(Proof):
  equations: List[Proof]
  body: Proof

  def __str__(self) -> str:
      return 'replace ' + '|'.join([str(eqn) for eqn in self.equations]) \
        + '\n' + str(self.body)

@dataclass
class RewriteFact(Proof):
  subject: Proof
  equations: List[Proof]

  def __str__(self) -> str:
      return 'replace ' + ','.join([str(eqn) for eqn in self.equations]) \
        + ' in ' + str(self.subject)
