"""Cross-cutting whole-AST operations and dispatcher helpers.

Scope: passes and predicates that traverse arbitrary AST shapes —
operations that have to know about every node category and therefore
sit at the top of the import order. Includes the driver
``uniquify_deduce``, the invariant audits ``check_post_uniquify_invariants``
and ``check_post_typecheck_invariants``, ``alpha_equiv`` (with its
private ``_alpha_equiv_*`` helpers), ``explicit_term_inst``, ``type_match``,
``flatten_assoc``/``flatten_assoc_list``, ``make_switch_for``, and the
small symbol/name helpers that bridge categories
(``callable_name``, ``named_callable_name``, ``is_associative``,
``type_names``).

Goes here:
  * a new AST-wide pass / consistency check
  * a helper that has to dispatch on more than one node category
    (Term + Proof + Statement, etc.)

Does NOT go here:
  * the proof-checker proper — that lives in ``proof_checker`` /
    ``checker_*`` and consumes these helpers
  * single-category helpers; put those next to their node definitions
"""

from __future__ import annotations

from .core import *
from .terms import *
from .proofs import *
from .declarations import *
from .env import *
from .literals import *
from .rewrite import *

def type_names(loc: Meta, names: List[str]) -> list[ResolvedVar]:
  index = 0
  result: List["ResolvedVar"] = []
  for n in reversed(names):
    result.insert(0, ResolvedVar(loc, None, n))
    index += 1
  return result


def type_match(
    loc: Meta,
    tyvars: Sequence[VarRef | str],
    param_ty: Type | VarRef | None,
    arg_ty: Type | VarRef | None,
    matching: dict[str, Type | VarRef | None],
) -> None:
  if get_verbose():
    print("type_match(" + str(param_ty) + "," + str(arg_ty) + ")")
    print("\tin  " + ', '.join([str(x) for x in tyvars]))
    print("\twith " + str(matching))
  # `param_ty` may be a tyvar reference encoded as either an
  # OverloadedVar (if it came straight from uniquify) or a ResolvedVar
  # (if a prior narrowing has already occurred). `get_name()` gives us
  # the canonical identifier in both cases.
  if isinstance(param_ty, VarRef) and param_ty in tyvars:
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
  if isinstance(param_ty, VarRef) and isinstance(arg_ty, VarRef) \
     and param_ty.get_name() == arg_ty.get_name():
    return
  match (param_ty, arg_ty):
    case (FunctionType(_, tv1, pts1, rt1), FunctionType(_, tv2, pts2, rt2)) \
      if len(tv1) == len(tv2) and len(pts1) == len(pts2):
      for (pt1, pt2) in zip(pts1, pts2):
        type_match(loc, tyvars, pt1, pt2, matching)
      type_match(loc, tyvars, rt1, rt2, matching)
    case (TypeInst(_, n1, args1), TypeInst(_, n2, args2)):
      if n1 != n2 or len(args1) != len(args2):
        match_failed(loc, str(arg_ty) + " does not match " + str(param_ty))
      for (arg1, arg2) in zip(args1, args2):
        type_match(loc, tyvars, arg1, arg2, matching)
    # How to handle GenericUnknownInst?
    case (TypeInst(_, n1, args1), GenericUnknownInst(_, n2)):
      if n1 != n2:
        match_failed(loc, str(arg_ty) + " does not match " + str(param_ty))
    case (MutableArrayType(_, elt1), MutableArrayType(_, elt2)):
      type_match(loc, tyvars, elt1, elt2, matching)
    case _:
      if param_ty != arg_ty:
        match_failed(loc, str(arg_ty) + " does not match " + str(param_ty))


def is_associative(loc: Meta, opname: str, typ: Type | None, env: Env) -> bool:
  for (typarams, ty) in env.get_assoc_types(opname):
    type_params = type_names(loc, typarams)
    matching: dict[str, Type | VarRef | None] = {}
    try:
      type_match(loc, type_params, ty, typ, matching)
      return True
    except MatchFailed:
      pass
  return False

def named_callable_name(t: VarRef | RecFun | GenRecFun) -> str:
  if isinstance(t, VarRef):
    return t.get_name()
  return t.name


def callable_name(t: Term | RecFun | GenRecFun) -> str | None:
  if isinstance(t, VarRef | RecFun | GenRecFun):
    return named_callable_name(t)
  match t:
    case TermInst(_, _, subject, _, _):
      return callable_name(subject)
    case _:
      return None


def flatten_assoc(op_name: str, trm: Term) -> list[Term]:
  match trm:
    case Call(_, _, rator, args) if callable_name(rator) == op_name:
      return sum([flatten_assoc(op_name, arg) for arg in args], [])
    case _:
      return [trm]


def flatten_assoc_list(op_name: str, args: Sequence[Term]) -> list[Term]:
  return sum([flatten_assoc(op_name, arg) for arg in args], [])


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

def _walk_ast_descendants(roots: object) -> Iterator[object]:
  """Yield every AST descendant reachable from ``roots`` (a single
  node or an iterable). Memoized by ``id()`` so shared sub-ASTs
  (e.g. cached imported-module statements) aren't revisited."""
  from dataclasses import fields, is_dataclass
  seen: set[int] = set()
  stack: list[object] = []
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

def check_post_uniquify_invariants(ast_list: Sequence[Statement]) -> None:
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

def check_post_typecheck_invariants(ast_list: Sequence[Statement]) -> None:
  """Post-typecheck invariants. Hard error on any pre-uniquify ``Var``.
  Single-candidate ``OverloadedVar`` is currently a soft warning:
  the type checker doesn't visit proof bodies yet, so those leak
  OverloadedVars even when they aren't actually overloaded. The
  invariant will go strict once ``check_proof_of`` is refactored to
  rebuild proof ASTs (tracked separately).

  Multi-candidate ``OverloadedVar`` is permitted (genuine unresolved
  overload).
  """
  def loc_prefix(loc: Meta | None) -> str:
    try:
      if loc is not None and not getattr(loc, 'empty', True):
        return f'{getattr(loc, "filename", "")}:{getattr(loc, "line", "")}: '
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

def uniquify_deduce(ast: Sequence[Statement], ctx: UniquifyContext) -> list[Statement]:
  """Uniquify ``ast`` against ``ctx``'s counter, returning the
  post-uniquify AST.

  ``ctx`` is required and threaded through every recursive
  ``uniquify`` call so the counter is explicit at every step --
  no module-level shared state.  Two calls on the same AST with a
  fresh ``UniquifyContext`` each produce byte-equal output.

  Production callers (the LSP pipeline, the CLI) typically share
  a context across the prelude bootstrap and the user's file so
  freshly generated user-file names never collide with cached
  prelude names.  Tests typically pass a fresh context for
  reproducibility.

  Each top-level statement gets its own scope segment (``"sN_"``
  appended to the caller's scope, ``name_id`` reset to ``0``) so
  edits confined to statement *N* don't perturb the bound-name
  suffixes in statement *M > N*.  That edit-invariance is what
  Phase-3 Step 14's dependency-aware cache invalidation relies on
  -- without it, the structural hash of every downstream statement
  drifts on every edit and the cache is useless.
  """
  env: dict[str, object] = {}
  env['≠'] = ['≠']
  env['='] = ['=']
  # Using a space in the name to not collide with deduce identifiers
  env['no overload'] = {}
  outer_scope = ctx.scope
  outer_name_id = ctx.name_id
  result: list[Statement] = []
  for i, stmt in enumerate(ast):
    ctx.scope = outer_scope + 's' + str(i) + '_'
    ctx.name_id = 0
    result.append(stmt.uniquify(env, ctx))
  # Restore the caller's scope/counter -- the per-statement reset is
  # purely local to this call.  The caller's snapshot (e.g. the LSP
  # post-prelude baseline) sees the same state it passed in, and a
  # nested ``uniquify_deduce`` (called from ``Import.uniquify``)
  # leaves no residue in the surrounding statement's scope.
  ctx.scope = outer_scope
  ctx.name_id = outer_name_id
  check_post_uniquify_invariants(result)
  return result

def make_switch_for(meta: Meta, defs: Sequence[str], subject: Term,
                    cases: Sequence[SwitchProofCase]) -> SwitchProof:
  new_cases = [SwitchProofCase(c.location, c.pattern, c.assumptions,
                               ApplyDefsGoal(meta, [ResolvedVar(meta, None, t) for t in defs],
                                             c.body)) \
               for c in cases]
  return SwitchProof(meta, subject, new_cases)

@overload
def explicit_term_inst(term: Term) -> Term: ...

@overload
def explicit_term_inst(term: SwitchCase) -> SwitchCase: ...

def explicit_term_inst(term: Term | SwitchCase) -> Term | SwitchCase:
  match term:
    case TermInst(loc2, tyof, subject, tyargs, _):
      return TermInst(loc2, tyof, subject, tyargs, False)
    case Switch(loc2, tyof, subject, cases):
      return Switch(loc2, tyof, explicit_term_inst(subject),
                    [explicit_term_inst(c) for c in cases])
    case SwitchCase(loc2, pat, body):
      return SwitchCase(loc2, pat, explicit_term_inst(body))
    case Lambda(loc2, tyof, vars, body):
      return Lambda(loc2, tyof, vars, explicit_term_inst(body), env=term.env)
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


################################################################################
# Alpha Equivalence
################################################################################

def alpha_equiv(t1: object, t2: object) -> bool:
  """Test alpha-equivalence between two ASTs.

  Uses a parallel walk with a two-sided binding environment: each
  side tracks ``name -> fresh tag`` for the names it has bound. At
  a variable reference, look up the name in the side's environment:
  if bound on both sides, the tags must match; if bound on one side
  only, the terms are not alpha-equivalent; if free on both, the
  names must match (modulo the pre/post-uniquify isolation that
  ``Var.__eq__`` already encodes).

  Used by ``Lambda.__eq__`` / ``All.__eq__`` / ``Some.__eq__`` /
  ``TLet.__eq__``. Replaces the older approach of substituting one
  body to rename binders before comparing -- that approach was
  per-comparison O(|body|) allocation and got the asymmetric case
  (``Lambda(y, Var(x))`` vs ``Lambda(x, Var(x))``, the constant-x
  function vs the identity function) wrong in one direction.
  """
  return _alpha_equiv(t1, t2, {}, {})


def _alpha_equiv(t1: object, t2: object,
                 env1: dict[str, object], env2: dict[str, object]) -> bool:
  # TermInst / TAnnote are transparent for equality -- existing
  # __eq__ methods unwrap them. Unwrap on both sides so the rest of
  # this function only deals with the wrapped term.
  while isinstance(t1, (TermInst, TAnnote)):
    t1 = t1.subject
  while isinstance(t2, (TermInst, TAnnote)):
    t2 = t2.subject
  # Fast path: top-level (no renaming in scope). Defer to existing
  # __eq__ which encodes the leaf-level cross-class semantics.
  if not env1 and not env2:
    return bool(t1 == t2)
  if not isinstance(t1, AST):
    return bool(t1 == t2)
  if isinstance(t1, (Var, OverloadedVar, ResolvedVar, RecFun, GenRecFun)):
    return _alpha_equiv_varref(t1, t2, env1, env2)
  if isinstance(t1, Lambda):
    if not isinstance(t2, Lambda):
      return False
    return _alpha_equiv_binders(t1, t2, env1, env2)
  if isinstance(t1, All):
    if not isinstance(t2, All):
      return False
    return _alpha_equiv_all(t1, t2, env1, env2)
  if isinstance(t1, Some):
    if not isinstance(t2, Some):
      return False
    return _alpha_equiv_binders(t1, t2, env1, env2)
  if isinstance(t1, TLet):
    if not isinstance(t2, TLet):
      return False
    return _alpha_equiv_tlet(t1, t2, env1, env2)
  if isinstance(t1, FunctionType):
    return _alpha_equiv_function_type(t1, t2, env1, env2)
  # Default: structural walk. TermInst/TAnnote already unwrapped, so
  # a class mismatch here is real.
  if type(t1) is not type(t2):
    return False
  for fld in dc_fields(t1):
    if fld.name in t1._NON_STRUCTURAL_FIELDS:
      continue
    if not _alpha_equiv_value(getattr(t1, fld.name),
                              getattr(t2, fld.name), env1, env2):
      return False
  return True


def _alpha_equiv_value(v1: object, v2: object,
                       env1: dict[str, object], env2: dict[str, object]) -> bool:
  if isinstance(v1, AST):
    return _alpha_equiv(v1, v2, env1, env2)
  if isinstance(v1, list):
    if not isinstance(v2, list) or len(v1) != len(v2):
      return False
    return all(_alpha_equiv_value(a, b, env1, env2) for a, b in zip(v1, v2))
  if isinstance(v1, tuple):
    if not isinstance(v2, tuple) or len(v1) != len(v2):
      return False
    return all(_alpha_equiv_value(a, b, env1, env2) for a, b in zip(v1, v2))
  return bool(v1 == v2)


def _alpha_equiv_varref(
    t1: Var | OverloadedVar | ResolvedVar | RecFun | GenRecFun,
    t2: object,
    env1: dict[str, object],
    env2: dict[str, object],
) -> bool:
  # Names of comparable kinds. If t2 is not a comparable kind, fail.
  if not isinstance(t2, (Var, OverloadedVar, ResolvedVar, RecFun, GenRecFun)):
    return False
  n1 = named_callable_name(t1)
  n2 = named_callable_name(t2)
  in1 = n1 in env1
  in2 = n2 in env2
  if in1 != in2:
    # One bound, the other free -- not equal.
    return False
  if in1:
    # Both bound -- tags must match (i.e. same binder pair).
    if env1[n1] is not env2[n2]:
      return False
  else:
    # Both free -- names must match.
    if n1 != n2:
      return False
  # Phase isolation, mirroring the existing __eq__ rules:
  #   * Var (pre-uniquify) only matches Var / RecFun / GenRecFun
  #   * OverloadedVar / ResolvedVar (post-uniquify) match each other
  #     and RecFun / GenRecFun, never Var
  #   * RecFun / GenRecFun match any variant by name (no phase)
  if isinstance(t1, (RecFun, GenRecFun)):
    return True
  if isinstance(t1, Var):
    return isinstance(t2, (Var, RecFun, GenRecFun))
  return isinstance(t2, (OverloadedVar, ResolvedVar, RecFun, GenRecFun))


def _alpha_equiv_binder_types(vars1: Sequence[Tuple[str, Type | None]],
                              vars2: Sequence[Tuple[str, Type | None]],
                              env1:dict[str,object],
                              env2:dict[str,object]) -> bool:
  # Shared by Lambda / Some: matched (name, type) pairs where `None`
  # types match any concrete type. Types are compared under the
  # *outer* envs -- the inner binder names are added only for the
  # body. This matters when a type annotation references an outer
  # bound name (e.g. `Set<T>` in `all T:type. all A:Set<T>. ...`).
  if len(vars1) != len(vars2):
    return False
  for ((_, t1), (_, t2)) in zip(vars1, vars2):
    if t1 is not None and t2 is not None and not _alpha_equiv(t1, t2, env1, env2):
      return False
  return True


def _bind(env: dict[str, object], name: str, tag: object) -> dict[str, object]:
  new = dict(env)
  new[name] = tag
  return new


def _bind_all(env: dict[str, object],
              pairs: list[tuple[str, object]]) -> dict[str, object]:
  new = dict(env)
  for (name, tag) in pairs:
    new[name] = tag
  return new


def _alpha_equiv_binders(t1:Lambda | Some, t2:Lambda | Some,
                         env1:dict[str,object], env2:dict[str,object]) -> bool:
  # Shared by `Lambda` and `Some`: both bind a list of `.vars` (each an
  # optionally-typed `(name, type?)` pair) over a `.body`. Check the
  # binder types agree, then compare the bodies with a fresh tag bound
  # per position so the comparison is insensitive to the bound names.
  if not _alpha_equiv_binder_types(t1.vars, t2.vars, env1, env2):
    return False
  tags = [object() for _ in t1.vars]
  new_env1 = _bind_all(env1, [(x, tag) for ((x, _), tag) in zip(t1.vars, tags)])
  new_env2 = _bind_all(env2, [(y, tag) for ((y, _), tag) in zip(t2.vars, tags)])
  return _alpha_equiv(t1.body, t2.body, new_env1, new_env2)


def _alpha_equiv_all(t1:All, t2:All,
                     env1:dict[str,object], env2:dict[str,object]) -> bool:
  (x, tx) = t1.var
  (y, ty) = t2.var
  if tx is not None and ty is not None and not _alpha_equiv(tx, ty, env1, env2):
    return False
  tag = object()
  return _alpha_equiv(t1.body, t2.body, _bind(env1, x, tag), _bind(env2, y, tag))


def _alpha_equiv_tlet(t1:TLet, t2:TLet,
                      env1:dict[str,object], env2:dict[str,object]) -> bool:
  if not _alpha_equiv(t1.rhs, t2.rhs, env1, env2):
    return False
  tag = object()
  return _alpha_equiv(t1.body, t2.body,
                      _bind(env1, t1.var, tag),
                      _bind(env2, t2.var, tag))


def _alpha_equiv_function_type(t1: FunctionType, t2: object,
                               env1: dict[str, object],
                               env2: dict[str, object]) -> bool:
  # The only `Type`-level binder: `type_params` is a list of names
  # bound in `param_types` and `return_type`. Same parallel-walk
  # pattern as `_alpha_equiv_binders`, but `type_params` carries no
  # per-parameter type annotation -- it's just names.
  if not isinstance(t2, FunctionType):
    return False
  if len(t1.type_params) != len(t2.type_params):
    return False
  if len(t1.param_types) != len(t2.param_types):
    return False
  tags = [object() for _ in t1.type_params]
  new_env1 = _bind_all(env1, list(zip(t1.type_params, tags)))
  new_env2 = _bind_all(env2, list(zip(t2.type_params, tags)))
  for (p1, p2) in zip(t1.param_types, t2.param_types):
    if not _alpha_equiv(p1, p2, new_env1, new_env2):
      return False
  return _alpha_equiv(t1.return_type, t2.return_type, new_env1, new_env2)
