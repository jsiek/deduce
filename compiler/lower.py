"""Lower a checked Deduce AST to the compiler IR.

Input: the post-uniquify, post-typecheck list of `Statement`s that the
proof checker would otherwise hand to `check_proofs`. We rely on
`Var.resolved_names` having been filled in.

Output: an `ir.Program`. Anything outside the executable fragment
(theorems, postulates, predicates, holes, ...) is dropped or rejected
explicitly — there is no silent fallthrough.

Phase 1 supports: Bool, Int literals; Var; Conditional; TLet; Lambda;
Generic; TermInst; TAnnote; Mark; Call (function or constructor);
Switch (PatternCons / PatternBool); Define; RecFun; Union; Print;
Assert. MakeArray/ArrayGet/GenRecFun/Array etc. raise CompileError.
"""

from __future__ import annotations

from typing import Dict, List, Optional, Set

import abstract_syntax as ast

from compiler import ir


class CompileError(Exception):
    """Raised when lowering hits a node that the compiler does not yet
    handle. Carries the AST node's location when available so the
    front-end can format it like any other Deduce error."""

    def __init__(self, location, message: str):
        self.location = location
        self.message = message
        super().__init__(_format_loc(location) + message)


def _format_loc(loc) -> str:
    if loc is None:
        return ""
    try:
        if getattr(loc, "empty", True):
            return ""
        return f"{loc.filename}:{loc.line}: "
    except Exception:
        return ""


# --------------------------------------------------------------------------
# Top-level lowering
# --------------------------------------------------------------------------

def lower_program(stmts: List[ast.Statement]) -> ir.Program:
    """Entry point. Walks the top-level statement list once to collect
    constructor names (so `Call(Var(ctor), ...)` can become `Con` rather
    than `App`), then lowers each statement."""
    ctors: Set[str] = set()
    arities: Dict[str, int] = {}
    for s in stmts:
        if isinstance(s, ast.Union):
            for c in s.alternatives:
                ctors.add(c.name)
                arities[c.name] = len(c.parameters)

    lc = LoweringCtx(ctors=ctors, ctor_arities=arities)
    out: List[ir.TopLevel] = []
    for s in stmts:
        d = lc.lower_stmt(s)
        if d is not None:
            if isinstance(d, list):
                out.extend(d)
            else:
                out.append(d)
    return ir.Program(decls=out)


class LoweringCtx:
    def __init__(self, ctors: Set[str], ctor_arities: Dict[str, int]):
        self.ctors = ctors
        self.ctor_arities = ctor_arities
        self._gensym = 0

    def fresh(self, hint: str = "_t") -> str:
        n = self._gensym
        self._gensym += 1
        # `$` in the prefix avoids collision with Deduce uniquified names,
        # which use `.` and digits but not `$`.
        return f"${hint}{n}"

    # ---- statements --------------------------------------------------

    def lower_stmt(self, s: ast.Statement):
        if isinstance(s, ast.Theorem) or isinstance(s, ast.Postulate) \
           or isinstance(s, ast.Predicate) or isinstance(s, ast.Auto) \
           or isinstance(s, ast.Inductive) or isinstance(s, ast.Module) \
           or isinstance(s, ast.Export) or isinstance(s, ast.Associative) \
           or isinstance(s, ast.Trace):
            return None
        if isinstance(s, ast.Import):
            # Imports are lowered to a flat statement list upstream
            # (the proof checker walks them via `Import.ast`); the
            # caller decides whether to splice them in. Here we treat
            # an `Import` as "no top-level code", which is the right
            # answer if the caller already inlined imports. If the
            # caller did NOT inline imports the compiler will simply
            # be missing definitions; that fails later with a clearer
            # "undefined name" error.
            return None
        if isinstance(s, ast.Union):
            return ir.UnionDecl(
                name=s.name,
                ctors=[ir.Constructor(c.name, len(c.parameters))
                       for c in s.alternatives],
            )
        if isinstance(s, ast.Define):
            return self.lower_define(s)
        if isinstance(s, ast.RecFun):
            return self.lower_recfun(s)
        if isinstance(s, ast.GenRecFun):
            raise CompileError(
                s.location,
                "GenRecFun (recfun with measure) is not supported in Phase 1; "
                "see docs/compile-plan.md Step 7",
            )
        if isinstance(s, ast.Print):
            return ir.Print(self.lower_term(s.term))
        if isinstance(s, ast.Assert):
            return self.lower_assert(s)
        raise CompileError(
            getattr(s, "location", None),
            f"compiler does not yet support top-level: {type(s).__name__}",
        )

    def lower_define(self, d: ast.Define):
        body = d.body
        # `define f = generic <T> { fun x { ... } }` and
        # `define f = fun x { ... }` should both become a top-level
        # function rather than a global pointing at a closure. This
        # unwraps Generic to expose the inner Lambda.
        unwrapped = body
        if isinstance(unwrapped, ast.Generic):
            unwrapped = unwrapped.body
        if isinstance(unwrapped, ast.Lambda):
            params = [x for (x, _t) in unwrapped.vars]
            return ir.Function(
                name=d.name,
                params=params,
                body=self.lower_term(unwrapped.body),
            )
        return ir.Global(name=d.name, body=self.lower_term(body))

    def lower_recfun(self, r: ast.RecFun):
        if len(r.cases) == 0:
            raise CompileError(r.location, "RecFun with no cases")

        n_args = len(r.params)
        scrutinee = self.fresh("scr")
        # The other parameter names come from the first case; we then
        # rename later cases' parameter lists to match.
        first = r.cases[0]
        other_params = [p for p in first.parameters]
        # Sanity: the FunCase contract is N total args, where the first
        # is matched and the rest are named in `parameters`. Confirm
        # arity lines up with the RecFun's declared parameter count.
        if 1 + len(other_params) != n_args:
            raise CompileError(
                r.location,
                f"RecFun {r.name} arity mismatch: header expects {n_args} "
                f"but first case names {1 + len(other_params)}",
            )

        arms: List[ir.MatchArm] = []
        for case in r.cases:
            # Rename this case's `parameters` to the canonical names
            # taken from the first case.
            sub: Dict[str, str] = {}
            for old, new in zip(case.parameters, other_params):
                if old != new:
                    sub[old] = new
            body = self.lower_term(case.body)
            if sub:
                body = subst_vars(body, sub)
            pat = self.lower_pattern(case.pattern)
            arms.append(ir.MatchArm(pat, body))

        match = ir.Match(ir.Var(scrutinee), arms)
        return ir.Function(
            name=r.name,
            params=[scrutinee] + other_params,
            body=match,
        )

    def lower_assert(self, s: ast.Assert):
        # `assert lhs = rhs` becomes a structural-equality check;
        # everything else (incl. `assert b` for a bool b) becomes
        # AssertBool.
        f = s.formula
        if isinstance(f, ast.Call) and isinstance(f.rator, ast.Var) \
           and ast.base_name(f.rator.name) == "=" and len(f.args) == 2:
            return ir.AssertEq(
                self.lower_term(f.args[0]),
                self.lower_term(f.args[1]),
            )
        return ir.AssertBool(self.lower_term(f))

    # ---- terms -------------------------------------------------------

    def lower_term(self, t: ast.Term) -> ir.Term:
        # Strip transparent wrappers first.
        if isinstance(t, ast.TAnnote):
            return self.lower_term(t.subject)
        if isinstance(t, ast.Mark):
            return self.lower_term(t.subject)
        if isinstance(t, ast.TermInst):
            return self.lower_term(t.subject)
        if isinstance(t, ast.Generic):
            return self.lower_term(t.body)

        if isinstance(t, ast.Bool):
            return ir.Bool(t.value)
        if isinstance(t, ast.Int):
            return ir.Int(t.value)
        if isinstance(t, ast.Var):
            name = self._resolve(t)
            if name in self.ctors and self.ctor_arities.get(name, 0) == 0:
                # Nullary constructor used as a value.
                return ir.Con(name, [])
            return ir.Var(name)
        if isinstance(t, ast.Conditional):
            return ir.If(
                self.lower_term(t.cond),
                self.lower_term(t.thn),
                self.lower_term(t.els),
            )
        if isinstance(t, ast.TLet):
            return ir.Let(
                t.var,
                self.lower_term(t.rhs),
                self.lower_term(t.body),
            )
        if isinstance(t, ast.Lambda):
            params = [x for (x, _t) in t.vars]
            return ir.Lam(params, self.lower_term(t.body))
        if isinstance(t, ast.Call):
            return self.lower_call(t)
        if isinstance(t, ast.Switch):
            return self.lower_switch(t)
        if isinstance(t, ast.Hole) or isinstance(t, ast.Omitted):
            raise CompileError(
                t.location,
                "hole/omitted term reached compilation; the proof "
                "checker should have rejected this earlier",
            )
        if isinstance(t, ast.MakeArray) or isinstance(t, ast.ArrayGet) \
           or isinstance(t, ast.Array):
            raise CompileError(
                t.location,
                "arrays are not yet supported by the compiler "
                "(Phase 2 step 8)",
            )
        raise CompileError(
            getattr(t, "location", None),
            f"compiler does not yet support term: {type(t).__name__}",
        )

    def lower_call(self, c: ast.Call) -> ir.Term:
        rator = c.rator
        # Peel TermInst: the type instantiation is irrelevant at runtime.
        while isinstance(rator, ast.TermInst):
            rator = rator.subject
        if isinstance(rator, ast.Var):
            name = self._resolve(rator)
            if name in self.ctors:
                return ir.Con(name, [self.lower_term(a) for a in c.args])
        return ir.App(
            self.lower_term(c.rator),
            [self.lower_term(a) for a in c.args],
        )

    def lower_switch(self, sw: ast.Switch) -> ir.Term:
        arms: List[ir.MatchArm] = []
        for case in sw.cases:
            arms.append(ir.MatchArm(
                self.lower_pattern(case.pattern),
                self.lower_term(case.body),
            ))
        return ir.Match(self.lower_term(sw.subject), arms)

    def lower_pattern(self, p: ast.Pattern) -> ir.Pattern:
        if isinstance(p, ast.PatternBool):
            return ir.PatBool(p.value)
        if isinstance(p, ast.PatternCons):
            ctor = p.constructor
            # The constructor field is typically a Var; sometimes a
            # bare string slips through. Either way we want the
            # uniquified name.
            if isinstance(ctor, ast.Var):
                name = self._resolve(ctor)
            else:
                name = str(ctor)
            return ir.PatCon(name, list(p.parameters))
        raise CompileError(
            getattr(p, "location", None),
            f"compiler does not support pattern: {type(p).__name__}",
        )

    # ---- helpers -----------------------------------------------------

    def _resolve(self, v: ast.Var) -> str:
        # `resolved_names` is filled in by uniquify and may contain
        # multiple entries when the name is overloaded. After
        # type-checking, the first entry is the resolved overload.
        if v.resolved_names:
            return v.resolved_names[0]
        return v.name


# --------------------------------------------------------------------------
# IR-level variable substitution
# --------------------------------------------------------------------------

def subst_vars(t: ir.Term, sub: Dict[str, str]) -> ir.Term:
    """Rename free variable occurrences according to `sub`. Respects
    binders (Lam params, Let names, Match arm pattern binds)."""

    def go(t: ir.Term, blocked: Set[str]) -> ir.Term:
        match t:
            case ir.Var(name):
                if name in blocked:
                    return t
                return ir.Var(sub.get(name, name))
            case ir.Bool(_) | ir.Int(_):
                return t
            case ir.Lam(params, body):
                inner = blocked | set(params)
                return ir.Lam(params, go(body, inner))
            case ir.MkClosure(fn, caps):
                return ir.MkClosure(fn, [go(c, blocked) for c in caps])
            case ir.App(rator, args):
                return ir.App(go(rator, blocked), [go(a, blocked) for a in args])
            case ir.Let(name, rhs, body):
                new_rhs = go(rhs, blocked)
                inner = blocked | {name}
                return ir.Let(name, new_rhs, go(body, inner))
            case ir.If(c, th, el):
                return ir.If(go(c, blocked), go(th, blocked), go(el, blocked))
            case ir.Con(ctor, args):
                return ir.Con(ctor, [go(a, blocked) for a in args])
            case ir.Match(subj, arms):
                new_arms = []
                for arm in arms:
                    if isinstance(arm.pattern, ir.PatCon):
                        inner = blocked | set(arm.pattern.binds)
                    else:
                        inner = blocked
                    new_arms.append(ir.MatchArm(arm.pattern, go(arm.body, inner)))
                return ir.Match(go(subj, blocked), new_arms)
        raise AssertionError(f"subst_vars: unknown {type(t).__name__}")

    return go(t, set())
