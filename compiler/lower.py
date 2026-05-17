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

from typing import Dict, List, Optional, Set, Tuple

from lark.tree import Meta

import abstract_syntax as ast

from compiler import ir


class CompileError(Exception):
    """Raised when lowering hits a node that the compiler does not yet
    handle. Carries the AST node's location when available so the
    front-end can format it like any other Deduce error."""

    def __init__(self, location: Optional[Meta], message: str):
        self.location = location
        self.message = message
        super().__init__(_format_loc(location) + message)


def _format_loc(loc: Optional[Meta]) -> str:
    if loc is None:
        return ""
    try:
        if getattr(loc, "empty", True):
            return ""
        # `filename` is stashed onto Meta by the parser
        # (see abstract_syntax / parser.py); not a declared field.
        return f"{getattr(loc, 'filename', '?')}:{loc.line}: "
    except Exception:
        return ""


def _ast_loc(loc: Optional[Meta]) -> Optional[str]:
    """Format a `lark.tree.Meta` location as `file:line`, or None if
    the location is empty / missing. Used to populate `loc` fields on
    IR nodes for source-map output."""
    if loc is None:
        return None
    try:
        if getattr(loc, "empty", True):
            return None
        return f"{getattr(loc, 'filename', '?')}:{loc.line}"
    except Exception:
        return None


# --------------------------------------------------------------------------
# Top-level lowering
# --------------------------------------------------------------------------

def lower_program(stmts: List[ast.Statement],
                  main_module: str = "main",
                  separate: bool = False) -> ir.Program:
    """Entry point. Walks the top-level statement list, lowering each
    statement to an IR node.

    `main_module` is the module name attached to user-file statements
    (those not inside any `Import.ast`). Used for symbol mangling in
    the C emitter — `<Module>__<base_name>` keeps two compilation
    units' names from colliding at link time.

    `separate` controls how imports are handled:

    - `False` (default — monolithic mode): walks each `Import.ast`
      recursively and splices the imported module's declarations
      into the same flat list. Each module is recursed into at most
      once (matching the interpreter's `imported_modules`). Pruning
      downstream removes whatever isn't reached from a `print`.

    - `True` (per-module mode, Step 27): imports are NOT inlined.
      Only the user's own statements are lowered. The set of
      directly-imported modules is collected on `Program.imports`
      so the emitter can `#include` their headers and the runtime
      can call their `_init` functions in the right order.
      Pruning is skipped — cross-module reachability is the
      linker's job (`-Wl,--gc-sections`)."""
    (flat, name_to_module, name_to_seq, imports,
     import_funcs, import_globals, import_ctors) = _flatten_imports(
        stmts, main_module, separate=separate,
    )

    ctors: Set[str] = set()
    arities: Dict[str, int] = {}
    for s, _mod in flat:
        if isinstance(s, ast.Union):
            for c in s.alternatives:
                ctors.add(c.name)
                arities[c.name] = len(c.parameters)
    # In per-module mode, lower_call still needs to identify
    # imported ctors so `Call(Var(suc), args)` lowers to `Con(suc, args)`
    # rather than a function call. The ctor's body isn't ours to emit;
    # the macro and singleton come from the imported header.
    for cname, carity in import_ctors.items():
        ctors.add(cname)
        arities[cname] = carity

    lc = LoweringCtx(ctors=ctors, ctor_arities=arities)
    out: List[ir.TopLevel] = []
    for s, mod in flat:
        d = lc.lower_stmt(s, mod)
        if d is not None:
            if isinstance(d, list):
                out.extend(d)
            else:
                out.append(d)
    return ir.Program(
        decls=out,
        name_to_module=name_to_module,
        name_to_seq=name_to_seq,
        main_module=main_module,
        imports=imports,
        import_funcs=import_funcs,
        import_globals=import_globals,
        import_ctors=import_ctors,
    )


def _flatten_imports(
    stmts: List[ast.Statement],
    main_module: str,
    separate: bool = False,
) -> Tuple[
    List[Tuple[ast.Statement, str]],
    Dict[str, str],
    Dict[str, int],
    List[str],
    Dict[str, int],
    Set[str],
    Dict[str, int],
]:
    """Walk `stmts` and produce a flat list of (statement, module).

    In monolithic mode (`separate=False`) splices each `Import.ast`
    (the imported module's post-typecheck statement list — see
    `process_declaration` in proof_checker.py) in place of the
    import itself, deduplicating by module name. In per-module mode
    (`separate=True`) records the direct imports' names and stops —
    the imported modules are compiled separately.

    Returns:
      - statements paired with their module names,
      - name → module map covering every uniquified top-level name
        the lowered statements expose (function/global/union/
        constructor),
      - list of directly-imported module names, in source order
        with duplicates removed (only meaningful in per-module
        mode; empty in monolithic mode since there's no separate
        compilation unit boundary to record).
    """
    seen: Set[str] = set()
    out: List[tuple[ast.Statement, str]] = []
    name_to_module: Dict[str, str] = {}
    name_to_seq: Dict[str, int] = {}
    direct_imports: List[str] = []
    import_funcs: Dict[str, int] = {}
    import_globals: Set[str] = set()
    import_ctors: Dict[str, int] = {}
    counters_by_module: Dict[str, int] = {}

    def assign_seq(uniq_name: str, module: str) -> None:
        """Per-module ordinal for `uniq_name` based on order of
        encounter inside `module`. The ordinal is stable across
        compilation contexts because we walk a module's AST in the
        same order regardless of whether we're compiling that module
        standalone or pulling it in via `Import.ast` from another
        module's lowering. emit_c uses this as the within-module
        symbol disambiguator instead of the uniquify counter (whose
        values shift with the import set seen during one compile)."""
        n = counters_by_module.get(module, 0)
        name_to_seq[uniq_name] = n
        counters_by_module[module] = n + 1

    def record_decl_module(s: ast.Statement, module: str) -> None:
        if isinstance(s, ast.Define):
            name_to_module[s.name] = module
            assign_seq(s.name, module)
        elif isinstance(s, ast.RecFun):
            name_to_module[s.name] = module
            assign_seq(s.name, module)
        elif isinstance(s, ast.GenRecFun):
            name_to_module[s.name] = module
            assign_seq(s.name, module)
        elif isinstance(s, ast.Union):
            name_to_module[s.name] = module
            assign_seq(s.name, module)
            for c in s.alternatives:
                name_to_module[c.name] = module
                assign_seq(c.name, module)

    def record_imported_kind(s: ast.Statement) -> None:
        """In per-module mode we additionally need the kind/arity of
        every imported decl so emit_c can pick the right call shape
        and look up ctor macros via the imported `.h`."""
        if isinstance(s, ast.Define):
            unwrapped = s.body
            if isinstance(unwrapped, ast.Generic):
                unwrapped = unwrapped.body
            if isinstance(unwrapped, ast.Lambda):
                import_funcs[s.name] = len(unwrapped.vars)
            else:
                import_globals.add(s.name)
        elif isinstance(s, ast.RecFun):
            import_funcs[s.name] = len(s.params)
        elif isinstance(s, ast.GenRecFun):
            import_funcs[s.name] = len(s.vars)
        elif isinstance(s, ast.Union):
            for c in s.alternatives:
                import_ctors[c.name] = len(c.parameters)

    def register_imported(items: List[ast.Statement], current_module: str) -> None:
        """Walk an imported module's AST recording each top-level
        decl's name → module mapping plus its kind/arity. We don't
        emit anything for these statements — that happens in their
        own per-module compile — but we DO need both maps so
        references from the importing module's code mangle the
        same way as the definitions in the imported module's `.c`
        and dispatch through the right call shape."""
        for s in items:
            if isinstance(s, ast.Import):
                if s.name in seen:
                    continue
                seen.add(s.name)
                if s.ast is not None:
                    register_imported(s.ast, s.name)
            else:
                record_decl_module(s, current_module)
                record_imported_kind(s)

    def walk(items: List[ast.Statement], current_module: str) -> None:
        for s in items:
            if isinstance(s, ast.Import):
                if s.name in seen:
                    continue
                seen.add(s.name)
                if separate and current_module == main_module:
                    # Direct import: record so emit_c emits the
                    # right `#include` and the right module-init
                    # call, then recurse just to populate
                    # name_to_module so references mangle correctly.
                    direct_imports.append(s.name)
                    if s.ast is not None:
                        register_imported(s.ast, s.name)
                    continue
                if separate:
                    # Indirect import inside an already-handled
                    # module: don't recurse — it's the imported
                    # module's build-system dependency, not ours.
                    continue
                if s.ast is not None:
                    walk(s.ast, s.name)
            else:
                out.append((s, current_module))
                record_decl_module(s, current_module)

    walk(stmts, main_module)
    return (
        out, name_to_module, name_to_seq, direct_imports,
        import_funcs, import_globals, import_ctors,
    )


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

    def lower_stmt(self, s: ast.Statement, module: str) -> Optional[ir.TopLevel]:
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
                module=module,
            )
        if isinstance(s, ast.Define):
            return self.lower_define(s, module)
        if isinstance(s, ast.RecFun):
            return self.lower_recfun(s, module)
        if isinstance(s, ast.GenRecFun):
            return self.lower_genrecfun(s, module)
        if isinstance(s, ast.Print):
            return ir.Print(self.lower_term(s.term))
        if isinstance(s, ast.Assert):
            # Asserts have already been validated by `check_proofs`
            # before lowering runs. Re-checking them at the compiled
            # binary's startup is wasted work, and treating them as
            # roots would force the prelude's many sanity-check asserts
            # to drag in their dependencies. Drop them.
            return None
        raise CompileError(
            getattr(s, "location", None),
            f"compiler does not yet support top-level: {type(s).__name__}",
        )

    def lower_define(self, d: ast.Define, module: str) -> ir.TopLevel:
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
                loc=_ast_loc(d.location),
                module=module,
            )
        return ir.Global(name=d.name, body=self.lower_term(body),
                         module=module)

    def lower_recfun(self, r: ast.RecFun, module: str) -> ir.Function:
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

        match = ir.Match(ir.Var(scrutinee), arms, loc=_ast_loc(r.location))
        return ir.Function(
            name=r.name,
            params=[scrutinee] + other_params,
            body=match,
            loc=_ast_loc(r.location),
            module=module,
        )

    def lower_genrecfun(self, r: ast.GenRecFun, module: str) -> ir.Function:
        """Recfun-with-measure: a single-body recursive function. The
        measure expression and the `terminates` proof are erased — the
        compiler does no termination checking, just like the Deduce
        interpreter at runtime. The user already proved termination at
        check time, so a non-terminating compiled binary is on us only
        if the proof checker accepted a buggy proof."""
        params = [x for (x, _t) in r.vars]
        return ir.Function(
            name=r.name,
            params=params,
            body=self.lower_term(r.body),
            loc=_ast_loc(r.location),
            module=module,
        )

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
        if isinstance(t, ast.VarRef):
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
        if isinstance(t, ast.IfThen):
            # `if P then Q` (formula form) is `(not P) or Q`. As a
            # boolean term: `if P then Q else true`.
            return ir.If(
                self.lower_term(t.premise),
                self.lower_term(t.conclusion),
                ir.Bool(True),
            )
        if isinstance(t, ast.And):
            # n-ary short-circuit AND, right-folded.
            if not t.args:
                return ir.Bool(True)
            result = self.lower_term(t.args[-1])
            for a in reversed(t.args[:-1]):
                result = ir.If(self.lower_term(a), result, ir.Bool(False))
            return result
        if isinstance(t, ast.Or):
            if not t.args:
                return ir.Bool(False)
            result = self.lower_term(t.args[-1])
            for a in reversed(t.args[:-1]):
                result = ir.If(self.lower_term(a), ir.Bool(True), result)
            return result
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
        # Quantifiers are formulas — they show up in `fun`/`define`
        # bodies in the prelude (e.g. `fun EvenNat(n) { some m. … }`)
        # but are not computational. Lower to a panic stub; pruning
        # drops it if no `print`-reachable path actually evaluates it.
        if isinstance(t, (ast.Some, ast.All)):
            kind = "some" if isinstance(t, ast.Some) else "all"
            return ir.Panic(
                f"non-computational `{kind}` quantifier evaluated",
                loc=_ast_loc(t.location),
            )
        if isinstance(t, ast.MakeArray):
            return ir.MakeArray(
                self.lower_term(t.subject),
                loc=_ast_loc(t.location),
            )
        if isinstance(t, ast.ArrayGet):
            return ir.ArrayGet(
                self.lower_term(t.subject),
                self.lower_term(t.position),
                loc=_ast_loc(t.location),
            )
        if isinstance(t, ast.Array):
            # `Array` only appears in source as the result of reducing
            # `MakeArray` (literal `array([…])` uses the latter). The
            # post-uniquify AST should not contain `Array` directly.
            raise CompileError(
                t.location,
                "Array term reached compilation; expected MakeArray instead",
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
        if isinstance(rator, ast.VarRef):
            name = self._resolve(rator)
            base = ast.base_name(name)
            # Built-in equality. `=` is not a Deduce-source-level
            # function — it's parsed as `Call(Var('='), [a, b])` and
            # the type checker accepts it for any pair of same-typed
            # values. The runtime decides via `deduce_equal`.
            if base == "=" and len(c.args) == 2:
                return ir.Eq(
                    self.lower_term(c.args[0]),
                    self.lower_term(c.args[1]),
                )
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
        return ir.Match(
            self.lower_term(sw.subject), arms, loc=_ast_loc(sw.location),
        )

    def lower_pattern(self, p: ast.Pattern) -> ir.Pattern:
        if isinstance(p, ast.PatternBool):
            return ir.PatBool(p.value)
        if isinstance(p, ast.PatternCons):
            ctor = p.constructor
            # The constructor field is typically a Var; sometimes a
            # bare string slips through. Either way we want the
            # uniquified name.
            if isinstance(ctor, ast.VarRef):
                name = self._resolve(ctor)
            else:
                name = str(ctor)
            return ir.PatCon(name, list(p.parameters))
        raise CompileError(
            getattr(p, "location", None),
            f"compiler does not support pattern: {type(p).__name__}",
        )

    # ---- helpers -----------------------------------------------------

    def _resolve(self, v: ast.VarRef) -> str:
        # `OverloadedVar.name` is a derived property returning
        # `resolved_names[0]`, so this works uniformly: post-uniquify
        # variables always present a uniquified name via `.name`.
        # Pre-uniquify `Var` would return the source name, which is
        # only sensible if the lowering is processing a sub-AST that
        # bypasses uniquify (rare; left intact).
        return v.get_name()


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
            case ir.Match(subj, arms, loc):
                new_arms = []
                for arm in arms:
                    if isinstance(arm.pattern, ir.PatCon):
                        inner = blocked | set(arm.pattern.binds)
                    else:
                        inner = blocked
                    new_arms.append(ir.MatchArm(arm.pattern, go(arm.body, inner)))
                return ir.Match(go(subj, blocked), new_arms, loc=loc)
            case ir.Eq(l, r):
                return ir.Eq(go(l, blocked), go(r, blocked))
            case ir.Panic(_, _):
                return t
            case ir.MakeArray(s, loc):
                return ir.MakeArray(go(s, blocked), loc=loc)
            case ir.ArrayGet(s, i, loc):
                return ir.ArrayGet(go(s, blocked), go(i, blocked), loc=loc)
        raise AssertionError(f"subst_vars: unknown {type(t).__name__}")

    return go(t, set())
