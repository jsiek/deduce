"""Closure conversion: hoist every `Lam` to a top-level `Function`.

Input: an `ir.Program` produced by lowering, possibly containing
`Lam` nodes inside function/global/print/assert bodies.

Output: an `ir.Program` with no `Lam` nodes. Each lambda becomes:
  - a fresh top-level `Function` whose `captures` list records the
    free variables that were in scope at the lambda's site, and
  - an `MkClosure(fn_name, [Var(fv) for fv in captures])` at the
    lambda's original position.

Top-level user-defined functions remain as they were — they cannot be
captured and never gain a `captures` list. References to top-level
names appearing as the rator of `App` are direct calls; references to
top-level names used as first-class values are not yet supported and
raise `CompileError` in the emitter, not here.

Pure rewriting; no I/O, no globals.
"""

from __future__ import annotations

from typing import Dict, List, Set

from compiler import ir


def closure_convert(p: ir.Program) -> ir.Program:
    top_names: Set[str] = set()
    for d in p.decls:
        if isinstance(d, (ir.Function, ir.Global)):
            top_names.add(d.name)
        elif isinstance(d, ir.UnionDecl):
            for c in d.ctors:
                top_names.add(c.name)

    # The `lifted` list collects new top-level Functions produced by
    # hoisting lambdas. Generated names embed the enclosing module so
    # link-time symbols don't collide across compilation units —
    # `<module>$lam<n>` is the source-IR name; emit_c mangles `$` to
    # `__`. The counter is per-module so per-module compiles produce
    # the same names as monolithic compiles for the same module.
    lifted: List[ir.Function] = []
    new_name_to_module: Dict[str, str] = dict(p.name_to_module)
    counters: Dict[str, int] = {}

    def fresh_lam_name(module: "str | None") -> str:
        key = module if module is not None else ""
        counters[key] = counters.get(key, 0) + 1
        n = counters[key]
        if module is None:
            return f"$lam{n}"
        # Place `$` between module and `lam` so `_mangle` produces a
        # readable `<module>__lam<n>` identifier without an awkward
        # `____` collision between the module/`$` separators.
        return f"{module}$lam{n}"

    def go(t: ir.Term, enclosing_module: "str | None") -> ir.Term:
        match t:
            case ir.Var(_) | ir.Bool(_) | ir.Int(_):
                return t
            case ir.Lam(params, body):
                # Convert the body first so any nested Lam is hoisted
                # and the body is now lambda-free.
                new_body = go(body, enclosing_module)
                # Free vars of the original lambda; deterministic order
                # (sorted) so the generated `captures` list and the
                # corresponding `MkClosure` args are stable across runs.
                fvs = sorted(ir.free_vars(t) - top_names)
                fn_name = fresh_lam_name(enclosing_module)
                if enclosing_module is not None:
                    new_name_to_module[fn_name] = enclosing_module
                lifted.append(ir.Function(
                    name=fn_name,
                    params=list(params),
                    body=new_body,
                    captures=list(fvs),
                    module=enclosing_module,
                ))
                return ir.MkClosure(
                    fn_name=fn_name,
                    captures=[ir.Var(fv) for fv in fvs],
                )
            case ir.MkClosure(fn, caps):
                # Already converted; recurse into capture expressions
                # in case some are themselves complex terms (current
                # converter only puts Vars there, but be defensive).
                return ir.MkClosure(fn, [go(c, enclosing_module) for c in caps])
            case ir.App(rator, args):
                return ir.App(go(rator, enclosing_module),
                              [go(a, enclosing_module) for a in args])
            case ir.Let(name, rhs, body):
                return ir.Let(name, go(rhs, enclosing_module),
                              go(body, enclosing_module))
            case ir.If(c, th, el):
                return ir.If(go(c, enclosing_module),
                             go(th, enclosing_module),
                             go(el, enclosing_module))
            case ir.Con(ctor, args):
                return ir.Con(ctor, [go(a, enclosing_module) for a in args])
            case ir.Match(subj, arms, loc):
                new_arms = [
                    ir.MatchArm(arm.pattern, go(arm.body, enclosing_module))
                    for arm in arms
                ]
                return ir.Match(go(subj, enclosing_module), new_arms, loc=loc)
            case ir.Eq(l, r):
                return ir.Eq(go(l, enclosing_module),
                             go(r, enclosing_module))
            case ir.Panic(_, _):
                return t
            case ir.MakeArray(s, loc):
                return ir.MakeArray(go(s, enclosing_module), loc=loc)
            case ir.ArrayGet(s, i, loc):
                return ir.ArrayGet(go(s, enclosing_module),
                                   go(i, enclosing_module), loc=loc)
        raise AssertionError(f"closure_convert: unknown term {type(t).__name__}")

    new_decls: List[ir.TopLevel] = []
    for d in p.decls:
        match d:
            case ir.UnionDecl():
                new_decls.append(d)
            case ir.Function(name, params, body, captures, loc, module):
                if captures:
                    raise AssertionError(
                        "closure_convert: input already has lifted functions; "
                        "refusing to convert a converted program"
                    )
                new_decls.append(ir.Function(
                    name=name, params=list(params),
                    body=go(body, module), captures=[], loc=loc,
                    module=module,
                ))
            case ir.Global(name, body, module):
                new_decls.append(ir.Global(name=name, body=go(body, module),
                                           module=module))
            case ir.Print(t):
                # Prints are top-level user-program code; their
                # lambdas belong to the program's main module.
                new_decls.append(ir.Print(go(t, p.main_module)))
            case ir.AssertEq(l, r):
                new_decls.append(ir.AssertEq(go(l, p.main_module),
                                             go(r, p.main_module)))
            case ir.AssertBool(t):
                new_decls.append(ir.AssertBool(go(t, p.main_module)))
            case _:
                raise AssertionError(
                    f"closure_convert: unknown top-level {type(d).__name__}"
                )

    return ir.Program(
        decls=new_decls + lifted,
        name_to_module=new_name_to_module,
        name_to_seq=p.name_to_seq,
        main_module=p.main_module,
        imports=p.imports,
        import_funcs=p.import_funcs,
        import_globals=p.import_globals,
        import_ctors=p.import_ctors,
    )
