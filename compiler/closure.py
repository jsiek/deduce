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

from typing import List, Set

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
    # hoisting lambdas. Generated names use `$lam<n>` so they cannot
    # collide with Deduce's uniquified names (which never contain `$`).
    lifted: List[ir.Function] = []
    counter = [0]

    def fresh_lam_name() -> str:
        counter[0] += 1
        return f"$lam{counter[0]}"

    def go(t: ir.Term) -> ir.Term:
        match t:
            case ir.Var(_) | ir.Bool(_) | ir.Int(_):
                return t
            case ir.Lam(params, body):
                # Convert the body first so any nested Lam is hoisted
                # and the body is now lambda-free.
                new_body = go(body)
                # Free vars of the original lambda; deterministic order
                # (sorted) so the generated `captures` list and the
                # corresponding `MkClosure` args are stable across runs.
                fvs = sorted(ir.free_vars(t) - top_names)
                fn_name = fresh_lam_name()
                lifted.append(ir.Function(
                    name=fn_name,
                    params=list(params),
                    body=new_body,
                    captures=list(fvs),
                ))
                return ir.MkClosure(
                    fn_name=fn_name,
                    captures=[ir.Var(fv) for fv in fvs],
                )
            case ir.MkClosure(fn, caps):
                # Already converted; recurse into capture expressions
                # in case some are themselves complex terms (current
                # converter only puts Vars there, but be defensive).
                return ir.MkClosure(fn, [go(c) for c in caps])
            case ir.App(rator, args):
                return ir.App(go(rator), [go(a) for a in args])
            case ir.Let(name, rhs, body):
                return ir.Let(name, go(rhs), go(body))
            case ir.If(c, th, el):
                return ir.If(go(c), go(th), go(el))
            case ir.Con(ctor, args):
                return ir.Con(ctor, [go(a) for a in args])
            case ir.Match(subj, arms):
                new_arms = [ir.MatchArm(arm.pattern, go(arm.body)) for arm in arms]
                return ir.Match(go(subj), new_arms)
        raise AssertionError(f"closure_convert: unknown term {type(t).__name__}")

    new_decls: List[ir.TopLevel] = []
    for d in p.decls:
        match d:
            case ir.UnionDecl():
                new_decls.append(d)
            case ir.Function(name, params, body, captures):
                if captures:
                    raise AssertionError(
                        "closure_convert: input already has lifted functions; "
                        "refusing to convert a converted program"
                    )
                new_decls.append(ir.Function(
                    name=name, params=list(params),
                    body=go(body), captures=[],
                ))
            case ir.Global(name, body):
                new_decls.append(ir.Global(name=name, body=go(body)))
            case ir.Print(t):
                new_decls.append(ir.Print(go(t)))
            case ir.AssertEq(l, r):
                new_decls.append(ir.AssertEq(go(l), go(r)))
            case ir.AssertBool(t):
                new_decls.append(ir.AssertBool(go(t)))
            case _:
                raise AssertionError(
                    f"closure_convert: unknown top-level {type(d).__name__}"
                )

    return ir.Program(decls=new_decls + lifted)
