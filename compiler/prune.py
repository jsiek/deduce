"""Reachability-based pruning of an IR program.

Drops top-level `Function`, `Global`, and `UnionDecl` declarations that
are not transitively referenced from a "root" — anything that runs at
binary startup. Today the only roots are top-level `Print` decls.
(`AssertEq`/`AssertBool` are dropped in lowering; see lower.py.)

The pass is purely subtractive: it never reorders, never rewrites, and
never collapses two decls into one. If pruning produces an
under-pruned program (something kept that wasn't actually needed) the
binary works correctly but bigger; if it over-prunes (something
dropped that was needed) the emitter's `unbound name in emission`
error fires before any C is written. Both failure modes are loud.

Constructors are reached transitively: `Con(c, …)` and `PatCon(c, …)`
mark the constructor's owning union as live. We don't prune
individual constructors of a live union — they share the tag enum and
emitting half a union is more pain than it's worth.
"""

from __future__ import annotations

from typing import Dict, List, Set

from compiler import ir


def prune(p: ir.Program) -> ir.Program:
    name_to_decl: Dict[str, ir.TopLevel] = {}
    ctor_to_union: Dict[str, str] = {}
    for d in p.decls:
        if isinstance(d, ir.UnionDecl):
            for c in d.ctors:
                ctor_to_union[c.name] = d.name
        elif isinstance(d, (ir.Function, ir.Global)):
            name_to_decl[d.name] = d

    reached_names: Set[str] = set()
    reached_unions: Set[str] = set()
    work: List[str] = []

    def mark(n: str) -> None:
        if n in name_to_decl and n not in reached_names:
            reached_names.add(n)
            work.append(n)
        elif n in ctor_to_union:
            reached_unions.add(ctor_to_union[n])

    for d in p.decls:
        if isinstance(d, ir.Print):
            for n in _referenced(d.term):
                mark(n)
        elif isinstance(d, ir.AssertEq):
            for n in _referenced(d.lhs):
                mark(n)
            for n in _referenced(d.rhs):
                mark(n)
        elif isinstance(d, ir.AssertBool):
            for n in _referenced(d.term):
                mark(n)

    while work:
        name = work.pop()
        decl = name_to_decl[name]
        if isinstance(decl, ir.Function):
            for n in _referenced(decl.body):
                mark(n)
        elif isinstance(decl, ir.Global):
            for n in _referenced(decl.body):
                mark(n)

    new_decls: List[ir.TopLevel] = []
    for d in p.decls:
        if isinstance(d, ir.UnionDecl):
            if d.name in reached_unions:
                new_decls.append(d)
        elif isinstance(d, (ir.Function, ir.Global)):
            if d.name in reached_names:
                new_decls.append(d)
        else:
            # Print / AssertEq / AssertBool always survive — they are
            # the roots themselves (and asserts are normally dropped in
            # lowering, so they shouldn't be here anyway).
            new_decls.append(d)
    return ir.Program(decls=new_decls)


def _referenced(t: ir.Term) -> Set[str]:
    """All names transitively referenced from a term: variables,
    constructors, and the `fn_name` inside a `MkClosure`. Local
    bindings shadow nothing in practice (uniquify gives every name
    a globally-unique id), so we don't track scopes here."""
    out: Set[str] = set()

    def walk(t: ir.Term) -> None:
        match t:
            case ir.Var(n):
                out.add(n)
            case ir.Bool(_) | ir.Int(_):
                pass
            case ir.Lam(_, body):
                walk(body)
            case ir.MkClosure(fn, caps):
                out.add(fn)
                for c in caps:
                    walk(c)
            case ir.App(rator, args):
                walk(rator)
                for a in args:
                    walk(a)
            case ir.Let(_, rhs, body):
                walk(rhs)
                walk(body)
            case ir.If(c, th, el):
                walk(c)
                walk(th)
                walk(el)
            case ir.Con(ctor, args):
                out.add(ctor)
                for a in args:
                    walk(a)
            case ir.Match(subj, arms, _):
                walk(subj)
                for arm in arms:
                    if isinstance(arm.pattern, ir.PatCon):
                        out.add(arm.pattern.ctor)
                    walk(arm.body)
            case ir.Eq(l, r):
                walk(l)
                walk(r)
            case ir.Panic(_, _):
                pass
            case ir.MakeArray(s, _):
                walk(s)
            case ir.ArrayGet(s, i, _):
                walk(s)
                walk(i)

    walk(t)
    return out
