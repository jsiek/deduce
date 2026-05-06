"""Intermediate representation for the Deduce compiler.

This is a small functional core in the spirit of an ANF/SSA cousin:
- Types are erased. Generics, type-instantiations, and type annotations
  do not appear here. A backend treats every value uniformly.
- Proofs are erased. Theorems, holes, marks etc. never reach the IR.
- Names are the uniquified names that the type-checker produced. The IR
  inherits the global-uniqueness invariant; backends can rely on it.

A program is a flat list of top-level declarations: union types,
functions, and statements (`print`, `assert`). After Phase 1 step 3
(closure conversion) every `Lam` has been hoisted to the top level and
the only remaining lambdas are `MkClosure` placeholders. Pre-closure-
conversion the IR still contains nested `Lam` nodes; that's fine — the
shape is stable, only the population of nodes changes.

The pretty-printer's output is the contract that lowering tests assert
against; keep it stable.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import List, Tuple, Union


# ---------- terms ----------

@dataclass
class Var:
    """Reference to any in-scope name: parameter, let-binding, top-level."""
    name: str


@dataclass
class Bool:
    value: bool


@dataclass
class Int:
    value: int


@dataclass
class Lam:
    """Anonymous function. Eliminated by closure conversion (Step 3).
    After closure conversion only `MkClosure` remains."""
    params: List[str]
    body: "Term"


@dataclass
class MkClosure:
    """Created by closure conversion. `fn_name` refers to a top-level
    `Function`; `captures` are the values of the lambda's free variables
    at the point the closure was constructed."""
    fn_name: str
    captures: List["Term"]


@dataclass
class App:
    """Apply a value (closure or top-level function) to arguments."""
    rator: "Term"
    args: List["Term"]


@dataclass
class Let:
    name: str
    rhs: "Term"
    body: "Term"


@dataclass
class If:
    cond: "Term"
    thn: "Term"
    els: "Term"


@dataclass
class Con:
    """Constructor application. Nullary constructors have args=[]."""
    ctor: str
    args: List["Term"]


@dataclass
class PatCon:
    """Match a constructor and bind its parameters to fresh names."""
    ctor: str
    binds: List[str]


@dataclass
class PatBool:
    value: bool


Pattern = Union[PatCon, PatBool]


@dataclass
class MatchArm:
    pattern: Pattern
    body: "Term"


@dataclass
class Match:
    subject: "Term"
    arms: List[MatchArm]


Term = Union[Var, Bool, Int, Lam, MkClosure, App, Let, If, Con, Match]


# ---------- top-level ----------

@dataclass
class Constructor:
    name: str
    arity: int


@dataclass
class UnionDecl:
    name: str
    ctors: List[Constructor]


@dataclass
class Function:
    """A top-level function.

    After closure conversion (Step 3), `captures` lists the names that
    are bound from the closure's environment at function entry, in the
    order they appear in the matching `MkClosure(fn_name, ...)`. The
    body refers to captures by name, like any other variable; the
    backend is responsible for materialising those bindings on entry.

    Functions originating from top-level user `Define`/`RecFun` decls
    are never captured by closures and have `captures=[]`. Lambda-lifted
    functions produced by closure conversion have `captures=[fv0, ...]`."""
    name: str
    params: List[str]
    body: Term
    captures: List[str] = field(default_factory=list)


@dataclass
class Global:
    """A top-level non-function binding. Initialised at program start."""
    name: str
    body: Term


@dataclass
class Print:
    term: Term


@dataclass
class AssertEq:
    """`assert lhs = rhs` — runtime structural equality check."""
    lhs: Term
    rhs: Term


@dataclass
class AssertBool:
    """`assert <bool-typed-term>` — runtime check that it evaluates to true."""
    term: Term


TopLevel = Union[UnionDecl, Function, Global, Print, AssertEq, AssertBool]


@dataclass
class Program:
    """A complete IR program. `decls` is in source order; backends
    typically emit unions and functions first, then `main`-like glue
    that runs the globals/prints/asserts in order."""
    decls: List[TopLevel] = field(default_factory=list)


# ---------- pretty printer ----------
#
# The printer's output is the regression-test contract for lowering:
# stable, parseable-by-eye, no source locations. One declaration per
# block of lines.

def pp_program(p: Program) -> str:
    return "\n".join(pp_top(d) for d in p.decls) + ("\n" if p.decls else "")


def pp_top(d: TopLevel) -> str:
    match d:
        case UnionDecl(name, ctors):
            body = ", ".join(f"{c.name}/{c.arity}" for c in ctors)
            return f"union {name} {{{body}}}"
        case Function(name, params, body, captures):
            head = f"fn {name}"
            if captures:
                head += "[" + ", ".join(captures) + "]"
            head += "(" + ", ".join(params) + ")"
            return head + " = " + pp_term(body, 2)
        case Global(name, body):
            return f"global {name} = " + pp_term(body, 2)
        case Print(t):
            return "print " + pp_term(t, 2)
        case AssertEq(l, r):
            return "assert_eq " + pp_term(l, 2) + " == " + pp_term(r, 2)
        case AssertBool(t):
            return "assert " + pp_term(t, 2)
    raise AssertionError(f"pp_top: unknown decl {type(d).__name__}")


def pp_term(t: Term, indent: int) -> str:
    match t:
        case Var(name):
            return name
        case Bool(b):
            return "true" if b else "false"
        case Int(v):
            return str(v)
        case Lam(params, body):
            return "λ(" + ", ".join(params) + "). " + pp_term(body, indent)
        case MkClosure(fn, caps):
            return f"closure[{fn}]({', '.join(pp_term(c, indent) for c in caps)})"
        case App(rator, args):
            return pp_term(rator, indent) + "(" + ", ".join(pp_term(a, indent) for a in args) + ")"
        case Let(name, rhs, body):
            return f"let {name} = " + pp_term(rhs, indent) + " in " + pp_term(body, indent)
        case If(c, th, el):
            return "if " + pp_term(c, indent) + " then " + pp_term(th, indent) + " else " + pp_term(el, indent)
        case Con(ctor, []):
            return ctor
        case Con(ctor, args):
            return ctor + "(" + ", ".join(pp_term(a, indent) for a in args) + ")"
        case Match(subj, arms):
            arm_strs = []
            for arm in arms:
                match arm.pattern:
                    case PatBool(v):
                        ps = "true" if v else "false"
                    case PatCon(c, []):
                        ps = c
                    case PatCon(c, binds):
                        ps = c + "(" + ", ".join(binds) + ")"
                    case _:
                        raise AssertionError("pp_term: bad pattern")
                arm_strs.append("| " + ps + " -> " + pp_term(arm.body, indent))
            return "match " + pp_term(subj, indent) + " { " + " ".join(arm_strs) + " }"
    raise AssertionError(f"pp_term: unknown term {type(t).__name__}")


# ---------- traversal helpers ----------
#
# Used by closure conversion (free-variable analysis) and by emitters.
# Kept here so the contract is local to the IR module.

def free_vars(t: Term, bound: frozenset = frozenset()) -> set:
    match t:
        case Var(name):
            return set() if name in bound else {name}
        case Bool(_) | Int(_):
            return set()
        case Lam(params, body):
            return free_vars(body, bound | set(params))
        case MkClosure(_, caps):
            out: set = set()
            for c in caps:
                out |= free_vars(c, bound)
            return out
        case App(rator, args):
            out = free_vars(rator, bound)
            for a in args:
                out |= free_vars(a, bound)
            return out
        case Let(name, rhs, body):
            return free_vars(rhs, bound) | free_vars(body, bound | {name})
        case If(c, th, el):
            return free_vars(c, bound) | free_vars(th, bound) | free_vars(el, bound)
        case Con(_, args):
            out = set()
            for a in args:
                out |= free_vars(a, bound)
            return out
        case Match(subj, arms):
            out = free_vars(subj, bound)
            for arm in arms:
                match arm.pattern:
                    case PatCon(_, binds):
                        out |= free_vars(arm.body, bound | set(binds))
                    case PatBool(_):
                        out |= free_vars(arm.body, bound)
            return out
    raise AssertionError(f"free_vars: unknown term {type(t).__name__}")
