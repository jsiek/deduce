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
from typing import Dict, List, Union


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
    loc: "str | None" = None  # source `file:line`, for runtime panic messages


@dataclass
class Panic:
    """Stand-in for a non-computational term (e.g. a `some`/`all`
    formula in a `fun` body) or a reference to a name we couldn't
    lower. Emits a `deduce_unreachable_value` call at the C level —
    the compiled program aborts if execution actually reaches it.

    The whole point is to let the rest of the function lower
    successfully so the pruner can drop it if it isn't reached at
    runtime. If pruning keeps it, the user gets a clear runtime
    message naming what went wrong."""
    msg: str
    loc: "str | None" = None  # source `file:line`, prepended to msg in output


@dataclass
class Eq:
    """Structural equality, the only built-in primitive in the IR.
    Comes from `Call(Var('='), [a, b])` in the source. Closures
    compare by pointer identity (matches the runtime `deduce_equal`)."""
    lhs: "Term"
    rhs: "Term"


@dataclass
class MakeArray:
    """Convert a `List<T>`-shaped value (a chain of `node(_, _)` ending
    in `empty`) into a runtime array. Uses base-name dispatch at the
    runtime, matching the interpreter's `isNodeList` semantics — any
    union with constructors named `empty`/`node` works."""
    subject: "Term"
    loc: "str | None" = None  # source `file:line`, for runtime panic messages


@dataclass
class ArrayGet:
    """Read an array element by index. The index is a Nat or UInt;
    the runtime decodes it by inspecting constructor names. Out-of-
    bounds returns the original ArrayGet — matches the interpreter
    convention of not raising on OOB. (We diverge: the compiled
    binary aborts via `deduce_panic` instead.)"""
    subject: "Term"
    index: "Term"
    loc: "str | None" = None  # source `file:line`, for OOB panic messages


Term = Union[Var, Bool, Int, Lam, MkClosure, App, Let, If, Con, Match, Eq, Panic, MakeArray, ArrayGet]


# ---------- top-level ----------

@dataclass
class Constructor:
    name: str
    arity: int


@dataclass
class UnionDecl:
    name: str
    ctors: List[Constructor]
    # Source module the union was declared in. Used by emit_c to mangle
    # constructor symbols as `<Module>__<base_name>`. None means
    # "synthetic / no specific home" — emit_c falls back to a generic
    # mangle of the uniquified name in that case.
    module: "str | None" = None


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
    functions produced by closure conversion have `captures=[fv0, ...]`.

    `loc` is the original `.pf` file:line where the function was
    declared. Emitted as a `// from foo.pf:42` comment so a debugger
    or human reader can navigate from the generated C back to source.

    `module` is the source module the function came from (or None for
    synthesised functions like closure-conversion `$lam<N>`). Used by
    emit_c for `<Module>__<base_name>` symbol mangling."""
    name: str
    params: List[str]
    body: Term
    captures: List[str] = field(default_factory=list)
    loc: "str | None" = None
    module: "str | None" = None


@dataclass
class Global:
    """A top-level non-function binding. Initialised at program start."""
    name: str
    body: Term
    module: "str | None" = None


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
    that runs the globals/prints/asserts in order.

    `name_to_module` is a flat lookup from each top-level decl's
    uniquified name (function/global/union/constructor) to its source
    module. emit_c consults it to mangle reference sites — calls,
    constructor applications, pattern matches — without needing to
    chase parents.

    `main_module` is the module name attached to user-file
    statements that aren't inside any `Import.ast`. Used by closure
    conversion to module-prefix lifted lambdas inside Print/Global
    bodies, and by emit_c to know which module's `_init` to call
    from `deduce_program_main`.

    `imports` lists the directly-imported module names, in source
    order with duplicates removed. Only populated in per-module
    mode (Step 27 of `docs/separate-compile-plan.md`); empty in
    monolithic mode.

    `import_funcs` / `import_globals` / `import_ctors` describe
    decls that live in imported modules. emit_c needs to know
    these so calls and ctor applications dispatch correctly
    (direct call vs. closure call, ctor IDs available via the
    imported header). All three are empty in monolithic mode
    (where the decls are flattened into `decls` directly)."""
    decls: List[TopLevel] = field(default_factory=list)
    name_to_module: Dict[str, str] = field(default_factory=dict)
    # Per-module ordinal of each top-level uniquified name (function /
    # global / union / constructor). emit_c uses this as the
    # within-module symbol disambiguator instead of the uniquify
    # counter, because the uniquify counter shifts with the import
    # set seen during one compile while the ordinal is computed by
    # walking the module's AST in source order — stable regardless
    # of whether the module was compiled standalone or pulled in via
    # `Import.ast`.
    name_to_seq: Dict[str, int] = field(default_factory=dict)
    main_module: "str | None" = None
    imports: List[str] = field(default_factory=list)
    import_funcs: Dict[str, int] = field(default_factory=dict)
    import_globals: "set[str]" = field(default_factory=set)
    import_ctors: Dict[str, int] = field(default_factory=dict)


# ---------- pretty printer ----------
#
# The printer's output is the regression-test contract for lowering:
# stable, parseable-by-eye, no source locations. One declaration per
# block of lines.

def pp_program(p: Program) -> str:
    return "\n".join(pp_top(d) for d in p.decls) + ("\n" if p.decls else "")


def pp_top(d: TopLevel) -> str:
    match d:
        case UnionDecl(name, ctors, _):
            body = ", ".join(f"{c.name}/{c.arity}" for c in ctors)
            return f"union {name} {{{body}}}"
        case Function(name, params, body, captures, _, _):
            head = f"fn {name}"
            if captures:
                head += "[" + ", ".join(captures) + "]"
            head += "(" + ", ".join(params) + ")"
            return head + " = " + pp_term(body, 2)
        case Global(name, body, _):
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
        case Match(subj, arms, _):
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
        case Eq(l, r):
            return "(" + pp_term(l, indent) + " == " + pp_term(r, indent) + ")"
        case Panic(msg, _):
            return f"panic({msg!r})"
        case MakeArray(s, _):
            return "array(" + pp_term(s, indent) + ")"
        case ArrayGet(s, i, _):
            return pp_term(s, indent) + "[" + pp_term(i, indent) + "]"
    raise AssertionError(f"pp_term: unknown term {type(t).__name__}")


# ---------- traversal helpers ----------
#
# Used by closure conversion (free-variable analysis) and by emitters.
# Kept here so the contract is local to the IR module.

def verify(p: Program) -> None:
    """Walk an IR program and assert every node is a known IR class.

    This is a safety net: it would fire if a future change to lowering
    accidentally embedded an `abstract_syntax.*` AST node (a Type, or a
    Term that wasn't translated) inside an IR term. The IR has no
    field that holds a type — there is nothing to "erase" at this
    layer; the check enforces that the layer below us did its job.

    Raises `AssertionError` on the first stray node it finds, with the
    enclosing decl name in the message so the failure is locatable."""
    top_classes = (UnionDecl, Function, Global, Print, AssertEq, AssertBool)
    term_classes = (
        Var, Bool, Int, Lam, MkClosure, App, Let, If, Con, Match, Eq,
        Panic, MakeArray, ArrayGet,
    )

    def check_term(t: object, ctx: str) -> None:
        if not isinstance(t, term_classes):
            raise AssertionError(
                f"verify: non-IR term {type(t).__name__} in {ctx}"
            )
        match t:
            case Var(_) | Bool(_) | Int(_):
                return
            case Lam(_, body):
                check_term(body, ctx)
            case MkClosure(_, caps):
                for c in caps:
                    check_term(c, ctx)
            case App(rator, args):
                check_term(rator, ctx)
                for a in args:
                    check_term(a, ctx)
            case Let(_, rhs, body):
                check_term(rhs, ctx)
                check_term(body, ctx)
            case If(c, th, el):
                check_term(c, ctx)
                check_term(th, ctx)
                check_term(el, ctx)
            case Con(_, args):
                for a in args:
                    check_term(a, ctx)
            case Match(subj, arms, _):
                check_term(subj, ctx)
                for arm in arms:
                    if not isinstance(arm, MatchArm):
                        raise AssertionError(
                            f"verify: non-MatchArm in {ctx}"
                        )
                    if not isinstance(arm.pattern, (PatBool, PatCon)):
                        raise AssertionError(
                            f"verify: non-IR pattern in {ctx}"
                        )
                    check_term(arm.body, ctx)
            case Eq(l, r):
                check_term(l, ctx)
                check_term(r, ctx)
            case Panic(_, _):
                pass
            case MakeArray(s, _):
                check_term(s, ctx)
            case ArrayGet(s, i, _):
                check_term(s, ctx)
                check_term(i, ctx)

    if not isinstance(p, Program):
        raise AssertionError(f"verify: not a Program: {type(p).__name__}")
    for d in p.decls:
        if not isinstance(d, top_classes):
            raise AssertionError(
                f"verify: non-IR top-level {type(d).__name__}"
            )
        match d:
            case UnionDecl(_, ctors, _):
                for c in ctors:
                    if not isinstance(c, Constructor):
                        raise AssertionError("verify: non-IR ctor")
            case Function(name, _, body, _, _, _):
                check_term(body, f"function {name}")
            case Global(name, body, _):
                check_term(body, f"global {name}")
            case Print(t):
                check_term(t, "print")
            case AssertEq(l, r):
                check_term(l, "assert_eq")
                check_term(r, "assert_eq")
            case AssertBool(t):
                check_term(t, "assert_bool")


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
        case Match(subj, arms, _):
            out = free_vars(subj, bound)
            for arm in arms:
                match arm.pattern:
                    case PatCon(_, binds):
                        out |= free_vars(arm.body, bound | set(binds))
                    case PatBool(_):
                        out |= free_vars(arm.body, bound)
            return out
        case Eq(l, r):
            return free_vars(l, bound) | free_vars(r, bound)
        case Panic(_, _):
            return set()
        case MakeArray(s, _):
            return free_vars(s, bound)
        case ArrayGet(s, i, _):
            return free_vars(s, bound) | free_vars(i, bound)
    raise AssertionError(f"free_vars: unknown term {type(t).__name__}")
