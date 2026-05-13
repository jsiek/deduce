"""Emit C source from a closure-converted IR program.

The output `#include`s `deduce.h` (the runtime header). Every Deduce
value is a `deduce_value` (opaque pointer); every function takes
`(deduce_value* env, deduce_value* args)` and returns `deduce_value`.

Top-level functions are emitted as `static deduce_value F_<mangled>(...)`.
Top-level globals are emitted as `static deduce_value G_<mangled>;` and
their initialisation is appended to `deduce_program_main`. Print and
assert statements are appended to `deduce_program_main` in source order.

Emit is purely functional in the IR: walks the program once, builds a
list of strings, joins. No global state.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Set, Tuple

from compiler import ir


class EmitError(Exception):
    pass


# --------------------------------------------------------------------------
# Name mangling
# --------------------------------------------------------------------------

def _mangle(name: str) -> str:
    """Turn a Deduce uniquified name (which may contain `.`, `<`, `>`,
    digits, operator characters) into a valid C identifier suffix."""
    out: List[str] = []
    for c in name:
        if c.isalnum() or c == "_":
            out.append(c)
        elif c == ".":
            out.append("_")
        elif c == "$":
            out.append("__")  # generated names like `$lam1`
        else:
            out.append(f"_x{ord(c):02x}")
    s = "".join(out)
    # First char must be a letter or underscore. Prefix if needed.
    if not (s and (s[0].isalpha() or s[0] == "_")):
        s = "_" + s
    return s


def _local_id(name: str) -> str:
    return "v_" + _mangle(name)


def _base_name(name: str) -> str:
    """Strip the uniquify suffix. Mirrors `abstract_syntax.base_name`
    but local so emit_c.py has no dependency on the AST module."""
    return name.split(".", 1)[0]


def _c_string(s: str) -> str:
    out = ['"']
    for ch in s:
        b = ch.encode("utf-8")
        for byte in b:
            if 0x20 <= byte < 0x7f and byte not in (ord('"'), ord("\\")):
                out.append(chr(byte))
            else:
                out.append("\\x%02x" % byte)
    out.append('"')
    return "".join(out)


# --------------------------------------------------------------------------
# Emit context
# --------------------------------------------------------------------------

@dataclass
class EmitCtx:
    top_funcs: Dict[str, int] = field(default_factory=dict)   # name -> arity
    top_globals: Set[str] = field(default_factory=set)
    ctor_ids: Dict[str, int] = field(default_factory=dict)
    ctor_arities: Dict[str, int] = field(default_factory=dict)
    # Per-name source module for `<Module>__<base_name>` symbol
    # mangling (Step 25 of separate-compile-plan.md). Names absent
    # from this map (closure-conversion `$lam<N>` lifts) mangle
    # without a module prefix.
    name_to_module: Dict[str, str] = field(default_factory=dict)
    # Per-module ordinal disambiguator. Used in place of the uniquify
    # counter so a module's symbols are stable regardless of what
    # other modules were processed in the same compile (Step 28 of
    # separate-compile-plan.md).
    name_to_seq: Dict[str, int] = field(default_factory=dict)
    tmp_counter: int = 0

    def fresh_tmp(self) -> str:
        n = self.tmp_counter
        self.tmp_counter += 1
        return f"t{n}"

    def _mangle_top(self, name: str) -> str:
        """Mangle a top-level name. If we know its source module,
        prefix with `<Module>__`. The within-module disambiguator is
        the per-module ordinal from `name_to_seq` (stable across
        compile contexts) when available; otherwise fall back to
        mangling the uniquified name directly (covers closure-lifted
        lambdas and any synthesised name that was never assigned an
        ordinal during lowering)."""
        module = self.name_to_module.get(name)
        seq = self.name_to_seq.get(name)
        base = _mangle(_base_name(name))
        if module is not None and seq is not None:
            return _mangle(module) + "__" + base + f"_{seq}"
        if module is not None:
            return _mangle(module) + "__" + _mangle(name)
        return _mangle(name)

    def func_id(self, name: str) -> str:
        return "F_" + self._mangle_top(name)

    def global_id(self, name: str) -> str:
        return "G_" + self._mangle_top(name)

    def ctor_id_macro(self, name: str) -> str:
        return "CTOR_" + self._mangle_top(name)

    def ctor_singleton(self, name: str) -> str:
        """Per-ctor static value for nullary constructors. Allocated
        once at program startup and reused at every `Con(c, [])` site."""
        return "C_" + self._mangle_top(name)


def emit_program(p: ir.Program) -> str:
    ctx = EmitCtx(name_to_module=dict(p.name_to_module), name_to_seq=dict(p.name_to_seq))
    next_ctor_id = 0
    for d in p.decls:
        if isinstance(d, ir.UnionDecl):
            for c in d.ctors:
                ctx.ctor_ids[c.name] = next_ctor_id
                ctx.ctor_arities[c.name] = c.arity
                next_ctor_id += 1
        elif isinstance(d, ir.Function):
            ctx.top_funcs[d.name] = len(d.params)
        elif isinstance(d, ir.Global):
            ctx.top_globals.add(d.name)

    # Collect every nullary constructor that survives pruning. Each
    # gets a single `C_<mangled>` storage location allocated once at
    # startup; `print zero` ends up doing zero per-call allocations
    # after the first. (Bool literals are interned in the runtime
    # itself, no codegen needed.)
    nullary_ctors = [
        c.name for d in p.decls if isinstance(d, ir.UnionDecl)
        for c in d.ctors if c.arity == 0
    ]

    out: List[str] = []
    out.append('#include "deduce.h"')
    out.append("")

    # Constructor id macros
    for name, cid in ctx.ctor_ids.items():
        out.append(f"#define {ctx.ctor_id_macro(name)} {cid}")
    out.append("")

    # Forward declarations
    for d in p.decls:
        if isinstance(d, ir.Function):
            out.append(_emit_fn_decl(d, ctx) + ";")
    out.append("")

    # Singleton storage for nullary ctors.
    for name in nullary_ctors:
        out.append(f"deduce_value {ctx.ctor_singleton(name)};")
    out.append("")

    # Global variables. Same reasoning as the function declarations:
    # not `static`, so unused globals don't trip -Wunused-variable.
    for d in p.decls:
        if isinstance(d, ir.Global):
            out.append(f"deduce_value {ctx.global_id(d.name)};")
    out.append("")

    # Function bodies
    for d in p.decls:
        if isinstance(d, ir.Function):
            out.append(_emit_function(d, ctx))
            out.append("")

    # The single program-entry function with globals + prints + asserts
    # in source order.
    out.append("void deduce_program_main(void) {")
    # Initialise the nullary-ctor singletons. Must run before any
    # global initialiser because user-level Globals like
    # `define two = suc(suc(zero))` reference these.
    for name in nullary_ctors:
        out.append(
            f"    {ctx.ctor_singleton(name)} = deduce_make_ctor("
            f"{ctx.ctor_id_macro(name)}, {_c_string(_base_name(name))}, 0, NULL);"
        )
    for d in p.decls:
        if isinstance(d, ir.Global):
            tmp = ctx.fresh_tmp()
            stmts, expr = _emit_term(d.body, ctx, locals_in_scope=set())
            for s in stmts:
                out.append("    " + s)
            out.append(f"    {ctx.global_id(d.name)} = {expr};")
        elif isinstance(d, ir.Print):
            stmts, expr = _emit_term(d.term, ctx, locals_in_scope=set())
            for s in stmts:
                out.append("    " + s)
            out.append(f"    deduce_println({expr});")
        elif isinstance(d, ir.AssertEq):
            sl, el = _emit_term(d.lhs, ctx, locals_in_scope=set())
            sr, er = _emit_term(d.rhs, ctx, locals_in_scope=set())
            for s in sl + sr:
                out.append("    " + s)
            out.append(f"    deduce_assert_eq({el}, {er}, NULL);")
        elif isinstance(d, ir.AssertBool):
            stmts, expr = _emit_term(d.term, ctx, locals_in_scope=set())
            for s in stmts:
                out.append("    " + s)
            out.append(f"    deduce_assert_bool({expr}, NULL);")
    out.append("}")

    return "\n".join(out) + "\n"


def _seed_ctx_with_imports(ctx: "EmitCtx", p: ir.Program,
                           own_ctor_count: int) -> None:
    """In per-module mode, register every imported decl in `ctx`
    so reference sites in this module's code dispatch correctly.
    Imported ctor IDs are assigned values past this module's
    range — they're never emitted as `#define`s (the imported
    `.h` does that), and emit_c only uses `ctor_id_macro` (a
    string mangle) for them, but the dict-membership tests
    elsewhere need an entry to be present."""
    next_imp_id = own_ctor_count
    for cname, carity in p.import_ctors.items():
        ctx.ctor_ids[cname] = next_imp_id
        ctx.ctor_arities[cname] = carity
        next_imp_id += 1
    for fname, arity in p.import_funcs.items():
        ctx.top_funcs[fname] = arity
    for gname in p.import_globals:
        ctx.top_globals.add(gname)


def emit_module(p: ir.Program, is_main: bool) -> "tuple[str, str]":
    """Emit (c_source, h_source) for a single-module IR program.

    Step 27 of `docs/separate-compile-plan.md`. The input program is
    expected to have been lowered with `separate=True`: `p.decls`
    contains only this module's declarations, `p.imports` lists the
    direct imports, and `p.main_module` is the module name.

    The `.c` file:
    - `#include "deduce.h"` and the imported modules' headers.
    - Defines this module's ctor singletons, functions, and globals.
    - Defines `void <Module>_init(void)` — idempotent; calls each
      direct import's `_init` (so the user only has to call the main
      module's `_init`), then allocates the singletons and runs
      global initialisers.
    - If `is_main`, also defines `void deduce_program_main(void)`
      that calls `<Module>_init()` and runs the prints in source
      order.

    The `.h` file is what `emit_header` produces, plus the module's
    `_init` prototype so downstream consumers can call it (or
    declare an extern dependency on it).
    """
    if p.main_module is None:
        raise EmitError("emit_module: program has no main_module")

    module = p.main_module
    ctx = EmitCtx(name_to_module=dict(p.name_to_module), name_to_seq=dict(p.name_to_seq))
    next_ctor_id = 0
    for d in p.decls:
        if isinstance(d, ir.UnionDecl):
            for c in d.ctors:
                ctx.ctor_ids[c.name] = next_ctor_id
                ctx.ctor_arities[c.name] = c.arity
                next_ctor_id += 1
        elif isinstance(d, ir.Function):
            ctx.top_funcs[d.name] = len(d.params)
        elif isinstance(d, ir.Global):
            ctx.top_globals.add(d.name)
    own_ctor_count = next_ctor_id
    _seed_ctx_with_imports(ctx, p, own_ctor_count)

    # Imported modules' headers must be available before we use any
    # of their functions, ctor IDs, or singletons. The corresponding
    # `<import>_init` extern decls come from the same headers.
    nullary_ctors = [
        c.name for d in p.decls if isinstance(d, ir.UnionDecl)
        for c in d.ctors if c.arity == 0
    ]

    # ----- the .c file -----
    out: List[str] = []
    out.append('#include "deduce.h"')
    for imp in p.imports:
        out.append(f'#include "{imp}.h"')
    out.append("")

    # Constructor id macros for THIS module's ctors only. Imported
    # ctors' macros come from the corresponding `<import>.h` we
    # already `#include`d above; redefining them here would conflict.
    own_ctor_macros: List[str] = []
    for d in p.decls:
        if isinstance(d, ir.UnionDecl):
            for c in d.ctors:
                own_ctor_macros.append(
                    f"#define {ctx.ctor_id_macro(c.name)} {ctx.ctor_ids[c.name]}"
                )
    if own_ctor_macros:
        out.extend(own_ctor_macros)
        out.append("")

    # Forward declarations for this module's functions.
    for d in p.decls:
        if isinstance(d, ir.Function):
            out.append(_emit_fn_decl(d, ctx) + ";")
    if any(isinstance(d, ir.Function) for d in p.decls):
        out.append("")

    # Ctor singleton storage (definitions, not externs — the .h
    # declares them extern; here we provide the storage).
    for name in nullary_ctors:
        out.append(f"deduce_value {ctx.ctor_singleton(name)};")
    if nullary_ctors:
        out.append("")

    # Global storage.
    for d in p.decls:
        if isinstance(d, ir.Global):
            out.append(f"deduce_value {ctx.global_id(d.name)};")
    if any(isinstance(d, ir.Global) for d in p.decls):
        out.append("")

    # Function bodies.
    for d in p.decls:
        if isinstance(d, ir.Function):
            out.append(_emit_function(d, ctx))
            out.append("")

    # Per-module init: idempotent (per-module flag), calls direct
    # imports' inits first so any singletons / globals they own are
    # ready before this module's globals try to reference them.
    init_name = _module_init_name(module)
    out.append(f"static int {init_name}__inited;")
    out.append(f"void {init_name}(void) {{")
    out.append(f"    if ({init_name}__inited) return;")
    out.append(f"    {init_name}__inited = 1;")
    for imp in p.imports:
        out.append(f"    {_module_init_name(imp)}();")
    for name in nullary_ctors:
        out.append(
            f"    {ctx.ctor_singleton(name)} = deduce_make_ctor("
            f"{ctx.ctor_id_macro(name)}, {_c_string(_base_name(name))}, 0, NULL);"
        )
    for d in p.decls:
        if isinstance(d, ir.Global):
            stmts, expr = _emit_term(d.body, ctx, locals_in_scope=set())
            for s in stmts:
                out.append("    " + s)
            out.append(f"    {ctx.global_id(d.name)} = {expr};")
    out.append("}")
    out.append("")

    # Main-module entry point: calls our init, then runs prints.
    if is_main:
        out.append("void deduce_program_main(void) {")
        out.append(f"    {init_name}();")
        for d in p.decls:
            if isinstance(d, ir.Print):
                stmts, expr = _emit_term(d.term, ctx, locals_in_scope=set())
                for s in stmts:
                    out.append("    " + s)
                out.append(f"    deduce_println({expr});")
            elif isinstance(d, ir.AssertEq):
                sl, el = _emit_term(d.lhs, ctx, locals_in_scope=set())
                sr, er = _emit_term(d.rhs, ctx, locals_in_scope=set())
                for s in sl + sr:
                    out.append("    " + s)
                out.append(f"    deduce_assert_eq({el}, {er}, NULL);")
            elif isinstance(d, ir.AssertBool):
                stmts, expr = _emit_term(d.term, ctx, locals_in_scope=set())
                for s in stmts:
                    out.append("    " + s)
                out.append(f"    deduce_assert_bool({expr}, NULL);")
        out.append("}")

    c_source = "\n".join(out) + "\n"

    # ----- the .h file -----
    h_source = emit_header(p, module, init_name=init_name, imports=p.imports)

    return c_source, h_source


def _module_init_name(module: str) -> str:
    """Mangle a module name to its `_init` function symbol."""
    return _mangle(module) + "_init"


def emit_header(
    p: ir.Program,
    module_name: str,
    *,
    init_name: "str | None" = None,
    imports: "list[str] | None" = None,
) -> str:
    """Generate the C header for a single module of an IR program.

    Declares (forward-decl / extern) every top-level decl whose
    `module == module_name`, plus the module's nullary-ctor
    singletons and constructor-ID macros for its unions. Wrapped in
    a standard `#ifndef`/`#define`/`#endif` include guard so a
    consumer can `#include "Foo.h"` from multiple translation units
    without redefinition errors.

    The constructor IDs match the IDs `emit_program` assigns for the
    same `Program`, so a `.c` and its `.h` agree.

    `init_name` and `imports` are filled in by `emit_module`: when
    the header is part of a per-module compile pair, it also
    re-includes the imported modules' headers and prototypes the
    module's `_init` function. In monolithic mode (Step 26's
    fixture testing) these are None and the header is just static
    declarations.
    """
    ctx = EmitCtx(name_to_module=dict(p.name_to_module), name_to_seq=dict(p.name_to_seq))
    next_ctor_id = 0
    for d in p.decls:
        if isinstance(d, ir.UnionDecl):
            for c in d.ctors:
                ctx.ctor_ids[c.name] = next_ctor_id
                ctx.ctor_arities[c.name] = c.arity
                next_ctor_id += 1
        elif isinstance(d, ir.Function):
            ctx.top_funcs[d.name] = len(d.params)
        elif isinstance(d, ir.Global):
            ctx.top_globals.add(d.name)

    def in_module(decl: ir.TopLevel) -> bool:
        return getattr(decl, "module", None) == module_name

    guard = "DEDUCE_" + _mangle(module_name) + "_H"
    out: List[str] = [
        f"#ifndef {guard}",
        f"#define {guard}",
        '#include "deduce.h"',
    ]
    if imports:
        for imp in imports:
            out.append(f'#include "{imp}.h"')
    out.append("")

    # Constructor ID macros — one per ctor of any union in this module.
    macros: List[str] = []
    for d in p.decls:
        if isinstance(d, ir.UnionDecl) and in_module(d):
            for c in d.ctors:
                macros.append(
                    f"#define {ctx.ctor_id_macro(c.name)} {ctx.ctor_ids[c.name]}"
                )
    if macros:
        out.extend(macros)
        out.append("")

    # Nullary-ctor singleton externs.
    singletons: List[str] = []
    for d in p.decls:
        if isinstance(d, ir.UnionDecl) and in_module(d):
            for c in d.ctors:
                if c.arity == 0:
                    singletons.append(
                        f"extern deduce_value {ctx.ctor_singleton(c.name)};"
                    )
    if singletons:
        out.extend(singletons)
        out.append("")

    # Function prototypes.
    fn_protos: List[str] = []
    for d in p.decls:
        if isinstance(d, ir.Function) and in_module(d):
            fn_protos.append(_emit_fn_decl(d, ctx) + ";")
    if fn_protos:
        out.extend(fn_protos)
        out.append("")

    # Globals.
    global_externs: List[str] = []
    for d in p.decls:
        if isinstance(d, ir.Global) and in_module(d):
            global_externs.append(
                f"extern deduce_value {ctx.global_id(d.name)};"
            )
    if global_externs:
        out.extend(global_externs)
        out.append("")

    if init_name is not None:
        out.append(f"void {init_name}(void);")
        out.append("")

    out.append("#endif")
    return "\n".join(out) + "\n"


def modules_in(p: ir.Program) -> List[str]:
    """Return the set of source modules that have at least one
    top-level decl in `p`, sorted for stable iteration. Used by the
    header-emit test runner to know which `emit_header` calls to
    make per fixture."""
    seen: Set[str] = set()
    for d in p.decls:
        m = getattr(d, "module", None)
        if m is not None:
            seen.add(m)
    return sorted(seen)


def _emit_fn_decl(f: ir.Function, ctx: EmitCtx) -> str:
    # Not `static`: a function may be unused at runtime if it's only
    # referenced by an erased proof (e.g. used inside a `terminates`
    # block that compiled to nothing). `static` would trip
    # -Wunneeded-internal-declaration; an extern function is silently
    # dropped by the linker if nothing references it.
    return f"deduce_value {ctx.func_id(f.name)}(deduce_value* env, deduce_value* args)"


def _emit_function(f: ir.Function, ctx: EmitCtx) -> str:
    # Locals in scope inside the body include the params (bound from
    # args[]) and the captures (bound from env[]).
    in_scope: Set[str] = set(f.params) | set(f.captures)
    body_stmts: List[str] = []
    if f.loc:
        body_stmts.append(f"// from {f.loc}")
    body_stmts.append(_emit_fn_decl(f, ctx) + " {")
    if not f.params:
        body_stmts.append("    (void)args;")
    if not f.captures:
        body_stmts.append("    (void)env;")
    for i, p in enumerate(f.params):
        body_stmts.append(f"    deduce_value {_local_id(p)} = args[{i}];")
        body_stmts.append(f"    (void){_local_id(p)};")
    for i, c in enumerate(f.captures):
        body_stmts.append(f"    deduce_value {_local_id(c)} = env[{i}];")
        body_stmts.append(f"    (void){_local_id(c)};")
    stmts, expr = _emit_term(f.body, ctx, in_scope)
    for s in stmts:
        body_stmts.append("    " + s)
    body_stmts.append(f"    return {expr};")
    body_stmts.append("}")
    return "\n".join(body_stmts)


# --------------------------------------------------------------------------
# Term emission
# --------------------------------------------------------------------------
#
# Returns (statements, expr): statements run before the expression is
# evaluated; expr is a deduce_value-typed C expression. The caller is
# free to use `expr` multiple times if it's a single C variable, but
# only once otherwise (avoiding double-evaluation of side effects).
# The current emitter always assigns multi-step results to a fresh tmp,
# so callers can treat `expr` as side-effect-free.

def _emit_term(t: ir.Term, ctx: EmitCtx, locals_in_scope: Set[str]) -> Tuple[List[str], str]:
    match t:
        case ir.Var(name):
            if name in locals_in_scope:
                return [], _local_id(name)
            if name in ctx.top_globals:
                return [], ctx.global_id(name)
            if name in ctx.top_funcs:
                # First-class top-level function reference: build a
                # closure with empty env. Phase 1 doesn't exercise this,
                # but supporting it is a few lines.
                arity = ctx.top_funcs[name]
                stmts: List[str] = []
                tmp = ctx.fresh_tmp()
                stmts.append(
                    f"deduce_value {tmp} = deduce_make_closure("
                    f"{ctx.func_id(name)}, {_c_string(_base_name(name))}, "
                    f"{arity}, 0, NULL);"
                )
                return stmts, tmp
            if name in ctx.ctor_ids:
                # Bare constructor reference (rare; usually constructors
                # appear as Con(...) in the IR). Phase 1 doesn't expect
                # this; surface the case as an error so we notice.
                raise EmitError(
                    f"constructor {name} used as a value; not yet supported"
                )
            # Reference to a name we never produced a definition for —
            # almost always because a Predicate / theorem / `some`/`all`
            # in the source code reduced to a name that the compiler
            # can't materialise. Emit a runtime panic so the binary
            # still builds; if pruning kept this code path it'll abort
            # with a clear message.
            tmp = ctx.fresh_tmp()
            return [
                f"deduce_value {tmp} = deduce_unreachable_value("
                f"{_c_string(f'undefined name: {name}')});"
            ], tmp

        case ir.Bool(b):
            return [], f"deduce_make_bool({'true' if b else 'false'})"

        case ir.Int(v):
            return [], f"deduce_make_int({v})"

        case ir.If(cond, thn, els):
            scond, econd = _emit_term(cond, ctx, locals_in_scope)
            sthn, ethn = _emit_term(thn, ctx, locals_in_scope)
            sels, eels = _emit_term(els, ctx, locals_in_scope)
            tmp = ctx.fresh_tmp()
            stmts = []
            stmts.extend(scond)
            stmts.append(f"deduce_value {tmp};")
            stmts.append(f"if (deduce_get_bool({econd})) {{")
            for s in sthn:
                stmts.append("    " + s)
            stmts.append(f"    {tmp} = {ethn};")
            stmts.append("} else {")
            for s in sels:
                stmts.append("    " + s)
            stmts.append(f"    {tmp} = {eels};")
            stmts.append("}")
            return stmts, tmp

        case ir.Let(name, rhs, body):
            srhs, erhs = _emit_term(rhs, ctx, locals_in_scope)
            stmts = []
            stmts.extend(srhs)
            stmts.append(f"deduce_value {_local_id(name)} = {erhs};")
            sbody, ebody = _emit_term(body, ctx, locals_in_scope | {name})
            stmts.extend(sbody)
            return stmts, ebody

        case ir.Con(ctor, args):
            if ctor not in ctx.ctor_ids:
                raise EmitError(f"unknown constructor: {ctor}")
            # Nullary ctors are pre-allocated singletons.
            if not args:
                return [], ctx.ctor_singleton(ctor)
            arg_stmts: List[str] = []
            arg_exprs: List[str] = []
            for a in args:
                sa, ea = _emit_term(a, ctx, locals_in_scope)
                arg_stmts.extend(sa)
                arg_exprs.append(ea)
            stmts = list(arg_stmts)
            arr = ctx.fresh_tmp() + "_args"
            stmts.append(
                f"deduce_value {arr}[] = {{ {', '.join(arg_exprs)} }};"
            )
            tmp = ctx.fresh_tmp()
            stmts.append(
                f"deduce_value {tmp} = deduce_make_ctor("
                f"{ctx.ctor_id_macro(ctor)}, {_c_string(_base_name(ctor))}, "
                f"{len(args)}, {arr});"
            )
            return stmts, tmp

        case ir.MkClosure(fn, caps):
            if fn not in ctx.top_funcs:
                raise EmitError(f"closure refers to unknown function: {fn}")
            arity = ctx.top_funcs[fn]
            cap_stmts: List[str] = []
            cap_exprs: List[str] = []
            for c in caps:
                sc, ec = _emit_term(c, ctx, locals_in_scope)
                cap_stmts.extend(sc)
                cap_exprs.append(ec)
            stmts = list(cap_stmts)
            if cap_exprs:
                arr = ctx.fresh_tmp() + "_env"
                stmts.append(
                    f"deduce_value {arr}[] = {{ {', '.join(cap_exprs)} }};"
                )
                arr_arg = arr
            else:
                arr_arg = "NULL"
            tmp = ctx.fresh_tmp()
            stmts.append(
                f"deduce_value {tmp} = deduce_make_closure("
                f"{ctx.func_id(fn)}, {_c_string(_base_name(fn))}, {arity}, "
                f"{len(caps)}, {arr_arg});"
            )
            return stmts, tmp

        case ir.App(rator, args):
            arg_stmts = []
            arg_exprs = []
            for a in args:
                sa, ea = _emit_term(a, ctx, locals_in_scope)
                arg_stmts.extend(sa)
                arg_exprs.append(ea)
            stmts = list(arg_stmts)

            # Direct call to a top-level function: no env, args[].
            if isinstance(rator, ir.Var) \
               and rator.name in ctx.top_funcs \
               and rator.name not in locals_in_scope:
                if ctx.top_funcs[rator.name] != len(args):
                    raise EmitError(
                        f"arity mismatch calling {rator.name}: "
                        f"declared {ctx.top_funcs[rator.name]}, called with {len(args)}"
                    )
                if arg_exprs:
                    arr = ctx.fresh_tmp() + "_args"
                    stmts.append(
                        f"deduce_value {arr}[] = {{ {', '.join(arg_exprs)} }};"
                    )
                    arr_arg = arr
                else:
                    arr_arg = "NULL"
                tmp = ctx.fresh_tmp()
                stmts.append(
                    f"deduce_value {tmp} = {ctx.func_id(rator.name)}(NULL, {arr_arg});"
                )
                return stmts, tmp

            # Closure call: dispatch via runtime.
            srator, erator = _emit_term(rator, ctx, locals_in_scope)
            stmts = srator + stmts
            if arg_exprs:
                arr = ctx.fresh_tmp() + "_args"
                stmts.append(
                    f"deduce_value {arr}[] = {{ {', '.join(arg_exprs)} }};"
                )
                arr_arg = arr
            else:
                arr_arg = "NULL"
            tmp = ctx.fresh_tmp()
            stmts.append(
                f"deduce_value {tmp} = deduce_call({erator}, {len(args)}, {arr_arg});"
            )
            return stmts, tmp

        case ir.Match(subj, arms, match_loc):
            ssubj, esubj = _emit_term(subj, ctx, locals_in_scope)
            stmts = list(ssubj)
            subj_var = ctx.fresh_tmp()
            stmts.append(f"deduce_value {subj_var} = {esubj};")
            tmp = ctx.fresh_tmp()
            stmts.append(f"deduce_value {tmp};")

            # Detect bool vs ctor patterns. Mixing is not allowed in
            # Deduce source so we don't try to handle it.
            is_bool = any(isinstance(arm.pattern, ir.PatBool) for arm in arms)

            if is_bool:
                stmts.append(f"if (deduce_get_bool({subj_var})) {{")
                # Separate true/false branches; pattern order may vary.
                true_arm = next((a for a in arms if isinstance(a.pattern, ir.PatBool) and a.pattern.value), None)
                false_arm = next((a for a in arms if isinstance(a.pattern, ir.PatBool) and not a.pattern.value), None)
                if true_arm is None or false_arm is None:
                    raise EmitError("bool match must have both true and false arms")
                ts, te = _emit_term(true_arm.body, ctx, locals_in_scope)
                for s in ts:
                    stmts.append("    " + s)
                stmts.append(f"    {tmp} = {te};")
                stmts.append("} else {")
                fs, fe = _emit_term(false_arm.body, ctx, locals_in_scope)
                for s in fs:
                    stmts.append("    " + s)
                stmts.append(f"    {tmp} = {fe};")
                stmts.append("}")
            else:
                stmts.append(f"switch (deduce_ctor_id({subj_var})) {{")
                for arm in arms:
                    if not isinstance(arm.pattern, ir.PatCon):
                        raise EmitError("expected constructor pattern in ctor match")
                    pc: ir.PatCon = arm.pattern
                    stmts.append(f"case {ctx.ctor_id_macro(pc.ctor)}: {{")
                    inner_scope = locals_in_scope | set(pc.binds)
                    for i, bind in enumerate(pc.binds):
                        # Cast to (void) to silence -Wunused on bindings
                        # the case body happens to ignore.
                        stmts.append(
                            f"    deduce_value {_local_id(bind)} = "
                            f"deduce_ctor_field({subj_var}, {i});"
                        )
                        stmts.append(f"    (void){_local_id(bind)};")
                    bs, be = _emit_term(arm.body, ctx, inner_scope)
                    for s in bs:
                        stmts.append("    " + s)
                    stmts.append(f"    {tmp} = {be};")
                    stmts.append("    break;")
                    stmts.append("}")
                msg = "non-exhaustive match"
                if match_loc:
                    msg = f"{match_loc}: {msg}"
                stmts.append(f"default: deduce_panic({_c_string(msg)});")
                stmts.append("}")
            return stmts, tmp

        case ir.Eq(l, r):
            sl, el = _emit_term(l, ctx, locals_in_scope)
            sr, er = _emit_term(r, ctx, locals_in_scope)
            stmts = list(sl) + list(sr)
            tmp = ctx.fresh_tmp()
            stmts.append(
                f"deduce_value {tmp} = deduce_make_bool(deduce_equal({el}, {er}));"
            )
            return stmts, tmp

        case ir.Panic(msg, loc):
            tmp = ctx.fresh_tmp()
            full = f"{loc}: {msg}" if loc else msg
            return [
                f"deduce_value {tmp} = deduce_unreachable_value({_c_string(full)});"
            ], tmp

        case ir.MakeArray(s, loc):
            ssub, esub = _emit_term(s, ctx, locals_in_scope)
            stmts = list(ssub)
            tmp = ctx.fresh_tmp()
            loc_arg = _c_string(loc) if loc else "NULL"
            stmts.append(
                f"deduce_value {tmp} = deduce_make_array_from_list({esub}, {loc_arg});"
            )
            return stmts, tmp

        case ir.ArrayGet(s, i, loc):
            ssub, esub = _emit_term(s, ctx, locals_in_scope)
            sidx, eidx = _emit_term(i, ctx, locals_in_scope)
            stmts = list(ssub) + list(sidx)
            tmp = ctx.fresh_tmp()
            loc_arg = _c_string(loc) if loc else "NULL"
            stmts.append(
                f"deduce_value {tmp} = deduce_array_get({esub}, {eidx}, {loc_arg});"
            )
            return stmts, tmp

        case ir.Lam(_, _):
            raise EmitError(
                "Lam reached emit_c; closure conversion should have lifted it"
            )

    raise EmitError(f"emit: unknown term {type(t).__name__}")
