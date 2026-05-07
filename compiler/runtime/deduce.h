/* Deduce-to-C runtime, Phase 1.
 *
 * Single uniform value representation (boxed). No GC: the runtime
 * mallocs and never frees. That's fine for short-lived test programs
 * and keeps the runtime under 200 lines. Phase 4 of the compile plan
 * is where memory management gets revisited.
 *
 * Every Deduce value is a `deduce_value` (an opaque pointer). The
 * concrete shape depends on the tag stored at offset 0; do not access
 * fields directly — use the helpers below.
 */

#ifndef DEDUCE_RUNTIME_H
#define DEDUCE_RUNTIME_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef struct deduce_obj* deduce_value;

typedef enum {
    D_BOOL,
    D_INT,
    D_CTOR,
    D_CLOSURE,
    D_ARRAY
} deduce_tag;

/* The actual struct shape is hidden in deduce.c. */

/* Allocation. */
void* deduce_alloc(size_t size);

/* Constructors for the four value kinds. `env_vals` and `fields` are
 * copied; the caller does not need to keep the array alive. */
deduce_value deduce_make_bool(bool b);
deduce_value deduce_make_int(int64_t i);
deduce_value deduce_make_ctor(int ctor_id, const char* name,
                              int n_fields, deduce_value* fields);
deduce_value deduce_make_closure(deduce_value (*fn)(deduce_value* env,
                                                     deduce_value* args),
                                 const char* name,
                                 int arity,
                                 int n_env,
                                 deduce_value* env_vals);

/* Accessors (with tag checks; abort on mismatch). */
deduce_tag deduce_tag_of(deduce_value v);
bool        deduce_get_bool(deduce_value v);
int64_t     deduce_get_int(deduce_value v);
int         deduce_ctor_id(deduce_value v);
deduce_value deduce_ctor_field(deduce_value v, int i);

/* Closure call: dispatches through the closure's function pointer. */
deduce_value deduce_call(deduce_value clo, int n_args, deduce_value* args);

/* `array(<list>)` — walk a `node(_, _)` … `empty` chain and pack into
 * a flat array. Dispatches by the constructor's stored base name, so
 * any union with `empty` and `node` constructors works (matches the
 * interpreter's `isNodeList` semantics). Aborts on a non-list value.
 * `loc` is a `file:line` string used in panic messages; OK to be
 * NULL. */
deduce_value deduce_make_array_from_list(deduce_value list, const char* loc);

/* `arr[idx]` — read an element. The index must be a Nat or UInt; the
 * runtime decodes by inspecting constructor base names (`zero`/`suc`
 * for Nat, `bzero`/`dub_inc`/`inc_dub` for UInt). Out-of-bounds
 * aborts; the interpreter's behaviour of leaving the term un-reduced
 * has no compiled-program analogue. `loc` is a `file:line` string
 * used in panic messages; OK to be NULL. */
deduce_value deduce_array_get(deduce_value arr, deduce_value idx, const char* loc);

/* Structural equality. Closures compare by pointer identity (the
 * surface language has no closure-equality primitive at runtime, but
 * `assert lhs = rhs` may end up comparing them anyway — pointer is the
 * least-bad answer). */
bool deduce_equal(deduce_value a, deduce_value b);

/* Pretty-print to stdout, no trailing newline. */
void deduce_print(deduce_value v);

/* Pretty-print followed by a newline. Generated programs use this for
 * top-level `print`. */
void deduce_println(deduce_value v);

/* Diagnostics. `loc` is a "file:line" string; OK to be NULL. */
void deduce_assert_eq(deduce_value lhs, deduce_value rhs, const char* loc);
void deduce_assert_bool(deduce_value b, const char* loc);
void deduce_panic(const char* msg) __attribute__((noreturn));

/* Value-returning panic. Same as `deduce_panic` but its return type
 * is `deduce_value`, so it can stand in for an expression. The
 * compiler emits this for IR `Panic` nodes — reachable only if the
 * pruner couldn't drop the surrounding code. */
deduce_value deduce_unreachable_value(const char* msg) __attribute__((noreturn));

/* Generated programs call this from main(). */
void deduce_program_main(void);

#endif
