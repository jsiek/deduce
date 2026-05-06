/* Deduce-to-C runtime, Phase 1. See deduce.h. */

#include "deduce.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct deduce_obj {
    deduce_tag tag;
    union {
        bool b;
        int64_t i;
        struct {
            int id;
            const char* name;   /* statically-allocated, do not free */
            int n_fields;
            /* fields[] is allocated separately to avoid mixing
             * flexible arrays with a union. */
            deduce_value* fields;
        } ctor;
        struct {
            deduce_value (*fn)(deduce_value* env, deduce_value* args);
            const char* name;
            int arity;
            int n_env;
            deduce_value* env;
        } closure;
        struct {
            int n;
            deduce_value* elements;
        } array;
    } u;
};

void* deduce_alloc(size_t size) {
    void* p = calloc(1, size);
    if (!p) {
        fprintf(stderr, "deduce: out of memory\n");
        exit(1);
    }
    return p;
}

deduce_value deduce_make_bool(bool b) {
    deduce_value v = deduce_alloc(sizeof(struct deduce_obj));
    v->tag = D_BOOL;
    v->u.b = b;
    return v;
}

deduce_value deduce_make_int(int64_t i) {
    deduce_value v = deduce_alloc(sizeof(struct deduce_obj));
    v->tag = D_INT;
    v->u.i = i;
    return v;
}

deduce_value deduce_make_ctor(int ctor_id, const char* name,
                              int n_fields, deduce_value* fields) {
    deduce_value v = deduce_alloc(sizeof(struct deduce_obj));
    v->tag = D_CTOR;
    v->u.ctor.id = ctor_id;
    v->u.ctor.name = name;
    v->u.ctor.n_fields = n_fields;
    if (n_fields > 0) {
        v->u.ctor.fields = deduce_alloc(sizeof(deduce_value) * (size_t)n_fields);
        memcpy(v->u.ctor.fields, fields, sizeof(deduce_value) * (size_t)n_fields);
    } else {
        v->u.ctor.fields = NULL;
    }
    return v;
}

deduce_value deduce_make_closure(deduce_value (*fn)(deduce_value*, deduce_value*),
                                 const char* name, int arity,
                                 int n_env, deduce_value* env_vals) {
    deduce_value v = deduce_alloc(sizeof(struct deduce_obj));
    v->tag = D_CLOSURE;
    v->u.closure.fn = fn;
    v->u.closure.name = name;
    v->u.closure.arity = arity;
    v->u.closure.n_env = n_env;
    if (n_env > 0) {
        v->u.closure.env = deduce_alloc(sizeof(deduce_value) * (size_t)n_env);
        memcpy(v->u.closure.env, env_vals, sizeof(deduce_value) * (size_t)n_env);
    } else {
        v->u.closure.env = NULL;
    }
    return v;
}

deduce_tag deduce_tag_of(deduce_value v) {
    return v->tag;
}

bool deduce_get_bool(deduce_value v) {
    if (v->tag != D_BOOL) deduce_panic("expected bool");
    return v->u.b;
}

int64_t deduce_get_int(deduce_value v) {
    if (v->tag != D_INT) deduce_panic("expected int");
    return v->u.i;
}

int deduce_ctor_id(deduce_value v) {
    if (v->tag != D_CTOR) deduce_panic("expected constructor");
    return v->u.ctor.id;
}

deduce_value deduce_ctor_field(deduce_value v, int i) {
    if (v->tag != D_CTOR) deduce_panic("expected constructor");
    if (i < 0 || i >= v->u.ctor.n_fields) deduce_panic("ctor field out of range");
    return v->u.ctor.fields[i];
}

deduce_value deduce_call(deduce_value clo, int n_args, deduce_value* args) {
    if (clo->tag != D_CLOSURE) deduce_panic("call: not a function");
    if (clo->u.closure.arity != n_args) deduce_panic("call: arity mismatch");
    return clo->u.closure.fn(clo->u.closure.env, args);
}

/* --- arrays ----------------------------------------------------------- */

/* Count list length by walking node(_, rest) until empty. */
static int list_length(deduce_value v) {
    int n = 0;
    while (1) {
        if (v->tag != D_CTOR) deduce_panic("array: subject is not a list");
        const char* name = v->u.ctor.name;
        if (strcmp(name, "empty") == 0 || strcmp(name, "[]") == 0) return n;
        if (strcmp(name, "node") != 0)
            deduce_panic("array: list constructor not empty/node");
        if (v->u.ctor.n_fields != 2)
            deduce_panic("array: node arity != 2");
        n++;
        v = v->u.ctor.fields[1];
    }
}

deduce_value deduce_make_array_from_list(deduce_value list) {
    int n = list_length(list);
    deduce_value v = deduce_alloc(sizeof(struct deduce_obj));
    v->tag = D_ARRAY;
    v->u.array.n = n;
    if (n > 0) {
        v->u.array.elements = deduce_alloc(sizeof(deduce_value) * (size_t)n);
        deduce_value cur = list;
        for (int i = 0; i < n; ++i) {
            v->u.array.elements[i] = cur->u.ctor.fields[0];
            cur = cur->u.ctor.fields[1];
        }
    } else {
        v->u.array.elements = NULL;
    }
    return v;
}

/* Decode a Nat (zero / suc) or UInt (bzero / dub_inc / inc_dub) value
 * to a non-negative C int. `lit` (and any wrapper that the user may
 * have defined for literal-display purposes) is unwrapped silently. */
static int64_t decode_index(deduce_value v) {
    while (1) {
        if (v->tag != D_CTOR) deduce_panic("array index is not Nat/UInt");
        const char* n = v->u.ctor.name;
        if (strcmp(n, "zero") == 0) return 0;
        if (strcmp(n, "bzero") == 0) return 0;
        if (strcmp(n, "suc") == 0) {
            if (v->u.ctor.n_fields != 1) deduce_panic("suc arity != 1");
            return 1 + decode_index(v->u.ctor.fields[0]);
        }
        if (strcmp(n, "dub_inc") == 0) {
            if (v->u.ctor.n_fields != 1) deduce_panic("dub_inc arity != 1");
            return 2 * (1 + decode_index(v->u.ctor.fields[0]));
        }
        if (strcmp(n, "inc_dub") == 0) {
            if (v->u.ctor.n_fields != 1) deduce_panic("inc_dub arity != 1");
            return 1 + 2 * decode_index(v->u.ctor.fields[0]);
        }
        if (strcmp(n, "lit") == 0 || strcmp(n, "fromNat") == 0) {
            if (v->u.ctor.n_fields != 1) deduce_panic("lit/fromNat arity != 1");
            v = v->u.ctor.fields[0];
            continue;
        }
        deduce_panic("array index: unrecognized constructor");
    }
}

deduce_value deduce_array_get(deduce_value arr, deduce_value idx) {
    if (arr->tag != D_ARRAY) deduce_panic("array get: not an array");
    int64_t i = decode_index(idx);
    if (i < 0 || i >= arr->u.array.n) deduce_panic("array index out of range");
    return arr->u.array.elements[(int)i];
}

bool deduce_equal(deduce_value a, deduce_value b) {
    if (a == b) return true;
    if (a->tag != b->tag) return false;
    switch (a->tag) {
        case D_BOOL:    return a->u.b == b->u.b;
        case D_INT:     return a->u.i == b->u.i;
        case D_CTOR: {
            if (a->u.ctor.id != b->u.ctor.id) return false;
            if (a->u.ctor.n_fields != b->u.ctor.n_fields) return false;
            for (int i = 0; i < a->u.ctor.n_fields; ++i) {
                if (!deduce_equal(a->u.ctor.fields[i], b->u.ctor.fields[i]))
                    return false;
            }
            return true;
        }
        case D_ARRAY: {
            if (a->u.array.n != b->u.array.n) return false;
            for (int i = 0; i < a->u.array.n; ++i) {
                if (!deduce_equal(a->u.array.elements[i],
                                  b->u.array.elements[i]))
                    return false;
            }
            return true;
        }
        case D_CLOSURE: return false;
    }
    return false;
}

void deduce_println(deduce_value v) {
    deduce_print(v);
    fputc('\n', stdout);
}

void deduce_print(deduce_value v) {
    switch (v->tag) {
        case D_BOOL:
            fputs(v->u.b ? "true" : "false", stdout);
            return;
        case D_INT:
            printf("%lld", (long long)v->u.i);
            return;
        case D_CTOR:
            fputs(v->u.ctor.name, stdout);
            if (v->u.ctor.n_fields > 0) {
                fputc('(', stdout);
                for (int i = 0; i < v->u.ctor.n_fields; ++i) {
                    if (i > 0) fputs(", ", stdout);
                    deduce_print(v->u.ctor.fields[i]);
                }
                fputc(')', stdout);
            }
            return;
        case D_CLOSURE:
            printf("<closure %s>", v->u.closure.name ? v->u.closure.name : "?");
            return;
        case D_ARRAY:
            fputs("array(", stdout);
            for (int i = 0; i < v->u.array.n; ++i) {
                if (i > 0) fputs(", ", stdout);
                deduce_print(v->u.array.elements[i]);
            }
            fputc(')', stdout);
            return;
    }
}

void deduce_assert_eq(deduce_value lhs, deduce_value rhs, const char* loc) {
    if (deduce_equal(lhs, rhs)) return;
    /* Match the interpreter, which routes assert failures through the
     * normal Deduce error path (ends up on stdout via deduce.py). */
    printf("%s: assertion failed:\n\t", loc ? loc : "?");
    deduce_print(lhs);
    fputs(" \xe2\x89\xa0 ", stdout);
    deduce_print(rhs);
    fputc('\n', stdout);
    exit(1);
}

void deduce_assert_bool(deduce_value b, const char* loc) {
    if (b->tag != D_BOOL) {
        printf("%s: assertion expected Boolean result\n", loc ? loc : "?");
        exit(1);
    }
    if (!b->u.b) {
        printf("%s: assertion failed\n", loc ? loc : "?");
        exit(1);
    }
}

void deduce_panic(const char* msg) {
    fprintf(stderr, "deduce: %s\n", msg);
    exit(1);
}

int main(void) {
    deduce_program_main();
    return 0;
}
