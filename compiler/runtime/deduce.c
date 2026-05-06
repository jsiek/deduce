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
