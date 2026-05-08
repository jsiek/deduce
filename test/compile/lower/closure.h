// === module closure ===
#ifndef DEDUCE_closure_H
#define DEDUCE_closure_H
#include "deduce.h"

#define CTOR_closure__zero_1 0
#define CTOR_closure__suc_2 1

extern deduce_value C_closure__zero_1;

deduce_value F_closure__add_3(deduce_value* env, deduce_value* args);
deduce_value F_closure__adder_4(deduce_value* env, deduce_value* args);
deduce_value F_closure__closure__lam1(deduce_value* env, deduce_value* args);

#endif

