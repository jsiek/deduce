// === module generic ===
#ifndef DEDUCE_generic_H
#define DEDUCE_generic_H
#include "deduce.h"

#define CTOR_generic__box_1 0
#define CTOR_generic__zero_5 1
#define CTOR_generic__suc_6 2

extern deduce_value C_generic__zero_5;

deduce_value F_generic__unbox_2(deduce_value* env, deduce_value* args);
deduce_value F_generic__id_3(deduce_value* env, deduce_value* args);

#endif

