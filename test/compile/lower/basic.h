// === module basic ===
#ifndef DEDUCE_basic_H
#define DEDUCE_basic_H
#include "deduce.h"

#define CTOR_basic__zero_1 0
#define CTOR_basic__suc_2 1

extern deduce_value C_basic__zero_1;

deduce_value F_basic__add_3(deduce_value* env, deduce_value* args);
deduce_value F_basic__add_two_5(deduce_value* env, deduce_value* args);
deduce_value F_basic__pick_6(deduce_value* env, deduce_value* args);

extern deduce_value G_basic__two_4;

#endif

