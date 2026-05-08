// === module genrecfun ===
#ifndef DEDUCE_genrecfun_H
#define DEDUCE_genrecfun_H
#include "deduce.h"

#define CTOR_genrecfun__zero_1 0
#define CTOR_genrecfun__suc_2 1

extern deduce_value C_genrecfun__zero_1;

deduce_value F_genrecfun__iszero_5(deduce_value* env, deduce_value* args);
deduce_value F_genrecfun__pred_8(deduce_value* env, deduce_value* args);
deduce_value F_genrecfun__count_down_22(deduce_value* env, deduce_value* args);

#endif

