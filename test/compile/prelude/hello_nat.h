// === module Nat ===
#ifndef DEDUCE_Nat_H
#define DEDUCE_Nat_H
#include "deduce.h"

deduce_value F_Nat__gcd_0(deduce_value* env, deduce_value* args);

#endif

// === module NatDefs ===
#ifndef DEDUCE_NatDefs_H
#define DEDUCE_NatDefs_H
#include "deduce.h"

#define CTOR_NatDefs__zero_1 0
#define CTOR_NatDefs__suc_2 1

extern deduce_value C_NatDefs__zero_1;

deduce_value F_NatDefs___x2b_3(deduce_value* env, deduce_value* args);
deduce_value F_NatDefs___x2a_4(deduce_value* env, deduce_value* args);
deduce_value F_NatDefs___x2238_10(deduce_value* env, deduce_value* args);
deduce_value F_NatDefs___x2264_11(deduce_value* env, deduce_value* args);
deduce_value F_NatDefs___x3c_12(deduce_value* env, deduce_value* args);
deduce_value F_NatDefs__pow2_17(deduce_value* env, deduce_value* args);
deduce_value F_NatDefs__lit_27(deduce_value* env, deduce_value* args);

#endif

// === module NatDiv ===
#ifndef DEDUCE_NatDiv_H
#define DEDUCE_NatDiv_H
#include "deduce.h"

deduce_value F_NatDiv___x2f_0(deduce_value* env, deduce_value* args);
deduce_value F_NatDiv___x25_1(deduce_value* env, deduce_value* args);

#endif

