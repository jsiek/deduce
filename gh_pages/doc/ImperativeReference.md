# Experimental Imperative Reference

This page documents Deduce's imperative-verification surface. The
design is described in
[docs/imperative-verification-plan.md](../../docs/imperative-verification-plan.md)
and tracked by [issue #854](https://github.com/jsiek/deduce/issues/854).

**Status:** Phase 1 (parser/AST only). The grammar entries below are
recognized by both parsers, the pretty-printer round-trips them, and
import/export plumbing accepts the new declaration names. The
imperative verifier itself does not exist yet — the checker rejects
every `proc` and `observer` declaration until later phases land.

Most of the surface lives behind the `--experimental-imperative`
flag. The exceptions are noted per-section.

## Contents

- [Frame Expression](#frame-expression)
- [Mutable Array Type](#mutable-array-type)
- [Object (Statement)](#object-statement)
- [Observer (Statement)](#observer-statement)
- [Procedure (Statement)](#procedure-statement)

## Frame Expression

```deduce-grammar
frame_expr ::= "{" "}"
frame_expr ::= "footprint" "(" term ")"
frame_expr ::= term "." identifier
frame_expr ::= term
frame_list ::= frame_expr
frame_list ::= frame_expr "," frame_list
```

A frame expression denotes a set of heap locations referenced by the
`reads` and `modifies` clauses of a [Procedure](#procedure-statement)
or the `reads` clause of an [Observer](#observer-statement). The empty
set is written `{}`, `footprint(e)` names the ghost footprint owned
by `e`, `e.f` names one mutable object field, and a bare term `e`
names every cell of a mutable structure. A frame list is a
comma-separated union.

## Mutable Array Type

The mutable-array type `[T]!` is defined in the main
[Type](./Reference.md#type) grammar. It is parser-only today and
requires `--experimental-imperative`.

## Object (Statement)

```deduce-grammar
statement ::= visibility "object" IDENT type_params_opt object_body_opt
object_body_opt ::= ε
object_body_opt ::= "{" object_field_list "}"
object_field_list ::= ε
object_field_list ::= object_field object_field_list
object_field ::= "var" identifier ":" type
object_field ::= "ghost" "var" identifier ":" type
```

An `object` declaration introduces a heap-allocated type with a fixed
set of fields. Each field is introduced by `var`, optionally preceded
by `ghost` to mark a specification-only field. The body braces may be
omitted to declare a bodyless object.

```{.deduce^#object_example}
object Empty

object Cell<T> {
  var value : T
  ghost var Repr : bool
}
```

Field-level visibility is determined by the enclosing object: an
`opaque object` hides its fields outside the defining module;
otherwise fields follow the object's visibility.

Object declarations parse without `--experimental-imperative`, but
mutation, allocation, and field reads/writes still have no runtime or
proof semantics — those land with the verifier in later phases.

## Observer (Statement)

```deduce-grammar
statement ::= visibility "observer" identifier type_params_opt "(" proc_param_list ")" "->" type observer_reads_list observer_body_opt
observer_reads_list ::= ε
observer_reads_list ::= observer_reads observer_reads_list
observer_reads ::= "reads" frame_list
observer_body_opt ::= ε
observer_body_opt ::= "{" term "}"
```

An `observer` is a pure specification function over mutable state. It
may read the heap through its [Frame Expression](#frame-expression)
`reads` clauses but cannot mutate it. Repeated `reads` clauses union
their frames. The optional body, when present, is an ordinary Deduce
term computing the observer's result.

```deduce
observer sorted(a: [UInt]!) -> bool
  reads a
{
  all i:UInt, j:UInt.
    i < j and j < length(a) -> a[i] <= a[j]
}
```

Observer declarations require `--experimental-imperative`. The checker
rejects them until the imperative verifier exists.

## Procedure (Statement)

```deduce-grammar
statement ::= visibility "proc" identifier type_params_opt "(" proc_param_list ")" proc_return_opt proc_spec_list "{" "}"
proc_param_list ::= ε
proc_param_list ::= proc_param
proc_param_list ::= proc_param "," proc_param_list
proc_param ::= identifier ":" type
proc_param ::= "ghost" identifier ":" type
proc_return_opt ::= ε
proc_return_opt ::= "->" type
proc_spec_list ::= ε
proc_spec_list ::= proc_spec proc_spec_list
proc_spec ::= "requires" term
proc_spec ::= "ensures" identifier ":" term
proc_spec ::= "ensures" term
proc_spec ::= "reads" frame_list
proc_spec ::= "modifies" frame_list
proc_spec ::= "decreases" term
```

A `proc` declares an imperative procedure. Parameters may be marked
`ghost` to indicate they exist only for specification. The optional
`-> type` annotates the procedure's return type. Specification clauses
may be repeated and are interpreted as conjunction for `requires` and
`ensures`, and union for `reads` and `modifies`. An `ensures` clause
may carry a label so that callers can cite the postcondition by name.

```deduce
proc swap(a: [UInt]!, i: UInt, j: UInt)
  requires i < length(a)
  requires j < length(a)
  modifies a[i], a[j]
  ensures a[i] = old(a[j])
  ensures a[j] = old(a[i])
{
}
```

Procedure declarations require `--experimental-imperative`. Only an
empty body is accepted today and the checker rejects every procedure
until the imperative verifier exists. Frame clauses use the
[Frame Expression](#frame-expression) grammar.

<!--
```{.deduce^file=ImperativeReference.pf}
<<object_example>>
```
-->

