# Syntax and Grammar Overview

## Phrases

The Deduce language includes four kinds of phrases:

1. Statements
2. Proofs
3. Terms
4. Types

## Statements

A deduce file contains a list of statements. Each statement can be one of:

1. [Theorem](./Reference.md#theorem-statement)
2. [Union](./Reference.md#union-statement)
3. [Predicate](./Reference.md#predicate-statement) (or [Relation](./Reference.md#relation-statement))
4. [Function](./Reference.md#function-statement)
5. [Recursive Function](./Reference.md#recursive-function-statement)
6. [View](./Reference.md#view-statement)
7. [Define](./Reference.md#define-statement)
8. [Import](./Reference.md#import-statement)
9. [Assert](./Reference.md#assert-statement)
10. [Print](./Reference.md#print-statement)
11. [Object](./Reference.md#object-statement)
12. [Observer](./Reference.md#observer-statement) (experimental)
13. [Procedure](./Reference.md#procedure-statement) (experimental)

The `observer` and `proc` forms, the mutable array type `[T]!`, and
frame expressions (`{}`, `footprint(...)`, field, and bare-term
frames) belong to the Phase 1 imperative-verification surface tracked
by issue #854. They are parser/AST only today: enabling them requires
`--experimental-imperative`, and the checker rejects every procedure
and observer until later phases land. Object declarations parse
without the flag but their fields likewise have no proof semantics
yet.

## Proofs

In Deduce, one must give a reason for why a theorem is true, and the reason is given by a proof. Proofs are constructed using the rules of logic together with ways to organize proofs by working backwards from the goal, or forwards from the assumptions.

## Terms

Both logical formulas and program expressions are represented in Deduce by terms. For example, `if P then Q` is a logical formula and `x + 5` is a program expression, and to Deduce they are both terms.
    
## Types

Each term has a type that classifies the kinds of values that are produced by the term.
    
1. The type `bool` classifies `true` or `false`.
2. The function type `fn T1,...,Tn -≥ Tr` classifies a function whose `n` parameters are of type `T1, ..., Tn` and whose return type is `Tr`.
3. The generic function type `fn <X1,...,Xk> T1,...,Tn -≥ Tr` classifies a generic function with type parameters `X1, ..., Xk`.
4. A union type given by its name.
5. An instance of a generic union is given by its name followed by `<`, a comma-separated list of type arguments, followed by `>`.
6. With `--experimental-imperative`, `[T]!` is parsed as an experimental mutable-array type.

## Deduce Unicode

Deduce uses some Unicode characters, but in case it is difficult for you to use Unicode, there are regular ASCI equivalents that you can use instead.

| Unicode | ASCI |
| ------- | ---- |
| ≠       | /=   |
| ≤       | <=   |
| ≥       | >=   |
| ⊆       | (=   |
| ∈       | in   |
| ∪       | \|   |
| ∩       | &    |
| ⨄       | .+.  |
| ∘       | .o.  |
| ∅      | .0.  |
| λ       | fun  |
    
