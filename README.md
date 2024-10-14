# Deduce 

![Deduce logo: blue and purple hippo](logos/Main-Logo.svg)
Deduce is an automated proof checker meant for use in education. The
intended audience is students with (roughly) the following background
knowledge and skills:

* Basic programming skills in a mainstream language such as Java,
  Python, or C++, as one would learn in the introductory computer
  science course at a university.
* Some exposure to logic, as one would learn in a course on Discrete
  Mathematics (aka. Discrete Structures).

The primary goal of Deduce is to help students learn how to prove the
correctness of pure functional programs. The reason for the focus on
pure functional programs is because (1) those proofs are much more
straightforward to write than proofs of correctness of imperative
programs, so it serves as a better starting place educationally, and
(2) the technology for automatically checking those proofs is well
understood, so it's straightforward to build and maintain the Deduce
proof checker.

## Example

As a taster for what it looks like to write programs and proofs in
Deduce, the following is an implementation of the Linear Search
algorithm and a proof that item `y` does not occur in the list `xs` at
a position before the index returned by `search(xs, y)`.

``` {.deduce #search_take}
function search(List<Nat>, Nat) -> Nat {
  search(empty, y) = 0
  search(node(x, xs), y) =
    if x = y then
      0
    else
      suc(search(xs, y))
}

theorem search_take: all xs: List<Nat>. all y:Nat.
    not (y ∈ set_of(take(search(xs, y), xs)))
proof
  induction List<Nat>
  case empty {
    arbitrary y:Nat
    suffices not (y ∈ ∅) by definition {search, take, set_of}
    empty_no_members<Nat>
  }
  case node(x, xs') suppose
    IH: (all y:Nat. not (y ∈ set_of(take(search(xs', y), xs'))))
  {
    arbitrary y:Nat
    switch x = y for search {
      case true {
        suffices not (y ∈ ∅) by definition {take, set_of}
        empty_no_members<Nat>
      }
      case false assume xy_false: (x = y) = false {
        suffices not (y ∈ single(x) ∪ set_of(take(search(xs', y), xs')))
            by definition {take, set_of}
        suppose c: y ∈ single(x) ∪ set_of(take(search(xs', y), xs'))
        cases (apply member_union<Nat> to c)
        case y_in_x: y ∈ single(x) {
          have: x = y by apply single_equal<Nat> to y_in_x
          conclude false by rewrite xy_false in (recall x = y)
        }
        case y_in_rest: y ∈ set_of(take(search(xs', y), xs')) {
          conclude false by apply IH to y_in_rest
        }
      }
    }
  }
end
```

## Installation

You will need [Python](https://www.python.org/) version 3.10 or later.
Here are some
[instructions](https://wiki.python.org/moin/BeginnersGuide/Download)
and links to the download for various systems.

<!--

[A copy of Lark is now included in Deduce. -Jeremy]

You also need to install the
[Lark](https://github.com/lark-parser/lark) Parsing library, which you
can do by running the following command in the same directory as
`deduce.py`.

```bash
python -m pip install lark
```
-->

## Getting Started
This introduction to Deduce has two parts. The first part gives a
tutorial on how to write functional programs in Deduce.  The second
part shows how to write proofs in Deduce.

* [Functional Programming in Deduce](./FunctionalProgramming.md)
* [Writing Proofs in Deduce](./ProofIntro.md)

I recommend that you work through the examples in this
introduction. Create a file named `examples.pf` in the top `deduce`
directory and add the examples one at a time. To check the file, run
the `deduce.py` script on the file from the `deduce` directory.

```bash
python ./deduce.py ./examples.pf
```

You can also download one of these extensions for programming in Deduce in some common text editors. 
- VSCode ([deduce-mode](https://github.com/HalflingHelper/deduce-mode))
- Emacs ([deduce-mode](https://github.com/mateidragony/deduce-mode))
- Vim (not now, not ever)

The Deduce Reference manual is linked to below. It provides an
alphabetical list of all the features in Deduce.

* [Reference Manual](./Reference.md)

## Syntax/Grammar Overview

The Deduce language includes four kinds of phrases:

1. statements
2. proofs
3. terms
4. types

A Deduce file contains a list of **statements**. Each statement can be one of
1. [Theorem](./Reference.md#Theorem-Statement)
2. [Function](./Reference.md#Function-Statement)
3. [Define](./Reference.md#Define-Statement)
4. [Import](./Reference.md#Import-Statement)
5. [Assert](./Reference.md#Assert-Statement)
6. [Print](./Reference.md#Print-Statement)

In Deduce, one must give a reason for why a theorem is true, and the
reason is given by a **proof**. Proofs are typically formed of smaller
proofs that are put together using the many ways that Deduce provides
for combining proofs.

Both logical formulas and program expressions are represented in
Deduce by **terms**. For example, `if P then Q` is a logical formula
and `x + 5` is a program expression, and to Deduce they are both terms.

Each term has a **type** that classifies the kinds of values that are
produced by the term. 

1. The type `bool` classifies `true` and `false`.
2. The function type `fn T1,...,Tn -> Tr` classifies a function
   whose n parameters are of type `T1`,...,`Tn` and whose return type is `Tr`.
3. The generic function type `fn <X1,...,Xk> T1,...,Tn -> Tr` classifies a generic
   function with type parameters `X1`,...,`Xk`.
4. A [union](./Reference.md#Union-Type) type given by its name.
5. An instance of a generic union is given by its name followed
   by `<`, a comma-separated list of type arguments, followed by `>`.

## Deduce Unicode
Deduce uses some Unicode characters, but in case it is difficult
for you to use Unicode, there are regular ASCI equivalents that
you can use instead.

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
| ∅       | .0.  |
| λ       | fun  |


<!--  LocalWords:  aka fn ys xs IH pf py NatList builtin suc bool nat
 -->
<!--  LocalWords:  Equational Deduce's subterm pos subformulas tri eq
 -->
<!--  LocalWords:  subformula le refl ls cond Pxs Px ponens conc prem
 -->
<!--  LocalWords:  contra foo sx xy dist mult
 -->

<!--
``` {.deduce file=README.pf}
import List
import Set

<<search_take>>
```
-->
