
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

```{.deduce^#search_take}
function search(List<Nat>, Nat) -> Nat {
  search(empty, y) = 0
  search(node(x, xs), y) =
    if x = y then 0
    else suc(search(xs, y))
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

You also need to install the
[Lark](https://github.com/lark-parser/lark) Parsing library, which you
can do by running the following command in the same directory as
`deduce.py`.

```bash
python -m pip install lark
```

## Getting Started

The source code for Deduce can be obtained from the following github repository.

[https://github.com/jsiek/deduce](https://github.com/jsiek/deduce)

This introduction to Deduce has two parts. The first part gives a
tutorial on how to write programs in Deduce.  The second
part shows how to write proofs in Deduce.

* [Programming in Deduce](./doc/FunctionalProgramming.md)
* [Writing Proofs in Deduce](./doc/ProofIntro.md)

I recommend that you work through the examples in this
introduction. Create a file named `examples.pf` in the top `deduce`
directory and add the examples one at a time. To check the file, run
the `deduce.py` script on the file from the `deduce` directory.

```bash
python ./deduce.py ./examples.pf
```

You can also download one of these extensions for programming in Deduce in some common text editors. 
- VSCode ([deduce-mode](https://github.com/HalflingHelper/deduce-mode)). Install it from the extensions tab in VSCode.
- Emacs ([deduce-mode](https://github.com/mateidragony/deduce-mode))
- Vim (not now, not ever)

The Deduce Reference manual is linked to below. It provides an
alphabetical list of all the features in Deduce. The Cheat Sheet gives
some advice regarding proof strategy and which Deduce keyword to use
next in a proof.

* [Reference Manual](./doc/Reference.md)
* [Cheat Sheet](./doc/CheatSheet.md)

## Command Line Arguments

The `deduce.py` script supports certain command line arguments which
are documented below. If an argument is not preceeded by one of the
keywords listed below, then it is treated as the name of a file or
directory and will be processed by Deduce.

`--dir directory-name`

Tells Deduce to include the given `directory-name` in the list of
directories to search when importing a file. For example, if `test.pf`
imports `Curry`, and `Curry.pf` resides in a folder named `howard`,
then `--dir howard` will allow `test.pf` to import `Church`. Note that
`--dir` expects a directory name, not an individual file.

`--no-stdlib`

Deduce, by default, will locate and link the standard library (in
`/lib` of the Deduce repository). However if this argument is
supplied, it will not do so.

`--lalr`

Deduce normally uses a custom recursive descent parser to parse any
input files, however this argument will make Deduce instead use lark's
LALR parser. This argument exists solely for checking that
`Deduce.lark` maintains parity with the recursive descent parser.

`--recursive-descent`

Tells Deduce to use the recursive descent (default) parser. If
`--lalr` is also supplied, then only the recursive descent parser will
be used.

`--recursive-directories` or `-r`

Instead of only processing files in the specified directories, Deduce
will also descend into any subdirectories.

`--traceback`

Prints out the exception if processing a file triggers an error.

`--unique-names`

Prints out all variables and types with an unique name. For example,
if a program defines a variable `x` in several different scopes, `x`
would instead be printed out as `x.1` in one scope and printed as
`x.2` in a different scope.

`--verbose`

Makes Deduce print out the debug logs. It is generally recommended to
use `--traceback` instead, as this argument can make Deduce print out
thousands of lines.

`--error`

Deduce will expect all files that it processes to contain an error. If
there is a file that does not contain an error, Deduce will exit with
a return code of 255.


## Syntax/Grammar Overview

The Deduce language includes four kinds of phrases:

1. statements
2. proofs
3. terms
4. types

A Deduce file contains a list of **statements**. Each statement can be one of
1. [Theorem](./doc/Reference.md#theorem-statement)
2. [Union](./doc/Reference.md#union-statement)
3. [Function](./doc/Reference.md#function-statement)
4. [Define](./doc/Reference.md#define-statement)
5. [Import](./doc/Reference.md#import-statement)
6. [Assert](./doc/Reference.md#assert-statement)
7. [Print](./doc/Reference.md#print-statement)

In Deduce, one must give a reason for why a theorem is true, and the
reason is given by a **proof**. Proofs are constructed using the rules
of logic together with ways to organize proofs by working backwards
from the goal, or forwards from the assumptions.

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
4. A union type given by its name.
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
```{.deduce^file=index.pf}
import Nat
import List
import Set

<<search_take>>
```
-->
