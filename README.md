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

## Proof Example

As a taster for what it looks like to write proofs in Deduce, the
following is a proof that appending two lists and then applying the
`map` function is the same as first applying `map` to the two lists
and then appending them.

``` {.deduce #map_append}
theorem map_append: <T> all f : fn T->T, ys : List<T>. all xs : List<T>.
  map(xs ++ ys, f) = map(xs,f) ++ map(ys,f)
proof
  arbitrary T : type
  arbitrary f : fn T->T, ys : List<T>
  induction List<T>
  case empty {
    equations
      map(@empty<T> ++ ys, f)
          = map(ys, f)                            by definition operator++
      ... ={ @empty<T> ++ map(ys, f) }            by definition operator++
      ... ={ map(@empty<T>, f) } ++ map(ys, f)    by definition map
  }
  case node(x, xs')
    suppose IH: map(xs' ++ ys, f) = map(xs',f) ++ map(ys, f)
  {
    equations
      map(node(x,xs') ++ ys, f)
          = map(node(x,xs' ++ ys), f)               by definition operator++
      ... = node(f(x), map(xs' ++ ys, f))           by definition map
      ... = node(f(x), map(xs',f) ++ map(ys,f))     by rewrite IH
      ... ={ node(f(x), map(xs', f)) ++ map(ys,f) } by definition operator++
      ... ={ map(node(x,xs'),f) ++ map(ys,f) }      by definition map
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

<<map_append>>
```
-->
