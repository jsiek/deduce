

<!-- section: header -->
# A proof checker meant for education

Teaching correctness proofs of functional programs to students.

- [Get Started](../pages/getting-started.html)
- [Live Code](../sandbox.html)

![Deduce hippopotamus logo](../images/logo.svg)
<!-- end section -->

<!-- section: about -->
<!-- block -->
## What is Deduce?

Deduce is an automated proof checker meant for use in education to help students:
- Ease their way into proving the correctness of programs.
- Deepening their understanding of logic.
- Improve their ability to write mathematical proofs.

```{.deduce^#home_example1}
function search(List<Nat>, Nat) -> Nat {
  search(empty, y) = 0
  search(node(x, xs), y) =
    if x = y then 0
    else suc(search(xs, y))
}
```
<!-- end block -->

<!-- block -->
## Who can use Deduce?

The intended audience is students with (roughly) the following background knowledge and skills:

- Basic programming skills in a mainstream language such as Java, Python, or C++
- Some exposure to logic, as one would learn in a course on Discrete Mathematics

```{.deduce^#home_example2}
theorem less_implies_not_equal:
  all x:Nat, y:Nat.
  if x < y then not (x = y)
proof
  arbitrary x:Nat, y:Nat
  assume: x < y
  assume xy: x = y
  have: y < y by rewrite xy in recall x < y
  conclude false by apply less_irreflexive
                    to recall y < y
end
```
<!-- end block -->
<!-- end section -->

<!-- section: blocks -->
<!-- block -->
## Get Started

Get started by installing the necessary prerequisites and downloading the Deduce source code.

You can also find handy information on setting up your Deduce workspace.

- [Get Started](../pages/getting-started.html)
<!-- end block -->

<!-- block -->
## Write Deduce Code

Go through a series of examples to familiarize yourself with Deduce functional programming.

Check your understanding with exercises to test your knowledge of the language.

- [Start Programming](../pages/deduce-programming.html)
<!-- end block -->

<!-- block -->
## Prove Your Programs

Follow a detailed tutorial to learn how to write logical proofs using Deduce effectively.

Explore all of the features of the Deduce proof language in this comprehensive guide.

- [Start Proving](../pages/deduce-proofs.html)
<!-- end block -->

<!-- block -->
## Need Help?

The Deduce Reference manual provides an alphabetical list of all the features in Deduce.

The Cheat Sheet gives some advice regarding proof strategy and which Deduce keyword to use next in a proof.

- [Reference Manual](../pages/reference.html)
- [Cheat Sheet](../pages/cheat-sheet.html)
<!-- end block -->
<!-- end section -->


<!-- section: example -->
## Example Proof

As a taster for what it looks like to write programs and proofs in Deduce, the following is an implementation of the **Linear Search** algorithm and a proof that item `y` does not occur in the list `xs` at a position before the index returned by `search(xs, y)`

```{.deduce^#home_example3}
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
  case [] {
    arbitrary y:Nat
    suffices not (y ∈ ∅) by evaluate
    empty_no_members<Nat>
  }
  case node(x, xs')
    assume IH: all y:Nat. not (y ∈ set_of(take(search(xs', y), xs')))
  {
    arbitrary y:Nat
    switch x = y for search {
      case true {
        suffices not (y ∈ ∅) by evaluate
        empty_no_members<Nat>
      }
      case false assume xy_false: (x = y) = false {
        suffices not (x = y or y ∈ set_of(take(search(xs', y), xs')))
            by evaluate
        assume prem: x = y or y ∈ set_of(take(search(xs', y), xs'))
        cases prem
        case: x = y {
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
<!-- end section -->

<!-- section: credits -->
## Credits

This open-source software is brought to you by the volunteer work of the following people. 

- Matei Cloteaux
- Shulin Gonsalves
- Calvin Josenhans
- Jeremy Siek
<!-- end section -->


<!--
```{.deduce^file=Reference.pf} 
import Nat
import List
import Set
import MultiSet
import Maps

<<home_example1>>
<<home_example2>>
<<home_example3>>
```
-->
