<!-- 
How index generation works:
  For the most part this is just a regular  markdown file
  However, there's extra "comments" to specify the structure
  of the html content. 
  
  Any links to images or pages should be relative to the gh_pages 
  directory, not the gh_pages/doc  directory. Do not link to 
  '../pages/blah'. Instead  link to './pages/blah'

There are four kinds of html "comments":
  - section : to separate large sections of the page
  - block   : next level separation within sections
  - figure  : next level separation within block
  - buttons : to create inline button groups

The syntax for the html "comments" is as follows:
  Start a type of divider with the name of the divider along with
  a potential class name. example:

    type
      or
    type: blah
  
  Then end that divider with end followed by the name of the type
  example:

    end type

There are four main sections whose structure should NOT change:

Header:
  Header contains a block with two bold headers and a button 
  group. You can add as many links to the button group as you 
  want! The header also contains an extra side image (the logo)

About:
  About contains two blocks which each contain a figure and a
  code block. This section appears with a gray background

Blocks:
  Blocks is the 4 information blocks that appear in a grid on
  the site. Each block in blocks contains a header, some text
  and a button group (again this group can have as many buttons
  as you want (just make sure they fit in the page))

Example:
  Example contains a bold header, some text, and a large code
  block. This section also appears with a gray background.

You can add as many additional sections as you want. For example,
the credits section, but I wouldn't recommend adding blocks or
figures within them since no css rules are written for that.
Feel free to add as many paragraphs and lists as you want!

-->

<!-- section: header -->
<!-- block -->
# A proof checker meant for education

## Teaching correctness proofs of functional programs to students.

<!-- buttons -->
[Get Started](./pages/getting-started.html)
[Live Code](./sandbox.html)
<!-- end buttons -->
<!-- end block -->

![Deduce hippopotamus logo](./images/logo.svg)
<!-- end section -->

<!-- section: about -->
<!-- block -->
<!-- figure -->
## What is Deduce?

Deduce is an automated proof checker meant for use in education to help students:
- Ease their way into proving the correctness of programs.
- Deepening their understanding of logic.
- Improve their ability to write mathematical proofs.
<!-- end figure -->

```{.deduce^#home_example1}
recursive search(List<Nat>, Nat) -> Nat {
  search(empty, y) = 0
  search(node(x, xs), y) =
    if x = y then 0
    else suc(search(xs, y))
}
```
<!-- end block -->

<!-- block -->

```{.deduce^#home_example2}
theorem less_implies_not_equal:
  all x:Nat, y:Nat.
  if x < y then not (x = y)
proof
  arbitrary x:Nat, y:Nat
  assume: x < y
  assume xy: x = y
  have: y < y by replace xy in recall x < y
  conclude false by apply less_irreflexive
                    to recall y < y
end
```

<!-- figure -->
## Who can use Deduce?

The intended audience is students with (roughly) the following background knowledge and skills:

- Basic programming skills in a mainstream language such as Java, Python, or C++
- Some exposure to logic, as one would learn in a course on Discrete Mathematics
<!-- end figure -->
<!-- end block -->
<!-- end section -->

<!-- section: blocks -->
<!-- block -->
## Get Started

Get started by installing the necessary prerequisites and downloading the Deduce source code.

You can also find handy information on setting up your Deduce workspace.

<!-- buttons -->
[Get Started](./pages/getting-started.html)
<!-- end buttons -->
<!-- end block -->

<!-- block -->
## Write Deduce Code

Go through a series of examples to familiarize yourself with Deduce functional programming.

Check your understanding with exercises to test your knowledge of the language.

<!-- buttons -->
[Start Programming](./pages/deduce-programming.html)
<!-- end buttons -->
<!-- end block -->

<!-- block -->
## Prove Your Programs

Follow a detailed tutorial to learn how to write logical proofs using Deduce effectively.

Explore all of the features of the Deduce proof language in this comprehensive guide.

<!-- buttons -->
[Start Proving](./pages/deduce-proofs.html)
<!-- end buttons -->
<!-- end block -->

<!-- block -->
## Need Help?

The Deduce Reference manual provides an alphabetical list of all the features in Deduce.

The Cheat Sheet gives some advice regarding proof strategy and which Deduce keyword to use next in a proof.

<!-- buttons -->
[Reference Manual](./pages/reference.html)
[Cheat Sheet](./pages/cheat-sheet.html)
<!-- end buttons -->
<!-- end block -->
<!-- end section -->


<!-- section: example -->
## Example Proof

As a taster for what it looks like to write programs and proofs in Deduce, the following is an implementation of the **Linear Search** algorithm and a proof that item `y` does not occur in the list `xs` at a position before the index returned by `search(xs, y)`

```{.deduce^#home_example3}
import Nat
import List
import Set

recursive search(List<Nat>, Nat) -> Nat {
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
    empty_no_members
  }
  case node(x, xs')
    assume IH: all y:Nat. not (y ∈ set_of(take(search(xs', y), xs')))
  {
    arbitrary y:Nat
    switch x = y for search {
      case true {
        suffices not (y ∈ ∅) by evaluate
        empty_no_members
      }
      case false assume xy_false: (x = y) = false {
        expand take | set_of
        assume prem: y ∈ single(x) ∪ set_of(take(search(xs', y), xs'))
        cases (apply member_union to prem)
        case yx: y ∈ single(x) {
          have: x = y by apply single_equal to yx
          conclude false by replace xy_false in recall x = y
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
```{.deduce^file=Index.pf} 
<<home_example3>>
<<home_example2>>
```
-->
