# Insertion Sort

This is the second blog post in a
[series](https://siek.blogspot.com/2024/06/data-structures-and-algorithms-correctly.html)
about developing correct implementations of basic data structures and
algorithms using the [Deduce](https://github.com/jsiek/deduce)
language and proof checker.

In this blog post we study a simple but slow sorting algorithm,
Insertion Sort. (We will study the faster Merge Sort in the next blog
post.) Insertion Sort is, roughly speaking, how many people sort the
cards in their hand when playing a card game. The basic idea is to
take one card at a time and place it into the correct location amongst
the cards that you've already sorted.

**Specification:** The `insertion_sort(xs)` function returns a list
that contains the same elements as `xs` but the elements in the result
are in sorted order.

Of course, to make this specification precise, we need to define
&quot;sorted&quot;. There are several ways to go with this formal
definition. Here is one that works well for me. It requires each
element in the list to be less-or-equal to all the elements that come
after it.

``` {.deduce #sorted }
function sorted(List<Nat>) -> bool {
  sorted(empty) = true
  sorted(node(a, next)) =
    sorted(next) and all_elements(next, λb{ a ≤ b })
}
```

We follow the write-test-prove approach to develop a correct
implementation of `insertion_sort`.

# Write the `insertion_sort` function

Because `insertion_sort` operates on the recursive type `List`, we'll
try to implement `insertion_sort` as a recursive function.

```
function insertion_sort(List<Nat>) -> List<Nat> {
  insertion_sort(empty) = ?
  insertion_sort(node(x, xs')) = ?
}
```

In the case for the `empty` list, we need to return a list with
the same contents, so we better return `empty`.

```
function insertion_sort(List<Nat>) -> List<Nat> {
  insertion_sort(empty) = empty
  insertion_sort(node(x, xs')) = ?
}
```

In the case for `node(x, xs')`, we can make the recursive
call `insertion_sort(xs')` to sort the rest of the list.

```
function insertion_sort(List<Nat>) -> List<Nat> {
  insertion_sort(empty) = empty
  insertion_sort(node(x, xs')) = ... insertion_sort(xs') ...
}
```

But what do we do with the element `x`?  This is where we need to
define an auxiliary function that inserts `x` into the appropriate
location within the result of sorting the rest of the list. We'll
choose the name `insert` for this auxiliary function.

``` {.deduce #insertion_sort}
function insertion_sort(List<Nat>) -> List<Nat> {
  insertion_sort(empty) = empty
  insertion_sort(node(x, xs')) = insert(insertion_sort(xs'), x)
}
```

Of course, we'll follow the write-test-prove approach to develop the
`insert` function. The first thing we need to do is write down the
specification. The specification of `insert` will play an important
role in the proof of correctness of `insertion_sort`, because we'll
use the correctness theorems about `insert` in the proof of the
correctness theorems about `insertion_sort`. With this in mind,
here's a specification for `insert`.

**Specification:** The `insert(xs, y)` function returns a sorted list
that contains `y` and the elements of `xs`.

Next we write the code for `insert`. This function also has a `List`
as input, so we define yet another recursive function.

```
function insert(List<Nat>,Nat) -> List<Nat> {
  insert(empty, y) = ?
  insert(node(x, xs), y) = ?
}
```

For the case `empty` we must return a list that contains `y`,
so it must be `node(y, empty)`

```
function insert(List<Nat>,Nat) -> List<Nat> {
  insert(empty, y) = node(y, empty)
  insert(node(x, xs), y) = ?
}
```

In the case for `node(x, xs')`, we need to check whether `y` should
come before `x`. So we test `y ≤ x` and if that's the case, we return
`node(y, node(x, xs'))`. Otherwise, `y` belongs somewhere later in the
sequence, so we make the recursive call and return `node(x,
insert(xs', y))`.

``` {.deduce #insert}
function insert(List<Nat>,Nat) -> List<Nat> {
  insert(empty, y) = node(y, empty)
  insert(node(x, xs'), y) =
    if y ≤ x then
      node(y, node(x, xs'))
    else
      node(x, insert(xs', y))
}
```

# Test 

This time we have 2 functions to test, `insert` and `insertion_sort`.
We start with `insert` because if there are bugs in `insert`, then it
will be confusing to find out about them when testing
`insertion_sort`.

## Test `insert`

Looking at the specification for `insert`, we need to check whether
the resulting list is sorted and we need to check that the resulting
list contains the elements from the input and the inserted element,
and no other elements. We can do that using the `search` function that
we developed in the previous blog post and by checking the length of
the list.

``` {.deduce #test_insert_124}
define list_124 = node(1, node(2, node(4, empty)))
define list_1234 = insert(list_124, 3)
assert sorted(list_1234)
assert all_elements(list_124, λx{ search(list_1234, x) < length(list_1234) })
assert search(list_1234, 3) < length(list_1234)
assert length(list_1234) = suc(length(list_124))
```

It's a good idea to test corner cases, that is, inputs that trigger
different code paths through the `insert` function.  As there is a
case for the `empty` list in the code, that's a good test case to
consider.

``` {.deduce #test_insert_empty}
define list_3 = insert(empty, 3)
assert sorted(list_3)
assert search(list_3, 3) < length(list_3)
assert length(list_3) = suc(length(empty))
```

For good measure, let's also test with a 1-element list where the
element is less-than the inserted element.

``` {.deduce #test_insert_1}
define list_1 = node(1, empty)
define list_13 = insert(list_1, 3)
assert sorted(list_13)
assert all_elements(list_1, λx{ search(list_13, x) < length(list_13) })
assert search(list_13, 3) < length(list_13)
assert length(list_13) = suc(length(list_1))
```

And finally, we'll test a 1-element list where the element is
greater-than the inserted element.

``` {.deduce #test_insert_4}
define list_4 = node(4, empty)
define list_34 = insert(list_4, 3)
assert sorted(list_34)
assert all_elements(list_4, λx{ search(list_34, x) < length(list_34) })
assert search(list_34, 3) < length(list_34)
assert length(list_34) = suc(length(list_4))
```

Ideally we would also test with hundreds of randomly-generated
lists. Adding support for random number generation is high on the TODO
list for Deduce.

## Test `insertion_sort`

If we refer back to the specification of `insertion_sort`, we need to
check that the output list is sorted and that it contains the same
elements as the input list.

``` {.deduce #test_insertion_sort}
define list_8373 = node(8, node(3, node(7, node(3, empty))))
define list_3378 = insertion_sort(list_8373)
assert sorted( list_3378 )
assert all_elements(list_8373, λx{ search(list_3378, x) < length(list_3378) })
assert length(list_3378) = length(list_8373)
```




<!--
``` {.deduce file=InsertionSort.pf} 
import Base
import Nat
import Set
import LinkedLists
import LinearSearch

<<sorted>>
<<insert>>
<<insertion_sort>>

<<test_insert_124>>
<<test_insert_empty>>
<<test_insert_1>>
<<test_insert_4>>

<<test_insertion_sort>>
```
-->
