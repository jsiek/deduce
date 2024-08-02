# Insertion Sort

This is the third blog post in a
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
  sorted(node(x, xs)) =
    sorted(xs) and all_elements(xs, λy{ x ≤ y })
}
```

We follow the write-test-prove approach to develop a correct
implementation of `insertion_sort`. We then propose an exercise for
the reader.

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
Here is the completed code for `insertion_sort`.

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

**Specification:** The `insert(xs, y)` function takes a sorted list
`xs` and value `y` as input and returns a sorted list that contains
`y` and the elements of `xs`.

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
list contains the elements from the input and the inserted element.
We could use the `search` function that we developed in the previous
blog post to check whether the elements from the input list are in the
output list. However, doing that would ignore a subtle issue, which is
that there can be one or more occurrences of the same element in the
input list, and the output list should have the same number of
occurrences. To take this into account, we need a new function to
`count` the number of occurrences of an element.

``` {.deduce #count}
function count<T>(List<T>) -> fn T->Nat {
  count(empty) = λy{ 0 }
  count(node(x, xs')) = λy{
    if y = x then 
      suc(count(xs')(y))
    else
      count(xs')(y) 
  }
}
```

Here's a test that checks whether `insert` produces a sorted list with
the correct `count` for every element on the input list as well as the
inserted element.

``` {.deduce #test_insert_1234}
define list_1234 = node(1, node(2, node(3, node(4, empty))))
define list_12334 = insert(list_1234, 3)
assert sorted(list_12334)
assert all_elements(node(3, list_1234), λx{
  if x = 3 then
    count(list_12334)(x) = suc(count(list_1234)(x))
  else
    count(list_12334)(x) = count(list_1234)(x)
  })
```

It's a good idea to test corner cases, that is, inputs that trigger
different code paths through the `insert` function.  As there is a
case for the `empty` list in the code, that's a good test case to
consider.

``` {.deduce #test_insert_empty}
define list_3 = insert(empty, 3)
assert sorted(list_3)
assert all_elements(node(3, empty), λx{
  if x = 3 then
    count(list_3)(x) = suc(count(empty : List<Nat>)(x))
  else
    count(list_3)(x) = count(empty : List<Nat>)(x)
  })
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
assert all_elements(list_8373, λx{count(list_3378)(x) = count(list_8373)(x)})
```

# Prove

The next step in the process is to prove the correctness of `insert`
and `insertion_sort` with respect to their specification.

## Prove correctness of `insert`

Our first task is to prove that `insert(xs, y)` produces a list that
contains `y` and the elements of `xs`. In our tests, we used the
`count` function to accomplish this. Note that `count` returns a
function `fn T->Nat`, which is the same thing as a multiset.  The file
`MultiSet.pf` defines the `MultiSet<T>` type and operations on them such
as `m_one(x)` for creating a multiset that only contains `x` and
the operator `A ⨄ B` for combining two multisets.
The file `List.pf` defines a function
`mset_of` that converts a list into a multiset.

```
function mset_of<T>(List<T>) -> MultiSet<T> {
  mset_of(empty) = m_fun(λ{0})
  mset_of(node(x, xs)) = m_one(x) ⨄ mset_of(xs)
}
```

So we express the requirements on the contents of `insert(xs, y)` as
follows: converting `insert(xs, y)` into a multiset is the same as
converting `xs` into a multiset and then adding `y`. The proof is
relatively straightforward, making use of several theorems about
multisets from `MultiSet.pf`.

``` {.deduce #insert_contents} 
theorem insert_contents: all xs:List<Nat>. all y:Nat.
  mset_of(insert(xs,y)) = m_one(y) ⨄ mset_of(xs)
proof
  induction List<Nat>
  case empty {
    arbitrary y:Nat
    conclude mset_of(insert(empty,y)) = m_one(y) ⨄ mset_of(empty)
        by definition {insert, mset_of, mset_of}
  }
  case node(x, xs') suppose IH {
    arbitrary y:Nat
    switch y ≤ x for insert {
      case true suppose yx_true {
        conclude mset_of(node(y,node(x,xs'))) = m_one(y) ⨄ mset_of(node(x,xs'))
            by definition {mset_of, mset_of}
      }
      case false suppose yx_false {
        equations
              mset_of(node(x,insert(xs',y))) 
            = m_one(x) ⨄ mset_of(insert(xs',y))
              by definition mset_of
        ... = m_one(x) ⨄ (m_one(y) ⨄ mset_of(xs'))
              by rewrite IH[y]
        ... = (m_one(x) ⨄ m_one(y)) ⨄ mset_of(xs')
              by rewrite m_sum_assoc[Nat,m_one(x),m_one(y),mset_of(xs')]
        ... = (m_one(y) ⨄ m_one(x)) ⨄ mset_of(xs')
              by rewrite m_sum_commutes[Nat, m_one(x), m_one(y)]
        ... = m_one(y) ⨄ (m_one(x) ⨄ mset_of(xs'))
              by rewrite m_sum_assoc[Nat,m_one(y),m_one(x),mset_of(xs')]
        ... = m_one(y) ⨄ mset_of(node(x,xs'))
              by definition mset_of
      }
    }
  }
end
```

Our second task is to prove that `insert` produces a sorted list,
assuming the input list is sorted.

```
theorem insert_sorted: all xs:List<Nat>. all y:Nat.
  if sorted(xs) then sorted(insert(xs, y))
proof
  ?
end
```

Because `insert` is a recursive function, we proceed by induction on
its first argument `xs`.

```
  induction List<Nat>
```

The case for `xs = empty` is a straightforward use of definitions.

```{.deduce #insert_sorted_case_empty}
    // <<insert_sorted_case_empty>> =
    arbitrary y:Nat
    suppose _
    conclude sorted(insert(empty,y))
        by definition {insert, sorted, sorted, all_elements}
```

Here's the beginning of the case for `xs = node(x, xs')`.

```
  case node(x, xs') suppose IH {
    arbitrary y:Nat
    suppose s_xxs: sorted(node(x,xs'))
    suffices sorted(insert(node(x,xs'),y))  by .
    ?
  }
```

In the goal we see an opportunity to use the definition of
`insert`. However, `insert` branches on whether `y ≤ x`, so we use a
`switch`-`for` statement to do the same in our proof.

```
  switch y ≤ x for insert {
    case true suppose yx_true {
      ?
    }
    case false suppose yx_false {
      ?
    }
  }
```

In the case when `y ≤ x` is `true`, we apply the relevant definitions
to arive at the following four subgoals.


```{.deduce #insert_sorted_case_node_less_defs}
    suffices sorted(xs') 
         and all_elements(xs', λb{x ≤ b}) 
         and y ≤ x
         and all_elements(xs', λb{y ≤ b})
             with definition {sorted, sorted, all_elements}
```

The first two of these follows from the premise `sorted(node(x,xs'))`.

```{.deduce #insert_sorted_case_node_s_xs__x_le_xs}
  // <<insert_sorted_case_node_s_xs__x_le_xs>> =
  have s_xs: sorted(xs') by definition sorted in s_xxs
  have x_le_xs': all_elements(xs',λb{(x ≤ b)}) by definition sorted in s_xxs
```

The third is true in the current case.

```{.deduce #insert_sorted_y_le_x}
  // <<insert_sorted_y_le_x>> =
  have y_le_x: y ≤ x by rewrite yx_true
```

The fourth, which states that `y` is less-or-equal all the elements in
`xs'` follows transitively from `y ≤ x` and the that `x` is
less-or-equal all the elements in `xs'` (`x_le_xs'`) using the theorem
`all_elements_implies` (in `List.pf`):

```
theorem all_elements_implies: 
  all T:type. all xs:List<T>. all P: fn T -> bool, Q: fn T -> bool.
  if all_elements(xs,P) and (all z:T. if P(z) then Q(z)) 
  then all_elements(xs,Q)
```

To satisfy the second premise of `all_elements_implies`, we use `y ≤
x` to prove that if `x` is less than any other element, then so is
`y`.

```{.deduce #insert_sorted_x_le_implies_y_le}
  // <<insert_sorted_x_le_implies_y_le>> =
  have x_le_implies_y_le: all z:Nat. (if x ≤ z then y ≤ z)
    by arbitrary z:Nat  suppose x_le_z: x ≤ z
       conclude y ≤ z by apply less_equal_trans[y][x,z] to y_le_x , x_le_z
```

Now we apply `all_elements_implies` to prove `all_elements(xs',λb{(y ≤ b)})`.

```{.deduce #insert_sorted_y_le_xs}
  // <<insert_sorted_y_le_xs>> =
  have y_le_xs': all_elements(xs',λb{(y ≤ b)})
    by apply all_elements_implies[Nat][xs']
             [λb{(x ≤ b)} : fn Nat->bool, λb{(y ≤ b)} : fn Nat->bool]
       to x_le_xs', x_le_implies_y_le
```
and then conclude this case for when `y ≤ x`.
```{.deduce #insert_sorted_case_node_le_conclusion}
  // <<insert_sorted_case_node_le_conclusion>> =
  s_xs, x_le_xs', y_le_x, y_le_xs'
```

Next we turn our attention to the case for when `y ≤ x` is `false`.
After applying the definition of `insert`, Deduce tells us that
we need to prove.

```{.deduce #insert_sorted_case_node_g_def}
    // <<insert_sorted_case_node_g_def>> =
    suffices sorted(insert(xs',y)) 
         and all_elements(insert(xs',y),λb{x ≤ b})
             with definition sorted
```

The first follows from the induction hypothesis.  (Though we need to
move the proof of `s_xs` out of the `y ≤ x` case so that we can use it
here.)

```{.deduce #insert_sorted_s_xs_y}
  // <<insert_sorted_s_xs_y>> =
  have s_xs'_y: sorted(insert(xs',y)) by apply IH[y] to s_xs
```

The second requires more thinking. We know that `x ≤ y` in this case
and we already proved that `x` is less-or-equal all the elements in
`xs'`. So we know that
```
all_elements(node(y, xs'), λb{x ≤ b})
```
but what we need is
```
all_elements(insert(xs', y), λb{x ≤ b})
```

Here are the proofs of what we know so far.
```
  have x_le_y: x ≤ y
      by have not_yx: not (y ≤ x)  by suppose yx rewrite yx_false in yx
         have x_l_y: x < y   by apply or_not[y ≤ x, x < y] 
                                to dichotomy[y,x], not_yx
         apply less_implies_less_equal[x][y] to x_l_y
  have x_le_y_xs': all_elements(node(y, xs'),λb{(x ≤ b)})
         by _definition all_elements  x_le_y, x_le_xs'
```

Now the `all_elements` function shouldn't care about the ordering of the
elements in the list, and indeed there is the following theorem in
`List.pf`:

```
theorem all_elements_set_of:
  all T:type, xs:List<T>, ys:List<T>, P:fn T -> bool.
  if set_of(xs) = set_of(ys)
  then all_elements(xs, P) = all_elements(ys, P)
```

So we need to show that `set_of(insert(xs',y)) = set_of(node(y,xs'))`.
Thankfully, we already showed that this is true for `mset_of` in the
`insert_contents` theorem, and multiset equality implies set equality:
(also from `List.pf`)

```
theorem mset_equal_implies_set_equal: 
  all T:type, xs:List<T>, ys:List<T>.
  if mset_of(xs) = mset_of(ys)
  then set_of(xs) = set_of(ys)
```

So we use these three theorems to prove the following.

``` {.deduce #all_elements_insert_node}
theorem all_elements_insert_node:
  all xs:List<Nat>, x:Nat, P:fn Nat->bool.
  all_elements(insert(xs,x), P) = all_elements(node(x,xs), P)
proof
  arbitrary xs:List<Nat>, x:Nat, P:fn Nat->bool
  have m_xs_x: mset_of(insert(xs, x)) = mset_of(node(x, xs))
      by _definition mset_of insert_contents[xs][x]
  have ixsx_xxs: set_of(insert(xs, x)) = set_of(node(x, xs))
     by apply mset_equal_implies_set_equal[Nat,insert(xs, x), node(x, xs)] 
        to m_xs_x
  apply all_elements_set_of[Nat, insert(xs,x), node(x, xs), P]
  to ixsx_xxs
end
```

We apply this theorem to prove that `x` is less-or-equal all the
elements in `insert(xs',y)` and then we conclude this final case of
proof of `insert_sorted`.

```
  have x_le_xs'_y: all_elements(insert(xs',y), λb{x ≤ b})
      by _rewrite all_elements_insert_node[xs',y,λb{x≤b}:fn Nat->bool]
         x_le_y_xs'
  conclude sorted(insert(xs',y)) and
           all_elements(insert(xs',y),λb{x ≤ b})
      by s_xs'_y, x_le_xs'_y
```

Here is the complete proof of `insert_sorted`.

``` {.deduce #insert_sorted}
theorem insert_sorted: all xs:List<Nat>. all y:Nat.
  if sorted(xs) then sorted(insert(xs, y))
proof
  induction List<Nat>
  case empty {
    <<insert_sorted_case_empty>>
  }
  case node(x, xs') suppose IH {
    arbitrary y:Nat
    suppose s_xxs: sorted(node(x,xs'))
    suffices sorted(insert(node(x,xs'),y))  by .
    <<insert_sorted_case_node_s_xs__x_le_xs>>
    switch y ≤ x for insert {
      case true suppose yx_true {
        suffices sorted(node(y,node(x,xs')))  by .
        <<insert_sorted_case_node_less_defs>>
        <<insert_sorted_y_le_x>>
        <<insert_sorted_x_le_implies_y_le>>
        <<insert_sorted_y_le_xs>>
        <<insert_sorted_case_node_le_conclusion>>
      }
      case false suppose yx_false {
        <<insert_sorted_case_node_g_def>>
        <<insert_sorted_s_xs_y>>
        have x_le_y: x ≤ y
            by have not_yx: not (y ≤ x)  by suppose yx rewrite yx_false in yx
               have x_l_y: x < y   by apply or_not[y ≤ x, x < y] 
                                      to dichotomy[y,x], not_yx
               apply less_implies_less_equal[x][y] to x_l_y
        have x_le_y_xs': all_elements(node(y, xs'),λb{(x ≤ b)})
            by _definition all_elements  x_le_y, x_le_xs'
        have x_le_xs'_y: all_elements(insert(xs',y), λb{x ≤ b})
            by _rewrite all_elements_insert_node[xs',y,λb{x≤b}:fn Nat->bool]
               x_le_y_xs'
        conclude sorted(insert(xs',y)) 
             and all_elements(insert(xs',y),λb{x ≤ b})
                 by s_xs'_y, x_le_xs'_y
      }
    }
  }
end
```

## Prove the correctness of `insertion_sort`

Referring back at the specification of `insertion_sort(xs)`, we need
to prove that (1) it outputs a list that contains the same elements as
`xs`, and (2) the output is sorted.

As we did for `insert`, we use multisets and `mset_of` to express the
requirement o the contents of the output of `insertion_sort`.

```
theorem insertion_sort_contents: all xs:List<Nat>.
  mset_of(insertion_sort(xs)) = mset_of(xs)
```

The `insertion_sort(xs)` function is recursive, so we
proceed by induction on `xs`. In the case for `xs = empty`,
we conclude the following using the definitions
of `insertion_sort` and `mset_of`.

```
  case empty {
    conclude mset_of(insertion_sort(empty)) = mset_of(empty)
	  by definition {insertion_sort, mset_of}
  }
```

In the case for `xs = node(x, xs')`, after applying the definitions of
`insertion_sort` and `mset_of`, we need to show that

```
mset_of(insert(insertion_sort(xs'),x)) = m_one(x) ⨄ mset_of(xs')
```

This follows from the `insert_contents` theorem and
the induction hypothesis as follows.

```
  equations
		  mset_of(insert(insertion_sort(xs'),x)) 
		= m_one(x) ⨄ mset_of(insertion_sort(xs'))
		  by insert_contents[insertion_sort(xs')][x]
	... = m_one(x) ⨄ mset_of(xs')
		  by rewrite IH
```

Here is the complete proof of `insertion_sort_contents`.

``` {.deduce #insertion_sort_contents}
theorem insertion_sort_contents: all xs:List<Nat>.
  mset_of(insertion_sort(xs)) = mset_of(xs)
proof
  induction List<Nat>
  case empty {
    conclude mset_of(insertion_sort(empty)) = mset_of(empty)
	  by definition {insertion_sort, mset_of}
  }
  case node(x, xs') suppose IH {
    suffices mset_of(insert(insertion_sort(xs'),x)) 
           = m_one(x) ⨄ mset_of(xs')
        with definition {insertion_sort, mset_of}
	equations
 	        mset_of(insert(insertion_sort(xs'),x)) 
	      = m_one(x) ⨄ mset_of(insertion_sort(xs'))
		    by insert_contents[insertion_sort(xs')][x]
	  ... = m_one(x) ⨄ mset_of(xs')
	        by rewrite IH
  }
end
```

Finally, we prove that `insertion_sort(xs)` produces a sorted list.
Of course the proof is by induction on `xs`. The case for `empty`
follows from the relevant definitions. The case for `node(x, xs')`
follows from the `insert_sorted` theorem and the induction hypothesis.

``` {.deduce #insertion_sort_sorted}
theorem insertion_sort_sorted: all xs:List<Nat>. 
  sorted( insertion_sort(xs) )
proof
  induction List<Nat>
  case empty {
    conclude sorted(insertion_sort(empty))
  	    by definition {insertion_sort, sorted}
  }
  case node(x, xs') suppose IH: sorted( insertion_sort(xs') ) {
	suffices sorted(insert(insertion_sort(xs'),x))
        with definition {insertion_sort, sorted}
	apply insert_sorted[insertion_sort(xs')][x] to IH
  }
end
```


## Exercise: tail-recursive variant of `insertion_sort`

The `insertion_sort` function uses more computer memory than necessary
because it uses one frame on the procedure call stack for every
element in the input list. This can be avoided if we instead implement
Insertion Sort using a tail-recursive function. That is, as a function
that immediately returns after the recursive call. For this exercise,
formulate a tail recursive version of `insertion_sort` and prove that
it is correct.

As a hint, define an auxiliary function `isort(xs,ys)` that takes a
list `xs` and an already sorted list `ys` and returns a sorted list
that includes the contents of both `xs` and `ys`.

```
function isort(List<Nat>, List<Nat>) -> List<Nat> {
  FILL IN HERE
}
```

Once you have defined `isort`, you can implement Insertion Sort as
follows.

```
define insertion_sort2 : fn List<Nat> -> List<Nat>
    = λxs{ isort(xs, empty) }
```


<!--
``` {.deduce file=InsertionSort.pf} 
import Base
import Nat
import MultiSet
import List


<<sorted>>
<<insert>>
<<insertion_sort>>
<<count>>

<<test_insert_1234>>
<<test_insert_empty>>

<<test_insertion_sort>>

<<insert_contents>>
<<all_elements_insert_node>>
<<insert_sorted>>

<<insertion_sort_contents>>
<<insertion_sort_sorted>>
```
-->

<!--  LocalWords:  xs quot bool fn suc TODO MultiSet pf mset IH yx le
 -->
<!--  LocalWords:  assoc sym xxs trans ys ixsx isort InsertionSort
 -->
<!--  LocalWords:  diff neq
 -->
