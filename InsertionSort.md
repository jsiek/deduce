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
that there can be one or more occurences of the same element in the
input list, and the output list should have the same number of
occurences. To take this into account, we need a new function to
`count` the number of occurences of an element.

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

Our first task is to prove that `insert(xs, y)` produces a list
that contains `y` and the elements of `xs`.

``` {.deduce #insert_contents} 
theorem insert_contents: all xs:List<Nat>. all y:Nat.
  mset_of(insert(xs,y)) = m_one(y) ⨄ mset_of(xs)
proof
  induction List<Nat>
  case empty {
    arbitrary y:Nat
    conclude mset_of(insert(empty,y)) = m_one(y) ⨄ mset_of(empty)
        by definition {insert, mset_of, mset_of}.
  }
  case node(x, xs') suppose IH {
    arbitrary y:Nat
    definition {insert, mset_of}
    switch y ≤ x {
      case true suppose yx_true {
        definition mset_of.
      }
      case false suppose yx_false {
        rewrite IH[y]
    rewrite symmetric m_sum_assoc[Nat, m_one(y), m_one(x), mset_of(xs')]
    rewrite m_sum_sym[Nat, m_one(y), m_one(x)]
    rewrite m_sum_assoc[Nat, m_one(x), m_one(y), mset_of(xs')].
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

```
  case empty {
    arbitrary y:Nat
    suppose _
    conclude sorted(insert(empty,y))
        by definition {insert, sorted, sorted, all_elements}.
  }
```

Here's the beginning of the case for `xs = node(x, xs')`.

```
  case node(x, xs') suppose IH {
    arbitrary y:Nat
    suppose s_xxs: sorted(node(x,xs'))
    suffices sorted(insert(node(x,xs'),y))
    definition insert
    ?
  }
```

As we can see in the goal, `insert` branches on whether `y ≤ x`.

```
Goal:
    sorted(if y ≤ x then node(y,node(x,xs')) 
           else node(x,insert(xs',y)))
```

So our proof also branches on `y ≤ x`.

```
  switch y ≤ x {
    case true {
      ?
    }
    case false {
      ?
    }
  }
```

In the case when `y ≤ x` is `true`, the goal simplifies to
`sorted(node(y,node(x,xs')))`. After applying the relevant
definitions, 

```
  definition {sorted, sorted, all_elements}
```

we need to prove

```
  sorted(xs') and
  all_elements(xs',λb{x ≤ b}) and
  y ≤ x and
  all_elements(xs',λb{y ≤ b})
```

The first two of these follows from the premise `sorted(node(x,xs'))`.

```
  have s_xs: sorted(xs') by definition sorted in s_xxs
  have x_le_xs': all_elements(xs',λb{(x ≤ b)}) by definition sorted in s_xxs
```

The third is true in the current case.

```
  have y_le_x: y ≤ x by rewrite yx_true.
```

The fourth, which states that `y` is less-or-equal all the elements in
`xs'` follows transitively from `y ≤ x` and the that `x` is
less-or-equal all the elements in `xs'` (`x_le_xs'`) using the theorem
`all_elements_implies`:

```
theorem all_elements_implies: all T:type. all xs:List<T>. all P: fn T -> bool, Q: fn T -> bool.
  if all_elements(xs,P) and (all z:T. if P(z) then Q(z)) 
  then all_elements(xs,Q)
```

To satisfy the second premise of `all_elements_implies`, we use `y ≤
x` to prove that if `x` is less than any other element, then so is
`y`.

```
  have x_le_implies_y_le: all z:Nat. (if x ≤ z then y ≤ z)
    by arbitrary z:Nat  suppose x_le_z: x ≤ z
       conclude y ≤ z by apply less_equal_trans[y][x,z] to y_le_x , x_le_z
```

Now we apply `all_elements_implies` to prove `all_elements(xs',λb{(y ≤ b)})`
and then conclude this case for when `y ≤ x`.

```
  have y_le_xs': all_elements(xs',λb{(y ≤ b)})
    by apply all_elements_implies[Nat][xs']
             [λb{(x ≤ b)} : fn Nat->bool, λb{(y ≤ b)} : fn Nat->bool]
       to x_le_xs', x_le_implies_y_le
  s_xs, x_le_xs', y_le_x, y_le_xs'
```

Next we turn our attention to the case for when `y ≤ x` is `false`.
After applying the definition of `insert`, Deduce tells us that
we need to prove.

```
  sorted(insert(xs',y)) and
  all_elements(insert(xs',y), λb{x ≤ b})
```

The first follows from the induction hypothesis.  (Though we need to
move the proof of `s_xs` out of the `y ≤ x` case so that we can use it
here.)

```
  have s_xs'_y: sorted(insert(xs',y)) by apply IH[y] to s_xs
```



``` {.deduce #less_equal_insert}
theorem less_equal_insert:
  all xs:List<Nat>, x:Nat, y:Nat.
  if y ≤ x and all_elements(xs, λb{y ≤ b})
  then all_elements(insert(xs,x), λb{y ≤ b})
proof
  arbitrary xs:List<Nat>, x:Nat, y:Nat
  suppose y_le_x_and_y_le_xs
  have m_xs_x: mset_of(insert(xs, x)) = mset_of(node(x, xs))
      by definition mset_of insert_contents[xs][x]
  have ixsx_xxs: set_of(insert(xs, x)) = set_of(node(x, xs))
     by apply mset_equal_implies_set_equal[Nat,insert(xs, x), node(x, xs)] 
	    to m_xs_x
  have all_ixsx_xxs: all_elements(insert(xs,x),λb{y ≤ b})
                   = all_elements(node(x, xs),λb{y ≤ b})
      by apply all_elements_set_of[Nat, insert(xs,x), node(x, xs), 
	                               λb{y ≤ b} : fn Nat->bool]
	     to ixsx_xxs
  rewrite all_ixsx_xxs		 
  definition all_elements
  y_le_x_and_y_le_xs
end
```


``` {.deduce #insert_sorted}
theorem insert_sorted: all xs:List<Nat>. all y:Nat.
  if sorted(xs) then sorted(insert(xs, y))
proof
  induction List<Nat>
  case empty {
    arbitrary y:Nat
    suppose _
    conclude sorted(insert(empty,y))
        by definition {insert, sorted, sorted, all_elements}.
  }
  case node(x, xs') suppose IH {
    arbitrary y:Nat
    suppose s_xxs: sorted(node(x,xs'))
    have s_xs: sorted(xs') by definition sorted in s_xxs
    suffices sorted(insert(node(x,xs'),y))
    definition insert
    switch y ≤ x {
      case true suppose yx_true {
        suffices sorted(node(y,node(x,xs')))
        definition {sorted, sorted, all_elements}
        have x_le_xs': all_elements(xs',λb{(x ≤ b)}) by definition sorted in s_xxs
        have y_le_x: y ≤ x by rewrite yx_true.
        have x_le_implies_y_le: all z:Nat. (if x ≤ z then y ≤ z)
          by arbitrary z:Nat  suppose x_le_z: x ≤ z
             conclude y ≤ z by apply less_equal_trans[y][x,z] to y_le_x , x_le_z
        have y_le_xs': all_elements(xs',λb{(y ≤ b)})
          by apply all_elements_implies[Nat][xs']
                       [λb{(x ≤ b)} : fn Nat->bool, λb{(y ≤ b)} : fn Nat->bool]
             to x_le_xs', x_le_implies_y_le
        s_xs, x_le_xs', y_le_x, y_le_xs'
      }
      case false {
        definition {sorted}
		suffices sorted(insert(xs',y)) and
		         all_elements(insert(xs',y),λb{x ≤ b})
        have s_xs'_y: sorted(insert(xs',y)) by apply IH[y] to s_xs
        ?
      }
    }
/*
    cases dichotomy[y,x]
    case y_le_x: y ≤ x {
      rewrite y_le_x
      suffices sorted(node(y,node(x,xs')))
      definition {sorted, sorted, all_elements}
      have y_xs': all_elements(xs',λb{(y ≤ b)})
        by apply all_elements_implies[Nat][xs']
             [λb{(x ≤ b)} : fn Nat -> bool, λb{(y ≤ b)} : fn Nat -> bool]
       to x_xs' , (arbitrary z:Nat
                    suppose x_z: x ≤ z
                    conclude y ≤ z by apply less_equal_trans[y][x,z]
                              to y_le_x , x_z)
      s_xs, x_xs', y_le_x, y_xs'
    }
    case x_l_y: x < y {
      have not_y_le_x: not (y ≤ x)
          by apply less_not_greater_equal[x][y] to x_l_y
      rewrite not_y_le_x
      suffices sorted(node(x,insert(xs',y)))
      definition {sorted, all_elements}
      have s_xs'_y: sorted(insert(xs',y)) by apply IH[y] to s_n
      have x_le_y: x ≤ y by apply less_implies_less_equal[x][y] to x_l_y
      have x_le_xs'_y: all_elements(insert(xs',y),λb{(x ≤ b)})
          by apply less_equal_insert[xs'][y,x] to x_le_y, x_xs'
      s_xs'_y, x_le_xs'_y
    }
    */
  }
end
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
<<less_equal_insert>>
<<insert_sorted>>
```

``` {.deduce #insert_count_same}
theorem insert_count_same: all xs:List<Nat>. all y:Nat.
  count(insert(xs, y), y) = suc(count(xs, y))
proof
  induction List<Nat>
  case empty {
    arbitrary y:Nat
    conclude count(insert(empty,y),y) = suc(count(empty,y))
        by definition {insert, count, count}.
  }
  case node(x, xs') suppose IH {
    arbitrary y:Nat
    definition{insert, count}
    switch y ≤ x {
      case true {
        definition count.
      }
      case false {
        switch y = x {
          case true {
            rewrite IH[y].
          }
          case false {
            rewrite IH[y].
          }
        }
      }
    }
  }
end
```

``` {.deduce #insert_count_diff}
theorem insert_count_same: all xs:List<Nat>. all y:Nat, z:Nat.
  if not (z = y)
  then count(insert(xs, y), z) = count(xs, z)
proof
  induction List<Nat>
  case empty {
    arbitrary y:Nat, z:Nat
    suppose z_neq_y
    suffices count(insert(empty,y),z) = count(empty,z)
    definition {insert, count}
    rewrite z_neq_y
    definition count.
  }
  case node(x, xs') suppose IH {
    arbitrary y:Nat, z:Nat
    suppose z_neq_y
    suffices count(insert(node(x,xs'),y),z) = count(node(x,xs'),z)
    definition {insert, count}
    switch y ≤ x {
      case true {
        rewrite z_neq_y
        definition count.
      }
      case false {
        rewrite z_neq_y
        rewrite apply IH[y,z] to z_neq_y.
      }
    }
  }
end
```
-->
