# Merge Sort with Leftovers

This is the fourth blog post in a
[series](https://siek.blogspot.com/2024/06/data-structures-and-algorithms-correctly.html)
about developing correct implementations of basic data structures and
algorithms using the [Deduce](https://github.com/jsiek/deduce)
language and proof checker.

In this blog post we study a fast sorting algorithm, Merge Sort.  This
classic algorithm splits the input list in half, recursively sorts
each half, and then merges the two results back into a single sorted
list.

The specification of Merge Sort is the same as Insertion Sort.

**Specification:** The `merge_sort(xs)` function returns a list
that contains the same elements as `xs` but the elements in the result
are in sorted order.

We follow the write-test-prove approach to develop a correct
implementation of `merge_sort`. 


# Write the `merge_sort` function

The classic implementation of `merge_sort` would be something like the
following.

```
function merge_sort(List<Nat>) -> List<Nat> {
  merge_sort(empty) = empty
  merge_sort(node(x,xs')) =
    let p = split(node(x,xs'))
	merge(merge_sort(first(p)), merge_sort(second(p)))
}
```

Unfortunately, Deduce rejects the above function definition because
Deduce uses a very simple restriction to ensure the termination of
recursive function, which is that a recursive call may only be made on
a part of the input. In this case, the recursive call may only be
applied to the sublist `xs'`, not `first(p)` or `second(p)`.

How can we work around this restriction?  There's an old trick that
goes by many names (gas, fuel, etc.), which is to add another
parameter of type `Nat` and use that for termination. Let us use the
name `msort` for the following, and then we define `merge_sort` in
terms of `msort`.

```
function msort(Nat, List<Nat>) -> List<Nat> {
  msort(0, xs) = xs
  msort(suc(n'), xs) =
    let p = split(xs)
	merge(msort(n', first(p)), msort(n', second(p)))
}

define merge_sort : fn List<Nat> -> List<Nat>
  = λxs{ msort(log(length(xs)), xs) }
```

In the above definition of `merge_sort`, we need to suppply enough gas
so that `msort` won't prematurely run out.  Here we use the logarithm
(base 2, rounding up) defined in `Log.pf`.

This definition of `merge_sort` and `msort` is fine, it has `O(n
log(n))` time complexity, so it is efficient.  However, the use of
`split` rubs me the wrong way because it requires traversing half of
the input list. The use of `split` is necessary if one wanted to use
parallelism to speed up the code, performing the two recursive calls
in parallel. However, we are currently only interested in a
single-threaded implementation.

Suppose you just finished baking a pie and intend to eat half now and
half tomorrow night. One approach would be to split it in half and
then eat one of the halves. Another approach is to just start eating
the pie and stop when half of it is gone. That's the approach that we
will take with the next version of `msort`.

The following `msort(n,xs)` function sorts the first `min(2ⁿ,length(xs))` 
many elements of `xs` and returns a pair containing (1)
the sorted list and (2) the leftovers that were not yet sorted.

``` {.deduce #msort}
function msort(Nat, List<Nat>) -> Pair< List<Nat>, List<Nat> > {
  msort(0, xs) =
    switch xs {
      case empty { pair(empty, empty) }
      case node(x, xs') { pair(node(x, empty), xs') }
    }
  msort(suc(n'), xs) =
    let p1 = msort(n', xs)
    let p2 = msort(n', second(p1))
    let ys = first(p1)
    let zs = first(p2)
    pair(merge(length(ys) + length(zs), ys, zs), second(p2))
}
```

In the above case for `suc(n')`, the first recursive call to `msort`
produces the pair `p1` that includes a sorted list and the leftovers.
We sort the leftovers with the second recursive call to `msort`.  We
return (1) the merge of the two sorted sublists and (2) the leftovers
from the second recursive call to `msort`.

With the code for `msort` complete, we can turn to `merge_sort`.
Similar to the previous version, we involke `msort` with the input
list `xs` and use the logarithm of list length for the gas.  This
`msort` returns a pair, with the sorted results in the first
component. The second component of the pair is an empty list because
we supplied enough gas.

``` {.deduce #merge_sort}
define merge_sort : fn List<Nat> -> List<Nat>
    = λxs{ first(msort(log(length(xs)), xs)) }
```

So far, we have neglected the implementation of `merge`.
Here's its specification.

**Specification:** The `merge(xs,ys)` function takes two sorted lists
and returns a sorted list that contains just the elements from the two
input lists.

Here's the classic implementation of `merge`. The idea is to compare
the two elements at the front of each list and use the lower of the
two as the first element of the output.  Then do the recursive call
with the two lists, minus the element that was chosen. Again, we use
an extra gas parameter to ensure termination. To ensure that we have
enough gas, we will choose the sum of the lengths of the two input
lists.

``` {.deduce #merge}
function merge(Nat, List<Nat>, List<Nat>) -> List<Nat> {
  merge(0, xs, ys) = empty
  merge(suc(n), xs, ys) =
    switch xs {
      case empty { ys }
      case node(x, xs') {
        switch ys {
          case empty {
            node(x, xs')
          }
          case node(y, ys') {
            if x ≤ y then
              node(x, merge(n, xs', node(y, ys')))
            else
              node(y, merge(n, node(x, xs'), ys'))
          }
        }
     }
   }
}
```


# Test

We have three functions to test, `merge`, `msort` and `merge_sort`.

## Test `merge`

We test that the result of `merge` is sorted and that it contains all
the elements from the two input lists, which we check using `count`.

``` {.deduce #test_merge}
define L_1337 = node(1, node(3, node(3, node(7, empty))))
define L_2348 = node(2, node(3, node(4, node(8, empty))))
define L_12333478 = merge(length(L_1337) + length(L_2348), L_1337, L_2348)
assert sorted(L_12333478)
assert all_elements(append(L_1337, L_2348),
  λx{count(L_1337)(x) + count(L_2348)(x) = count(L_12333478)(x) })
```

## Test `msort`

In the following tests, we vary the gas from `0` to `3`, varying how
much of the input list `L18` gets sorted in the call to `msort`.  The
`take(n,xs)` function returns the first `n` elements of `xs` and
`drop(n,xs)` drops the first `n` elements of `xs` and returns the
remaining portion of `xs`.

``` {.deduce #test_msort}
define L18 = append(L_1337, L_2348)

define p0 = msort(0, L18)
define t0 = take(pow2(0), L18)
define d0 = drop(pow2(0), L18)
assert sorted(first(p0))
assert all_elements(t0, λx{count(t0)(x) = count(first(p0))(x) })
assert all_elements(d0, λx{count(d0)(x) = count(second(p0))(x) })

define p1 = msort(1, L18)
define t1 = take(pow2(1), L18)
define d1 = drop(pow2(1), L18)
assert sorted(first(p1))
assert all_elements(t1, λx{count(t1)(x) = count(first(p1))(x) })
assert all_elements(d1, λx{count(d1)(x) = count(second(p1))(x) })

define p2 = msort(2, L18)
define t2 = take(pow2(2), L18)
define d2 = drop(pow2(2), L18)
assert sorted(first(p2))
assert all_elements(t2, λx{count(t2)(x) = count(first(p2))(x) })
assert all_elements(d2, λx{count(d2)(x) = count(second(p2))(x) })

define p3 = msort(3, L18)
define t3 = take(pow2(3), L18)
define d3 = drop(pow2(3), L18)
assert sorted(first(p3))
assert all_elements(t3, λx{count(t3)(x) = count(first(p3))(x) })
assert all_elements(d3, λx{count(d3)(x) = count(second(p3))(x) })
```

## Test `merge_sort`

Next we test that `merge_sort` returns a sorted list that contains the
same elements as the input list. For input, we reuse the list `L18`
from above.

``` {.deduce #test_merge_sort}
define s_L18 = merge_sort(L18)
assert sorted(s_L18)
assert all_elements(t0, λx{count(L18)(x) = count(s_L18)(x) })
```

We can bundle several tests, with varying-length inputs, into one
`assert` by using `all_elements` and `interval`. 

``` {.deduce #test_merge_sort_many}
assert all_elements(interval(3, 0),
    λn{ let xs = reverse(interval(n, 0))
	    let ls = merge_sort(xs)
	    sorted(ls) and
		all_elements(xs, λx{count(xs)(x) = count(ls)(x)})
	})
```

# Prove

Compared to the proof of correctness for `insertion_sort`, we have
considerably more work to do for `merge_sort`. Instead of two
functions, we have three functions to consider: `merge`, `msort`, and
`merge_sort`. Furthermore, these functions are more complex than
`insert` and `insertion_sort`. Nevertheless, we are up to the
challenge!

## Prove correctness of `merge`

The specificaiton of `merge` has two parts, one part saying that the
elements of the output must be the elements of the two input lists,
and the another part saying that the output must be sorted, provided
the two input lists are sorted.

Here is how we state the theorem for the first part.
```
theorem merge_contents: all n:Nat. all xs:List<Nat>, ys:List<Nat>.
  if length(xs) + length(ys) = n
  then mset_of(merge(n, xs, ys)) = mset_of(xs) ⨄ mset_of(ys)
```

Here is the theorem stating that the output of `merge` is sort.

```
theorem merge_sorted: all n:Nat. all xs:List<Nat>, ys:List<Nat>.
  if sorted(xs) and sorted(ys)
     and length(xs) + length(ys) = n
  then sorted(merge(n, xs, ys))
```

We begin with the proof of `merge_contents`.  Because `merge(n, xs,
ys)` is recursive on the natural number `n`, we proceed by induction
on `Nat`.

```
  induction Nat
  case 0 {
    arbitrary xs:List<Nat>, ys:List<Nat>
    suppose _
    ?
  }
  case suc(n') suppose IH {
    ?
  }
```

In the case for `n = 0`, we need to prove `sorted(merge(0, xs, ys))`.
But `merge(0, xs, ys) = empty`, and `sorted(empty)` is trivially true.
So we conclude the case for `n = 0` as follows.

```
    definition merge
    conclude sorted(empty) by definition sorted.
```

We move on to the case for `n = suc(n')`.

```
  case suc(n') suppose IH {
    arbitrary xs:List<Nat>, ys:List<Nat>
    suppose prem: sorted(xs) and sorted(ys) 
	              and length(xs) + length(ys) = suc(n')
    ?
  }
```

The goal is:

```
  sorted(merge(suc(n'),xs,ys))
```

Looking a the `suc` clause of `merge`, there is a `switch` on `xs` and
then on `ys`. So our proof will be structured analogously.

```
  definition merge
  switch xs {
	case empty {
	  ?
	}
	case node(x, xs') suppose xs_xxs {
	  ?
	}
```

In the case for `xs = empty`, `merge` returns `ys`, and we already
know that `ys` is sorted from the premise.

```
	case empty {
	  conclude sorted(ys) by prem
	}
```

In the case for `xs = node(x, xs')` we need to switch on `ys`.

```
  case node(x, xs') suppose xs_xxs {
	switch ys {
	  case empty {
		?
	  }
	  case node(y, ys') suppose ys_yys {
		?
	  }
	}
  }
```

In the case for `ys = empty`, `merge` returns `node(x, xs')`
(aka. `xs`), and we already know that `xs` is sorted from the premise.

```
  case empty {
	conclude sorted(node(x,xs'))  by rewrite xs_xxs in prem
  }
```

In the case for `ys = node(y, ys')`, `merge` branches on whether `x ≤ y`.
We'll do the same in the proof.

```
  switch x ≤ y {
    case true suppose xy_true {
	  ?
	}
	case false suppose xy_false {
	  ?
	}
  }
```

In the case where `x ≤ y`, `merge` returns
`merge(n',xs',node(y,ys'))`. So we need to prove the following.

```
  sorted(merge(n',xs',node(y,ys'))) 
  and all_elements(merge(n',xs',node(y,ys')),λb{x ≤ b})
```





## Prove correctness of `msort`

## Prove correctness of `merge_sort`


<!--
``` {.deduce file=MergeSort.pf} 
import Base
import Nat
import MultiSet
import List
import InsertionSort
import Log

<<merge>>
<<msort>>
<<merge_sort>>
<<test_merge>>
<<test_msort>>
<<test_merge_sort>>
<<test_merge_sort_many>>
```
-->
