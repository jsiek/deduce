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

``` {.deduce #test_msort}
assert msort(0, append(L_1337, L_2348)) 
  = pair(insertion_sort(take(pow2(0), append(L_1337, L_2348))), 
         drop(pow2(0), append(L_1337, L_2348)))

assert msort(1, append(L_1337, L_2348)) 
  = pair(insertion_sort(take(pow2(1), append(L_1337, L_2348))), 
         drop(pow2(1), append(L_1337, L_2348)))

assert msort(2, append(L_1337, L_2348)) 
  = pair(insertion_sort(take(pow2(2), append(L_1337, L_2348))), 
         drop(pow2(2), append(L_1337, L_2348)))

assert msort(3, append(L_1337, L_2348)) 
  = pair(insertion_sort(take(pow2(3), append(L_1337, L_2348))), 
         drop(pow2(3), append(L_1337, L_2348)))
```

## Test `merge_sort`

``` {.deduce #test_merge_sort}

```


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
```
-->
