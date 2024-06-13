# Sequential Search

In this blog post we'll study a classic and simple algorithm known as
Sequential Search (aka. Linear Search). The basic idea of the
algorithm is to look for the location of a particular item within a
linked list, traversing the list front to back.  Here is the
specification of the `search` function that we will create.

**Specification:** The `search(xs, y)` function returns a
natural number `i`. If `i < length(xs)`, then
`i` is the index of the first occurence of `y` in the list `xs`.
If `length(xs) ≤ i`, `y` is not in the list `xs`.

We follow the write-test-prove approach to develop a correct
implementation of `search`. We then propose two exercises for the
reader.

## Write `search`

Before diving into the code for `search`, let us look again at the
definition of the `List` type.

```
union List<T> {
  empty
  node(T, List<T>)
}
```

We say that `List` is a *recursive union* because one of its
constructors has a parameter that is also of the `List` type (e.g. the
second parameter of the `node` constructor).

In general, when defining a function with a parameter that is a
recursive union, first consider making that function a recursive
function that pattern-matches on that parameter.

For example, with `search`, we choose for the `List<Nat>` to be the
first parameter so that we can pattern-match on it as follows.

```
function search(List<Nat>, Nat) -> Nat {
  search(empty, y) = ?
  search(node(x, xs'), y) = ?
}
```

Let us consider the case for the `empty` list. Looking at the
specification of `search`, we need to return a number that
is greater or equal to zero because `y` is certainly not in the
`empty` list. Let us choose `0`.

```
function search(List<Nat>, Nat) -> Nat {
  search(empty, y) = 0
  search(node(x, xs'), y) = ?
}
```

In the case for `node(x, xs')`, we can check whether `x = y`.  If so,
then we should return `0` because `y` is at index `0` of `node(x,
xs')` and that is certainly the first occurence of `y` in
`node(x, xs')`. 

```
function search(List<Nat>, Nat) -> Nat {
  search(empty, y) = 0
  search(node(x, xs'), y) =
    if x = y then
	  0
	else
	  ?
}
```

If `x ≠ y`, then we need to search the rest of the list `xs'` for `y`.
We can make the recursive call `search(xs', y)`, but then we need to
decide how to adapt its result to produce a result that makes sense
for `node(x, xs')`. The only way to reason about the result of a
recursive call is to use the specification of the function.
The specification of `search` splits into two cases on the result:
(1) `search(xs', y) < length(xs')` and (2) `length(xs) ≤ search(xs', y)`.
In case (1), `search(xs',y)` is returning the index of the first `y` 
inside `xs'`. Because `x ≠ y`, that location will also be the
first `y` inside `node(x, xs')`. However, we need to add one to the
index to take into account that we're adding a node to the front of the list.
So for case (1), the result should be `suc(search(xs', y))`.
In case (2), `search(xs',y)` did not find `y` in `xs'`, so it is
returning a number that is greater or equal to `length(xs)`.
Because `x ≠ y`, we need to indicate that `y` was not found in
`node(x, xs')`, so we need to return a number that is greater
or equal to `length(node(x, xs'))`. Thus, we need to add one
to the index, so the result should again be `suc(search(xs', y))`.

Here is the completed code for `search`.

``` {.c #search}
function search(List<Nat>, Nat) -> Nat {
  search(empty, y) = 0
  search(node(x, xs'), y) =
    if x = y then
	  0
	else
	  suc(search(xs', y))
}
```

## Test `search`

Focusing on the specification of `search`, there are several things
that we should test. We should test whether `search` finds the correct
index of the elements in the list. To do that we can make use of `nth`
to lookup the element at a given index and we can use `all_elements`
to automate the testing over all the elements of the list. 

``` {.c #search_test1}
define list_1223 = node(1, node(2, node(2, node(3, empty))))

assert all_elements(list_1223,
  λx{ nth(list_1223, 0)( search(list_1223, x) ) = x })
```

Next, we should test whether `search` finds the first occurence. We
can do this by iterating over all the indexes and checking that what
`search` returns is an index that is less-than or equal to the current
index.

``` {.c #search_test2}
assert all_elements(interval(0, length(list_1223)),
   λi{ search(list_1223, nth(list_1223, 0)(i)) ≤ i })
```

Finally, we check that `search` fails gracefully when the value being
searched for is not present in the list.

``` {.c #search_test3}
assert length(list_1223) ≤ search(list_1223, 0)
assert length(list_1223) ≤ search(list_1223, 4)
```



## Prove `search` Correct

<!--
``` {.c file=LinearSearch.pf}
import Nat
import LinkedLists
<<search>>
<<search_test1>>
<<search_test2>>
<<search_test3>>

```
-->
