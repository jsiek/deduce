# Linear Search

In this blog post we'll study a classic and simple algorithm known as
Linear Search. The basic idea of the algorithm is to look for the
location of a particular item within a linked list.  Here is the
specification of the `search` function that we will create.

**Specification:** The `search(xs, y)` function returns a
natural number `i`. If `i < length(xs)`, then
`i` is the index of the first occurence of `y` in the list `xs`.
If `length(xs) ≤ i`, `y` is not in the list `xs`.

We will follow the write-test-prove approach to develop a correct
implementation of `search`.

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
constructors has a parameter that is also the `List` type (e.g. the
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
decide what to do with the result. 

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



## Prove `search` Correct

<!--
``` {.c file=ex/LinearSearch.pf}
import Nat
import List
<<search>>
```
-->
