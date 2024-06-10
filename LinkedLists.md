## Introduction to Linked Lists

A **linked list** is a data structure that represents a sequence of
elements.  Each element is stored inside a `node` and each node also
stores a link to the next node, or to the special empty value that
signifies the end of the list. In Deduce we can implement linked
lists with the following `union` type.

``` {.c #list}
union List<T> {
  empty
  node(T, List<T>)
}
```

For example, the sequence of numbers `1, 2, 3` is represented
by the following linked list.

``` {.c #list_123}
define list_123 : List<Nat> = node(1, node(2, node(3, empty)))
```

Next we introduce two fundamental operations on linked lists.  The
first operation is `length`, which returns the number of elements in a
given list. The length of an empty list is `0` and the length of a
list that starts with a node is one more than the length of the list
starting at the next node.

``` {.c #length}
function length<E>(List<E>) -> Nat {
  length(empty) = 0
  length(node(n, next)) = suc(length(next))
}
```

``` {.c #test_length_123}
assert length(list_123) = 3
```

We will be representing numbers using the `Nat` type, which stands for
**natural number** (that is, the non-negative integers).  The `suc(n)`
operation (short for successor) computes `1 + n`.

```{.c #importNat}
import Nat
```

The second fundamental operation on linked lists is `nth(xs,d)(i)`, which
retrieves the element at position `i` in the list `xs`. However, if `i`
is greater or equal to the length of `xs`, then `nth` returns the
default value `d`.

```{.c #nth}
function nth<T>(List<T>, T) -> (fn Nat -> T) {
  nth(empty, default) = λi{default}
  nth(node(x, xs), default) = λi{
    if i = 0 then
      x
    else
       nth(xs, default)(pred(i))
  }
}
```

```{.c file=ex/LinkedLists.pf}
<<importNat>>

<<list>>
<<length>>
<<nth>>

<<list_123>>
<<test_length_123>>
```
