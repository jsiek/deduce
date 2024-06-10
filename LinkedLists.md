
A **linked list** is a data structure that represents a sequence of
elements.  Each element is stored inside a `node` and each node also
includes a link to the next node, or to the special empty value that
signifies the end of the list. In Deduce we can represent a linked
list with the following `union` type.

``` {.deduce #list}
union List<T> {
  empty
  node(T, List<T>)
}
```

``` {.deduce #length}
function length<E>(List<E>) -> Nat {
  length(empty) = 0
  length(node(n, next)) = suc(length(next))
}
```

```{.deduce #nth}
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

```{.deduce file=ex/LinkedLists.pf}
import Nat

<<list>>
<<length>>
<<nth>>
```
