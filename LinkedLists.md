# Introduction to Linked Lists

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

Of course, the length of `list_123` is `3`. We can ask Deduce to check
this fact using the `assert` statement.

``` {.c #test_length_123}
assert length(list_123) = 3
```

The return type of `length` is `Nat` which stands for **natural
number** (that is, the non-negative integers).  The `suc(n)` operation
computes `1 + n` and is short for successor. Similarly, the `pred(n)`
operation is short for predecessor and computes `n - 1`, except that
`pred(0) = 0`.

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

Here are examples of applying `nth` to the list `1, 2, 3`,
using `0` as the default value.

``` {.c #test_nth_123}
assert nth(list_123, 0)(0) = 1
assert nth(list_123, 0)(1) = 2
assert nth(list_123, 0)(2) = 3
assert nth(list_123, 0)(3) = 0
```

We have formulated the `nth` operation in an unusual way. It has two
parameters and returns a function of one parameter that returns an
element `T`. We could have instead made `nth` take three parameters
and directly return an element `T`. We made this design choice because
it means we can use `nth` with several other functions and theorems that 
work with functions of the type `fn Nat -> T`.


## Exercise: Define Append

Create a `function` named `append` that satisfies the following
specification.

**Specification** `append` combines two lists into a single list.  The
elements of the output list must be ordered in a way that 1) the
elements from the first input list come before the elements of the
second list, and 2) the ordering of elements must preserve the
internal ordering of each input.

```
function append<E>(List<E>, List<E>) -> List<E> {
  FILL IN HERE
}
```

The following is an example use of `append` to combine the sequence
`1,2,3` with `5,6` to produce the sequence `1,2,3,4,5`.

``` {.c #test_append_123_45}
define list_45 : List<Nat> = node(4, node(5, empty))
define list_1_5 = append(list_123, list_45)

assert nth(list_1_5, 0)(0) = nth(list_123,0)(0)
assert nth(list_1_5, 0)(1) = nth(list_123,0)(1)
assert nth(list_1_5, 0)(2) = nth(list_123,0)(2)

assert nth(list_1_5, 0)(3) = nth(list_45,0)(0)
assert nth(list_1_5, 0)(4) = nth(list_45,0)(1)
```

We have formulated the above `assert` statements in a
subtly different way. We could have written

```
assert nth(list_1_5, 0)(0) = 1
```

but we instead wrote 

```
assert nth(list_1_5, 0)(0) = nth(list_123,0)(0)
```

The difference is that the later assertion is more directly related to
the specification of `append`.  The element at position `0` of
`list_1_5` has to be the same as the element at position of `0` of
`list_123` because 1) `list_123` was the first input list in the call
to `append` and 2) because the element at position `0` of `list_123`
came before the other elements of `list_123`.

## Exercise: Prove that Append is Correct

Prove that `append` satisfies its specification on all possible
inputs.  First, we need to translate the specification into a Deduce
formula.  We can do this by generalizing the above assertions. Instead
of using specific lists and specific indices, we use `all` formulas to
talk about all possible lists and indices. Also, for convenience, we
split up correctness into two theorems, one about the first input list
`xs` and the other about the second input list `ys`.

```
theorem nth_append_front: all T:type. all xs:List<T>. all ys:List<T>, i:Nat, d:T.
  if i < length(xs)
  then nth(append(xs, ys), d)(i) = nth(xs, d)(i)
proof
  FILL IN HERE
end

theorem nth_append_back: all T:type. all xs:List<T>. all ys:List<T>, i:Nat, d:T.
  nth(append(xs, ys), d)(length(xs) + i) = nth(ys, d)(i)
proof
  FILL IN HERE
end
```

<!--
```{.c file=ex/LinkedLists.pf}
<<importNat>>

<<list>>
<<length>>
<<nth>>

function append<E>(List<E>, List<E>) -> List<E> {
  append(empty, ys) = ys
  append(node(n, xs), ys) = node(n, append(xs, ys))
}

<<list_123>>
<<test_length_123>>
<<test_nth_123>>
<<test_append_123_45>>

theorem nth_append_front: all T:type. all xs:List<T>. all ys:List<T>, i:Nat, d:T.
  if i < length(xs)
  then nth(append(xs, ys), d)(i) = nth(xs, d)(i)
proof
  arbitrary T:type
  induction List<T>
  case empty {
    arbitrary ys:List<T>, i:Nat, d:T
    suppose i_z: i < length(empty)
    conclude false by definition {length, operator <, operator ≤} in i_z
  }
  case node(x, xs) suppose IH {
    arbitrary ys:List<T>, i:Nat, d:T
    suppose i_xxs: i < length(node(x,xs))
    definition append
    switch i {
      case zero {
        definition nth.
      }
      case suc(i') suppose i_si {
        definition {nth, pred}
	have i_xs: i' < length(xs) by
	    enable {operator <, operator ≤}
	    conclude i' < length(xs) by rewrite i_si in definition length in i_xxs
	apply IH[ys, i', d] to i_xs
      }
    }
  }
end

theorem nth_append_back: all T:type. all xs:List<T>. all ys:List<T>, i:Nat, d:T.
  nth(append(xs, ys), d)(length(xs) + i) = nth(ys, d)(i)
proof
  arbitrary T:type
  induction List<T>
  case empty {
    arbitrary ys:List<T>, i:Nat, d:T
    definition {append, nth, length, operator +}.
  }
  case node(x, xs) suppose IH {
    arbitrary ys:List<T>, i:Nat, d:T
    definition {append,length, nth}
    have X: not (suc(length(xs)) + i = 0) by suppose eq_z enable operator + have false by eq_z
    rewrite X
    definition {operator +, pred}
    IH[ys, i, d]
  }
end
```
-->
