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

## Correct Software via Write, Test, Prove

We recommend a three step process to constructing correct software,

1. Write down the specification and the code for a subcomponent, such as a function,
2. Create tests for the function and run them (unit and property-based testing).
   If they all pass, proceed to step 2, otherwise return to step 1.
3. Prove that the function is correct with respect to its specification.

We recognize that once step 3 is complete, step 2 is obsolete.  The
proof of correctness supercedes the tests. However there are two good
reasons to perform testing even when you are planning to do a proof of
correctness. First, testing is faster than proof with respect to
revealing bugs in your code. Second, creating the tests will help you
formulate the statement of correctness.

## Example: Intervals

As an example of the write-test-prove methodology, we consider the
`interval` function.

**Specification:** `interval(count, start)` returns a list of natural
numbers of length `count`, where the element at position `i` is `i +
start`.

### Write

We most straightforward way to implement `interval` in Deduce
is to define it as a `function` that pattern matches on the `count`.

```
function interval(Nat, Nat) -> List<Nat> {
  interval(zero, n) = ???
  interval(suc(k), n) = ???
}
```

For the clause where `count=zero`, we must return a list of length `zero`.
So our only choice is the `empty` list.

```
  interval(zero, n) = empty
```

For the clause where `count=suc(k)`, we must return a list of length `suc(k)`.
So it has at least one node.

```
  interval(suc(k), n) = node(???, ???)
```

The specification tells us that the element at position `0` of the
return value is `n + 0` or simply `n`.

```
  interval(suc(k), n) = node(n, ???)
```

The `next` of this node should be a list of length `k` that starts
with the element `n + 1`. Thankfully we can construct such a list
with a recursive call to `interval`.

```
  interval(suc(k), n) = node(n, interval(k, suc(n)))
```

Putting these pieces together, we have the following complete
defintion of `interval`.

``` {.c #interval}
function interval(Nat, Nat) -> List<Nat> {
  interval(zero, n) = empty
  interval(suc(k), n) = node(n, interval(k, suc(n)))
}
```

### Test


### Prove



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


## Testing Append

The following code tests your `append` function, making sure that
appending `1,2,3` with `5,6` produces the sequence `1,2,3,4,5`.

``` {.c #test_append_123_45}
define list_45 : List<Nat> = node(4, node(5, empty))
define list_1_5 = append(list_123, list_45)

assert nth(list_1_5, 0)(0) = nth(list_123,0)(0)
assert nth(list_1_5, 0)(1) = nth(list_123,0)(1)
assert nth(list_1_5, 0)(2) = nth(list_123,0)(2)

assert nth(list_1_5, 0)(3) = nth(list_45,0)(0)
assert nth(list_1_5, 0)(4) = nth(list_45,0)(1)
```

We have formulated these `assert` statements in a subtly different way
than before. We could have written

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

Furthermore, by formulating the assertions in this way, we can better
automate our testing. In the following we collapse the three
assertions concerning `list_123` into a single assertion, and
similarly for `list_45`. We make use of two auxilliary functions
`interval` and `all_elements` that we describe next.

``` {.c #test_append_123_45_again}
assert all_elements(interval(3, 0), λi{ nth(list_1_5, 0)(i) = nth(list_123,0)(i) })
assert all_elements(interval(2, 0), λi{ nth(list_1_5, 0)(3 + i) = nth(list_45,0)(i) })
```

The `all_elements` function takes a list and a function and checks
whether applying the function to every element of the list always
produces `true`.

Going a step further, we can easily adapt the tests to apply to longer
lists. Here we increase the combined size to `20` elements. We could
go with longer lists, but Deduce currently has a slow interpreter, so
the assertions would take a long time (e.g., a minute for `100` elements).

``` {.c #test_append_large}
define num_elts = 20
define first_elts = 12
define second_elts = 8
define first_list = interval(first_elts,1)
define second_list = interval(second_elts, first_elts + 1)
define output_list = append(first_list, second_list)
assert all_elements(interval(first_elts, 0), 
                    λi{ nth(output_list, 0)(i) = nth(first_list,0)(i) })
assert all_elements(interval(second_elts, 0),
                    λi{ nth(output_list, 0)(first_elts + i) = nth(second_list,0)(i) })
```

## Exercise: Prove that Append is Correct

Prove that `append` satisfies its specification on all possible
inputs.  First, we need to translate the specification into a Deduce
formula.  We can do this by generalizing the above assertions. Instead
of using specific lists and specific indices, we use `all` formulas to
talk about all possible lists and indices. Also, for convenience, we
split up correctness into two theorems, one about the first input list
`xs` and the other about the second input list `ys`. We recommend
that your proofs use induction on `List<T>`.

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
<<interval>>

function append<E>(List<E>, List<E>) -> List<E> {
  append(empty, ys) = ys
  append(node(n, xs), ys) = node(n, append(xs, ys))
}

<<list_123>>
<<test_length_123>>
<<test_nth_123>>
<<test_append_123_45>>
function all_elements<T>(List<T>, fn (T) -> bool) -> bool {
  all_elements(empty, P) = true
  all_elements(node(x, xs'), P) = P(x) and all_elements(xs', P)
}
<<test_append_123_45_again>>
<<test_append_large>>

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