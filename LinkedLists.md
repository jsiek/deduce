# Introduction to Linked Lists

A **linked list** is a data structure that represents a sequence of
elements.  Each element is stored inside a `node` and each node also
stores a link to the next node, or to the special empty value that
signifies the end of the list. In Deduce we can implement linked
lists with the following `union` type.

``` {.deduce #list}
union List<T> {
  empty
  node(T, List<T>)
}
```

For example, the sequence of numbers `1, 2, 3` is represented
by the following linked list.

``` {.deduce #list_123}
define list_123 : List<Nat> = node(1, node(2, node(3, empty)))
```

Next we introduce two fundamental operations on linked lists.  The
first operation is `length`, which returns the number of elements in a
given list. The length of an empty list is `0` and the length of a
list that starts with a node is one more than the length of the list
starting at the next node.

``` {.deduce #length}
function length<E>(List<E>) -> Nat {
  length(empty) = 0
  length(node(n, next)) = 1 + length(next)
}
```

Of course, the length of `list_123` is `3`. We can ask Deduce to check
this fact using the `assert` statement.

``` {.deduce #test_length_123}
assert length(list_123) = 3
```

The return type of `length` is `Nat` which stands for **natural
number** (that is, the non-negative integers).

```{.deduce #importNat}
import Nat
```

The second fundamental operation on linked lists is `nth(xs,d)(i)`,
which retrieves the element at position `i` in the list `xs`. However,
if `i` is greater or equal to the length of `xs`, then `nth` returns
the default value `d`.  The `pred(n)` function is short for
predecessor and computes `n - 1`, except that `pred(0) = 0`.

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

Here are examples of applying `nth` to the list `1, 2, 3`,
using `0` as the default value.

``` {.deduce #test_nth_123}
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

## Correct Software via Write, Test, and Prove

We recommend a three step process to constructing correct software.

1. **Write** down the specification and the code for a subcomponent, such as a function,
2. **Test** the function on a diverse choice of inputs.
   If all the tests pass, proceed to step 3, otherwise return to step 1.
3. **Prove** that the function is correct with respect to its specification.

We recognize that once step 3 is complete, step 2 is obsolete because
a proof of correctness supersedes any amount of testing. However there
is a good reason to perform testing even when you are planning to do a
proof of correctness. More often than not, your code will have one or
more bugs. Testing is a fast way to detect most of the bugs. When you
detect a bug, you'll need to revise the code and then re-run the
tests. On the other hand, proving correctness is a much slower way to
detect bugs. You will spend a relatively long time to get part-way
through a proof and realize that there is no way to finish. You'll
then need to revise the code. But because of the changes in the code,
much of the proof will need to change. So you'll spend a significant
amount of time refactoring the parts of the proof that you've already
completed before continuing on to the new parts. Therefore, to reduce
the number of relatively-costly proof attempts, it is a good idea to
first spend a relatively short amount of time to test and fix the
code.


## Example: Intervals

As an example of the write-test-prove approach, we consider the
`interval` function.

**Specification:** `interval(count, start)` returns a list of natural
numbers of length `count`, where the element at position `i` is `i +
start`.

For example, `interval(3,5)` produces the list `5, 6, 7`:
``` {.deduce #interval_example}
assert interval(3, 5) = node(5, node(6, node(7, empty)))
```

### Write `interval`

A straightforward way to implement `interval` in Deduce is to define
it as a `function` that pattern-matches on the `count`.
The `suc(n)` constructor for natural numbers
represents `1 + n` and is short for successor. 

```
function interval(Nat, Nat) -> List<Nat> {
  interval(0, n) = ?
  interval(suc(k), n) = ?
}
```

For the clause where `count = 0`, we must return a list of length `0`.
So our only choice is the `empty` list.

```
  interval(0, n) = empty
```

For the clause where `count = suc(k)`, we must return a list of length `suc(k)`.
So it has at least one node.

```
  interval(suc(k), n) = node(?, ?)
```

The specification tells us that the element at position `0` of the
return value is `n + 0` or simply `n`.

```
  interval(suc(k), n) = node(n, ?)
```

The `next` of this node should be a list of length `k` that starts
with the element `n + 1`. Thankfully we can construct such a list
with a recursive call to `interval`.

```
  interval(suc(k), n) = node(n, interval(k, suc(n)))
```

Putting these pieces together, we have the following complete
definition of `interval`.

``` {.deduce #interval}
function interval(Nat, Nat) -> List<Nat> {
  interval(0, n) = empty
  interval(suc(k), n) = node(n, interval(k, suc(n)))
}
```

### Test `interval`

Let us test that our definition of `interval` is behaving the way we expect it to.
In general, one should test many variations of each input to a function.
Here we test with the values `0`, `1` and `2` for the first parameter
and `0` and `3` for the second parameter.

``` {.deduce #test_interval}
assert length(interval(0, 0)) = 0

assert length(interval(1, 0)) = 1
assert nth(interval(1, 0), 7)(0) = 0 + 0

assert length(interval(2, 0)) = 2
assert nth(interval(2, 0), 7)(0) = 0 + 0
assert nth(interval(2, 0), 7)(1) = 1 + 0

assert length(interval(0, 3)) = 0

assert length(interval(1, 3)) = 1
assert nth(interval(1, 3), 7)(0) = 0 + 3

assert length(interval(2, 3)) = 2
assert nth(interval(2, 3), 7)(0) = 0 + 3
assert nth(interval(2, 3), 7)(1) = 1 + 3
```

Yeah! All of these `assert` statements execute without error.

We have formulated these `assert` statements in a subtly different way
than above. When we tested the `length` and `nth` functions, we wrote
`assert` statements that compared the results to our expected
output. Here we have instead written the `assert` statements based on
the specification of `interval(count, start)`.  The specification says
that the length of the output should be the same as the `count`
parameter.  So in the above we wrote `assert` statements that check
whether the length is the same as the `count`.  Furthermore, the
specification says that the element at position `i` of the output is
`i + start`. So we have used the `nth` function to check, for every
position `i` in the output list, whether the element is `i + start`.

The benefit of writing tests based on the specification is that it
reduces the possibility of discrepancies between the specification and
the tests. After all, what it means for a function to be correct is
that it behaves according to its specification, not that it passes
some ad-hoc tests based on a loose interpretation of the
specification.

In general, when a test fails, it often means that either the
implementation of the function-under-test is incorrect, or the test
itself is incorrect. A careful reading of the function's specification
will help you figure out which is at fault. Unfortunately, it is also
possible for the specification to be incorrect! The good thing about
the testing approach described here is that it helps to reveal
inconsistencies between the specification, the tests, and the
implementation.

### Prove `interval` Correct

Once we have finished testing `interval` we can move on to proving
that `interval` is correct for all inputs.  Looking back at the
specification of `interval`, there are two
parts. We will prove each part with a separate theorem.

#### Prove the `interval_length` theorem

The first part of the specification says that `interval(count, start)`
returns a list of length `count`. We want to prove that this is true
for all possible choices of `count` and `start`, so we shall use
Deduce's `all` formula. Recall that there are two ways to prove an
`all` formula in Deduce: 1) using `arbitrary` or 2) using
`induction`. When proving a theorem about a recursive function, one
typically needs to use `induction` for the first parameter of the
function, in the case `count`. So our initial plan is to use
`induction` for `count` and `arbitrary` for `start`. Because we are
going to use different proof methods for each variable, we need to use
a separate `all` formula for each one, as follows.

```
theorem interval_length:
  all count:Nat. all start:Nat. length(interval(count, start)) = count
proof
  ?
end
```

There is also the question of whether `all count:Nat` should come
before or after `all start:Nat`. It is always safe to first choose the
variable for which you're using induction. If you make the other
choice, the induction hypothesis will be weaker, which sometimes is
convenient but other times prevents the proof from going through.

Now let us start the proof. We proceed by induction on the `count`. 

```
theorem interval_length:
  all count:Nat. all start:Nat. length(interval(count, start)) = count
proof
  induction Nat
  case 0 {
    ?
  }
  case suc(count') suppose IH {
    ?
  }
end
```

In the case for `count = 0`, Deduce tells us that we need to prove
```
  all start:Nat. length(interval(0,start)) = 0
```
As mentioned earlier, we'll use `arbitrary` for `start`.
```
  case 0 {
    arbitrary start:Nat
    ?
  }
```
So now we need to prove
```
  length(interval(0,start)) = 0
```
Of course, by definition we have `interval(0,start) = empty`
and `length(empty) = 0`, so we can conclude using those definitions.
```
  case 0 {
    arbitrary start:Nat
    conclude length(interval(0, start)) = 0
	    by definition {interval, length}.
  }
```

Turning to the case `count = suc(count')`, Deduce tells us the goal
for this case and the induction hypothesis.

```
incomplete proof
Goal:
    all start:Nat. length(interval(suc(count'),start)) = suc(count')
Givens:
    IH: all start:Nat. length(interval(count',start)) = count'
```

To improve readability of the proof, I often like to copy the formula
for the induction hypothesis and paste it into the `suppose` as shown
below.

```
  case suc(count') 
    suppose IH: all start:Nat. length(interval(count', start)) = count' 
  {
    ?
  }
```

For the proof of this case, we again start with `arbitrary` to handle
`all start` then use the definitions of `interval` and `length`.

```
  case suc(count')
    suppose IH: all start:Nat. length(interval(count', start)) = count'
  {
    arbitrary start:Nat
    definition {interval, length}
    ?
  }
```

Deduce tells us that we need to prove the following.
```
suc(length(interval(count',suc(start)))) = suc(count')
```
Here the induction hypothesis `IH` comes to the rescue. 
If we instantiate the `all start` with `suc(start)`, we get
```
length(interval(count',suc(start))) = count'
```
which is just what we need to conclude.
```
  case suc(count') 
    suppose IH: all start:Nat. length(interval(count', start)) = count' 
  {
    arbitrary start:Nat
    definition {interval, length}
    conclude suc(length(interval(count',suc(start)))) = suc(count')
	    by rewrite IH[suc(start)].
  }
```

Putting the two cases together, we have the following completed proof
that the output of `interval` has the appropriate length.

``` {.deduce #interval_length}
theorem interval_length:
  all count:Nat. all start:Nat. length(interval(count, start)) = count
proof
  induction Nat
  case 0 {
    arbitrary start:Nat
    conclude length(interval(0, start)) = 0
	    by definition {interval, length}.
  }
  case suc(count')
    suppose IH: all start:Nat. length(interval(count', start)) = count' 
  {
    arbitrary start:Nat
    definition {interval, length}
    conclude suc(length(interval(count',suc(start)))) = suc(count')
	    by rewrite IH[suc(start)].
  }
end
```

#### Prove the `interval_nth` theorem

The second part of the specification of `interval` says that
the element at position `i` of the output is `i + start`.
Of course, there is no element at position `i` if `i` is too big,
so our theorem needs to be conditional, with the premise `i < count`.

```
theorem interval_nth: all count:Nat. all start:Nat, d:Nat, i:Nat.
  if i < count
  then nth(interval(count, start), d)(i) = i + start
proof
   ?
end
```

Because this proof is about a recursive function whose first parameter
is of type `Nat`, we proceed by induction on `Nat`.

```
  induction Nat
  case 0 {
    ?
  }
  case suc(count') suppose IH {
    ?
  }
```

In the case `count = 0`, Deduce tells us that we need to prove

```
all start:Nat, d:Nat, i:Nat.
    if i < 0 then nth(interval(0,start),d)(i) = i + start
```

So we can start the proof of this case with `arbitrary` and `suppose`,
then use the definitions of `interval` and `nth`.

```
  case 0 {
    arbitrary start:Nat, d:Nat, i:Nat
    suppose i_l_z: i < 0
    definition {interval, nth}
    ?
  }
```

Deduce responds with
```
Goal:
    d = i + start
Givens:
    i_l_z: i < 0
```
Now we are in a strange situation. The goal seems rather difficult to prove 
because we don't know anything about `start` and `d`. The givens (aka. assumptions)
are also strange. How can the natural number `i` be less than `0`?
Of course it cannot. Thus, `i < 0` implies `false` and then we can use
the principle of explosion, which states that `false` implies anything,
to prove that `d = i + start`.

```
  case 0 {
    arbitrary start:Nat, d:Nat, i:Nat
    suppose i_l_z: i < 0
    definition {interval, nth}
    conclude false  by definition {operator <, operator ≤} in i_l_z
  }
```

Next we turn to the case for `count = suc(count')`. Deduce tells us
the formula for the induction hypothesis, so we paste that into
the `suppose IH`. Looking at the goal formula, we begin the proof
with `arbitrary`, `suppose`, and use the definitions of `interval` and `nth`.

```
  case suc(count') 
    suppose IH: all start:Nat, d:Nat, i:Nat. 
        if i < count' then nth(interval(count',start),d)(i) = i + start
  {
    arbitrary start:Nat, d:Nat, i:Nat
    suppose i_l_sc: i < suc(count')
    definition {interval, nth}
    ?
  }
```

Deduce responds with the following.

```
Goal:
    if i = 0 then start
	else nth(interval(count',suc(start)),d)(pred(i)) = i + start
```

What we're seeing here is that the `nth` function uses an `if`-`then`-`else`
with `i = 0` as the condition. So to reason about this goal, we need to
break our proof down into two cases, when `i = 0` and `i ≠ 0`. One
convenient way to do that in Deduce is with a `switch`.

```
  switch i {
	case 0 {
	  ?
	}
	case suc(i') suppose i_sc: i = suc(i') {
	  ?
	}
  }
```

Let us proceed with the case for `i = 0`. Deduce simplifies the goal
and responds with 
```
Goal:
    start = 0 + start
```

which follows directly from the definition of addition.

```
  case 0 {
	conclude start = 0 + start   by definition operator +.
  }
```

In the case for `i = suc(i')`, Deduce tells us that we need to prove
```
  nth(interval(count',suc(start)),d)(pred(suc(i'))) = suc(i') + start
```
This looks quite similar to the induction hypothesis instantiated with
`suc(start)`, `d`, and `i'`:
```
  if i' < count' 
  then nth(interval(count',suc(start)),d)(i') = i' + suc(start)
```
One difference is `pred(suc(i'))` versus `i'`, but they are equal by the
definition of `pred`.
```
  case suc(i') suppose i_sc: i = suc(i') {
	definition pred
	?
  }
```
Deduce responds with
```
Goal:
    nth(interval(count',suc(start)),d)(i') = suc(i') + start
```
So if we use the induction hypothesis, then we will just need to
prove that `i' + suc(start) = suc(i') + start`, which is certainly
true and will just require a little reasoning about addition.
But to use the induction hypothesis, we need to prove that `i' < count'`.
This follows from the givens `i_l_sc: i < suc(count')`
and `i_sc: i = suc(i')` and the definitions of `<` and `≤`.

```
  case suc(i') suppose i_sc: i = suc(i') {
	definition pred
	have i_l_cnt: i' < count'  by enable {operator <, operator ≤}
								  rewrite i_sc in i_l_sc
	?
  }
```

Now we can complete the proof of this case by linking together a few
equations, starting with the induction hypothesis, then using the
`add_suc` theorem from `Nat.pf` (which states that `m + suc(n) =
suc(m + n)`), and finally using the definition of addition (which
states that `suc(n) + m = suc(n + m)`).

```
  equations
	nth(interval(count',suc(start)),d)(i') 
		= i' + suc(start)        by apply IH[suc(start), d, i'] to i_l_cnt
	... = suc(i' + start)        by add_suc[i'][start]
	... = suc(i') + start        by definition operator +.
```

Putting together all these pieces, we have the following complete proof
of the `interval_nth` theorem. At this point we know that the `interval`
function is 100% correct!

``` {.deduce #interval_nth }
theorem interval_nth: all count:Nat. all start:Nat, d:Nat, i:Nat.
  if i < count
  then nth(interval(count, start), d)(i) = i + start
proof
  induction Nat
  case 0 {
    arbitrary start:Nat, d:Nat, i:Nat
    suppose i_l_z: i < 0
    definition {interval, nth}
    conclude false  by definition {operator <, operator ≤} in i_l_z
  }
  case suc(count') 
    suppose IH: all start:Nat, d:Nat, i:Nat. 
        if i < count' then nth(interval(count',start),d)(i) = i + start
  {
    arbitrary start:Nat, d:Nat, i:Nat
    suppose i_l_sc: i < suc(count')
    definition {interval, nth}
    switch i {
      case 0 {
        conclude start = 0 + start   by definition operator +.
      }
      case suc(i') suppose i_sc: i = suc(i') {
        definition pred
        have i_l_cnt: i' < count'  by enable {operator <, operator ≤}
                                      rewrite i_sc in i_l_sc
        equations
          nth(interval(count',suc(start)),d)(i') 
              = i' + suc(start)    by apply IH[suc(start), d, i'] to i_l_cnt
          ... = suc(i' + start)    by add_suc[i'][start]
          ... = suc(i') + start    by definition operator +.
      }
    }
  }
end
```


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


## Exercise: Test Append

Write `assert` statements to test the `append` function that you have
defined.  Formulate the assertions to closely match the above
specification of above.  Refer to the assertions that we wrote above
to test `interval` to see an example of how to write the tests.


## More Automation in Tests

An added benefit of formulating the assertions based on the
specification is that it enables us to automate our testing. In the
following code we append the list `1, 2, 3` with `4, 5` and then check
the resulting list using only two `assert` statements. The first
`assert` checks whether the front part of the result matches the first
input list and the second `assert` checks whether the back part of the
result matches the second input list. We make use of another function
named `all_elements` that we describe next.

``` {.deduce #test_append_123_45}
define list_45 : List<Nat> = node(4, node(5, empty))
define list_1_5 = append(list_123, list_45)
assert all_elements(interval(3, 0),
                    λi{ nth(list_1_5, 0)(i) = nth(list_123,0)(i) })
assert all_elements(interval(2, 0),
                    λi{ nth(list_1_5, 0)(3 + i) = nth(list_45,0)(i) })
```

The `all_elements` function takes a list and a function and checks
whether applying the function to every element of the list always
produces `true`.

``` {.deduce #all_elements}
function all_elements<T>(List<T>, fn (T) -> bool) -> bool {
  all_elements(empty, P) = true
  all_elements(node(x, xs'), P) = P(x) and all_elements(xs', P)
}
```

Going a step further, we can adapt the tests to apply to longer lists
by automating the creation of the input lists. Here we increase the
combined size to `20` elements. We could go with longer lists, but
Deduce currently has a slow interpreter, so the assertions would take
a long time (e.g., a minute for `100` elements).

``` {.deduce #test_append_large}
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
theorem nth_append_front:
  all T:type. all xs:List<T>. all ys:List<T>, i:Nat, d:T.
  if i < length(xs)
  then nth(append(xs, ys), d)(i) = nth(xs, d)(i)
proof
  FILL IN HERE
end

theorem nth_append_back: 
  all T:type. all xs:List<T>. all ys:List<T>, i:Nat, d:T.
  nth(append(xs, ys), d)(length(xs) + i) = nth(ys, d)(i)
proof
  FILL IN HERE
end
```

<!--
```{.deduce file=LinkedLists.pf}
<<importNat>>

<<list>>
<<length>>
<<nth>>
<<interval>>
<<interval_example>>

function append<E>(List<E>, List<E>) -> List<E> {
  append(empty, ys) = ys
  append(node(n, xs), ys) = node(n, append(xs, ys))
}

<<all_elements>>

<<test_interval>>
<<interval_length>>
<<interval_nth>>

<<list_123>>
<<test_length_123>>
<<test_nth_123>>

<<test_append_123_45>>

// Solution: Test Append
assert nth(list_1_5, 0)(0) = nth(list_123,0)(0)
assert nth(list_1_5, 0)(1) = nth(list_123,0)(1)
assert nth(list_1_5, 0)(2) = nth(list_123,0)(2)

assert nth(list_1_5, 0)(3) = nth(list_45,0)(0)
assert nth(list_1_5, 0)(4) = nth(list_45,0)(1)

<<test_append_large>>

theorem nth_append_front: all T:type. all xs:List<T>. all ys:List<T>, i:Nat, d:T.
  if i < length(xs)
  then nth(append(xs, ys), d)(i) = nth(xs, d)(i)
proof
  arbitrary T:type
  induction List<T>
  case empty {
    arbitrary ys:List<T>, i:Nat, d:T
    suppose i_z: i < length(empty : List<T>)
    conclude false by definition {length, operator <, operator ≤} in i_z
  }
  case node(x, xs) suppose IH {
    arbitrary ys:List<T>, i:Nat, d:T
    suppose i_xxs: i < length(node(x,xs))
    definition append
    switch i {
      case 0 {
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

<!--  LocalWords:  suc pred importNat xs fn Deduce's IH aka sc cnt pf
 -->
<!--  LocalWords:  num elts ys bool xxs si eq
 -->
