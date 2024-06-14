# Sequential Search

In this blog post we'll study a classic and simple algorithm known as
Sequential Search (aka. Linear Search). The basic idea of the
algorithm is to look for the location of a particular item within a
linked list, traversing the list front to back.  Here is the
specification of this `search` function.

**Specification:** The `search(xs, y)` function returns a natural
number `i` such that `i ≤ length(xs)`.  If `i < length(xs)`, then `i`
is the index of the first occurence of `y` in the list `xs`.  If `i =
length(xs)`, `y` is not in the list `xs`.

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
recursive call is to use the specification of the function.  The
specification of `search` splits into two cases on the result: (1)
`search(xs', y) < length(xs')` and (2) `length(xs) ≤ search(xs', y)`.
In case (1), `search(xs',y)` is returning the index of the first `y`
inside `xs'`. Because `x ≠ y`, that location will also be the first
`y` inside `node(x, xs')`. However, we need to add one to the index to
take into account that we're adding a node to the front of the list.
So for case (1), the result should be `suc(search(xs', y))`.  In case
(2), `search(xs',y)` did not find `y` in `xs'`, so it is returning
`length(xs')`.  Because `x ≠ y`, we need to indicate that `y` is also not
found in `node(x, xs')`, so we need to return `length(node(x,
xs'))`. Thus, we need to add one to the index, so the result should
again be `suc(search(xs', y))`.

Here is the completed code for `search`.

``` {.deduce #search}
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
that we should test. First, we should test whether `search` always
returns a number that is less-or-equal to the length of the list.  We
can use `all_elements` and `interval` to automate the testing over a
bunch of values, some of which are in the list and some are not.

``` {.deduce #search_test1}
define list_1223 = node(1, node(2, node(2, node(3, empty))))

assert all_elements(interval(0, 5),
  λx{ search(list_1223, x) ≤ length(list_1223) })
```

Most importantly, we should test whether `search` finds the correct
index of the elements in the list. To do that we can make use of `nth`
to lookup the element at a given index.

``` {.deduce #search_test2}
assert all_elements(list_1223,
  λx{ nth(list_1223, 0)( search(list_1223, x) ) = x })
```

Next, we should test whether `search` finds the first occurence. We
can do this by iterating over all the indexes and checking that what
`search` returns is an index that is less-than or equal to the current
index.

``` {.deduce #search_test3}
assert all_elements(interval(0, length(list_1223)),
   λi{ search(list_1223, nth(list_1223, 0)(i)) ≤ i })
```

Finally, we check that `search` fails gracefully when the value being
searched for is not present in the list.

``` {.deduce #search_test4}
assert search(list_1223, 0) = length(list_1223)
assert search(list_1223, 4) = length(list_1223)
```

## Prove `search` Correct

We break down the specification of `search` into four parts and prove
four theorems.

### Prove `search` is less-or-equal `length`

The first part of the specification of `search` says that
the `search(xs, y)` function returns a natural number `i` such that `i
≤ length(xs)`. Because `search` is recursive, we're going to 
prove this by induction on its first parameter `xs`.

```
theorem search_length: all xs:List<Nat>. all y:Nat.
  search(xs, y) ≤ length(xs)
proof
  induction List<Nat>
  case empty {
    ?
  }
  case node(x, xs') 
    suppose IH: all y:Nat. search(xs',y) ≤ length(xs') 
  {
    ?
  }
end
```

In the case for `xs = empty`, Deduce tells us that we need to prove

```
Goal:
    all y:Nat. search(empty,y) ≤ length(empty)
```

So we start with `arbitrary y:Nat` and then conclude using the
definitions of `search`, `length`, and `operator ≤`.

```
  case empty {
    arbitrary y:Nat
	conclude search(empty,y) ≤ length(empty)
        by definition {search, length, operator ≤}.
  }
```

In the case for `xs = node(x, xs')`, Deduce tells us that we need to prove

```
Goal:
	all y:Nat. search(node(x,xs'),y) ≤ length(node(x,xs'))
```

So we start with `arbitrary y:Nat` and use the definitions of `search`
and `length`.

```
  case node(x, xs') 
    suppose IH: all y:Nat. search(xs',y) ≤ length(xs') 
  {
    arbitrary y:Nat
	definition {search, length}
	?
  }
```

The goal is transformed to the following, with the body of `search`
expanded on the left of the `≤` and the body of `length` expanded on
the right.

```
Goal:
	if x = y then 0 else suc(search(xs',y)) ≤ suc(length(xs'))
```

In general, it is a good idea to let the structure of the code direct
the structure of your proof. In this case, the code for `search` is a
conditional on `x = y`, so in our proof we can `switch` on `x = y` as
follows.

```
  case node(x, xs') 
    suppose IH: all y:Nat. search(xs',y) ≤ length(xs') 
  {
    arbitrary y:Nat
	definition {search, length, operator ≤}
	switch x = y {
	  case true suppose xy_true: (x = y) = true {
        ?
	  }
	  case false suppose xy_false: (x = y) = false {
	    ?
	  }
	}
  }
```

In the case for `true`, the left-hand side of the `≤` becomes `0`, so
we can conclude by the definition of `operator ≤`.

```
  case true {
	conclude 0 ≤ suc(length(xs'))  by definition operator ≤.
  }
```

In the case for `false`, the left-hand side of the `≤` becomes
`suc(search(xs',y))`, so we have `suc` on both side of `≤`.  Therefore
we apply the definition of `≤` and it remains to prove the following.

```
Goal:
	search(xs',y) ≤ length(xs')
```

We conclude the proof of the `false` case by using the induction hypothesis

```
  case false {
	definition operator ≤
	conclude search(xs',y) ≤ length(xs')
	  by IH[y]
  }
```

Putting all of the pieces together, we have a complete proof of
`search_length`.

``` {.deduce #search_length}
theorem search_length: all xs:List<Nat>. all y:Nat.
  search(xs, y) ≤ length(xs)
proof
  induction List<Nat>
  case empty {
    arbitrary y:Nat
	conclude search(empty,y) ≤ length(empty)
        by definition {search, length, operator ≤}.
  }
  case node(x, xs') 
    suppose IH: all y:Nat. search(xs',y) ≤ length(xs') 
  {
    arbitrary y:Nat
	definition {search, length}
	switch x = y {
	  case true {
        conclude 0 ≤ suc(length(xs'))  by definition operator ≤.
	  }
	  case false {
	    definition operator ≤
	    conclude search(xs',y) ≤ length(xs')
		  by IH[y]
	  }
	}
  }
end
```


### Prove `search(xs, y)` finds an occurence of `y`

The specification of `search(xs, y)` says that if the result is
less-than `length(xs)`, then the result is the index of the first
occurence of `y` in `xs`. First off, this means that `search(xs, y)`
is indeed an index for `y`, which we can express using `nth` as
follows.

```
nth(xs, 0)( search(xs, y) ) = y
```

So we can formulate the following theorem, which we'll prove by
induction on `xs`.

```
theorem search_present: all xs:List<Nat>. all y:Nat.
  if search(xs, y) < length(xs)
  then nth(xs, 0)( search(xs, y) ) = y
proof
  induction List<Nat>
  case empty {
    arbitrary y:Nat
    ?
  }
  case node(x, xs') suppose IH {
    arbitrary y:Nat
    ?
  }
end
```

In the case for `xs = empty`, Deduce tells us that we need to prove

```
Goal:
	(if search(empty,y) < length(empty) then nth(empty,0)(search(empty,y)) = y)
```

Proceeding in a goal-directed way, we `suppose` the premise but then
realize that the premise is false. So we can conclude using the
principle of explosion.

```
  case empty {
    arbitrary y:Nat
	suppose prem: search(empty,y) < length(empty)
	conclude false by definition {search, length, operator <, operator ≤} 
	                  in prem
  }
```

Moving on to the case for `xs = node(x, xs')`, we again `suppose`
the premise.

```
  case node(x, xs') suppose IH {
    arbitrary y:Nat
	suppose sxxs_len: search(node(x,xs'),y) < length(node(x,xs'))
	?
  }
```

Deduce tells us that we need to prove

```
Goal:
	nth(node(x,xs'),0)(search(node(x,xs'),y)) = y
```

We see `search` applied to a `node` argument, so we can expand its
definition. (We could also expand `nth` but we postpone doing that
for the sake of readability.)

```
Goal:
	nth(node(x,xs'),0)((if x = y then 0 else suc(search(xs',y)))) = y
```

Similar to the proof of `search_length`, we now need to `switch` on `x
= y`.

```
	definition {search}
	switch x = y {
      case true suppose xy_true {
	    ?
	  }
	  case false suppose xy_false {
	    ?
	  }
	}
```

In the case for `true`, Deduce tells us that we need to prove

```
Goal:
	nth(node(x,xs'),0)(0) = y
```

We conclude using the definition of `nth` and the fact that `x = y`.

```
      case true suppose xy_true {
	    conclude nth(node(x,xs'),0)(0) = y
	      by definition nth rewrite xy_true.
	  }
```

In the case for `false`, we need to prove

```
Goal:
	nth(node(x,xs'),0)(suc(search(xs',y))) = y
```

Now if we apply the definitions of `nth` and `pred`, the goal becomes.

```
Goal:
	nth(xs',0)(search(xs',y)) = y
```

This looks a lot like the conclusion of our induction hypothesis:

```
Givens:
	...
	IH: all y:Nat. (if search(xs',y) < length(xs') 
	                then nth(xs',0)(search(xs',y)) = y)
```

So we just need to prove the premise, that `search(xs',y) < length(xs')`.
Thankfully, that can be proved from the premise 
`search(node(x,xs'),y) < length(node(x,xs'))`.

```
  have sxs_len: search(xs',y) < length(xs')
	by enable {search, length, operator <, operator ≤}
	   rewrite xy_false in sxxs_len
```

We conclude by applying the induction hypothesis.

```
  conclude nth(xs',0)(search(xs',y)) = y
	by apply IH[y] to sxs_len
```

Here is the the complete proof of `search_present`.

``` {.deduce #search_present}
theorem search_present: all xs:List<Nat>. all y:Nat.
  if search(xs, y) < length(xs)
  then nth(xs, 0)( search(xs, y) ) = y
proof
  induction List<Nat>
  case empty {
    arbitrary y:Nat
	suppose prem: search(empty,y) < length(empty)
	conclude false by definition {search, length, operator <, operator ≤} 
	                  in prem
  }
  case node(x, xs') suppose IH {
    arbitrary y:Nat
	suppose sxxs_len: search(node(x,xs'),y) < length(node(x,xs'))
	definition {search}
	switch x = y {
      case true suppose xy_true {
	    conclude nth(node(x,xs'),0)(0) = y
	      by definition nth rewrite xy_true.
	  }
	  case false suppose xy_false {
	    definition {nth, pred}
		have sxs_len: search(xs',y) < length(xs')
		  by enable {search, length, operator <, operator ≤}
		     rewrite xy_false in sxxs_len
	    conclude nth(xs',0)(search(xs',y)) = y
		  by apply IH[y] to sxs_len
	  }
	}
  }
end
```


### Prove `search(xs, y)` finds first occurence of `y`


Next, for the index to be the first, it means that for any other
location `i` of `y`, the result of `search(xs, y)` is less-or-equal to
`i`.

```
all i:Nat. if nth(xs, 0)(i) = y then search(xs, y) ≤ i
```


``` {.deduce #search_first}
theorem search_first: all xs:List<Nat>. all y:Nat.
  if search(xs, y) < length(xs)
  then nth(xs, 0)( search(xs, y) ) = y
  and (all i:Nat. if nth(xs, 0)(i) = y then search(xs, y) ≤ i)
proof
  induction List<Nat>
  case empty {
    arbitrary y:Nat
	definition {search, length, operator <, operator ≤}.
  }
  case node(x, xs') suppose IH {
    arbitrary y:Nat
	suppose sxxs_len: search(node(x,xs'),y) < length(node(x,xs'))
	definition {search, length}
	switch x = y {
      case true suppose xy_true {
	    definition {operator <, operator ≤}
	    definition {nth}
		rewrite xy_true
		arbitrary i:Nat
	    definition operator ≤.
	  }
	  case false suppose xy_false {
		have sxs_len: search(xs',y) < length(xs')
		  by enable {operator <, operator ≤}
		     rewrite xy_false in definition {search, length} in
			 sxxs_len
	    have IH1: nth(xs',0)(search(xs',y)) = y
		  by apply IH[y] to sxs_len
	    definition {nth, pred}
		have IH2: all i:Nat. (if (if i = 0 then x else nth(xs',0)(pred(i))) = y then suc(search(xs',y)) ≤ i)
		  by arbitrary i:Nat
		     suppose prem
			 switch i {
		       case 0 suppose i_z {
			     have x_y: x = y by rewrite i_z in prem
				 conclude false by rewrite xy_false in x_y
			   }
			   case suc(i') suppose i_si {
			     definition operator ≤
				 suffices search(xs',y) ≤ i'
				 have nth_i_y: nth(xs',0)(i') = y
				   by definition pred in rewrite i_si in prem
			     have IH': if nth(xs',0)(i') = y then search(xs',y) ≤ i'
			       by (conjunct 1 of (apply IH[y] to sxs_len))[i']
			     apply IH' to nth_i_y
			   }
		     }
        IH1, IH2
	  }
	}
  }
end
```

### Prove that search fails only when it should

```
theorem search_absent:
all xs:List<Nat>. all y:Nat, d:Nat.
  if search(xs, y) = length(xs)
  then not (y ∈ set_of(xs))
```

<!--
``` {.deduce file=LinearSearch.pf} 
import Nat import LinkedLists
<<search>>

<<search_test1>>
<<search_test2>>
<<search_test3>>
<<search_test4>>

<<search_length>>
<<search_present>>
<<search_first>>
```
-->
