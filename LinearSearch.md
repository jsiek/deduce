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

## Write the `search` function

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

## Test the `search` function

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
	  case true {
        ?
	  }
	  case false {
	    ?
	  }
	}
  }
```

In the case for `x = y`, the left-hand side of the `≤` becomes `0`, so
we can conclude by the definition of `operator ≤`.

```
  case true {
	conclude 0 ≤ suc(length(xs'))  by definition operator ≤.
  }
```

In the case for `x ≠ y`, the left-hand side of the `≤` becomes
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

In the case where `x = y`, Deduce tells us that we need to prove

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

In the case where `x ≠ y`, we need to prove

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


### Prove `search(xs, y)` finds the first occurence of `y`

Going back to the specification of `search(xs, y)`, it says that if
the result is less-than `length(xs)`, then the result is the index of
the first occurence of `y` in `xs`. To be the first means that the
result is smaller than the index of any other occurence of `y`.  We
express that in the following theorem.

```
theorem search_first: all xs:List<Nat>. all y:Nat, i:Nat.
  if search(xs, y) < length(xs) and nth(xs, 0)(i) = y
  then search(xs, y) ≤ i
```

We proceed by induction on `xs`. We can handle the case for `xs =
empty` in the same way as in `search_present`; the premise is false.

```
  induction List<Nat>
  case empty {
    arbitrary y:Nat, i:Nat
	suppose prem: search(empty,y) < length(empty) and nth(empty,0)(i) = y
	conclude false by definition {search, length, operator <, operator ≤} 
	                  in prem
  }
```

In the case for `xs = node(x, xs')`, we proceed in a goal-directed
fashion with an `arbitrary` and `suppose`.

```
  case node(x, xs') suppose IH {
    arbitrary y:Nat, i:Nat
	suppose prem: search(node(x,xs'),y) < length(node(x,xs')) 
	              and nth(node(x,xs'),0)(i) = y,
	?
  }
```

Deduce response with

```
Goal:
	search(node(x,xs'),y) ≤ i
```

We apply the definition of `search` and then `switch` on `x = y`.

```
  definition search
  switch x = y {
	case true {
	  ?
	}
	case false suppose xs_false {
	  ?
	}
  }
```

In the case where `x = y`, the result of `search` is `0`, so just
need to prove that `0 ≤ i`, which follows from the definition of `≤`.

```
  case true {
	conclude 0 ≤ i   by definition operator ≤.
  }
```

In the case where `x ≠ y`, we need to prove

```
Goal:
	suc(search(xs',y)) ≤ i
```

What do we now about `i`? The premise `nth(node(x,xs'),0)(i) = y`
tells us that `i ≠ 0`. So we can `switch` on `i` and use the principle
explosion to handle the case where `i = 0`.

```
  case 0 suppose i_z: i = 0 {
	conclude false
	  by enable nth rewrite i_z | xy_false in prem
  }
```

We are left with the case where `i = suc(i')`. Using the definition of
`≤`, the goal becomes

```
Goal:
	search(xs',y) ≤ i'
```

This looks like the conclusion of the induction hypothesis
instantiated at `i'`.

```
Givens:
	...
	IH: all y:Nat, i:Nat. (if search(xs',y) < length(xs') and nth(xs',0)(i) = y then search(xs',y) ≤ i)
```

So we need to prove the two premises of the `IH`. They follow from the
given `prem`:

```
Givens:
	prem: search(node(x,xs'),y) < length(node(x,xs')) and nth(node(x,xs'),0)(i) = y,
```

In particular, the first premise of `IH` follows from the
first conjunct of `prem`.
```
  have sxs_len: search(xs',y) < length(xs')
	by enable {search, length, operator <, operator ≤}
	   rewrite xy_false in (conjunct 0 of prem)
```

The second premise of the `IH` follows from the second
conjunct of `prem`.

```
  have nth_i_y: nth(xs',0)(i') = y
	by enable {nth, pred} rewrite i_si in (conjunct 1 of prem)
```

We conclude the case for `i = suc(i')` by applying the induction
hypothesis.

```
  conclude search(xs',y) ≤ i'   by apply IH[y,i'] to sxs_len, nth_i_y
```

Here is the complete proof of `search_first`.

``` {.deduce #search_first}
theorem search_first: all xs:List<Nat>. all y:Nat, i:Nat.
  if search(xs, y) < length(xs) and nth(xs, 0)(i) = y
  then search(xs, y) ≤ i
proof
  induction List<Nat>
  case empty {
    arbitrary y:Nat, i:Nat
	suppose prem: search(empty,y) < length(empty) and nth(empty,0)(i) = y
	conclude false by definition {search, length, operator <, operator ≤} 
	                  in prem
  }
  case node(x, xs') suppose IH {
    arbitrary y:Nat, i:Nat
	suppose prem: search(node(x,xs'),y) < length(node(x,xs')) 
	              and nth(node(x,xs'),0)(i) = y
	definition search
	switch x = y {
	  case true {
	    conclude 0 ≤ i   by definition operator ≤.
	  }
	  case false suppose xy_false {
	    switch i {
	      case 0 suppose i_z: i = 0 {
		    conclude false
	          by enable nth rewrite i_z | xy_false in prem
		  }
		  case suc(i') suppose i_si: i = suc(i') {
		    definition operator ≤
			have sxs_len: search(xs',y) < length(xs')
			  by enable {search, length, operator <, operator ≤}
				 rewrite xy_false in (conjunct 0 of prem)
	        have nth_i_y: nth(xs',0)(i') = y
			  by enable {nth, pred} rewrite i_si in (conjunct 1 of prem)
		    conclude search(xs',y) ≤ i'   by apply IH[y,i'] to sxs_len, nth_i_y
		  }
	    }
	  }
	}
  }
end
```

### Prove that search fails only when it should

The last sentence in the specification for `search(xs, y)` says that
if `i = length(xs)`, `y` is not in the list `xs`. How do we express
that `y` is not in the list? In some sense, that is what `search` is
for, but it would be vacuous to prove a theorem that says `search`
returns `length(xs)` if `search` returns `lengt(xs)`. Instead we need
an alternative and intuitive way to express membership in a list.

One approach to expressing list membership that works well is to
convert the list to a set and then use set membership.  The file
`Set.pf` defines the `Set` type, operations on sets such as
memberhsip, union, and intersection. The `Set.pf` files also proves
many theorems about these operations.  The following `set_of` function
converts a list into a set.

``` {.deduce #set_of}
function set_of<T>(List<T>) -> Set<T> {
  set_of(empty) = ∅
  set_of(node(x, xs)) = single(x) ∪ set_of(xs)
}
```

We can now express our last correctness theorem for `search` as
follows.

```
theorem search_absent: all xs:List<Nat>. all y:Nat, d:Nat.
  if search(xs, y) = length(xs)
  then not (y ∈ set_of(xs))
```

We proceed by induction on `xs`. 
In the case for `xs = empty`, we take the following goal-directed steps

```
  case empty {
    arbitrary y:Nat, d:Nat
    suppose _
	?
  }
```

and Deduce responds with

```
Goal:
	(if y ∈ set_of(empty) then false)
```

which we prove using the `empty_no_members` theorem from `Set.pf`.

```
  conclude not (y ∈ set_of(empty))
      by definition {set_of} empty_no_members[Nat,y]
```

Turning to the case for `xs = node(x, xs')`, we take several
goal-directed steps.

```
  case node(x, xs') suppose IH {
    arbitrary y:Nat, d:Nat
    suppose s_xxs_len_xxs: search(node(x,xs'),y) = length(node(x,xs'))
	definition set_of
    ?
```

We need to show that `y` is not in `node(x, xs')`, which amounts to
the following.

```
Goal:
	(if y ∈ single(x) ∪ set_of(xs') then false)
```

Towards proving a contradiction, we can assume `y ∈ single(x) ∪
set_of(xs')`.

```
  suppose y_in_x_union_xs: y ∈ single(x) ∪ set_of(xs')
```

Now the main information we have to work with is the premise
`s_xxs_len_xxs` above, concerning `search(node(x,xs'), y)`.  Thinking
about the code for `search`, we know it will branch on whether `x = y`,
so we better `switch` on that.

```
  switch x = y {
	case true suppose xy {
	  ?
	}
	case false suppose not_xy {
	  ?
	}
  }
```

In the case where `x = y`, we have `search(node(x,xs'),y) = 0` but
`length(node(x,xs'))` is at least `1`, so we have a contradition.

```
  case true suppose xy {
	have s_xxs_0: search(node(x,xs'),y) = 0
		by definition search  rewrite xy.
	have z_len_xxs: 0 = length(node(x,xs'))
		by rewrite s_xxs_0 in s_xxs_len_xxs
	conclude false  by definition length in z_len_xxs
  }
```

In the case where `x ≠ y`, we can show that `y ∈ set_of(xs')` and then
invoke the induction hypothesis to obtain the contradition.  In
patricular, the premise `y_in_x_union_xs` gives us the following.

```
  have ysx_or_y_xs: y ∈ single(x) or y ∈ set_of(xs')
	  by apply member_union[Nat,y,single(x),set_of(xs')]
		 to y_in_x_union_xs
```

But `x ≠ y` implies `not (y ∈ single(x))`.

```
  have not_ysx: not (y ∈ single(x))
	by suppose ysx
	   rewrite xy_false in
	   apply single_equal[Nat,x,y] to ysx
```

So it must be that `y ∈ set_of(xs')` (using `or_not` from `Base.pf`).

```
  have y_xs: y ∈ set_of(xs')
	by apply or_not[y ∈ single(x), y ∈ set_of(xs')] 
	   to ysx_or_y_xs, not_ysx
```

To satisfy the premise of the induction hypothesis, we prove the
following.

```
  have sxs_lxs: search(xs',y) = length(xs')
	by injective suc
	   rewrite xy_false in definition {search,length} in
	   s_xxs_len_xxs
```

So we apply the induction hypothesis to 
get `y ∉ set_of(xs')`, which contradicts `y ∈ set_of(xs)`.

```
  have y_not_xs: not (y ∈ set_of(xs'))
	by apply IH[y,d] to sxs_lxs
  conclude false  by apply y_not_xs to y_xs
```

Here is the complete proof of `search_absent`.

``` {.deduce #search_absent}
theorem search_absent: all xs:List<Nat>. all y:Nat, d:Nat.
  if search(xs, y) = length(xs)
  then not (y ∈ set_of(xs))
proof
  induction List<Nat>
  case empty {
    arbitrary y:Nat, d:Nat
    suppose _
    conclude not (y ∈ set_of(empty))
        by definition {set_of} empty_no_members[Nat,y]
  }
  case node(x, xs') suppose IH {
    arbitrary y:Nat, d:Nat
    suppose s_xxs_len_xxs: search(node(x,xs'),y) = length(node(x,xs'))
	definition set_of
	suppose y_in_x_union_xs: y ∈ single(x) ∪ set_of(xs')
    switch x = y {
      case true suppose xy {
	    have s_xxs_0: search(node(x,xs'),y) = 0
		    by definition search  rewrite xy.
	    have z_len_xxs: 0 = length(node(x,xs'))
		    by rewrite s_xxs_0 in s_xxs_len_xxs
	    conclude false  by definition length in z_len_xxs
      }
      case false suppose xy_false {
	    have ysx_or_y_xs: y ∈ single(x) or y ∈ set_of(xs')
	        by apply member_union[Nat,y,single(x),set_of(xs')]
			   to y_in_x_union_xs
	    have not_ysx: not (y ∈ single(x))
		  by suppose ysx
		     rewrite xy_false in
			 apply single_equal[Nat,x,y] to ysx
	    have y_xs: y ∈ set_of(xs')
		  by apply or_not[y ∈ single(x), y ∈ set_of(xs')] 
		     to ysx_or_y_xs, not_ysx
		have sxs_lxs: search(xs',y) = length(xs')
		  by injective suc
			 rewrite xy_false in definition {search,length} in
			 s_xxs_len_xxs
	    have y_not_xs: not (y ∈ set_of(xs'))
		  by apply IH[y,d] to sxs_lxs
		conclude false  by apply y_not_xs to y_xs
      }
    }
  }
end
```

## Exercise `search_last`

Apply the write-test-prove approach to develop a correct
implementation of the `search_last(xs, y)` function, which is like
`search(xs, y)` except that it finds the last occurence of `y` in `xs`
instead of the first.

In particular, you need to

* write a specification for `search_last`,
* write the code for `search_last`,
* test `search_last` on diverse inputs, and
* prove that `search_last` is correct.

```
function search_last(List<Nat>, Nat) -> Nat {
    FILL IN HERE
}
```

## Exercise `search_if`

The `search_if(xs, P)` function is a generalization of `search(xs, y)`.
Instead of searching for the first occurence of element `y`,
the `search_if` function searches for the location of the first 
element that satisfied predicate `P` (i.e. an element `y` in `xs`
such that `P(y)` is `true`). Apply the write-test-prove
approach to develop a correct implementation of `search_if`.

In particular, you need to

* write a specification for `search_if`,
* write the code for `search_if`,
* test `search_if` on diverse inputs, and
* prove that `search_if` is correct.

```
function search_if<T>(List<T>, fn T->bool) -> Nat {
    FILL IN HERE
}
```


<!--
``` {.deduce file=LinearSearch.pf} 
import Base
import Nat
import LinkedLists
import Set
<<search>>

<<search_test1>>
<<search_test2>>
<<search_test3>>
<<search_test4>>

<<search_length>>
<<search_present>>
<<search_first>>
<<set_of>>
<<search_absent>>
```
-->
