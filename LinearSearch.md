# Sequential Search

This is the second blog post in a
[series](https://siek.blogspot.com/2024/06/data-structures-and-algorithms-correctly.html)
about developing correct implementations of basic data structures and
algorithms using the [Deduce](https://github.com/jsiek/deduce)
language and proof checker.

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
specification of `search`, we need to return `0`, the length of the
`empty` list, because `y` is not in the `empty` list.

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

```{.deduce #search_length_case_empty}
    // <<search_length_case_empty>> =
    arbitrary y:Nat
	conclude search(empty,y) ≤ length(@empty<Nat>)
        by definition {search, length, operator ≤}
```

In these blog post we use a literate programming tool named Entangled to
translate the markdown files into Deduce proof files.  Entangled lets
us label chunks of proof and then paste them into larger proofs.  So
that you can see the label names, we include them in comments, as in
the `<<search_length_case_empty>>` label above.

In the case for `xs = node(x, xs')`, Deduce tells us that we need to prove

```
Goal:
	all y:Nat. search(node(x,xs'),y) ≤ length(node(x,xs'))
```

So we start with `arbitrary y:Nat` and note that the definitions of
`search` has an `if`-`then`-`else`, so we proceed with a 
`switch`-`for` statement.

```
    arbitrary y:Nat
	switch x = y for search {
	  case true {
        ?
	  }
	  case false {
        ?
	  }
    }
```

In the case for `x = y`, the goal becomes

```
0 ≤ length(node(x, xs'))
```

so we need to use the definition of `length` and then we
can complete the proof using the definition of `≤`.

```{.deduce #search_length_case_node_eq}
    // <<search_length_case_node_eq>> =
    suffices 0 ≤ 1 + length(xs')  with definition length
    definition operator ≤
```

In the case for `x ≠ y`, after applying the definitions of
`length`, `≤`, and `+`, it remains to prove that
`search(xs', y) ≤ length(xs')`. But that is just the induction
hypothesis


```{.deduce #search_length_case_node_not_eq}
    // <<search_length_case_node_not_eq>> =
    suffices search(xs', y) ≤ length(xs')
        with definition {length, operator ≤, operator+, operator+}
    IH[y]
```

Putting all of the pieces together, we have a complete proof of
`search_length`.

``` {.deduce #search_length}
theorem search_length: all xs:List<Nat>. all y:Nat.
  search(xs, y) ≤ length(xs)
proof
  induction List<Nat>
  case empty {
    <<search_length_case_empty>>
  }
  case node(x, xs') 
    suppose IH: all y:Nat. search(xs',y) ≤ length(xs') 
  {
    arbitrary y:Nat
	switch x = y for search {
	  case true {
        <<search_length_case_node_eq>>
	  }
	  case false {
        <<search_length_case_node_not_eq>>
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
    ?
  }
  case node(x, xs') suppose IH {
    ?
  }
end
```

In the case for `xs = empty`, we proceed in a goal-directed way using
`arbitrary` for the `all y` and then `suppose` for the `if`.

```
    arbitrary y:Nat
    suppose prem: search(empty,y) < length(@empty<Nat>)
    ?
```

Then we need to prove

```
nth(empty, 0)(search(empty, y)) = y
```

but that looks impossible! So hopefully the premise is also false,
which will let us finish this case using the principle of explosion.
Indeed, applying all of the relevant definitions to the premise yields
`false`.

```{.deduce #search_present_case_empty}
    arbitrary y:Nat
	suppose prem: search(empty,y) < length(@empty<Nat>)
	conclude false by definition {search, length, operator <, operator ≤} 
	                  in prem
```

Moving on to the case for `xs = node(x, xs')`, we again begin
with `arbitrary` and `suppose`.

```
    arbitrary y:Nat
	suppose sxxs_len: search(node(x,xs'),y) < length(node(x,xs'))
	?
```

Deduce tells us that we need to prove

```
Goal:
	nth(node(x,xs'),0)(search(node(x,xs'),y)) = y
```

We see `search` applied to a `node` argument and note that again that
the body of `search` contains an `if`-`then`-`else`, so we proceed
with a `switch`-`for` statement.

```
	switch x = y for search {
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

```{.deduce #search_present_case_node_eq}
    suffices x = y with definition nth
    rewrite xy_true
```

In the case where `x ≠ y`, we need to prove

```
Goal:
	nth(node(x,xs'),0)(suc(search(xs',y))) = y
```

Now if we apply the definitions of `nth` and `pred`, the goal becomes:

```{.deduce #search_present_case_node_nth_pred}
    // <<search_present_case_node_nth_pred>> =
    suffices nth(xs', 0)(search(xs', y)) = y
        with definition {nth, pred}
```

This looks a lot like the conclusion of our induction hypothesis:

```
Givens:
	...
	IH: all y:Nat. (if search(xs',y) < length(xs') 
	                then nth(xs',0)(search(xs',y)) = y)
```

So we just need to prove the premise of the `IH`, 
that `search(xs',y) < length(xs')`.
Thankfully, that can be proved from the premise 
`search(node(x,xs'),y) < length(node(x,xs'))`.

```{.deduce #search_present_IH_premise}
  // <<search_present_IH_premise>> =
    have sxs_len: search(xs',y) < length(xs')
      by enable {search, length, operator <, operator ≤, 
                 operator+, operator+}
         rewrite xy_false in sxxs_len
```

We conclude by applying the induction hypothesis.

```{.deduce #search_present_apply_IH}
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
    <<search_present_case_empty>>
  }
  case node(x, xs') suppose IH {
    arbitrary y:Nat
	suppose sxxs_len: search(node(x,xs'),y) < length(node(x,xs'))
	switch x = y for search {
      case true suppose xy_true {
        <<search_present_case_node_eq>>
	  }
	  case false suppose xy_false {
	    <<search_present_case_node_nth_pred>>
        <<search_present_IH_premise>>
        <<search_present_apply_IH>>
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

```{.deduce #search_first_case_empty}
    // <<search_first_case_empty>> =
    arbitrary y:Nat, i:Nat
	suppose prem: search(empty,y) < length(@empty<Nat>) and nth(@empty<Nat>, 0)(i) = y
	conclude false by definition {search, length, operator <, operator ≤} 
	                  in prem
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

We apply the definition of `search` and `switch` on `x = y`
with a `switch`-`for` statement.

```
  switch x = y for search {
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

```{.deduce #search_first_case_node_true}
    conclude 0 ≤ i   by definition operator ≤
```

In the case where `x ≠ y`, we need to prove

```
Goal:
	suc(search(xs',y)) ≤ i
```

What do we now about `i`? The premise `nth(node(x,xs'),0)(i) = y`
tells us that `i ≠ 0`, which means that `i` is the successor of
some other number `i′`.

```{.deduce #search_first_case_node_false_1}
    // <<search_first_case_node_false_1>> =
    have not_iz: not (i = 0)
      by suppose i_z 
         conclude false by rewrite i_z | xy_false in 
                           definition nth in prem
    obtain i' where i_si: i = suc(i') from apply not_zero_suc to not_iz
    suffices suc(search(xs', y)) ≤ suc(i')  with rewrite i_si
```

Now we can further simplify the goal with the definition of `≤`.

```{.deduce #search_first_case_node_false_2}
    // <<search_first_case_node_false_2>> =
    suffices search(xs', y) ≤ i'   with definition operator≤ 
```

The goal looks like the conclusion of the induction hypothesis
instantiated at `i'`.

```
Givens:
	...
	IH: all y:Nat, i:Nat. (if search(xs',y) < length(xs') and nth(xs',0)(i) = y 
                           then search(xs',y) ≤ i)
```

So we need to prove the two premises of the `IH`. They follow from the
given `prem`:

```
Givens:
	prem: search(node(x,xs'),y) < length(node(x,xs')) 
          and nth(node(x,xs'),0)(i) = y
```

In particular, the first premise of `IH` follows from the
first conjunct of `prem`.

```{.deduce #search_first_IH_prem_1}
    // <<search_first_IH_prem_1>> =
    have IH_prem_1: search(xs',y) < length(xs')
      by enable {search, length, operator <, operator ≤, 
                 operator+, operator+}
         rewrite xy_false in (conjunct 0 of prem)
```

The second premise of the `IH` follows from the second
conjunct of `prem`.

```{.deduce #search_first_IH_prem_2}
    // <<search_first_IH_prem_2>> =
    have IH_prem_2: nth(xs',0)(i') = y
      by enable {nth, pred} rewrite i_si in (conjunct 1 of prem)
```

We conclude the case for `i = suc(i')` by applying the induction
hypothesis.

```{.deduce #search_first_apply_IH}
    // <<search_first_apply_IH>> =
    apply IH[y,i'] to IH_prem_1, IH_prem_2
```

Here is the complete proof of `search_first`.

``` {.deduce #search_first}
theorem search_first: all xs:List<Nat>. all y:Nat, i:Nat.
  if search(xs, y) < length(xs) and nth(xs, 0)(i) = y
  then search(xs, y) ≤ i
proof
  induction List<Nat>
  case empty {
    <<search_first_case_empty>>
  }
  case node(x, xs') suppose IH {
    arbitrary y:Nat, i:Nat
	suppose prem: search(node(x,xs'),y) < length(node(x,xs')) 
	              and nth(node(x,xs'),0)(i) = y
	switch x = y for search {
	  case true {
	    <<search_first_case_node_true>>
	  }
	  case false suppose xy_false {
        <<search_first_case_node_false_1>>
        <<search_first_case_node_false_2>>
        <<search_first_IH_prem_1>>
        <<search_first_IH_prem_2>>
        <<search_first_apply_IH>>
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
	not y ∈ set_of(empty)
```

which we prove using the definition of `set_of` and
the `empty_no_members` theorem from `Set.pf`.

```{.deduce #search_absent_case_empty}
    // <<search_absent_case_empty>> =
    arbitrary y:Nat, d:Nat
    suppose _
    suffices not (y ∈ ∅) with definition set_of
    empty_no_members[Nat,y]
```

Turning to the case for `xs = node(x, xs')`, we take several
goal-directed steps.

```
  case node(x, xs') suppose IH {
    arbitrary y:Nat, d:Nat
    suppose s_xxs_len_xxs: search(node(x,xs'),y) = length(node(x,xs'))
	suffices not (y ∈ single(x) ∪ set_of(xs'))  with definition set_of
    ?
  }
```

Now we need to prove a `not` formula:

```
Goal:
	not (y ∈ single(x) ∪ set_of(xs'))
```

So we assume `y ∈ single(x) ∪ set_of(xs')` and then prove `false`
(a contradiction).

```
  suppose y_in_x_union_xs: y ∈ single(x) ∪ set_of(xs')
```

The main information we have to work with is the premise
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
`length(node(x,xs'))` is `1 + length(xs')`, so we have a contradiction.

```{.deduce #search_absent_case_node_equal}
    // <<search_absent_case_node_equal>> =
    have xy: x = y by rewrite xy_true
    have s_yxs_len_yxs: search(node(y,xs'),y) = length(node(y,xs'))
        by rewrite xy in s_xxs_len_xxs
    have zero_1_plus: 0 = 1 + length(xs')
        by definition {search, length} in s_yxs_len_yxs
    conclude false  by definition {operator+} in zero_1_plus
```

In the case where `x ≠ y`, we can show that `y ∈ set_of(xs')` and then
invoke the induction hypothesis to obtain the contradition.  In
particular, the premise `y_in_x_union_xs` gives us 
`y ∈ single(x) or y ∈ set_of(xs')`.
But `x ≠ y` implies `not (y ∈ single(x))`.
So it must be that `y ∈ set_of(xs')` (using `or_not` from `Base.pf`).

```{.deduce #search_absent_case_node_notequal_y_in_xs}
  // <<search_absent_case_node_notequal_y_in_xs>> =
  have ysx_or_y_xs: y ∈ single(x) or y ∈ set_of(xs')
	  by apply member_union[Nat] to y_in_x_union_xs
  have not_ysx: not (y ∈ single(x))
	by suppose ysx
	   rewrite xy_false in
	   apply single_equal[Nat] to ysx
  have y_xs: y ∈ set_of(xs')
	by apply or_not[y ∈ single(x), y ∈ set_of(xs')] 
	   to ysx_or_y_xs, not_ysx
```

To satisfy the premise of the induction hypothesis, we prove the
following.

```{.deduce #search_absent_IH_prem}
    // <<search_absent_IH_prem>> =
    have sxs_lxs: search(xs',y) = length(xs')
      by injective suc
         rewrite xy_false in
         definition {search,length,operator+,operator+} in
         s_xxs_len_xxs
```

So we apply the induction hypothesis to 
get `y ∉ set_of(xs')`, which contradicts `y ∈ set_of(xs)`.

```{.deduce #search_absent_apply_IH}
  // <<search_absent_apply_IH>> =
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
    <<search_absent_case_empty>>
  }
  case node(x, xs') suppose IH {
    arbitrary y:Nat, d:Nat
    suppose s_xxs_len_xxs: search(node(x,xs'),y) = length(node(x,xs'))
	suffices not (y ∈ single(x) ∪ set_of(xs'))  with definition set_of
	suppose y_in_x_union_xs: y ∈ single(x) ∪ set_of(xs')
    switch x = y {
      case true suppose xy_true {
        <<search_absent_case_node_equal>>
      }
      case false suppose xy_false {
        <<search_absent_case_node_notequal_y_in_xs>>
        <<search_absent_IH_prem>>
        <<search_absent_apply_IH>>
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
import LinkedLists
import Set
import Nat
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
