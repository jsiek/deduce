# Merge Sort with Leftovers

This is the fourth blog post in a
[series](https://siek.blogspot.com/2024/06/data-structures-and-algorithms-correctly.html)
about developing correct implementations of basic data structures and
algorithms using the [Deduce](https://github.com/jsiek/deduce)
language and proof checker.

In this blog post we study a fast sorting algorithm, Merge Sort.  This
classic algorithm splits the input list in half, recursively sorts
each half, and then merges the two results back into a single sorted
list.

The specification of Merge Sort is the same as Insertion Sort.

**Specification:** The `merge_sort(xs)` function returns a list
that contains the same elements as `xs` but the elements in the result
are in sorted order.

We follow the write-test-prove approach to develop a correct
implementation of `merge_sort`. 


# Write the `merge_sort` function

The classic implementation of `merge_sort` would be something like the
following.

```
function merge_sort(List<Nat>) -> List<Nat> {
  merge_sort(empty) = empty
  merge_sort(node(x,xs')) =
    define p = split(node(x,xs'))
    merge(merge_sort(first(p)), merge_sort(second(p)))
}
```

Unfortunately, Deduce rejects the above function definition because
Deduce uses a very simple restriction to ensure the termination of
recursive function, which is that a recursive call may only be made on
a part of the input. In this case, the recursive call may only be
applied to the sublist `xs'`, not `first(p)` or `second(p)`.

How can we work around this restriction?  There's an old trick that
goes by many names (gas, fuel, etc.), which is to add another
parameter of type `Nat` and use that for termination. Let us use the
name `msort` for the following, and then we define `merge_sort` in
terms of `msort`.

```
function msort(Nat, List<Nat>) -> List<Nat> {
  msort(0, xs) = xs
  msort(suc(n'), xs) =
    define p = split(xs)
    merge(msort(n', first(p)), msort(n', second(p)))
}

define merge_sort : fn List<Nat> -> List<Nat>
  = λxs{ msort(log(length(xs)), xs) }
```

In the above definition of `merge_sort`, we need to suppply enough gas
so that `msort` won't prematurely run out.  Here we use the logarithm
(base 2, rounding up) defined in `Log.pf`.

This definition of `merge_sort` and `msort` is fine, it has `O(n
log(n))` time complexity, so it is efficient.  However, the use of
`split` rubs me the wrong way because it requires traversing half of
the input list. The use of `split` is necessary if one wanted to use
parallelism to speed up the code, performing the two recursive calls
in parallel. However, we are currently only interested in a
single-threaded implementation.

Suppose you just finished baking a pie and intend to eat half now and
half tomorrow night. One approach would be to split it in half and
then eat one of the halves. Another approach is to just start eating
the pie and stop when half of it is gone. That's the approach that we
will take with the next version of `msort`.

**Specification** The `msort(n,xs)` function sorts the first
`min(2ⁿ,length(xs))` many elements of `xs` and returns a pair
containing (1) the sorted list and (2) the leftovers that were not yet
sorted.

``` {.deduce #msort}
function msort(Nat, List<Nat>) -> Pair< List<Nat>, List<Nat> > {
  msort(0, xs) =
    switch xs {
      case empty { pair(empty, empty) }
      case node(x, xs') { pair(node(x, empty), xs') }
    }
  msort(suc(n'), xs) =
    define p1 = msort(n', xs)
    define p2 = msort(n', second(p1))
    define ys = first(p1)
    define zs = first(p2)
    pair(merge(length(ys) + length(zs), ys, zs), second(p2))
}
```

In the above case for `suc(n')`, the first recursive call to `msort`
produces the pair `p1` that includes a sorted list and the leftovers.
We sort the leftovers with the second recursive call to `msort`.  We
return (1) the merge of the two sorted sublists and (2) the leftovers
from the second recursive call to `msort`.

With the code for `msort` complete, we can turn to `merge_sort`.
Similar to the previous version, we involke `msort` with the input
list `xs` and use the logarithm of list length for the gas.  This
`msort` returns a pair, with the sorted results in the first
component. The second component of the pair is an empty list because
we supplied enough gas.

``` {.deduce #merge_sort}
define merge_sort : fn List<Nat> -> List<Nat>
    = λxs{ first(msort(log(length(xs)), xs)) }
```

So far, we have neglected the implementation of `merge`.
Here's its specification.

**Specification:** The `merge(xs,ys)` function takes two sorted lists
and returns a sorted list that contains just the elements from the two
input lists.

Here's the classic implementation of `merge`. The idea is to compare
the two elements at the front of each list and use the lower of the
two as the first element of the output.  Then do the recursive call
with the two lists, minus the element that was chosen. Again, we use
an extra gas parameter to ensure termination. To ensure that we have
enough gas, we will choose the sum of the lengths of the two input
lists.

``` {.deduce #merge}
function merge(Nat, List<Nat>, List<Nat>) -> List<Nat> {
  merge(0, xs, ys) = empty
  merge(suc(n), xs, ys) =
    switch xs {
      case empty { ys }
      case node(x, xs') {
        switch ys {
          case empty {
            node(x, xs')
          }
          case node(y, ys') {
            if x ≤ y then
              node(x, merge(n, xs', node(y, ys')))
            else
              node(y, merge(n, node(x, xs'), ys'))
          }
        }
     }
   }
}
```


# Test

We have three functions to test, `merge`, `msort` and `merge_sort`.

## Test `merge`

We test that the result of `merge` is sorted and that it contains all
the elements from the two input lists, which we check using `count`.

``` {.deduce #test_merge}
define L_1337 = node(1, node(3, node(3, node(7, empty))))
define L_2348 = node(2, node(3, node(4, node(8, empty))))
define L_12333478 = merge(length(L_1337) + length(L_2348), L_1337, L_2348)
assert sorted(L_12333478)
assert all_elements(L_1337 ++ L_2348,
  λx{count(L_1337)(x) + count(L_2348)(x) = count(L_12333478)(x) })
```

## Test `msort`

In the following tests, we vary the gas from `0` to `3`, varying how
much of the input list `L18` gets sorted in the call to `msort`.  The
`take(n,xs)` function returns the first `n` elements of `xs` and
`drop(n,xs)` drops the first `n` elements of `xs` and returns the
remaining portion of `xs`.

``` {.deduce #test_msort}
define L18 = L_1337 ++ L_2348

define p0 = msort(0, L18)
define t0 = take(pow2(0), L18)
define d0 = drop(pow2(0), L18)
assert sorted(first(p0))
assert all_elements(t0, λx{count(t0)(x) = count(first(p0))(x) })
assert all_elements(d0, λx{count(d0)(x) = count(second(p0))(x) })

define p1 = msort(1, L18)
define t1 = take(pow2(1), L18)
define d1 = drop(pow2(1), L18)
assert sorted(first(p1))
assert all_elements(t1, λx{count(t1)(x) = count(first(p1))(x) })
assert all_elements(d1, λx{count(d1)(x) = count(second(p1))(x) })

define p2 = msort(2, L18)
define t2 = take(pow2(2), L18)
define d2 = drop(pow2(2), L18)
assert sorted(first(p2))
assert all_elements(t2, λx{count(t2)(x) = count(first(p2))(x) })
assert all_elements(d2, λx{count(d2)(x) = count(second(p2))(x) })

define p3 = msort(3, L18)
define t3 = take(pow2(3), L18)
define d3 = drop(pow2(3), L18)
assert sorted(first(p3))
assert all_elements(t3, λx{count(t3)(x) = count(first(p3))(x) })
assert all_elements(d3, λx{count(d3)(x) = count(second(p3))(x) })
```

## Test `merge_sort`

Next we test that `merge_sort` returns a sorted list that contains the
same elements as the input list. For input, we reuse the list `L18`
from above.

``` {.deduce #test_merge_sort}
define s_L18 = merge_sort(L18)
assert sorted(s_L18)
assert all_elements(t0, λx{count(L18)(x) = count(s_L18)(x) })
```

We can bundle several tests, with varying-length inputs, into one
`assert` by using `all_elements` and `interval`. 

``` {.deduce #test_merge_sort_many}
assert all_elements(interval(3, 0),
    λn{ define xs = reverse(interval(n, 0))
        define ls = merge_sort(xs)
        sorted(ls) and
        all_elements(xs, λx{count(xs)(x) = count(ls)(x)})
    })
```

# Prove

Compared to the proof of correctness for `insertion_sort`, we have
considerably more work to do for `merge_sort`. Instead of two
functions, we have three functions to consider: `merge`, `msort`, and
`merge_sort`. Furthermore, these functions are more complex than
`insert` and `insertion_sort`. Nevertheless, we are up to the
challenge!

## Prove correctness of `merge`

The specificaiton of `merge` has two parts, one part saying that the
elements of the output must be the elements of the two input lists,
and the another part saying that the output must be sorted, provided
the two input lists are sorted.

Here is how we state the theorem for the first part.
```
theorem mset_of_merge: all n:Nat. all xs:List<Nat>, ys:List<Nat>.
  if length(xs) + length(ys) = n
  then mset_of(merge(n, xs, ys)) = mset_of(xs) ⨄ mset_of(ys)
```

Here is the theorem stating that the output of `merge` is sort.

```
theorem merge_sorted: all n:Nat. all xs:List<Nat>, ys:List<Nat>.
  if sorted(xs) and sorted(ys) and
     length(xs) + length(ys) = n
  then sorted(merge(n, xs, ys))
```

### Prove the `mset_of_merge` theorem

We begin with the proof of `mset_of_merge`.  Because `merge(n, xs,
ys)` is recursive on the natural number `n`, we proceed by induction
on `Nat`.

```
  induction Nat
  case 0 {
    arbitrary xs:List<Nat>, ys:List<Nat>
    suppose prem: length(xs) + length(ys) = 0
    ?
  }
  case suc(n') suppose IH {
    ?
  }
```

In the case for `n = 0`, we need to prove

```
  mset_of(merge(0,xs,ys)) = mset_of(xs) ⨄ mset_of(ys)
```

and `merge(0,xs,ys)` returns `empty`, so we need to show
that `mset_of(xs) ⨄ mset_of(ys)` is the empty multiset.
From the premise `prem`, both `xs` and `ys` must be `empty`.

```{.deduce #mset_of_merge_case_zero_xs_ys_empty}
  // <<mset_of_merge_case_zero_xs_ys_empty>> =
  have lxs_lys_z: length(xs) = 0 and length(ys) = 0
    by apply add_to_zero[length(xs)][length(ys)] to prem
  have xs_mt: xs = empty
    by apply length_zero_empty[Nat,xs] to lxs_lys_z
  have ys_mt: ys = empty
    by apply length_zero_empty[Nat,ys] to lxs_lys_z
```

After rewriting with those equalities and applying the definition of
`merge` and `mset_of`:

```{.deduce #mset_of_merge_case_zero_suffices}
  suffices mset_of(merge(0, empty, empty)) = mset_of(empty) ⨄ mset_of(empty)
      with rewrite xs_mt | ys_mt
  suffices m_fun[Nat](λ{0}) = m_fun[Nat](λ{0}) ⨄ m_fun[Nat](λ{0})
      with definition {merge, mset_of}
```

it remains to prove `m_fun(λ{0}) = m_fun(λ{0}) ⨄ m_fun(λ{0})` (the sum
of two empty multisets is the empty multiset), which we prove with the
theorem `m_sum_empty` from `MultiSet.pf`.

```{.deduce #mset_of_merge_case_zero_conclusion}
  // <<mset_of_merge_case_zero_conclusion>> =
  symmetric m_sum_empty[Nat, m_fun[Nat](λx{0})]
```

In the case for `n = suc(n')`, we need to prove

```
  mset_of(merge(suc(n'),xs,ys)) = mset_of(xs) ⨄ mset_of(ys)
```

Looking a the `suc` clause of `merge`, there is a `switch` on `xs` and
then on `ys`. So our proof will be structured analogously.

```
  switch xs for merge {
    case empty {
      ?
    }
    case node(x, xs') suppose xs_xxs {
      ?
    }
  }
```

In the case for `xs = empty`, we conclude by the definition of
`mset_of` and the fact that combining `mset_of(ys)` with the empty
multiset produces `mset_of(ys)`.

```{.deduce #mset_of_merge_case_suc_empty}
    // <<mset_of_merge_case_suc_empty>> =
    suffices mset_of(ys) = m_fun(λx{0}) ⨄ mset_of(ys)
        with definition {mset_of}
    symmetric empty_m_sum[Nat, mset_of(ys)]
```

In the case for `xs = node(x, xs')`, `merge` performs a switch on
`ys`, so our proof does too.

```
  switch ys for merge {
    case empty {
      ?
    }
    case node(y, ys') suppose ys_yys {
      ?
    }
```

The case for `ys = empty`, is similar to the case for `xs = empty`.
We conclude by use of the definitions of `merge` and `mset_of` and the
fact that combining `mset_of(ys)` with the empty multiset produces
`mset_of(ys)`.

```{.deduce #mset_of_merge_case_suc_node_empty}
    // <<mset_of_merge_case_suc_node_empty>> =
    suffices m_one(x) ⨄ mset_of(xs')
           = (m_one(x) ⨄ mset_of(xs')) ⨄ m_fun(λ{0})
        with definition {mset_of}
    rewrite m_sum_empty[Nat, m_one(x) ⨄ mset_of(xs')]
```

In the case for `ys = node(y, ys')`, we continue to follow the
structure of `merge` and switch on `x ≤ y`.

```
  switch x ≤ y {
    case true suppose xy_true {
      ?
    }
    case false suppose xy_false {
      ?
    }
  }
```

In the case for `(x ≤ y) = true`, the goal becomes
```
  mset_of(node(x, merge(n', xs', node(y, ys')))) 
= mset_of(node(x, xs')) ⨄ mset_of(node(y, ys'))
```

Which follows from the conclusion of the induction hypothesis
(instantiated with `xs'` and `node(y,ys')`):

```
  mset_of(merge(n',xs',node(y,ys')))
= mset_of(xs') ⨄ mset_of(node(y, ys'))
```

The induction hypothesis is a conditional, so we first must prove its
premise as follows.

```{.deduce #mset_of_merge_x_le_y_IH_prem}
    // <<mset_of_merge_x_le_y_IH_prem>> =
    have IH_prem: length(xs') + length(node(y,ys')) = n'
      by enable {operator +, operator +,length}
         have suc_len: suc(length(xs')) + suc(length(ys')) = suc(n')
                by rewrite xs_xxs | ys_yys in prem
         injective suc suc_len
```

We conclude this case with the following equational reasoning, using
the induction hypothesis in the second step.

```{.deduce #mset_of_merge_x_le_y_equations}
    // <<mset_of_merge_x_le_y_equations>> =
    equations
          mset_of(node(x, merge(n', xs', node(y, ys')))) 
        = m_one(x) ⨄ mset_of(merge(n',xs',node(y,ys')))
            by definition mset_of
    ... = m_one(x) ⨄ (mset_of(xs') ⨄ mset_of(node(y, ys')))
            by rewrite (apply IH[xs', node(y, ys')] to IH_prem)
    ... = m_one(x) ⨄ (mset_of(xs') ⨄ (m_one(y) ⨄ mset_of(ys')))
            by definition mset_of
    ... = (m_one(x) ⨄ mset_of(xs')) ⨄ (m_one(y) ⨄ mset_of(ys'))
            by rewrite m_sum_assoc[Nat, m_one(x), mset_of(xs'),
                                  (m_one(y) ⨄ mset_of(ys'))]
    ... = mset_of(node(x, xs')) ⨄ mset_of(node(y, ys'))
            by definition mset_of
```

In the case for `(x ≤ y) = false`, the goal becomes
```
  mset_of(node(y, merge(n', node(x, xs'), ys'))) 
= mset_of(node(x, xs')) ⨄ mset_of(node(y, ys'))
```

The conclusion of the induction hypothesis
(instantiated with `node(x,xs')` and `ys'`) is

```
  mset_of(merge(n',node(x,xs'),ys'))
= mset_of(node(x,xs')) ⨄ mset_of(ys')
```

so the goal will follow from the fact that multiset sum is associative
and commutative.

We first prove the premise of the induction hypothesis.

```{.deduce #mset_of_merge_x_g_y_IH_prem}
    have IH_prem: length(node(x,xs')) + length(ys') = n'
      by enable {operator +, operator +, length}
         have suc_len: suc(length(xs')) + suc(length(ys')) = suc(n')
              by rewrite xs_xxs | ys_yys in prem
         injective suc
         rewrite add_suc[length(xs')][length(ys')] in suc_len
```

Then we proceed with applying the induction hypothesis in the second
step, followed by the equational reasoning about multiset sum.

```{.deduce #mset_of_merge_x_g_y_equations}
    equations
            mset_of(node(y, merge(n', node(x, xs'), ys')))
          = m_one(y) ⨄ mset_of(merge(n',node(x,xs'),ys'))
              by definition mset_of
      ... = m_one(y) ⨄ mset_of(node(x,xs')) ⨄ mset_of(ys')
              by rewrite (apply IH[node(x,xs'), ys'] to IH_prem)
      ... = m_one(y) ⨄ ((m_one(x) ⨄ mset_of(xs')) ⨄ mset_of(ys'))
              by definition mset_of
      ... = ((m_one(x) ⨄ mset_of(xs')) ⨄ mset_of(ys')) ⨄ m_one(y)
              by m_sum_commutes[Nat, m_one(y), (m_one(x) ⨄ mset_of(xs')) ⨄ mset_of(ys')]
      ... = (m_one(x) ⨄ mset_of(xs')) ⨄ (mset_of(ys') ⨄ m_one(y))
              by m_sum_assoc[Nat, m_one(x) ⨄ mset_of(xs'), mset_of(ys'), m_one(y)]
      ... = (m_one(x) ⨄ mset_of(xs')) ⨄ (m_one(y) ⨄ mset_of(ys'))
              by rewrite m_sum_commutes[Nat, mset_of(ys'), m_one(y)]
      ... = mset_of(node(x, xs')) ⨄ mset_of(node(y, ys'))
              by definition mset_of
```

Here is the completed proof of `mset_of_merge`.

``` {.deduce #mset_of_merge}
theorem mset_of_merge: all n:Nat. all xs:List<Nat>, ys:List<Nat>.
  if length(xs) + length(ys) = n
  then mset_of(merge(n, xs, ys)) = mset_of(xs) ⨄ mset_of(ys)
proof
  induction Nat
  case 0 {
    arbitrary xs:List<Nat>, ys:List<Nat>
    suppose prem: length(xs) + length(ys) = 0
    <<mset_of_merge_case_zero_xs_ys_empty>>
    <<mset_of_merge_case_zero_suffices>>
    <<mset_of_merge_case_zero_conclusion>>
  }
  case suc(n') suppose IH {
    arbitrary xs:List<Nat>, ys:List<Nat>
    suppose prem: length(xs) + length(ys) = suc(n')
    switch xs for merge {
      case empty {
        <<mset_of_merge_case_suc_empty>>
      }
      case node(x, xs') suppose xs_xxs {
        switch ys for merge {
          case empty {
            <<mset_of_merge_case_suc_node_empty>>
          }
          case node(y, ys') suppose ys_yys {
            switch x ≤ y {
              case true suppose xy_true {
                <<mset_of_merge_x_le_y_IH_prem>>
                <<mset_of_merge_x_le_y_equations>>
              }
              case false suppose xy_false {
                <<mset_of_merge_x_g_y_IH_prem>>
                <<mset_of_merge_x_g_y_equations>>
              }
            }
          }
        }
      }
    }
  }
end
```

The `mset_of_merge` theorem also holds for sets, using the `set_of`
function. We prove the following `set_of_merge` theorem as a corollary
of `mset_of_merge`.

``` {.deduce #set_of_merge}
theorem set_of_merge: all xs:List<Nat>, ys:List<Nat>.
  set_of(merge(length(xs) + length(ys), xs, ys)) = set_of(xs) ∪ set_of(ys)
proof
  arbitrary xs:List<Nat>, ys:List<Nat>
  equations
    set_of(merge(length(xs) + length(ys), xs, ys))
        = set_of_mset(mset_of(merge(length(xs) + length(ys), xs, ys)))
            by symmetric som_mset_eq_set[Nat]
                             [merge(length(xs) + length(ys), xs, ys)]
    ... = set_of_mset(mset_of(xs) ⨄ mset_of(ys))
            by rewrite mset_of_merge[length(xs) + length(ys)][xs, ys]
    ... = set_of_mset(mset_of(xs)) ∪ set_of_mset(mset_of(ys))
            by som_union[Nat, mset_of(xs), mset_of(ys)]
    ... = set_of(xs) ∪ set_of(ys)
            by rewrite som_mset_eq_set[Nat][xs] | som_mset_eq_set[Nat][ys]
end
```


### Prove the `merge_sorted` theorem

Next up is the `merge_sorted` theorem.

```
theorem merge_sorted: all n:Nat. all xs:List<Nat>, ys:List<Nat>.
  if sorted(xs) and sorted(ys) and length(xs) + length(ys) = n
  then sorted(merge(n, xs, ys))
```

The structure of the proof will be similar to the one for
`mset_of_merge`, because they both follow the structure of `merge`. So
begin with induction on `Nat`.

In the case for `n = 0`, we need to prove `sorted(merge(0, xs, ys))`.
But `merge(0, xs, ys) = empty`, and `sorted(empty)` is trivially true.
So we conclude the case for `n = 0` as follows.

```{.deduce #merge_sorted_case_zero}
    // <<merge_sorted_case_zero>> =
    arbitrary xs:List<Nat>, ys:List<Nat>
    suppose _
    suffices sorted(empty)  with definition merge
    definition sorted
```

We move on to the case for `n = suc(n')` and `xs = empty`. Here
`merge` returns `ys`, and we already know that `ys` is sorted from the
premise.

```{.deduce #merge_sorted_case_suc_empty}
    // <<merge_sorted_case_suc_empty>> =
    conclude sorted(ys) by prem
```

In the case for `xs = node(x, xs')` and `ys = empty`, the `merge`
function returns `node(x, xs')` (aka. `xs`), and we already know that
`xs` is sorted from the premise.

```{.deduce #merge_sorted_case_suc_node_empty}
    // <<merge_sorted_case_suc_node_empty>> =
    conclude sorted(node(x,xs'))  by rewrite xs_xxs in prem
```

In the case for `ys = node(y, ys')` and `(x ≤ y) = true`, the `merge`
function returns `node(x, merge(n',xs',node(y,ys')))`. So we need to
prove the following.

```{.deduce #merge_sorted_less_equal_suffices}
    suffices sorted(merge(n',xs',node(y,ys'))) and
             all_elements(merge(n',xs',node(y,ys')), λb{x ≤ b}) 
                 with definition sorted
```

To prove the first, we invoke the induction hypothesis intantiated to
`xs'` and `node(y,ys')` as follows.

```{.deduce #merge_sorted_IH_xs_yys}
    // <<merge_sorted_IH_xs_yys>> =
    have s_xs: sorted(xs')
      by definition sorted in rewrite xs_xxs in prem
    have s_yys: sorted(node(y,ys'))
      by rewrite ys_yys in prem
    have len_xs_yys: length(xs') + length(node(y,ys')) = n'
      by enable {operator +, operator +, length}
         have sxs: suc(length(xs')) + suc(length(ys')) = suc(n')
            by rewrite xs_xxs | ys_yys in prem
         injective suc sxs
    have IH_xs_yys: sorted(merge(n',xs',node(y,ys')))
      by apply IH[xs',node(y,ys')] to s_xs, s_yys, len_xs_yys
```

It remains to prove that `x` is less-or-equal to to all the elements
in the rest of the output list:

```
  all_elements(merge(n',xs',node(y,ys')),λb{x ≤ b})
```

The theorem `all_elements_eq_member` in `List.pf` says

```
  all_elements(xs,P) = (all x:T. if x ∈ set_of(xs) then P(x))
```

which combined with the `set_of_merge` corollary above,
simplifies our goal as follows

```{.deduce #x_le_merge_suffices}
    // <<x_le_merge_suffices>> =
    suffices (all z:Nat. (if z ∈ set_of(xs') ∪ set_of(node(y, ys')) then x ≤ z))
        with rewrite all_elements_eq_member[Nat, merge(n', xs', node(y,ys')),
                                            λb{x ≤ b}]
                   | symmetric len_xs_yys | set_of_merge[xs',node(y,ys')]
    arbitrary z:Nat
    suppose z_in_xs_yys: z ∈ set_of(xs') ∪ set_of(node(y,ys'))
```

So we have a few cases to consider and need to prove `x ≤ z` in each one.
Consider the case where `z ∈ set_of(xs')`.
Because `node(x, xs')` is sorted, we know `x` is less-or-equal every element
of `xs'`:

```{.deduce #merge_sorted_x_le_xs}
  // <<x_le_xs>> =
  have x_le_xs: all_elements(xs', λb{x ≤ b})
    by definition sorted in rewrite xs_xxs in prem
```

so `x` is less-or-equal to `z`, being one of the elements in `xs'`.

```{.deduce #merge_sorted_z_in_xs}
  conclude x ≤ z by
    apply all_elements_member[Nat][xs'][z, λb{x ≤ b}]
    to x_le_xs, z_in_xs
```

Next, consider the case where `z ∈ single(y)` and therefore
`y = z`. Then we can immediately conclude because `x ≤ y`.

```{.deduce #merge_sorted_z_in_y}
    have y_z: y = z   by definition {operator ∈, single, rep} in z_sy
    conclude x ≤ z    by rewrite symmetric y_z | xy_true
```

Finally, consider when `z ∈ set_of(ys')`. Because `node(y,ys')` is
sorted, we know that `y` is less-or-equal all elements of `ys'`.

```{.deduce #merge_sorted_y_le_ys}
    have y_le_ys: all_elements(ys', λb{y ≤ b})
      by definition sorted in rewrite ys_yys in prem
```

Therefore we have `y ≤ z`. Combined with `x ≤ y`, 
we conclude that `x ≤ z` by transitivity.

```{.deduce #merge_sorted_z_in_ys}
    // <<merge_sorted_z_in_ys>> =
    have y_z: y ≤ z
      by apply all_elements_member[Nat][ys'][z,λb{y ≤ b}]
         to y_le_ys, z_in_ys
    have x_y: x ≤ y by rewrite xy_true
    conclude x ≤ z
        by apply less_equal_trans[x][y,z] to x_y, y_z
```

The last case to consider is for `ys = node(y, ys')` and `(x ≤ y) =
false`. The reasoning is similar to the case for `(x ≤ y) = true`,
so we skip the detailed explanation and refer the reader to the
below proof.

Here's the completed proof of `merge_sorted`.

``` {.deduce #merge_sorted}
theorem merge_sorted: all n:Nat. all xs:List<Nat>, ys:List<Nat>.
  if sorted(xs) and sorted(ys) and length(xs) + length(ys) = n
  then sorted(merge(n, xs, ys))
proof
  induction Nat
  case 0 {
    <<merge_sorted_case_zero>>
  }
  case suc(n') suppose IH {
    arbitrary xs:List<Nat>, ys:List<Nat>
    suppose prem
    switch xs for merge {
      case empty {
        <<merge_sorted_case_suc_empty>>
      }
      case node(x, xs') suppose xs_xxs {
        switch ys for merge {
          case empty {
            <<merge_sorted_case_suc_node_empty>>
          }
          case node(y, ys') suppose ys_yys {
            <<merge_sorted_IH_xs_yys>>
            <<merge_sorted_x_le_xs>>
            <<merge_sorted_y_le_ys>>
            switch x ≤ y {
              case true suppose xy_true {
                <<merge_sorted_less_equal_suffices>>
                have x_le_merge: all_elements(merge(n',xs',node(y,ys')),λb{x ≤ b}) by
                    <<x_le_merge_suffices>>
                    suffices x ≤ z  by .
                    cases apply member_union[Nat] to z_in_xs_yys
                    case z_in_xs: z ∈ set_of(xs') {
                      <<merge_sorted_z_in_xs>>
                    }
                    case z_in_ys: z ∈ set_of(node(y,ys')) {
                      cases apply member_union[Nat] to definition set_of in z_in_ys
                      case z_sy: z ∈ single(y) {
                        <<merge_sorted_z_in_y>>
                      }
                      case z_in_ys: z ∈ set_of(ys') {
                        <<merge_sorted_z_in_ys>>
                      }
                    }
                IH_xs_yys, x_le_merge
              }
              case false suppose xy_false {
              
                /* Apply the induction hypothesis
                 * to prove sorted(merge(n',node(x,xs'),ys'))
                 */
                have len_xxs_ys: length(node(x,xs')) + length(ys') = n'
                  by enable {operator +, operator +, length}
                     have suc_len: suc(length(xs') + suc(length(ys'))) = suc(n')
                       by rewrite xs_xxs | ys_yys in prem
                     injective suc
                     rewrite add_suc[length(xs')][length(ys')] in suc_len
                have s_xxs: sorted(node(x, xs'))
                  by enable sorted rewrite xs_xxs in prem
                have s_ys: sorted(ys')
                  by definition sorted in rewrite ys_yys in prem
                have IH_xxs_ys: sorted(merge(n',node(x,xs'),ys'))
                  by apply IH[node(x,xs'),ys'] to s_xxs, s_ys, len_xxs_ys

                have not_x_y: not (x ≤ y)
                  by suppose xs rewrite xy_false in xs
                have y_x: y ≤ x
                  by apply less_implies_less_equal[y][x] to
                     (apply not_less_equal_greater[x,y] to not_x_y)
                suffices sorted(merge(n',node(x,xs'),ys')) and
                         all_elements(merge(n',node(x,xs'),ys'),λb{y ≤ b}) 
                    with definition sorted
                have y_le_merge: all_elements(merge(n',node(x,xs'),ys'),λb{y ≤ b}) by
                    suffices (all z:Nat. (if z ∈ set_of(node(x, xs')) ∪ set_of(ys') then y ≤ z))
                        with rewrite all_elements_eq_member[Nat,merge(n',node(x,xs'),ys'),λb{y ≤ b}]
                                   | symmetric len_xxs_ys | set_of_merge[node(x,xs'),ys']
                    arbitrary z:Nat
                    suppose z_in_xxs_ys: z ∈ set_of(node(x,xs')) ∪ set_of(ys')
                    suffices y ≤ z  by.
                    cases apply member_union[Nat] to z_in_xxs_ys
                    case z_in_xxs: z ∈ set_of(node(x,xs')) {
                      have z_in_sx_or_xs: z ∈ single(x) or z ∈ set_of(xs')
                        by apply member_union[Nat] to definition set_of in z_in_xxs
                      cases z_in_sx_or_xs
                      case z_in_sx: z ∈ single(x) {
                        have x_z: x = z  by definition {operator ∈, single, rep} in z_in_sx
                        conclude y ≤ z  by rewrite x_z in y_x
                      }
                      case z_in_xs: z ∈ set_of(xs') {
                        have x_z: x ≤ z
                          by apply all_elements_member[Nat][xs'][z,λb{x ≤ b}]
                             to x_le_xs, z_in_xs
                        conclude y ≤ z 
                           by apply less_equal_trans[y][x,z] to y_x, x_z
                      }
                    }
                    case z_in_ys: z ∈ set_of(ys') {
                      conclude y ≤ z by
                        apply all_elements_member[Nat][ys'][z,λb{y ≤ b}]
                        to y_le_ys, z_in_ys
                    }
                IH_xxs_ys, y_le_merge
              }
            }
          }
        }
      }
    }
  }
end
```

## Prove correctness of `msort`

First we show that the two lists produced by `msort` contain the same
elements as the input list.

``` {.deduce #mset_of_msort}
theorem mset_of_msort: all n:Nat. all xs:List<Nat>.
  mset_of(first(msort(n, xs)))  ⨄  mset_of(second(msort(n, xs))) = mset_of(xs)
proof
  induction Nat
  case 0 {
    arbitrary xs:List<Nat>
    switch xs for msort {
      case empty {
        suffices m_fun[Nat](λ{0}) ⨄ m_fun[Nat](λ{0}) = m_fun[Nat](λ{0})
            with definition {first, second, mset_of}
        rewrite m_sum_empty[Nat,m_fun(λx{0})]
      }
      case node(x, xs') {
        suffices (m_one(x) ⨄ m_fun[Nat](λ{0})) ⨄ mset_of(xs')
               = m_one(x) ⨄ mset_of(xs')
            with definition {first, second, mset_of, mset_of}
        rewrite m_sum_empty[Nat,m_one(x)]
      }
    }
  }
  case suc(n') suppose IH {
    arbitrary xs:List<Nat>
    suffices mset_of(merge(length(first(msort(n', xs))) 
                           + length(first(msort(n', second(msort(n', xs))))),
                           first(msort(n', xs)),
                           first(msort(n', second(msort(n', xs)))))) 
             ⨄ mset_of(second(msort(n', second(msort(n', xs))))) 
             = mset_of(xs)
        with definition {msort, first, second}
    define ys = first(msort(n',xs))
    define ls = second(msort(n',xs))
    define zs = first(msort(n', ls))
    define ms = second(msort(n', ls))
    equations
          mset_of(merge(length(ys) + length(zs),ys,zs)) ⨄ mset_of(ms)
        = (mset_of(ys) ⨄ mset_of(zs)) ⨄ mset_of(ms)
          by rewrite (mset_of_merge[length(ys) + length(zs)][ys,zs])
    ... = mset_of(ys) ⨄ (mset_of(zs) ⨄ mset_of(ms))
          by rewrite m_sum_assoc[Nat, mset_of(ys), mset_of(zs), mset_of(ms)]
    ... = mset_of(ys) ⨄ mset_of(ls)
          by rewrite conclude mset_of(zs) ⨄ mset_of(ms) = mset_of(ls)
                     by enable {zs, ms} IH[ls]
    ... = mset_of(xs)
          by enable {ys, ls} IH[xs]
  }
end
```

Next, we prove that the first output list is sorted. We make use of
the `merge_sorted` theorem in this proof.

``` {.deduce #msort_sorted}
theorem msort_sorted: all n:Nat. all xs:List<Nat>. 
  sorted(first(msort(n, xs)))
proof
  induction Nat
  case 0 {
    arbitrary xs:List<Nat>
    switch xs {
      case empty {
        suffices sorted(empty)  with definition {msort, first}
        definition sorted
      }
      case node(x, xs') {
        suffices sorted(node(x,empty))
            with definition {msort, first}
        definition {sorted, sorted, all_elements}
      }
    }
  }
  case suc(n') suppose IH {
    arbitrary xs:List<Nat>
    suffices sorted(merge(length(first(msort(n', xs))) 
                          + length(first(msort(n', second(msort(n', xs))))), 
                          first(msort(n', xs)), 
                          first(msort(n', second(msort(n', xs))))))
        with definition {msort, first}
    define ys = first(msort(n', xs))
    define ls = second(msort(n', xs))
    define zs = first(msort(n', ls))
    have IH1: sorted(ys)  by enable {ys}  IH[xs]
    have IH2: sorted(zs)  by enable {zs}  IH[ls]
    conclude sorted(merge(length(ys) + length(zs), ys, zs))
      by apply merge_sorted[length(ys) + length(zs)][ys, zs] to IH1, IH2
  }
end
```

It remains to show that first output of `msort` is of length
`min(2ⁿ,length(xs))`. Instead of using `min`, I separated the proof
into a couple cases depending on whether `2ⁿ ≤ length(xs)`.  However,
I first needed to prove the lengths of the two output lists adds up to
the length of the input list.

```
theorem msort_length: all n:Nat. all xs:List<Nat>.
  length(first(msort(n, xs)))  +  length(second(msort(n, xs))) = length(xs)
```

The proof of `msort_length` required a theorem that the length of the
output of `merge` is the sum of the lengths of the inputs.

```
theorem merge_length: all n:Nat. all xs:List<Nat>, ys:List<Nat>.
  if length(xs) + length(ys) = n
  then length(merge(n, xs, ys)) = n
```

So in the case when the length of the input list is greater than `2ⁿ`,
the first output of `msort` is of length `2ⁿ`.

``` {.deduce #msort_length_less_equal}
theorem msort_length_less_equal: all n:Nat. all xs:List<Nat>.
  if pow2(n) ≤ length(xs)
  then length(first( msort(n, xs) )) = pow2(n)
proof
  induction Nat
  case 0 {
    arbitrary xs:List<Nat>
    suppose prem
    switch xs {
      case empty suppose xs_mt {
        conclude false
            by definition {pow2, length, operator≤} in
               rewrite xs_mt in prem
      }
      case node(x, xs') suppose xs_xxs {
        suffices length(node(x,empty)) = pow2(0)
            with definition {msort,first}
        definition {length, length, pow2, operator+, operator+}
      }
    }
  }
  case suc(n') suppose IH {
    arbitrary xs:List<Nat>
    suppose prem
    have len_xs: pow2(n') + pow2(n') ≤ length(xs)
      by rewrite add_zero[pow2(n')] in
         definition {pow2, operator*, operator*,operator*} in prem
    suffices length(merge(length(first(msort(n', xs))) 
                            + length(first(msort(n', second(msort(n', xs))))), 
                          first(msort(n', xs)), 
                          first(msort(n', second(msort(n', xs))))))
             = 2 * pow2(n')
        with definition {pow2, msort, first}
    define ys = first(msort(n',xs))
    define ls = second(msort(n',xs))
    define zs = first(msort(n', ls))
    define ms = second(msort(n', ls))
    have len_ys: length(ys) = pow2(n') by {
         have p2n_le_xs: pow2(n') ≤ length(xs) by
             have p2n_le_2p2n: pow2(n') ≤ pow2(n') + pow2(n') by
                 less_equal_add[pow2(n')][pow2(n')]
             apply less_equal_trans[pow2(n')][pow2(n') + pow2(n'), length(xs)]
             to p2n_le_2p2n, len_xs
         enable {ys} 
         apply IH[xs] to p2n_le_xs
    }
    have len_zs: length(zs) = pow2(n') by {
         have len_ys_ls_eq_xs: length(ys) + length(ls) = length(xs)
           by enable {ys, ls} msort_length[n'][xs]
         have p2n_le_ls: pow2(n') ≤ length(ls)
           by have pp_pl: pow2(n') + pow2(n') ≤ pow2(n') + length(ls)
                by rewrite symmetric len_ys_ls_eq_xs | len_ys in len_xs
              apply less_equal_left_cancel[pow2(n')][pow2(n'), length(ls)] to pp_pl
         enable {zs} 
         apply IH[ls] to p2n_le_ls
    }
    have len_ys_zs: length(ys) + length(zs) = 2 * pow2(n') by {
      equations
        length(ys) + length(zs) 
          = pow2(n') + pow2(n')    by rewrite len_ys | len_zs
      ... = 2 * pow2(n')           by symmetric two_mult[pow2(n')]
    }
    equations
          length(merge(length(ys) + length(zs), ys, zs))
        = length(merge(2 * pow2(n'), ys, zs))   by rewrite len_ys_zs
    ... = 2 * pow2(n')                          by apply merge_length[2 * pow2(n')][ys, zs] to len_ys_zs
  }
end
```

When the length of the input list is less than `2ⁿ`, the length of the
first output is the same as the length of the input.

```{.deduce #msort_length_less}
theorem msort_length_less: all n:Nat. all xs:List<Nat>.
  if length(xs) < pow2(n)
  then length(first( msort(n, xs) )) = length(xs)
proof
  induction Nat
  case 0 {
    arbitrary xs:List<Nat>
    suppose prem
    switch xs {
      case empty suppose xs_mt {
        definition {msort, length, first}
      }
      case node(x, xs') suppose xs_xxs {
        suffices 1 + 0 = 1 + length(xs')
            with definition {msort, first, length, length}
        have xs_0: length(xs') = 0
            by definition {operator ≤, length, operator+, operator+, operator<, 
                           pow2, operator ≤, operator ≤} in 
               rewrite xs_xxs in prem
        rewrite xs_0
      }
    }
  }
  case suc(n') suppose IH {
    arbitrary xs:List<Nat>
    suppose prem
    suffices length(merge(length(first(msort(n', xs))) 
                          + length(first(msort(n', second(msort(n', xs))))), 
                          first(msort(n', xs)), 
                          first(msort(n', second(msort(n', xs))))))
             = length(xs)
        with definition{msort, first}
    define ys = first(msort(n',xs))
    define ls = second(msort(n',xs))
    define zs = first(msort(n', ls))
    define ms = second(msort(n', ls))

    have xs_le_two_p2n: length(xs) < pow2(n') + pow2(n')
      by rewrite add_zero[pow2(n')] in
         definition {pow2, operator*,operator*,operator*} in prem

    have ys_ls_eq_xs: length(ys) + length(ls) = length(xs)
      by enable {ys,ls} msort_length[n'][xs]

    have pn_xs_or_xs_pn: pow2(n') ≤ length(xs) or length(xs) < pow2(n')
      by dichotomy[pow2(n'), length(xs)]
    cases pn_xs_or_xs_pn
    case pn_xs: pow2(n') ≤ length(xs) {
    
      have ys_pn: length(ys) = pow2(n')
          by enable {ys} apply msort_length_less_equal[n'][xs] to pn_xs

      have ls_l_pn: length(ls) < pow2(n')
          by have pn_ls_l_2pn: pow2(n') + length(ls) < pow2(n') + pow2(n')
               by rewrite symmetric ys_ls_eq_xs | ys_pn in xs_le_two_p2n
             apply less_left_cancel[pow2(n'), length(ls), pow2(n')] to pn_ls_l_2pn

      have len_zs: length(zs) = length(ls)
          by enable {zs} apply IH[ls] to ls_l_pn

      equations
        length(merge(length(ys) + length(zs),ys,zs))
            = length(ys) + length(zs)
              by merge_length[length(ys) + length(zs)][ys,zs]
        ... = length(ys) + length(ls)
              by rewrite len_zs
        ... = length(xs)
              by ys_ls_eq_xs
    }
    case xs_pn: length(xs) < pow2(n') {
    
      have len_ys: length(ys) = length(xs)
        by enable {ys} apply IH[xs] to xs_pn

      have len_ls: length(ls) = 0
        by apply left_cancel[length(ys)][length(ls), 0] to
           suffices length(ys) + length(ls) = length(ys)
               by rewrite add_zero[length(ys)]
           rewrite symmetric len_ys in ys_ls_eq_xs

      have ls_l_pn: length(ls) < pow2(n')
        by rewrite symmetric len_ls in pow_positive[n'] 
      
      have len_zs: length(zs) = 0
        by enable {zs} rewrite len_ls in apply IH[ls] to ls_l_pn

      equations
        length(merge(length(ys) + length(zs),ys,zs))
          = length(ys) + length(zs)
            by merge_length[length(ys) + length(zs)][ys, zs]
      ... = length(xs)
            by rewrite len_zs | add_zero[length(ys)] | len_ys
    }
  }
end
```

## Prove correctness of `merge_sort`

The proof that `merge_sort` produces a sorted list is a
straightforward corollary of the `msort_sorted` theorem.

```{.deduce #merge_sort_sorted}
theorem merge_sort_sorted: all xs:List<Nat>.
  sorted(merge_sort(xs))
proof
  arbitrary xs:List<Nat>
  suffices sorted(first(msort(log(length(xs)), xs)))
      with definition merge_sort
  msort_sorted[log(length(xs))][xs]
end
```

The proof that the contents of the output of `merge_sort` are the same
as the input is a bit more involved. So if we use the definitoin of
`merge_sort`, we then need to show that

```
mset_of(first(msort(log(length(xs)),xs))) = mset_of(xs)
```

which means we need to show that all the elements in `xs` end up in
the first output and that there are not any leftovers.  Let `ys` be
the first output of `msort` and `ls` be the leftovers.  The theorem
`less_equal_pow_log` in `Log.pf` tells us that
`length(xs) ≤ pow2(log(length(xs)))`. 
So in the case where they are equal, we can
use the `msort_length_less_equal` theorem to show that `length(ys) =
length(xs)`. In the case where `length(xs)` is strictly smaller, we
use the `msort_length_less` theorem to prove that
`length(ys) = length(xs)`. Finally, we show that the length of `ls` is zero
by use of `msort_length` and some properties of arithmetic like
`left_cancel` (in `Nat.pf`).

Here is the proof of `mset_of_merge_sort` in full.

```{.deduce #mset_of_merge_sort}
theorem mset_of_merge_sort: all xs:List<Nat>.
  mset_of(merge_sort(xs)) = mset_of(xs)
proof
  arbitrary xs:List<Nat>
  suffices mset_of(first(msort(log(length(xs)), xs))) = mset_of(xs)
      with definition merge_sort
  define n = log(length(xs))
  define ys = first(msort(n,xs))
  define ls = second(msort(n,xs))

  have len_xs: length(xs) ≤ pow2(n)
    by enable {n} less_equal_pow_log[length(xs)]
  have len_ys: length(ys) = length(xs)
    by cases apply less_equal_implies_less_or_equal[length(xs)][pow2(n)]
             to len_xs
       case len_xs_less: length(xs) < pow2(n) {
         enable {ys} apply msort_length_less[n][xs] to len_xs_less
       }
       case len_xs_equal: length(xs) = pow2(n) {
         have pn_le_xs: pow2(n) ≤ length(xs)
           by apply equal_implies_less_equal to symmetric len_xs_equal
         have len_ys_pow2: length(ys) = pow2(n)
           by enable {ys} apply msort_length_less_equal[n][xs] to pn_le_xs
         transitive len_ys_pow2 (symmetric len_xs_equal)
       }
  have len_ys_ls_eq_xs: length(ys) + length(ls) = length(xs)
    by enable {ys, ls} msort_length[n][xs]
  have len_ls: length(ls) = 0
    by apply left_cancel[length(ys)][length(ls), 0] to
       suffices length(ys) + length(ls) = length(ys)
           with rewrite add_zero[length(ys)]
       rewrite symmetric len_ys in len_ys_ls_eq_xs
  have ls_mt: ls = empty
    by apply length_zero_empty[Nat, ls] to len_ls

  have ys_ls_eq_xs: mset_of(ys)  ⨄  mset_of(ls) = mset_of(xs)
    by enable {ys, ls} mset_of_msort[n][xs]

  equations
          mset_of(ys)
        = mset_of(ys)  ⨄  m_fun(λx{0})   by rewrite m_sum_empty[Nat,mset_of(ys)]
    ... = mset_of(ys)  ⨄  mset_of(empty) by definition mset_of
    ... = mset_of(ys)  ⨄  mset_of(ls)    by rewrite ls_mt 
    ... = mset_of(xs)                    by ys_ls_eq_xs
end
```

## Exercise: `merge_length` and `msort_length`

Prove the following theorems.

```
theorem merge_length: all n:Nat. all xs:List<Nat>, ys:List<Nat>.
  if length(xs) + length(ys) = n
  then length(merge(n, xs, ys)) = n

theorem msort_length: all n:Nat. all xs:List<Nat>.
  length(first(msort(n, xs)))  +  length(second(msort(n, xs))) = length(xs)
```

## Exercise: classic Merge Sort

Test and prove the correctness of the classic definition of
`merge_sort`, which we repeat here.

```
function msort(Nat, List<Nat>) -> List<Nat> {
  msort(0, xs) = xs
  msort(suc(n'), xs) =
    define p = split(xs)
    merge(msort(n', first(p)), msort(n', second(p)))
}

define merge_sort : fn List<Nat> -> List<Nat>
  = λxs{ msort(log(length(xs)), xs) }
```

You will need define the `split` function.


<!--
``` {.deduce file=MergeSort.pf} 
import Base
import Nat
import MultiSet
import List
import InsertionSort
import Log

<<merge>>
<<msort>>
<<merge_sort>>
<<test_merge>>
<<test_msort>>
<<test_merge_sort>>
<<test_merge_sort_many>>

<<mset_of_merge>>
<<set_of_merge>>
<<merge_sorted>>

<<mset_of_msort>>
<<msort_sorted>>

theorem merge_length: all n:Nat. all xs:List<Nat>, ys:List<Nat>.
  if length(xs) + length(ys) = n
  then length(merge(n, xs, ys)) = n
proof
  induction Nat
  case 0 {
    arbitrary xs:List<Nat>, ys:List<Nat>
    suppose _
    definition {merge, length}
  }
  case suc(n') suppose IH {
    arbitrary xs:List<Nat>, ys:List<Nat>
    suppose prem
    _definition {merge}
    switch xs {
      case empty suppose xs_empty {
        conclude length(ys) = suc(n')
          by definition {length, operator+} in
             rewrite xs_empty in prem
      }
      case node(x, xs') suppose xs_xxs {
        switch ys {
          case empty suppose ys_empty {
            conclude length(node(x,xs')) = suc(n')
              by _definition length
                 rewrite add_zero[1 + length(xs')] in
                 definition {length} in
                 rewrite xs_xxs | ys_empty in prem
          }
          case node(y, ys') suppose ys_yys {
            switch x ≤ y {
              case true {
                have suc_len_xs_yys:
                   suc(length(xs') + length(node(y,ys'))) = suc(n')
                  by _definition {length, operator+, operator+}
                     definition {operator+, operator+} in
                     rewrite ys_yys in
                     definition length in
                     rewrite xs_xxs in prem
                have len_xs_yys: length(xs') + length(node(y,ys')) = n'
                   by injective suc suc_len_xs_yys
                _definition length
                _rewrite apply IH[xs', node(y, ys')] to len_xs_yys
                conclude 1 + n' = suc(n')   by one_add_suc[n']
              }
              case false {
                _definition length
                have suc_len: suc(length(xs) + length(ys')) = suc(n')
                  by rewrite add_suc[length(xs)][length(ys')] in
                     definition {length, operator+, operator+} in
                     rewrite ys_yys in prem
                _rewrite (rewrite xs_xxs in apply IH[xs, ys']
                                          to injective suc suc_len)
                conclude 1 + n' = suc(n')    by one_add_suc[n']
              }
            }
          }
        }
      }
    }
  }
end

theorem msort_length: all n:Nat. all xs:List<Nat>.
  length(first(msort(n, xs)))  +  length(second(msort(n, xs))) = length(xs)
proof
  induction Nat
  case 0 {
    arbitrary xs:List<Nat>
    switch xs {
      case empty {
        definition {msort, first, second, length, operator+}
      }
      case node(x, xs') {
        definition {msort, length, length, first, second, operator+, operator+, length}
      }
    }
  }
  case suc(n') suppose IH {
    arbitrary xs:List<Nat>
    _definition {msort, first, second}

    define ys = first(msort(n',xs))
    define ls = second(msort(n',xs))
    have ys_def: first(msort(n',xs)) = ys  by definition ys
    have ls_def: second(msort(n',xs)) = ls  by definition ls
    
    define zs = first(msort(n', ls))
    define ms = second(msort(n', ls))
    have zs_def: first(msort(n', ls)) = zs by definition zs
    have ms_def: second(msort(n', ls)) = ms by definition ms

    have ys_ls_xs: length(ys) + length(ls) = length(xs)
      by rewrite ys_def | ls_def in IH[xs]
    have zs_ms_ls: length(zs) + length(ms) = length(ls)
      by rewrite zs_def | ms_def in IH[ls]
    _rewrite symmetric ys_ls_xs
    _rewrite symmetric zs_ms_ls
    
    _rewrite merge_length[length(ys) + length(zs)][ys,zs]
    _rewrite add_assoc[length(ys)][length(zs), length(ms)]
    .
  }
end

<<msort_length_less_equal>>
<<msort_length_less>>

<<merge_sort_sorted>>
<<mset_of_merge_sort>>
```
-->
