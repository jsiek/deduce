To demonstrate how to work with `if`-`then` formulas, we shall prove a
property about the `filter` function defined below. This function
takes a list and a predicate and produces a list that includes only
those elements from the input list that satisfy the predicate.

```{.deduce #filter}
function filter<E>(List<E>, fn (E)->bool) -> List<E> {
  filter(empty, P) = empty
  filter(node(x, ls), P) =
    if P(x) then node(x, filter(ls, P))
    else filter(ls, P)
}
```

Of course, if all the elements in the list satisfy the predicate, then
the output of `filter` is the same as the input list.  Note the use of
"if" and "then" in the previous sentence.  This statement translates
into Deduce in a straightforward ways, as follows.  (Recall that we
have already defined the `all_elements` function.)

    theorem filter_all: all T:type, P:fn (T)->bool. all xs:List<T>. 
      if all_elements(xs, P) then filter(xs, P) = xs
    proof
      ?
    end

The beginning of the proof proceeds as usual for a formula that begins
with `all`, using `arbitrary` for `T` and `P` and then `induction` for
`xs`.

```
arbitrary T:type, P:fn (T)->bool
induction List<T>
case empty {
  ?
}
case node(x, xs') suppose IH: if all_elements(xs',P) then filter(xs',P) = xs' {
  ?
}
```

In the case for `empty`, it remains to prove the following.

    unfinished proof:
        (if all_elements(empty,P) then filter(empty,P) = empty)

To prove an `if`-`then` formula, we `suppose` the condition and then
prove the conclusion. The `suppose` statement of Deduce requires a
label, so that you can use the assumption in the proof of the
conclusion. However, in this particular case the assumption is not
useful.

    suppose cond: all_elements(empty,P)
    ?

Now we need to prove the conclusion

    unfinished proof:
        filter(empty,P) = empty

but that is just the definition of `filter`, so we conclude this case
as follows.

    case empty {
      suppose cond: all_elements(empty,P)
      conclude filter(empty,P) = empty by definition filter.
    }

Next we turn our attention to the case for `node`.

```
case node(x, xs') suppose IH: if all_elements(xs',P) then filter(xs',P) = xs' {
  ?
}
```

The goal for this case is stated as follows.

```
unfinished proof:
	(if all_elements(node(x,xs'),P) then filter(node(x,xs'),P) = node(x,xs'))
```

Again we need to prove an `if`-`then` formula. So we assume the condition.

    suppose Pxs: all_elements(node(x,xs'),P)
    ?

Now we need to prove the conclusion.

    unfinished proof:
        filter(node(x,xs'),P) = node(x,xs')

We proceed by using the definition of filter.

    suppose Pxs: all_elements(node(x,xs'),P)
    definition filter
    ?

So the conclusion is transformed into the following.

    unfinished proof:
        if P(x) then node(x,filter(xs',P)) else filter(xs',P) = node(x,xs')

The right-hand side of the equation involves an `if`-`then`-`else`
term, so we need to figure out whether `P(x)` is true. Let us look at
the available facts.

    available facts:
        Pxs: all_elements(node(x,xs'),P),
        IH: (if all_elements(xs',P) then filter(xs',P) = xs'),
        ...

Thinking for a moment, we realize that `Pxs` implies that `P(x)` is true.
So we go ahead and prove `P(x)` using the definition of `all_elements`
and then rewrite the goal with the fact that `P(x)` is true
(i.e., `P(x) = true`).

    definition filter
    have Px: P(x) by definition all_elements in Pxs
    rewrite Px
    ?

The right-hand side of the equation simplifies to the "then" branch,
so it remains to prove the following.

    unfinished proof:
        node(x,filter(xs',P)) = node(x,xs')

At this point in the proof we need to use the induction hypothesis
`IH`.  However, `IH` is an `if-then` formula, so we need to prove
that its condition `all_elements(xs',P)` is true in order to use its
conclusion. Thankfully, this also follows from `Pxs`.

    have Pxs': all_elements(xs',P) by definition all_elements in Pxs

We use Deduce's `apply`-`to` statement (aka. modus ponens) to obtain
the conclusion of an `if`-`then` formula.

    have IH_conc: filter(xs',P) = xs' by apply IH to Pxs'

We conclude by using the equation `IH_conc` to rewrite the goal.

    rewrite IH_conc.
    
Our proof of `filter_all` is complete. Here is the proof in its entirety.

```{.deduce #filter_all}
theorem filter_all: all T:type, P:fn (T)->bool. all xs:List<T>. 
  if all_elements(xs, P) then filter(xs, P) = xs
proof
  arbitrary T:type, P:fn (T)->bool
  induction List<T>
  case empty {
    suppose cond: all_elements(empty,P)
    conclude filter(empty,P) = empty by definition filter.
  }
  case node(x, xs') suppose IH: if all_elements(xs',P) then filter(xs',P) = xs' {
    suppose Pxs: all_elements(node(x,xs'),P)
    definition filter
    have Px: P(x) by definition all_elements in Pxs
    rewrite Px
    suffices node(x,filter(xs',P)) = node(x,xs')
    have Pxs': all_elements(xs',P) by definition all_elements in Pxs
    have IH_conc: filter(xs',P) = xs' by apply IH to Pxs'
    rewrite IH_conc.
  }
end
```
