# Writing Proofs in Deduce

This section provides a tutorial on writing proofs in Deduce.  In the
following subsections we introduce the features of the Deduce proof
language and provide examples of their use.

* [Working with Definitions](#working-with-definitions)
* [Generalizing with `all` formulas](#generalizing-with-all-formulas)
* [Rewriting with Equations](#rewriting-with-equations)
* [Proving `all` Formulas with Induction](#proving-all-formulas-with-induction)
* [Equational Reasoning](#equational-reasoning)
* [Reasoning about natural numbers](#reasoning-about-natural-numbers)
* [Reasoning about `and` (Conjunction)](#reasoning-about-and-conjunction)
* [Reasoning about `or` (Disjunction)](#reasoning-about-or-disjunction)
* [Conditional Formulas (Implication)](#conditional-formulas-implication)
* [Reasoning about `true`](#reasoning-about-true)
* [Reasoning about `false`](#reasoning-about-false)
* [Reasoning about `not`](#reasoning-about-not)
* [`switch` Proof Statement](#switch-proof-statement)
* [Reasoning about `some` (Exists)](#reasoning-about-some-exists)

## Working with Definitions

We begin with an simple example, proving that the length of an empty
list is `0`. Of course, this is a direct consequence of the definition
of `length`, so this first example is about how to use definitions.
To get started, we write down the theorem we would like to prove.  A
theorem starts with a label, followed by a colon, then the formula
followed by the proof. But instead of writing the proof, we'll simply
write `?` to say that we're not done yet.

    theorem length_empty: length(empty) = 0
    proof
      ?
    end

Run Deduce on the file. Deduce will respond with the following message
to remind us of what is left to prove.

    unfinished proof:
        length(empty) = 0

To tell Deduce to apply the definition of `length`, we can use
the `definition` statement.

    theorem length_empty: length(empty) = 0
    proof
      definition length
      ?
    end

Now Deduce responds with

    unfinished proof:
        true

Deduce expanded the definition of `length` in the correct goal,
changing `length(empty) = 0` to `0 = 0`. In particular, Deduce noticed
that `length(empty)` matches the first clause in the definition of
`length` and then replaced it with the right-hand side of the first
clause. Deduce then simplified `0 = 0` to `true`. In general, whenever
Deduce sees an equality with the same left and right-hand side, it
automatically simplifies it to `true`.

To finish the proof, we just need to prove `true`, which is
accomplished with a period.

```{.deduce #length_empty}
theorem length_empty: length(empty) = 0
proof
  definition length.
end
```

Run Deduce on the file to see it respond that the file is valid.

Let's try a slightly more complex theorem, that the length
of a list with just a single node is indeed `1`. Based
on what we learned above, we better start by applying the
definition of `length` a couple of times.

    theorem length_node42: length(node(42, empty)) = 1
    proof
      definition {length, length}
      ?
    end

Deduce responds that we still need to prove the following obvious fact.

    unfinished proof:
        1 + 0 = 1

But that is just a consequence of the definition of addition, which
we can refer to as `operator +`.

    theorem length_node42: length(node(42, empty)) = 1
    proof
      definition {length, length, operator +, operator+}
      ?
    end

Deduce responds with

    unfinished proof:
        true

so we can conclude the proof with a period.

```{.deduce #length_node42}
theorem length_node42: length(node(42, empty)) = 1
proof
  definition {length, length, operator +, operator +}.
end
```

### Exercise

Prove that `append(node(1,empty), node(2, empty)) = node(1,node(2,empty))`.

## Generalizing with `all` formulas

In the proof of `length_node42` it did not matter that the element in
the node was `42`. We can generalize this theorem by using an `all`
formula. We begin the formula with `all x:Nat.` to say that the
formula must be true for all natural numbers and the variable `x` will
be used to refer to the natural number.  We then replace the `42` in
the formula with `x` to obtain the following theorem statement.

    theorem length_one_nat: all x:Nat. length(node(x, empty)) = 1
    proof
      ?
    end

Deduce responds with

    unfinished proof:
        all x:Nat. length(node(x,empty)) = 1

The most straightforward way to prove an `all` formula in Deduce is
with an `arbitrary` statement. When you use `arbitrary` you are
promising to prove the formula for a hypothetical entity that can
stand in for all entities of the specified type. The `arbitrary`
statement asks you to name the hypothetical entity. Here we choose `x`
but we could have chosen a different name.

    theorem length_one_nat: all x:Nat. length(node(x, empty)) = 1
    proof
      arbitrary x:Nat
      ?
    end

Deduce responds with

    unfinished proof:
        length(node(x,empty)) = 1

We don't know anything about this hypothetical `x` other than it being
a natural number. But as we previously observed, we don't need any
more information about `x` in this example.  We complete the proof as
before, using the definitions of `length` and addition.

```{.deduce #length_one_nat}
theorem length_one_nat: all x:Nat. length(node(x, empty)) = 1
proof
  arbitrary x:Nat
  definition {length, length, operator +, operator+}.
end
```

Once we have proved that an `all` formula is true, we can use it by
supplying an entity of the appropriate type inside square brackets. In
the following we prove the `length_node42` theorem again, but this
time the proof makes use of `length_one_nat`.

```{.deduce #length_node42_again}
theorem length_node42_again: length(node(42, empty)) = 1
proof
  length_one_nat[42]
end
```

We can generalize the theorem yet again by noticing that it does not
matter whether the element is a natural number. It could be a value of
any type. In Deduce we can also use the `all` statement to generalize
types. In the following, we add `U:type` to the `all` formula and to
the `arbitrary` statement.

```{.deduce #length_one}
theorem length_one: all U:type, x:U. length(node(x, empty)) = 1
proof
  arbitrary U:type, x:U
  definition {length, length, operator +, operator+}.
end
```

To summarize this section:
* To state that a formula is true for all entities of a given type,
  use Deduce's `all` formula.
* To prove that an `all` formula is true, use Deduce's `arbitrary` statement.
  (We'll see a second method in the next section.)
* To using a fact that is an `all` formula, instantiate the fact
  by using square brackets around the specific entity.

### Exercise

Prove that
```
all T:type, x:T, y:T. append(node(x,empty), node(y, empty)) = node(x,node(y,empty))
```

Prove again that 
```
append(node(1,empty), node(2, empty)) = node(1,node(2,empty))
```
but this time use the previous theorem.


## Rewriting with Equations

Deduce provides the `rewrite` statement to apply an equation to the
current goal, or to a fact. In particular, `rewrite` replaces each
occurence of the left-hand side of an equation with the right-hand
side of the equation.

For example, let us prove the following theorem using `rewrite`
with the above `length_one` theorem.

```
theorem length_one_equal: all U:type, x:U, y:U.
  length(node(x,empty)) = length(node(y,empty))
proof
  arbitrary U:type, x:U, y:U
  ?
end
```

To replace `length(node(x,empty))` with `1`, we rewrite
using the `length_one` theorem instantiated at `U` and `x`.

```
rewrite length_one[U,x]
```

Deduce tells us that the current goal has become

```
1 = length(node(y,empty))
```

We rewrite again using `length_one`, which time instantiated
with `y`.

```
  rewrite length_one[U,y]
```

Deduce changes the goal to `1 = 1`, which simplies to just `true`
so we can finish the proof with a period.

Here is the completed proof of `length_one_equal`.

```{.deduce #length_one_equal}
theorem length_one_equal: all U:type, x:U, y:U.
  length(node(x,empty)) = length(node(y,empty))
proof
  arbitrary U:type, x:U, y:U
  rewrite length_one[U,x]
  rewrite length_one[U,y].
end
```

## Proving `all` Formulas with Induction

Sometimes the `arbitrary` statement does not give us enough
information to prove an `all` formula. In those situations, so long as
the type of the `all` variable is a `union` type, we can use the more
powerful `induction` statement.

For example, consider the following theorem about appending a list to
an empty list. Suppose we try to use `arbitrary` for both the
`all U` and the `all xs`.

    theorem append_empty: all U :type. all xs :List<U>.
      append(xs, empty) = xs
    proof
      arbitrary U:type
      arbitrary xs:List<U>
      ?
    end

Deduce replies that we need to prove

    unfinished proof:
        append(xs,empty) = xs

We might try to expand the definition of `append` as follows.

    theorem append_empty: all U :type. all xs :List<U>.
      append(xs, empty) = xs
    proof
      arbitrary U:type
      arbitrary xs:List<U>
      definition append
      ?
    end

But Deduce replies with the same goal.

    unfinished proof:
        append(xs,empty) = xs

Deduce was unable to expand the definition of `append` because that
function pattern matches on its first argument, but we don't know
whether `xs` is an `empty` list or a `node`.

So instead of using `arbitrary xs:List<U>` to prove the `all xs`, we
proceed by induction as follows.

    theorem append_empty: all U :type. all xs :List<U>.
      append(xs, empty) = xs
    proof
      arbitrary U:type
      induction List<U>
      case empty {
        ?
      }
      case node(n, xs') suppose IH: append(xs',empty) = xs' {
        ?
      }
    end

When doing a proof by induction, there is one `case` for every
alternative in the `union` type. Here the union type is `List<U>`, so
we have a case for the `empty` and `node` alternatives. 
Furthermore, because `node` includes a recursive argument, that is,
and argument of type `List<U>`, in the case for `node` we get to
assume that the formula we are trying to prove is already true for
the argument. This is commonly known at the **induction hypothesis**.
We must give a label for the induction hypothesis so here we choose
`IH` for short.

Let us first focus on the case for `empty`. Deduce tells us that we
need to prove the following.

    unfinished proof:
        append(empty,empty) = empty

This follows directly from the definition of `append`.

    case empty {
      definition append.
    }

However, to make the proof more readable by other humans, I recommend
restating the goal using the `show` statement.

    case empty {
      conclude append(empty, empty) = empty  by definition append.
    }

Next let us focus on the case for `node`. Deduce tells us that we need
to prove the following and that `IH` has been added to the available
facts.

    unfinished proof:
        append(node(n,xs'),empty) = node(n,xs')

    available facts:
        IH: append(xs',empty) = xs',
        ...

Looking at the goal, we notice that we can expand the definition of
`append` on the right-hand side, because it is applied to a `node`.
Deduce provides the `term` statement as way to use Deduce to expand
definitions for us.

    case node(n, xs') suppose IH: append(xs',empty) = xs' {
      term append(node(n,xs'),empty) by definition append ?
      ?
    }

Deduce responds with

    unfinished proof:
        node(n,append(xs',empty))

We use Deduce's `have` statement to label this equality.
We choose the label `step1`, state the equality, and then
provide its proof after the `by` keyword.

    case node(n, xs') suppose IH: append(xs',empty) = xs' {
      have step1: append(node(n,xs'),empty)
                  = node(n, append(xs',empty))  by definition append.
      ?
    }

Next, we see that the subterm `append(xs',empty)` matches the
right-hand side of the induction hypothesis `IH`. We use the
`rewrite` statement to apply the `IH` equation to this subterm.

    have step2: node(n, append(xs',empty))
                = node(n,xs')                 by rewrite IH.

To complete the proof, we combine equations (1) and (2) using
the `transitive` statement.

    conclude append(node(n,xs'),empty) = node(n,xs')
        by transitive step1 step2

Here is the completed proof of `append_empty`.

```{.deduce #append_empty}
theorem append_empty: all U :type. all xs :List<U>.
  append(xs, empty) = xs
proof
  arbitrary U:type
  induction List<U>
  case empty {
    conclude append(empty, empty) = empty  by definition append.
  }
  case node(n, xs') suppose IH: append(xs',empty) = xs' {
    have step1: append(node(n,xs'),empty)
                = node(n, append(xs',empty))  by definition append.
    have step2: node(n, append(xs',empty))
                = node(n,xs')                 by rewrite IH.
    conclude append(node(n,xs'),empty) = node(n,xs')
        by transitive step1 step2
  }
end
```

To summarize this section:
* To prove an `all` formula that concerns entities of a `union` type,
  use Deduce's `induction` statement.
* Use the `rewrite` statement to apply an equation to the current
  goal.

### Exercise

Prove that `length(append(xs, ys)) = length(xs) + length(ys)`.

## Equational Reasoning

Combining a sequence of equations using `transitive` is quite common,
so Deduce provides the `equations` statement to streamline this
process.  After the first equation, the left-hand side of each
equation is written as `...` because it is just a repetition of the
right-hand side of the previous equation. We can refactor the
proof of the `node` case of the `append_empty` theorem using
`equations` as follows.

    case node(n, xs') suppose IH: append(xs',empty) = xs' {
      equations
        append(node(n,xs'),empty)
            = node(n, append(xs',empty))  by definition append.
        ... = node(n,xs')                 by rewrite IH.
    }

Here is the completed proof of the new `append_empty_eqn` theorem.

```{.deduce #append_empty_eqn}
theorem append_empty_eqn: all U :type. all xs :List<U>.
  append(xs, empty) = xs
proof
  arbitrary U:type
  induction List<U>
  case empty {
    conclude append(empty, empty) = empty  by definition append.
  }
  case node(n, xs') suppose IH: append(xs',empty) = xs' {
    equations
      append(node(n,xs'),empty)
          = node(n, append(xs',empty))  by definition append.
      ... = node(n,xs')                 by rewrite IH.
  }
end
```

### Exercise

Prove again that `length(append(xs, ys)) = length(xs) + length(ys)`,
but this time using the `equations` statement.

## Reasoning about natural numbers

As metioned previously, the `Nat.pf` file includes the definition of
natural numbers, operations on them (e.g. addition), and proofs about
those operations. Here we discuss how to reason about
addition. Reasoning about the other operations follows a similar
pattern.

Here is the definition of addition from `Nat.pf`:
```
function operator +(Nat,Nat) -> Nat {
  operator +(0, m) = m
  operator +(suc(n), m) = suc(n + m)
}
```

As we saw above with the `append` function, we can use Deduce's
`definition` statement whenever we want to rewrite the goal or a given
fact according to the equations for addition. Here are the two
defining equations, but written with infix notation:

```
  0 + m = m
  suc(n) + m = suc(n + m)
```

The `Nat.pf` file also includes proofs of many equations.
Here we list the names of the theorems and the formula. (To add more
theorems, pull requests on the github repository are most welcome!)

```
add_zero: all n:Nat.  n + 0 = n
add_commute: all n:Nat. all m:Nat.  n + m = m + n
add_assoc: all m:Nat. all n:Nat, o:Nat.  (m + n) + o = m + (n + o)
left_cancel: all x:Nat. all y:Nat, z:Nat.  if x + y = x + z then y = z
dist_mult_add: all a:Nat. all x:Nat, y:Nat. a * (x + y) = a * x + a * y
mult_zero: all n:Nat. n * 0 = 0
mult_one: all n:Nat. n * 1 = n
mult_commute: all m:Nat. all n:Nat. m * n = n * m
mult_assoc: all m:Nat. all n:Nat, o:Nat. (m * n) * o = m * (n * o)
```

You can use these theorems just like a given of the specified formula.
For example, `add_zero[x]` is a proof of `x + 0 = x` and `apply
left_cancel[2][a,b] to p` is a proof of `a = b` so long as `p` is a
given for the formula `2 + a = 2 + b`.

### Exercise

```
right_cancel: all x:Nat. all y:Nat, z:Nat.  if x + z = y + z then x = y
```

## Reasoning about `and` (Conjunction)

To create a single formula that expresses that two formulas are true,
combine the two formulas with `and` (i.e. conjunction). The following
example proves that `0 ≤ 1 and 0 ≤ 2`.  This is accomplished by
separately proving that `0 ≤ 1` is true and that `0 ≤ 2` is true, then
using the comma operator to combine those proofs: `one_pos, two_pos`.

```{.deduce #positive_1_and_2}
theorem positive_1_and_2: 0 ≤ 1 and 0 ≤ 2
proof
  have one_pos: 0 ≤ 1 by definition operator ≤.
  have two_pos: 0 ≤ 2 by definition operator ≤.
  conclude 0 ≤ 1 and 0 ≤ 2 by one_pos, two_pos
end
```

On the other hand, in Deduce you can use a conjunction as if it were
one of its subformulas, implicitly. In the following we use the
fact that `0 ≤ 1 and 0 ≤ 2` to prove `0 ≤ 2`.

```{.deduce #positive_2}
theorem positive_2: 0 ≤ 2
proof
  conclude 0 ≤ 2 by positive_1_and_2
end
```

To summarize this section:
* Use `and` in Deduce to express the truth of two formulas.
* To prove an `and` formula, prove its parts and then combine them using comma.
* You can implicitly use an `and` formula as one of its parts. 

## Reasoning about `or` (Disjunction)

Two create a formula that expresses that at least one of two formulas
is true (i.e. disjunction), use `or` to combine the formulas.

For example, consider the following variation on the trichotomy law
for numbers, which states that for any two natural numbers `x` and `y`, 
either `x ≤ y` or `y < x`.

    theorem dichotomy:  all x:Nat, y:Nat.  x ≤ y  or  y < x
    proof
      ?
    end

We can prove this using the `trichotomy` theorem from `Nat.pf`,
which tells us that `x < y` or `x = y` or `y < x`.

    theorem dichotomy:  all x:Nat, y:Nat.  x ≤ y  or  y < x
    proof
      arbitrary x:Nat, y:Nat
      have tri: x < y or x = y or y < x by trichotomy[x][y]
      ?
    end

In Deduce, you can use an `or` fact by doing case analysis with the
`cases` statement. There is one `case` for each subformula of the
`or`.

    have tri: x < y or x = y or y < x by trichotomy[x][y]
    cases tri
    case x_l_y: x < y {
      ?
    }
    case x_eq_y: x = y {
      ?
    }
    case y_l_x: y < x {
      ?
    }

In the first case, we consider the situation where `x < y` and still need to
prove that `x ≤ y or y < x`. Thankfully, the theorem 
`less_implies_less_equal` in `Nat.pf` tells us that `x ≤ y`.

    case x_l_y: x < y {
      have x_le_y: x ≤ y by apply less_implies_less_equal[x][y] to x_l_y
      ?
    }

In Deduce, an `or` formula can be proved using a proof of either
subformula, so here we prove `x ≤ y or y < x` with `x ≤ y`.

    case x_l_y: x < y {
      have x_le_y: x ≤ y by apply less_implies_less_equal[x][y] to x_l_y
      conclude x ≤ y or y < x by x_le_y
    }

In the second case, we consider the situation where `x = y`. Here we
can prove that `x ≤ y` by rewriting the `x` to `y` and then using the
reflexive property of the less-equal relation to prove that `y ≤ y`.

    case x_eq_y: x = y {
      have x_le_y: x ≤ y by rewrite x_eq_y less_equal_refl[y]
      conclude x ≤ y or y < x by x_le_y
    }

In the third case, we consider the situation where `y < x`.
So we can immediately conclude that `x ≤ y or y < x`.

    case y_l_x: y < x {
      conclude x ≤ y or y < x by y_l_x
    }

Here is the completed proof of the `dichotomy` theorem.

```{.deduce #dichotomy}
theorem dichotomy:  all x:Nat, y:Nat.  x ≤ y  or  y < x
proof
  arbitrary x:Nat, y:Nat
  have tri: x < y or x = y or y < x by trichotomy[x][y]
  cases tri
  case x_l_y: x < y {
    have x_le_y: x ≤ y by apply less_implies_less_equal[x][y] to x_l_y
    conclude x ≤ y or y < x by x_le_y
  }
  case x_eq_y: x = y {
    have x_le_y: x ≤ y by rewrite x_eq_y less_equal_refl[y]
    conclude x ≤ y or y < x by x_le_y
  }
  case y_l_x: y < x {
    conclude x ≤ y or y < x by y_l_x
  }
end
```

To summarize this section:
* Use `or` in Deduce to express that at least one of two or more formulas is true.
* To prove an `or` formula, prove either one of the formulas.
* To use a fact that is an `or` formula, use the `cases` statement.

## Conditional Formulas (Implication)

Some logical statements are true only under certain conditions, so
Deduce provides an `if`-`then` formula.  To demonstrate how to work
with `if`-`then` formulas, we shall prove a property about the
`filter` function defined below. This function takes a list and a
predicate and produces a list that includes only those elements from
the input list that satisfy the predicate.

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

    arbitrary T:type, P:fn (T)->bool
    induction List<T>
    case empty {
      ?
    }
    case node(x, xs') suppose IH: if all_elements(xs',P) then filter(xs',P) = xs' {
      ?
    }

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

    case node(x, xs') suppose IH: if all_elements(xs',P) then filter(xs',P) = xs' {
      ?
    }

The goal for this case is stated as follows.

    unfinished proof:
        (if all_elements(node(x,xs'),P) then filter(node(x,xs'),P) = node(x,xs'))

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
`IH`.  However, `IH` is an `if`-`then` formula, so we need to prove
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

To summarize this section:
* A conditional formula is stated in Deduce using the `if`-`then` syntax.
* To prove an `if`-`then` formula, `suppose` the premise and prove the conclusion.
* To use a fact that is an `if`-`then` formula, `apply` it `to` a proof of the
  condition.


## Reasoning about `true`

There's not much to say about `true`. It's true!  And as we've already
seen, proving `true` is easy. Just use a period.

```{.deduce #really_trivial}
theorem really_trivial: true
proof
  .
end
```

One almost never sees `true` written explicitly in a formula. However,
it is common for a formula to simplify to `true` after some rewriting.

## Reasoning about `false`

The formula `false` is also rarely written explicitly in a formula.
However, it can arise in contradictory situations. For example,
in the following we have a situation in which `true = false`.
That can't be, so Deduce simplifies `true = false` to just `false`.

```{.deduce #contra_false}
theorem contra_false: all a:bool, b:bool.
  if a = b and a = true and b = false then false
proof
  arbitrary a:bool, b:bool
  suppose prem: a = b and a = true and b = false
  have a_true: a = true by prem
  have b_true: b = false by prem
  conclude false by rewrite a_true | b_true in prem
end
```

More generally, Deduce knows that the different constructors of a
union are in fact different. So in the next example, because `foo` and
`bar` are different constructors, Deduce simplifies `foo = bar` to
`false`.

    union U {
      foo
      bar
    }
    
    theorem foo_bar_false: if foo = bar then false
    proof
      .
    end

The above proof is just a period because Deduce simplifies any formula
of the form `if false then ...` to `true`, which is related to our
next point.

So far we've discussed how a proof of `false` can arise.  Next let's
talk about how you can use `false` once you've got it.  The answer is
anything! The Principle of Explosion from logic tells us that `false`
implies anything. For example, normally we don't know whether or not
two arbitrary Booleans `x` and `y` are the same or different.  But if
we have a premise that is `false`, it doesn't matter.

```{.deduce #false_any}
theorem false_any: all x:bool, y:bool. if false then x = y
proof
  arbitrary x:bool, y:bool
  suppose f: false
  conclude x = y by f
end
```

To summarize this section:
* Deduce simplifies any obviously contradictory equation to `false`.
* `false` implies anything.

## Reasoning about `not`

To express that a formula is false, precede it with `not`.  For
example, for any natural number `x`, it is not the case that `x < x`.

    theorem less_irreflexive:  all x:Nat. not (x < x)
    proof
      ?
    end

Deduce treats `not` as syntactic sugar for a conditional formal with a
`false` conclusion. Thus, Deduce responds to the above partial proof
with the following message.

    unfinished proof:
        all x:Nat. (if x < x then false)

We can proceed by induction.

    induction Nat
    case zero {
      ?
    }
    case suc(x') suppose IH: not (x' < x') {
      ?
    }

In the first case, we must prove the following conditional formula.

    unfinished proof:
        (if 0 < 0 then false)

So we assume the premise `0 < 0`, from which we can conclude `false`
by the definitions of `<` and `≤`.

    case zero {
      suppose z_l_z: 0 < 0
      conclude false by definition {operator <, operator ≤} in z_l_z
    }

In the case where `x = suc(x')`, we must prove the following 

    unfinished proof:
        (if suc(x') < suc(x') then false)

So we assume the premise `suc(x') < suc(x')` from which we
can prove that `x' < x'` using the definitions of `<` and `≤`.

    suppose sx_l_sx: suc(x') < suc(x')
    enable {operator <, operator ≤}
    have x_l_x: x' < x' by sx_l_sx

We conclude this case by applying the induction hypothesis to `x' < x'`.

    conclude false by apply IH to x_l_x

Here is the completed proof that less-than is irreflexive.

```{.deduce #less_irreflexive}
theorem less_irreflexive:  all x:Nat. not (x < x)
proof
  induction Nat
  case zero {
    suppose z_l_z: 0 < 0
    conclude false by definition {operator <, operator ≤} in z_l_z
  }
  case suc(x') suppose IH: not (x' < x') {
    suppose sx_l_sx: suc(x') < suc(x')
    enable {operator <, operator ≤}
    have x_l_x: x' < x' by sx_l_sx
    conclude false by apply IH to x_l_x
  }
end
```

To summarize this section:
* To expression that a formula is false, use `not`.
* Deduce treats the formula `not P` just like `if P then false`.
* Therefore, to prove a `not` formula, suppose `P` then prove `false`.
* To use a formula like `not P`, apply it to a proof of `P` to
  obtain a proof of `false`.

## `switch` Proof Statement

Similar to Deduce's `switch` statement for writing functions, there is
also a `switch` statement for writing proofs. As an example, let us
consider how to prove the following theorem.

    theorem zero_or_positive: all x:Nat. x = 0 or 0 < x
    proof
      ?
    end

We could proceed by induction, but we it turns out we don't need the
induction hypothesis. In such situations, we can instead use `switch`.
Like induction, `switch` works on unions and there is one case for
each alternative of the union. Unlike induction, the goal formula does
not need to be an `all` formula. Instead, you indicate which entity to
switch on, as in `switch x` below.

    arbitrary x:Nat
    switch x {
      case zero {
        ?
      }
      case suc(x') {
        ?
      }
    }

Deduce responds that in the first case we need to prove the following.

    unfinished proof:
        true or 0 < 0

So we just need to prove `true`, which is what the period is for.

    case zero {
      conclude true or 0 < 0 by .
    }

In the second case, for `x = suc(x')`, we need to prove the following.

    unfinished proof:
        false or 0 < suc(x')

There's no hope of proving `false`, so we better prove `0 < suc(x')`.
Thankfully that follows from the definitions of `<` and `≤`.

    case suc(x') {
      have z_l_sx: 0 < suc(x') by definition {operator <, operator ≤}.
      conclude suc(x') = 0 or 0 < suc(x') by z_l_sx
    }

Here is the completed proof that every natural number is either zero
or positive.

```{.deduce #zero_or_positive}
theorem zero_or_positive: all x:Nat. x = 0 or 0 < x
proof
  arbitrary x:Nat
  switch x {
    case zero {
      conclude true or 0 < 0 by .
    }
    case suc(x') {
      have z_l_sx: 0 < suc(x') by definition {operator <, operator ≤}.
      conclude suc(x') = 0 or 0 < suc(x') by z_l_sx
    }
  }
end
```

To summarize this section:
* Use `switch` on an entity of union type to split the proof into
  cases, with one case for each alternative of the union.

## Reasoning about `some` (Exists)

In Deduce, you can express that there is at least one entity that
satisfies a given property using the `some` formula.  For example, one
way to define an even number is to say that it is a number that is 2
times some other number. We express this in Deduce as follows.

    define Even : fn Nat -> bool = λ n { some m:Nat. n = 2 * m }

As an example of how to reason about `some` formulas, let us prove a
classic property of the even numbers, that the addition of two even
numbers is an even number. Here's the beginning of the proof.

    theorem addition_of_evens:
      all x:Nat, y:Nat.
      if Even(x) and Even(y) then Even(x + y)
    proof
      arbitrary x:Nat, y:Nat
      suppose even_xy: Even(x) and Even(y)
      have even_x: some m:Nat. x = 2 * m by definition Even in even_xy
      have even_y: some m:Nat. y = 2 * m by definition Even in even_xy
      ?
    end

The next step in the proof is to make use of the facts `even_x` and `even_y`.
We can make use of a `some` formula using the `obtain` statement of Deduce.

    obtain a where x_2a: x = 2*a from even_x
    obtain b where y_2b: y = 2*b from even_y

Deduce responds with

    available facts:
        y_2b: y = 2 * b,
        x_2a: x = 2 * a,

The `a` and `b` are new variables and the two facts `y_2b` and `x_2a`
are the subformulas of the `some`, but with `a` and `b` replacing `m`.

We still need to prove the following:

    unfinished proof:
        Even(x + y)

So we use the definition of `Even`

    definition Even
    ?

and now we need to prove

    unfinished proof:
        some m:Nat. x + y = 2 * m

To prove a `some` formula, we use Deduce's `choose` statement.  This
requires some thinking on our part.  What number can we plug in for
`m` such that doubling it is equal to `x + y`? Given what we know
about `a` and `b`, the answer is `a + b`. We conclude the proof
by using the equations for `x` and `y` and the distributivity
property of multiplication over addition (from `Nat.pf`).

    choose a + b
    rewrite x_2a | y_2b
    conclude (2 * a) + (2 * b) = 2 * (a + b) by symmetric dist_mult_add[2][a,b]

Here is the complete proof.

```{.deduce #addition_of_evens}
theorem addition_of_evens:
  all x:Nat, y:Nat.
  if Even(x) and Even(y) then Even(x + y)
proof
  arbitrary x:Nat, y:Nat
  suppose even_xy: Even(x) and Even(y)
  have even_x: some m:Nat. x = 2 * m by definition Even in even_xy
  have even_y: some m:Nat. y = 2 * m by definition Even in even_xy
  obtain a where x_2a: x = 2*a from even_x
  obtain b where y_2b: y = 2*b from even_y
  definition Even
  suffices some m:Nat. x + y = 2 * m
  choose a + b
  rewrite x_2a | y_2b
  conclude (2 * a) + (2 * b) = 2 * (a + b) by symmetric dist_mult_add[2][a,b]
end
```

To summarize this section:
* The `some` formula expresses that a property is true for at least one entity.
* Deduce's `obtain` statement lets you make use of a fact that is a `some` formula.
* To prove a `some` formula, use Deduce's `choose` statement.

<!--
```{.deduce file=ProofIntro.pf}
import FunctionalProgramming

<<length_empty>>
<<length_node42>>

theorem append_12: 
  append(node(1,empty), node(2, empty)) = node(1,node(2,empty))
proof
  definition {append, append}.
end

<<length_one_nat>>
<<length_node42_again>>
<<length_one>>
<<length_one_equal>>

theorem append_xy: all T:type, x:T, y:T.
  append(node(x,empty), node(y, empty)) = node(x,node(y,empty))
proof
  definition {append, append}.
end

theorem append_12_again: 
  append(node(1,empty), node(2, empty)) = node(1,node(2,empty))
proof
  append_xy[Nat, 1, 2]
end

<<append_empty>>
<<append_empty_eqn>>

theorem length_append: all U :type. all xs :List<U>. all ys :List<U>.
  length(append(xs, ys)) = length(xs) + length(ys)
proof
  arbitrary U :type
  enable {length, append, operator +, operator +}
  induction List<U>
  case empty {
    arbitrary ys:List<U>
    conclude length(append(empty,ys)) = length(empty) + length(ys)  by .
  }
  case node(n, xs') suppose IH {
    arbitrary ys :List<U>
    equations
      length(append(node(n,xs'),ys))
          = 1 + length(append(xs', ys))        by .
      ... = 1 + (length(xs') + length(ys))     by rewrite IH[ys].
      ... = length(node(n,xs')) + length(ys)   by .
  }
end

theorem right_cancel: all z:Nat. all x:Nat, y:Nat.
  if x + z = y + z then x = y
proof
  induction Nat
  case 0 {
    arbitrary x:Nat, y:Nat
	rewrite add_zero[x] | add_zero[y]
	suppose x_y
	conclude x = y by x_y
  }
  case suc(z') suppose IH {
    arbitrary x:Nat, y:Nat
	rewrite add_commute[x][suc(z')] | add_commute[y][suc(z')]
	definition operator+
	suppose szx_eq_szy
	have zx_eq_zy: z' + x = z' + y
	  by injective suc szx_eq_szy
	conclude x = y  by apply IH[x,y] to
	  rewrite add_commute[z'][x] | add_commute[z'][y] in zx_eq_zy
  }
end

<<positive_1_and_2>>
<<positive_2>>
<<dichotomy>>
<<filter>>
<<filter_all>>
<<really_trivial>>
<<contra_false>>
<<false_any>>
<<less_irreflexive>>
<<zero_or_positive>>
<<addition_of_evens>>
```
-->
