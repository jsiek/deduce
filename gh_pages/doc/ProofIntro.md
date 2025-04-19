# Writing Proofs in Deduce

This section provides a tutorial on writing proofs in Deduce.  This
section relies on concepts that were introduced in the section on
[Programming in Deduce](./FunctionalProgramming.md), so if you have
not yet read that, please do. In the following subsections we
introduce the features of the Deduce proof language and provide
examples of their use.

* [Expanding Definitions in the Goal](#expanding-definitions-in-the-goal)
* [Generalizing with `all` formulas](#generalizing-with-all-formulas)
* [Replace equals for equals in goal](#replace-equals-for-equals-in-goal)
* [Reasoning about Natural Numbers](#reasoning-about-natural-numbers)
* [Proving Intermediate Facts with `have`](#proving-intermediate-facts-with-have)
* [Chaining Equations with `equations`](#chaining-equations-with-equations)
* [Proving `all` Formulas with Induction](#proving-all-formulas-with-induction)
* [Reasoning about `and` (Conjunction)](#reasoning-about-and-conjunction)
* [Reasoning about `or` (Disjunction)](#reasoning-about-or-disjunction)
* [The `switch` Proof Statement](#the-switch-proof-statement)
* [Conditional Formulas (Implication) and Applying Definitions to Facts](#conditional-formulas-implication-and-applying-definitions-to-facts)
* [Reasoning about `true`](#reasoning-about-true)
* [Reasoning about `false`](#reasoning-about-false)
* [Reasoning about `not`](#reasoning-about-not)
* [Replacing equals for equals in facts](#replacing-equals-for-equals-in-facts)
* [Reasoning about `some` (Exists) and asking for `help`](#reasoning-about-some-exists-and-asking-for-help)

## Expanding Definitions in the Goal

We begin with a simple example, proving that the length of an empty
list is `0`. Of course, this is a direct consequence of the definition
of `length`, so this first example is about how to use definitions.
We will be using features from the Deduce `Nat` and `List` libraries,
so first we import them.

```{.deduce^#import_nat_and_list}
import Nat
import List
```

To get started, we write down the theorem we would like to prove.  A
theorem starts with a label, followed by a colon, then the formula
followed by the proof. But instead of writing the proof, we'll simply
write `?` to say that we're not done yet. (Recall that `[]` is the
notation for an empty list (which is a generic) and `@...<Nat>` is the
notation for instantiating a generic at a particular type.)

    theorem length_nat_empty: length(@[]<Nat>) = 0
    proof
      ?
    end

Run Deduce on the file. Deduce will respond with the following message
to remind us of what is left to prove.

    incomplete proof
    Goal:
        length(@[]<Nat>) = 0
    
To tell Deduce to expand the definition of `length`, we can use
the `expand` statement.

    theorem length_nat_empty: length(@[]<Nat>) = 0
    proof
      expand length
      ?
    end

Deduce responds with the following message.

    incomplete proof
    Goal:
        true
    Advice:
        You can prove "true" with a period.

Deduce expanded the definition of `length` in the goal, changing
`length([]) = 0` to `0 = 0`. In particular, Deduce noticed that
`length([])` matches the first clause in the definition of `length`
and then replaced it with the right-hand side of the first
clause. Deduce then simplified `0 = 0` to `true`. In general, whenever
Deduce sees an equality with the same left and right-hand side, it
automatically simplifies it to `true`. 

We can complete the proof by adding a period, which is the proof of
`true`.

```{.deduce^#length_nat_empty}
theorem length_nat_empty: length(@[]<Nat>) = 0
proof
  expand length.
end
```

Run Deduce on the file to see it respond that the file is valid.

Let's try a slightly more complex theorem, that the length of a list
with just a single node is indeed `1`. Based on what we learned above,
we might try using the definition of `length`.

    theorem length_node42: length([42]) = 1
    proof
      expand length
      ?
    end

Deduce responds with

    incomplete proof
    Goal:
        1 + length(@[]<Nat>) = 1

It is quite common to expand a definition and then need to prove the
remaining goal. We need to expand the definition of `length` again to
simplify `length(@[]<Nat>)`, so we add another `length` to the `expand`
statement.

    theorem length_node42: length([42]) = 1
    proof
      expand length | length
      ?
    end

Deduce responds this time with

    incomplete proof
    Goal:
        1 + 0 = 1

We can make our proofs more readable by documenting the current goal at regular
intervals within the proof. We document the current goal with a `show` statment.

    theorem length_node42: length([42]) = 1
    proof
      expand length | length
      show 1 + 0 = 1
      ?
    end

Finally we prove `1 + 0 = 1` using the `add_zero` theorem from the
file `Nat.pf`, which we explain in the upcoming section on [Reasoning
about Natural Numbers](#reasoning-about-natural-numbers).


```{.deduce^#length_node42}
theorem length_node42: length([42]) = 1
proof
  expand length | length
  show 1 + 0 = 1
  add_zero[1]
end
```


### Exercise

Prove that `[1] ++ [2] = [1, 2]`
by filling in the `?` below.


```{.deduce^#append_node_1_node_2}
theorem append_node_1_node_2:
  [1] ++ [2] = [1, 2]
proof
  ?
end
```

## Generalizing with `all` formulas

In the proof of `length_node42` it did not matter that the element in
the node was `42`. We can generalize this theorem by using an `all`
formula. We begin the formula with `all x:Nat.` to say that the
formula must be true for all natural numbers and the variable `x` will
be used to refer to the natural number.  We then replace the `42` in
the formula with `x` to obtain the following theorem statement.

    theorem length_nat_one: all x:Nat. length([x]) = 1
    proof
      ?
    end

Deduce responds with

    incomplete proof:
        all x:Nat. length([x]) = 1

The most straightforward way to prove an `all` formula in Deduce is
with an `arbitrary` statement. When you use `arbitrary` you are
promising to prove the formula for a hypothetical entity that can
stand in for all entities of the specified type. The `arbitrary`
statement asks you to name the hypothetical entity. Here we choose `x`
but we could have chosen a different name.

    theorem length_nat_one: all x:Nat. length([x]) = 1
    proof
      arbitrary x:Nat
      ?
    end

Deduce responds with

    incomplete proof:
        length([x]) = 1

We don't know anything about this hypothetical `x` other than it being
a natural number. But as we previously observed, we don't need any
more information about `x` in this example.  We complete the proof as
before, using the definitions of `length` and the `add_zero` theorem.
The notation `2* length` is shorthand for `length | length`.

```{.deduce^#length_nat_one}
theorem length_nat_one: all x:Nat. length([x]) = 1
proof
  arbitrary x:Nat
  expand 2* length
  show 1 + 0 = 1
  add_zero[1]
end
```

Once we have proved that an `all` formula is true, we can use it by
supplying an entity of the appropriate type inside square brackets. In
the following we prove the `length_node42` theorem again, but this
time the proof makes use of `length_nat_one`.


```{.deduce^#length_node42_again}
theorem length_node42_again: length([42]) = 1
proof
  length_nat_one[42]
end
```

We can generalize the theorem yet again by noticing that it does not
matter whether the element is a natural number. It could be a value of
any type. In Deduce we can also use the `all` statement to generalize
types. In the following, we add `all U:type` to the formula and 
another `arbitrary` statement.


```{.deduce^#list_length_one}
theorem list_length_one: all U:type. all x:U. length([x]) = 1
proof
  arbitrary U:type
  arbitrary x:U
  expand 2* length
  show 1 + 0 = 1
  add_zero[1]
end
```

To summarize this section:

* To state that a formula is true for all entities of a given type, use Deduce's `all` formula.
* To prove that an `all` formula is true, use Deduce's `arbitrary` statement. (We'll see a second method in the section [Proving `all` Formulas with Induction](#proving-all-formulas-with-induction).)
* To use a fact that is an `all` formula, instantiate the fact by following it with square brackets around the specific entity.

### Exercise

Complete the following proof.

```{.deduce^#append_node_x_node_y}
theorem append_xy:
  all T:type. all x:T, y:T. [x] ++ [y] = [x, y]
proof
  ?
end
```

Prove again that 

```
[1] ++ [2] = [1, 2]
```

but this time use the previous theorem.


## Replace equals for equals in goal

Deduce provides the `replace` statement to apply an equation to the
current goal. In particular, `replace` replaces each occurrence of the
left-hand side of an equation with the right-hand side of the
equation.

For example, let us prove the following theorem using `replace`
with the above `list_length_one` theorem.

```
theorem list_length_one_equal: all U:type. all x:U, y:U.
  length([x]) = length([y])
proof
  arbitrary U:type
  arbitrary x:U, y:U
  ?
end
```

To replace `length([x])` with `1`, we `replace`
using the `list_length_one` theorem instantiated at `U` and `x`,
i.e., we are replacing using the following equation.

```
length([x]) = 1
```

Note that we use `<` and `>` when instantiating a type parameter
and we use `[` and `]` when instantiating a term parameter.

```
replace list_length_one<U>[x]
```

Deduce tells us that the current goal has become

```
remains to prove:
    1 = length([y])
```

We `replace` again, separated by a vertical bar, using `list_length_one`,
this time instantiated with `y`.

```
replace list_length_one<U>[x] | list_length_one<U>[y]
```

Deduce changes the goal to `1 = 1`, which simplifies to `true`.
So we finish the proof with a period.

Here is the completed proof of `list_length_one_equal`.


```{.deduce^#list_length_one_equal}
theorem list_length_one_equal: all U:type. all x:U, y:U.
  length([x]) = length([y])
proof
  arbitrary U:type
  arbitrary x:U, y:U
  replace list_length_one<U>[x] | list_length_one<U>[y].
end
```


## Reasoning about Natural Numbers

The `Nat.pf` file includes the definition of natural numbers,
operations on them (e.g. addition), and proofs about those
operations. Also, Deduce automatically generates a summary of the
theorems and puts them in the file `Nat.thm`.

Here we discuss how to reason about addition. Reasoning
about the other operations follows a similar pattern.

Here is the definition of natural numbers from `Nat.pf`:

```{.deduce}
union Nat {
  zero
  suc(Nat)
}
```

The parser for Deduce translates `0` into `zero`,
`1` into `suc(zero)`, `2` into `suc(suc(zero))`, and so on.


Here is the definition of addition from `Nat.pf`:

```{.deduce}
recursive operator +(Nat,Nat) -> Nat {
  operator +(0, m) = m
  operator +(suc(n), m) = suc(n + m)
}
```

Recall that we can use Deduce's `expand` statement whenever we
want to change the goal according to the equations for addition. Here
are the two defining equations, but written with infix notation:

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
left_cancel: all x:Nat. all y:Nat, z:Nat.  if x + y = x + z then y = z
add_to_zero: all n:Nat. all m:Nat. if n + m = 0 then n = 0 and m = 0
dist_mult_add: all a:Nat. all x:Nat, y:Nat. a * (x + y) = a * x + a * y
mult_zero: all n:Nat. n * 0 = 0
mult_one: all n:Nat. n * 1 = n
mult_commute: all m:Nat. all n:Nat. m * n = n * m
```

You can use these theorems by instantiating them with particular
entities. For example, `add_zero[2]` is a proof of `2 + 0 = 2`.
We have not yet discussed how to use the `if`-`then` formula in
`left_cancel`, but we will get to that in the section below on
[Conditional Formulas (Implication)](#conditional-formulas-implication-and-applying-definitions-to-facts).

### Exercise

Prove the following theorem using the `add_zero` and `mult_one`
theorems from `Nat.pf`.


```{.deduce^#x_0_x_eq_2_x}
theorem x_0_x_eq_2_x: 
  all x:Nat. (x + 0) + x = (x + x) * 1
proof
  ?
end
```

## Proving Intermediate Facts with `have`

One often needs to prove some intermediate facts on the way to proving
the final goal of a theorem. The `have` statement of Deduce provides a
way to state and prove a fact and give it a label so that it can be
used later in the proof. For example, consider the proof of

```
x + y + z = z + y + x
```

It takes several uses of `add_commute` to prove this.
To get started, we use `have` to give the label `step1` to a proof of
`x + y + z = x + z + y` (flipping the `y` and `z`).

```
theorem xyz_zyx: all x:Nat, y:Nat, z:Nat.
  x + y + z = z + y + x
proof
  arbitrary x:Nat, y:Nat, z:Nat
  have step1: x + y + z = x + z + y
    by replace add_commute[y,z].
  ?
end
```

Deduce prints the current goal and the **givens**, that is, the formulas
that we already know are true, which now includes `step1`.

```
incomplete proof
Goal:
    x + y + z = z + y + x
Givens:
    step1: x + y + z = x + z + y
```

We proceed four more times, using `have` to create each intermediate
step in the reasoning.

```
  have step2: x + z + y = z + x + y
    by replace add_commute[z,x].
  have step3: z + x + y = z + y + x
    by replace add_commute[x,y].
```

We finish the proof by connecting them all together using Deduce's
`transitive` statement. The `transitive` statement takes two proofs of
equations `a = b` and `b = c`, and proves `a = c`. Here we use the
intermediate facts `step1`, `step2`, etc. by referencing their
label. In general, to use one of the given facts, one just needs to
use its label.

```
  transitive step1 (transitive step2 step3)
```

Here is the complete proof of the `xyz_zyx` theorem.


```{.deduce^#xyz_zyx}
theorem xyz_zyx: all x:Nat, y:Nat, z:Nat.
  x + y + z = z + y + x
proof
  arbitrary x:Nat, y:Nat, z:Nat
  have step1: x + y + z = x + z + y
    by replace add_commute[y,z].
  have step2: x + z + y = z + x + y
    by replace add_commute[z,x].
  have step3: z + x + y = z + y + x
    by replace add_commute[x,y].
  transitive step1 (transitive step2 step3)
end
```

## Chaining Equations with `equations`

Combining a sequence of equations using `transitive` is quite common,
so Deduce provides the `equations` statement to streamline this
process.  After the first equation, the left-hand side of each
equation is written as `...` because it is just a repetition of the
right-hand side of the previous equation. Let's write another proof of
the theorem about `x + y + z`, this time using an `equations`
statement. We can start by just restating the goal inside `equations`
and use `?` for the reason.

```
theorem xyz_zyx_eqn: all x:Nat, y:Nat, z:Nat.
  x + y + z = z + y + x
proof
  arbitrary x:Nat, y:Nat, z:Nat
  equations
    x + y + z = z + y + x      by ?
end
```

The first step is to commute `y + z` to `z + y`. If we're feeling
extra lazy, we can use `?` for the new right-hand side and the
error from Deduce will tell us what it needs to be.

```
  equations
    x + y + z = ?              by replace add_commute[y,z] ?
          ... = z + y + x      by ?
```

Deduce responds with:

```
incomplete proof
Goal:
	x + z + y = ?
```

So we replace the `?` on the right-hand side of the `=` with `x + z + y`
and replace the `?` at the end of the line with a period.
Continuing in this way for several more steps, we incrementally arrive
at the following proof that `x + y + z = z + y + x` using `equations`.

```{.deduce^#xyz_zyx_eqn}
theorem xyz_zyx_eqn: all x:Nat, y:Nat, z:Nat.
  x + y + z = z + y + x
proof
  arbitrary x:Nat, y:Nat, z:Nat
  equations
    x + y + z = x + z + y    by replace add_commute[y,z].
          ... = z + x + y    by replace add_commute[x,z].
          ... = z + y + x    by replace add_commute[x,y].
end
```

If you want to skip the proof of one of the earlier steps, you can use
[`sorry`](./Reference.md#sorry-proof) for the reason.

If you want to work backwards by transforming the right-hand side of
an equation into the left-hand side using `replace` or `expand`,
then [mark](./Reference.md#mark) the right-hand side.

The `equations` feature is implemented in Deduce by translating into a
bunch of `transitive` statements.


## Proving `all` Formulas with Induction

Sometimes the `arbitrary` statement does not give us enough
information to prove an `all` formula. In those situations, so long as
the type of the `all` variable is a `union` type, we can use the more
powerful `induction` statement.

For example, consider the following theorem about appending a list to
an empty list. Suppose we try to use `arbitrary` for both the
`all U` and the `all xs`.

    theorem list_append_empty: all U :type. all xs :List<U>.
      xs ++ [] = xs
    proof
      arbitrary U:type
      arbitrary xs:List<U>
      ?
    end

Deduce replies that we need to prove

    incomplete proof:
        xs ++ [] = xs

But now we're stuck because the definition of append pattern matches
on its first argument, but we don't know whether `xs` is an `empty`
list or a `node`.

So instead of using `arbitrary xs:List<U>` to prove the `all xs`, we
proceed by induction as follows.

    theorem list_append_empty: all U :type. all xs :List<U>.
      xs ++ [] = xs
    proof
      arbitrary U:type
      induction List<U>
      case empty {
        ?
      }
      case node(n, xs') assume IH: xs' ++ [] = xs' {
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

    incomplete proof:
        [] ++ [] = []

This follows directly from the definition of append.

    case empty {
      expand operator++.
    }

However, to make the proof more readable by other humans, I recommend
restating the goal using the `conclude` statement.

    case empty {
      conclude @[]<U> ++ [] = []  by expand operator++.
    }

Next let us focus on the case for `node`. Deduce tells us that we need
to prove the following and that `IH` has been added to the available
facts.

    incomplete proof:
        node(n,xs') ++ [] = node(n,xs')

    available facts:
        IH: xs' ++ [] = xs',
        ...

Looking at the goal, we notice that we can expand the definition of
`++` on the right-hand side, because it is applied to a `node`.
Perhaps we forget the exact definition of `++`, so we can let
Deduce tell us the expansion by putting `?` on the right-hand side of
the equation.

    case node(n, xs') assume IH: xs' ++ [] = xs' {
      equations
        node(n,xs') ++ []
            = ?                       by expand operator++.
        ... = node(n,xs')             by ?
    }

Deduce responds with

    remains to prove:
        node(n, xs' ++ []) = ?

It has transformed the left-hand side of the equation by expanding the
definition of `++`.  We copy and paste the `node(n, xs' ++ empty)` to
replace the `?`.

    case node(n, xs') assume IH: xs' ++ [] = xs' {
      equations
        node(n,xs') ++ []
            = node(n, xs' ++ [])   by expand operator++.
        ... = node(n,xs')          by ?
    }

Next, we see that the subterm `xs' ++ []` matches the
right-hand side of the induction hypothesis `IH`. We use the
`replace` statement to apply the `IH` equation to this subterm.

    case node(n, xs') assume IH: xs' ++ [] = xs' {
      equations
        node(n,xs') ++ []
            = node(n, xs' ++ [])   by expand operator++.
        ... = node(n,xs')          by replace IH.
    }

Here is the completed proof of `list_append_empty`.


```{.deduce^#list_append_empty}
theorem list_append_empty: all U :type. all xs :List<U>.
  xs ++ [] = xs
proof
  arbitrary U:type
  induction List<U>
  case empty {
    conclude @[]<U> ++ [] = []  by expand operator++.
  }
  case node(n, xs') assume IH: xs' ++ [] = xs' {
    equations
      node(n,xs') ++ []
          = node(n, xs' ++ [])     by expand operator++.
      ... = node(n,xs')            by replace IH.
  }
end
```

To summarize this section:

* To prove an `all` formula that concerns entities of a `union` type,
  use Deduce's `induction` statement.

### Exercise

Fill in the proof of the following theorem about `length` and `++`.


```{.deduce^#length_append}
theorem length_append: all U :type. all xs :List<U>. all ys :List<U>.
  length(xs ++ ys) = length(xs) + length(ys)
proof
  ?
end
```

## Reasoning about `and` (Conjunction)

To create a single formula that expresses that two formulas are true,
combine the two formulas with `and` (i.e. conjunction). The following
example proves that `0 ≤ 1 and 0 ≤ 2`.  This is accomplished by
separately proving that `0 ≤ 1` is true and that `0 ≤ 2` is true, then
using the comma operator to combine those proofs: `one_pos, two_pos`.


```{.deduce^#pos_1_and_2}
theorem pos_1_and_2: 0 ≤ 1 and 0 ≤ 2
proof
  have one_pos: 0 ≤ 1 by expand operator ≤.
  have two_pos: 0 ≤ 2 by expand operator ≤.
  conclude 0 ≤ 1 and 0 ≤ 2 by one_pos, two_pos
end
```

On the other hand, in Deduce you can use a conjunction as if it were
one of its subformulas, implicitly. In the following we use the
fact that `0 ≤ 1 and 0 ≤ 2` to prove `0 ≤ 2`.


```{.deduce^#pos_2}
theorem pos_2: 0 ≤ 2
proof
  conclude 0 ≤ 2 by pos_1_and_2
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

    theorem intro_dichotomy:  all x:Nat, y:Nat.  x ≤ y  or  y < x
    proof
      ?
    end

We can prove this using the `trichotomy` theorem from `Nat.pf`,
which tells us that `x < y` or `x = y` or `y < x`.

    theorem intro_dichotomy:  all x:Nat, y:Nat.  x ≤ y  or  y < x
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
can prove that `x ≤ y` by replacing the `x` with `y` and then using the
reflexive property of the less-equal relation to prove that `y ≤ y`.

    case x_eq_y: x = y {
      have x_le_y: x ≤ y by
          suffices y ≤ y  by replace x_eq_y.
          less_equal_refl[y]
      conclude x ≤ y or y < x by x_le_y
    }

In the third case, we consider the situation where `y < x`.
So we can immediately conclude that `x ≤ y or y < x`.

    case y_l_x: y < x {
      conclude x ≤ y or y < x by y_l_x
    }

Here is the completed proof of the `intro_dichotomy` theorem.


```{.deduce^#intro_dichotomy}
theorem intro_dichotomy:  all x:Nat, y:Nat.  x ≤ y  or  y < x
proof
  arbitrary x:Nat, y:Nat
  have tri: x < y or x = y or y < x by trichotomy[x][y]
  cases tri
  case x_l_y: x < y {
    have x_le_y: x ≤ y by apply less_implies_less_equal[x][y] to x_l_y
    conclude x ≤ y or y < x by x_le_y
  }
  case x_eq_y: x = y {
    have x_le_y: x ≤ y by
        suffices y ≤ y  by replace x_eq_y.
        less_equal_refl[y]
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

## The `switch` Proof Statement

Similar to Deduce's `switch` statement for writing functions, there is
also a `switch` statement for writing proofs. As an example, let us
consider how to prove the following theorem.

    theorem intro_zero_or_positive: all x:Nat. x = 0 or 0 < x
    proof
      ?
    end

We could proceed by induction, but it turns out we don't need the
induction hypothesis. In such situations, we can instead use `switch`.
Like induction, `switch` works on unions and there is one case for
each alternative of the union. Unlike induction, the goal formula does
not need to be an `all` formula. Instead, you indicate which entity to
switch on, as in `switch x` below.

    arbitrary x:Nat
    switch x {
      case 0 assume xz: x = 0 {
        ?
      }
      case suc(x') assume xs: x = suc(x') {
        ?
      }
    }

Deduce responds that in the first case we need to prove the following.

    incomplete proof:
        true or 0 < 0

So we just need to prove `true`, which is what the period is for.

    case 0 assume xz: x = 0 {
      conclude true or 0 < 0 by .
    }

In the second case, for `x = suc(x')`, we need to prove the following.

    incomplete proof:
        false or 0 < suc(x')

There's no hope of proving `false`, so we better prove `0 < suc(x')`.
Thankfully that follows from the definitions of `<` and `≤`.

    case suc(x') assume xs: x = suc(x') {
      have z_l_sx: 0 < suc(x') by expand operator < | operator ≤.
      conclude suc(x') = 0 or 0 < suc(x') by z_l_sx
    }

Here is the completed proof that every natural number is either zero
or positive.


```{.deduce^#intro_zero_or_positive}
theorem intro_zero_or_positive: all x:Nat. x = 0 or 0 < x
proof
  arbitrary x:Nat
  switch x {
    case 0 assume xz: x = 0 {
      conclude true or 0 < 0 by .
    }
    case suc(x') assume xs: x = suc(x') {
      have z_l_sx: 0 < suc(x') by expand operator < | 2* operator ≤.
      conclude suc(x') = 0 or 0 < suc(x') by z_l_sx
    }
  }
end
```

To summarize this section:

* Use `switch` on an entity of union type to split the proof into cases, with one case for each alternative of the union.

## Conditional Formulas (Implication) and Expanding Definitions in Facts

Some logical statements are true only under certain conditions, so
Deduce provides an `if`-`then` formula.  To demonstrate how to work
with `if`-`then` formulas, we prove that if a list has length zero,
then it must be the `empty` list. Along the way we will also learn how
to expand a definition in an already-known fact.

```
theorem list_length_zero_empty: all T:type. all xs:List<T>.
  if length(xs) = 0 then xs = []
proof
  arbitrary T:type
  arbitrary xs:List<T>
  ?
end
```

Deduce tells us:

```
incomplete proof
Goal:
    (if length(xs) = 0 then xs = [])
```

To prove an `if`-`then` formula, we `assume` the condition and then
prove the conclusion.

```
  assume len_z: length(xs) = 0
```

Deduce adds `len_z` to the givens (similar to `have`).

```
incomplete proof
Goal:
    xs = []
Givens:
    len_z: length(xs) = 0
```

Next we `switch` on the list `xs`. In the case when `xs` is `empty` it
will be trivial to prove `xs = []`. In the other case, we will
obtain a contradiction.

```
  switch xs {
    case empty { . }
    case node(x, xs') assume xs_xxs: xs = node(x,xs') {
      ?
    }
  }
```

We can put the facts `len_z` and `xs_xxs` together
to obtain the dubious looking `length(node(x,xs')) = 0`.

```
    have len_z2: length(node(x,xs')) = 0  by replace xs_xxs in len_z
```

The contradiction becomes apparent to Deduce once we expand the
definition of `length` and `operator+` in this fact. We do so using
Deduce's `expand`-`in` statement as follows.

```
    have len_z3: suc(length(xs')) = 0
      by expand length | operator+ in len_z2
```

When Deduce sees an equality with different constructors on the left
and right-hand sides, it automatically simplies the formula to
`false`.

```
    conclude false  by len_z3
```

We discuss contradictions and `false` in more detail in the upcoming
section [Reasoning about `false`](#reasoning-about-false).

Here is the complete proof of `list_length_zero_empty`.


```{.deduce^#list_length_zero_empty}
theorem list_length_zero_empty: all T:type. all xs:List<T>.
  if length(xs) = 0 then xs = []
proof
  arbitrary T:type
  arbitrary xs:List<T>
  assume len_z: length(xs) = 0
  switch xs {
    case empty { . }
    case node(x, xs') assume xs_xxs: xs = node(x,xs') {
      have len_z2: length(node(x,xs')) = 0  by replace xs_xxs in len_z
      have len_z3: suc(length(xs')) = 0
        by expand length | operator+ in len_z2
      conclude false  by len_z3
    }
  }
end
```

The next topic to discuss is how to use an `if`-`then` fact that is
already proven.  We use Deduce's `apply`-`to` statement (aka. modus
ponens) to obtain the conclusion of an `if`-`then` formula by
supplying a proof of the condition.  We demonstrate several uses of
`apply`-`to` in the proof of the following theorem, which builds on
`list_length_zero_empty`.

```
theorem length_append_zero_empty: all T:type. all xs:List<T>, ys:List<T>.
  if length(xs ++ ys) = 0
  then xs = [] and ys = []
proof
  arbitrary T:type
  arbitrary xs:List<T>, ys:List<T>
  assume len_xs_ys: length(xs ++ ys) = 0
  ?
end
```

Recall that in a previous exercise, you proved that

```
length(xs ++ ys) = length(xs) + length(ys)
```

so we can prove that `length(xs) + length(ys) = 0` as follows.

```
  have len_xs_len_ys: length(xs) + length(ys) = 0
    by transitive (symmetric length_append<T>[xs][ys]) len_xs_ys
```

Note that Deduce's the `symmetric` statement takes a proof
of some equality like `a = b` and flips it around to `b = a`.

Now from `Nat.pf` we have the following `if`-`then` fact.

```
add_to_zero: all n:Nat. all m:Nat. if n + m = 0 then n = 0 and m = 0
```

Here is our first use of `apply`-`to` to obtain `length(xs) = 0` and
the same for `ys`. (Deduce can infer the arguments for the `all n` and `all m`
in `add_to_zero`.)

```
  have len_xs: length(xs) = 0  by apply add_to_zero to len_xs_len_ys
  have len_ys: length(ys) = 0  by apply add_to_zero to len_xs_len_ys
```

We conclude that `xs = empty and ys = empty` with our second use of
`apply`-`to`, where we make use of the previous theorem
`list_length_zero_empty`.

```
  conclude xs = empty and ys = empty
  by (apply list_length_zero_empty<T>[xs] to len_xs),
     (apply list_length_zero_empty<T>[ys] to len_ys)
```

Here is the complete proof of `length_append_zero_empty`.


```{.deduce^#length_append_zero_empty}
theorem length_append_zero_empty: all T:type. all xs:List<T>, ys:List<T>.
  if length(xs ++ ys) = 0
  then xs = [] and ys = []
proof
  arbitrary T:type
  arbitrary xs:List<T>, ys:List<T>
  assume len_xs_ys: length(xs ++ ys) = 0
  have len_xs_len_ys: length(xs) + length(ys) = 0
    by transitive (symmetric length_append<T>[xs][ys]) len_xs_ys
  have len_xs: length(xs) = 0  by apply add_to_zero to len_xs_len_ys
  have len_ys: length(ys) = 0  by apply add_to_zero to len_xs_len_ys
  conclude xs = [] and ys = []
  by (apply list_length_zero_empty<T>[xs] to len_xs),
     (apply list_length_zero_empty<T>[ys] to len_ys)
end
```

To summarize this section:

* A conditional formula is stated in Deduce using the `if`-`then` syntax.
* To prove an `if`-`then` formula, `assume` the condition and prove the conclusion.
* To use a fact that is an `if`-`then` formula, `apply` it `to` a proof of the condition.
* To expand a definition in a fact, use `expand`-`in`.

### Exercise

Prove that `all x:Nat. if x ≤ 0 then x = 0`.

## Reasoning about `true`

There's not much to say about `true`. It's true!  And as we've already
seen, proving `true` is easy. Just use a period.


```{.deduce^#really_trivial}
theorem really_trivial: true
proof
  .
end
```

One almost never sees `true` written explicitly in a formula. However,
it is common for a complex formula to simplify to `true`.

## Reasoning about `false`

The formula `false` is also rarely written explicitly in a formula.
However, it can arise in contradictory situations. For example,
in the following we have a situation in which `true = false`.
That can't be, so Deduce simplifies `true = false` to just `false`.


```{.deduce^#contra_false}
theorem contra_false: all a:bool, b:bool.
  if a = b and a = true and b = false then false
proof
  arbitrary a:bool, b:bool
  assume prem: a = b and a = true and b = false
  have a_true: a = true by prem
  have b_true: b = false by prem
  conclude false by replace a_true | b_true in prem
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


```{.deduce^#false_any}
theorem false_any: all x:bool, y:bool. if false then x = y
proof
  arbitrary x:bool, y:bool
  assume f: false
  conclude x = y by f
end
```

To summarize this section:

* Deduce simplifies any obviously contradictory equation to `false`.
* `false` implies anything.

## Reasoning about `not`

To express that a formula is false, precede it with `not`.  For
example, for any natural number `x`, it is not the case that `x < x`.

    theorem intro_less_irreflexive:  all x:Nat. not (x < x)
    proof
      ?
    end

We proceed by induction.

    induction Nat
    case zero {
      ?
    }
    case suc(x') assume IH: not (x' < x') {
      ?
    }

Deduce treats `not` as syntactic sugar for a conditional formula with a
`false` conclusion. So in the first case, we must prove 
that `0 < 0` implies `false`.
So we `assume` the premise `0 < 0` and then conclude `false` by the
definitions of `<` and `≤`.

    case zero {
      assume z_l_z: 0 < 0
      conclude false by expand operator < | operator ≤ in z_l_z
    }

In the case where `x = suc(x')`, we must prove 
that `suc(x') < suc(x')` implies `false`.
So we assume the premise `suc(x') < suc(x')` from which we
can prove that `x' < x'` using the definitions of `<` and `≤`.

    assume sx_l_sx: suc(x') < suc(x')
    have x_l_x: x' < x' by apply less_suc_iff_suc_less to sx_l_sx

We conclude this case by applying the induction hypothesis to `x' < x'`.

    conclude false by apply IH to x_l_x

Here is the completed proof that less-than is irreflexive.


```{.deduce^#intro_less_irreflexive}
theorem intro_less_irreflexive:  all x:Nat. not (x < x)
proof
  induction Nat
  case zero {
    assume z_l_z: 0 < 0
    conclude false by expand operator < | operator ≤ in z_l_z
  }
  case suc(x') assume IH: not (x' < x') {
    assume sx_l_sx: suc(x') < suc(x')
    have x_l_x: x' < x' by apply less_suc_iff_suc_less to sx_l_sx
    conclude false by apply IH to x_l_x
  }
end
```

To summarize this section:

* To expression that a formula is false, use `not`.
* Deduce treats the formula `not P` just like `if P then false`.
* Therefore, to prove a `not` formula, assume `P` then prove `false`.
* To use a formula like `not P`, apply it to a proof of `P` to
  obtain a proof of `false`.

## Replacing equals for equals in facts

In the section
[Replace equals for equals in goal](#replace-equals-for-equals-in-goal) 
we learned that the `replace` statement of Deduce applies an equation
to the current goal.  There is a second variant of `replace` that
applies an equation to a fact. As an example, we'll prove the
following theorem that is a straightforward use of `intro_less_irreflexive`.

```
theorem intro_less_not_equal: all x:Nat, y:Nat.
  if x < y then not (x = y)
proof
  arbitrary x:Nat, y:Nat
  assume x_l_y: x < y
  ?
end
```

Deduce responds with the current goal.

```
incomplete proof
Goal:
    not (x = y)
Givens:
    x_l_y: x < y
```

Because `not (x = y)` is equivalent to `if x = y then false`,
we follow the usual recipe to prove an `if`-`then`, that is,
we `assume` the condition `x = y`.

```
  assume x_y: x = y
```

Now we need to prove `false`, and we have the hint to use the
`intro_less_irreflexive` theorem.

```
incomplete proof
Goal:
    false
Givens:
    x_y: x = y,
    x_l_y: x < y
```

Here is where the second variant of `replace` comes in.  We can use it
to apply the equation `x = y` to the fact `x < y` to get `y < y`.
Note the extra keyword `in` that is used in this version of `replace`.

```
  have y_l_y: y < y   by replace x_y in x_l_y
```

We arrive at the contradiction by applying `intro_less_irreflexive` 
to `y < y`.

```
  conclude false by apply intro_less_irreflexive[y] to y_l_y
```

Here is the complete proof of `intro_less_not_equal`.


```{.deduce^#intro_less_not_equal}
theorem intro_less_not_equal: all x:Nat, y:Nat.
  if x < y then not (x = y)
proof
  arbitrary x:Nat, y:Nat
  assume x_l_y: x < y
  assume x_y: x = y
  have y_l_y: y < y by replace x_y in x_l_y
  conclude false by apply intro_less_irreflexive[y] to y_l_y
end
```

### Exercise

Using the `replace`-`in` statement, prove the following variation on
the transitivity theorem for `≤`. Prove that if `x = y` and `y ≤ z`,
then `x ≤ z`.


```{.deduce^#equal_less_trans}
theorem equal_less_trans: all x:Nat, y:Nat, z:Nat.
  if x = y and y ≤ z then x ≤ z
proof
  ?
end
```

## Reasoning about `some` (Exists) and asking for `help`

In Deduce, you can express that there is at least one entity that
satisfies a given property using the `some` formula.  For example, one
way to define an even number is to say that it is a number that is 2
times some other number. We express this in Deduce as follows.

    define Even = λ n:Nat { some m:Nat. n = 2 * m }

As an example of how to reason about `some` formulas, let us prove a
classic property of the even numbers, that the addition of two even
numbers is an even number. Here's the beginning of the proof.

    theorem intro_addition_of_evens:
      all x:Nat, y:Nat.
      if Even(x) and Even(y) then Even(x + y)
    proof
      arbitrary x:Nat, y:Nat
      assume even_xy: Even(x) and Even(y)
      have even_x: some m:Nat. x = 2 * m by expand Even in even_xy
      have even_y: some m:Nat. y = 2 * m by expand Even in even_xy
      ?
    end

The next step in the proof is to make use of the facts `even_x` and `even_y`.
We can ask Deduce for help in how to use a given with the `help` feature.

    help even_x
    
Deduce responds with
    
    Advice about using fact:
    some m:Nat. x = 2 * m

    Proceed with:
        obtain A where label: x = 2 * A from even_x
    where A is a new name of your choice

So we go ahead and write two `obtain` statements, one for `even_x` and
another for `even_y`, making different choices to replace the variable
`A` in the above advice.

    obtain a where x_2a: x = 2*a from even_x
    obtain b where y_2b: y = 2*b from even_y

Deduce responds with

    available facts:
        y_2b: y = 2 * b,
        x_2a: x = 2 * a,

The `a` and `b` are new variables and the two facts `y_2b` and `x_2a`
are the subformulas of the `some`, but with `a` and `b` replacing `m`.

We still need to prove the following:

    incomplete proof:
        Even(x + y)

So we use the definition of `Even` in a `suffices` statement

    suffices some m:Nat. x + y = 2 * m  by expand Even.
    ?

To prove a `some` formula, we use Deduce's `choose` statement.  This
requires some thinking on our part.  What number can we plug in for
`m` such that doubling it is equal to `x + y`? Given what we know
about `a` and `b`, the answer is `a + b`. We conclude the proof
by using the equations for `x` and `y` and the distributivity
property of multiplication over addition (from `Nat.pf`).

    choose a + b
    suffices 2 * a + 2 * b = 2 * (a + b)  by replace x_2a | y_2b.
    symmetric dist_mult_add[2][a,b]

Here is the complete proof.


```{.deduce^#intro_addition_of_evens}
theorem intro_addition_of_evens:
  all x:Nat, y:Nat.
  if Even(x) and Even(y) then Even(x + y)
proof
  arbitrary x:Nat, y:Nat
  assume even_xy: Even(x) and Even(y)
  have even_x: some m:Nat. x = 2 * m by expand Even in even_xy
  have even_y: some m:Nat. y = 2 * m by expand Even in even_xy
  obtain a where x_2a: x = 2*a from even_x
  obtain b where y_2b: y = 2*b from even_y
  suffices some m:Nat. x + y = 2 * m  by expand Even.
  choose a + b
  suffices 2 * a + 2 * b = 2 * (a + b)  by replace x_2a | y_2b.
  symmetric dist_mult_add[2][a,b]
end
```

To summarize this section:

* The `some` formula expresses that a property is true for at least one entity.
* Deduce's `obtain` statement lets you make use of a fact that is a `some` formula.
* To prove a `some` formula, use Deduce's `choose` statement.


<!--
```{.deduce^file=ProofIntro.pf}
<<import_nat_and_list>>

<<length_nat_empty>>
<<length_node42>>


theorem append_12: 
  node(1,empty) ++ node(2, empty) = node(1, node(2, empty))
proof
  expand 2* operator++.
end

<<length_nat_one>>
<<length_node42_again>>
<<list_length_one>>
<<list_length_one_equal>>

<<list_append_empty>>

<<xyz_zyx>>
<<xyz_zyx_eqn>>


<<pos_1_and_2>>
<<pos_2>>
<<intro_dichotomy>>
<<list_length_zero_empty>>
<<length_append_zero_empty>>
<<really_trivial>>
<<contra_false>>
<<false_any>>
<<intro_less_irreflexive>>
<<intro_less_not_equal>>

<<intro_zero_or_positive>>
<<intro_addition_of_evens>>
```
-->
