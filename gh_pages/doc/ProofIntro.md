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
* [Reasoning about Unsigned Integers](#reasoning-about-unsigned-integers)
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
* [Simplify the Goal](#simplify-the-goal)

## Expanding Definitions in the Goal

As a simple example of using `expand` we shall prove that the length
of an empty list is `0`. This fact is a direct consequence of the
definition of `length`, so this first example is about how to expand
definitions.  We will be using features from the Deduce usigned
integer (`UInt`) and `List` libraries, so first we import them.

```{.deduce^#import_uint_and_list}
import UInt
import List
```

To get started, we write down the theorem we would like to prove.  A
theorem starts with a label, followed by a colon, then the formula
followed by the proof. But instead of writing the proof, we'll simply
write `?` to say that we're not done yet. (Recall that `[]` is the
notation for an empty list (which is a generic) and `@...<UInt>` is the
notation for instantiating a generic at a particular type.)

    theorem length_uint_empty: length(@[]<UInt>) = 0
    proof
      ?
    end

Run Deduce on the file. Deduce will respond with the following message
to remind us of what is left to prove.

    incomplete proof
    Goal:
        length(@[]<UInt>) = 0
    
To tell Deduce to expand the definition of `length`, we can use
the `expand` statement.

    theorem length_uint_empty: length(@[]<UInt>) = 0
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

```{.deduce^#length_uint_empty}
theorem length_uint_empty: length(@[]<UInt>) = 0
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
        1 + length(@[]<UInt>) = 1

It is quite common to expand a definition and then need to prove the
remaining goal. We need to expand the definition of `length` again to
simplify `length(@[]<UInt>)`, so we add another `length` to the `expand`
statement.

    theorem length_node42: length([42]) = 1
    proof
      expand length | length
      ?
    end

Deduce responds this time with

    incomplete proof
    Goal:
        true

because the goal expanded to `1 + 0 = 1`, which of course is true.
So we can conclude the proof with a period.


```{.deduce^#length_node42}
theorem length_node42: length([42]) = 1
proof
  expand length | length.
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
formula. We begin the formula with `all x:UInt.` to say that the
formula must be true for all natural numbers and the variable `x` will
be used to refer to the natural number.  We then replace the `42` in
the formula with `x` to obtain the following theorem statement.

    theorem length_uint_one: all x:UInt. length([x]) = 1
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

    theorem length_uint_one: all x:UInt. length([x]) = 1
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
before, using the definitions of `length`.
The notation `2* length` is shorthand for `length | length`.

```{.deduce^#length_uint_one}
theorem length_uint_one: all x:UInt. length([x]) = 1
proof
  arbitrary x:UInt
  expand 2* length.
end
```

Once we have proved that an `all` formula is true, we can use it by
supplying an entity of the appropriate type inside square brackets. In
the following we prove the `length_node42` theorem again, but this
time the proof makes use of `length_uint_one`.


```{.deduce^#length_node42_again}
theorem length_node42_again: length([42]) = 1
proof
  length_uint_one[42]
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
  expand 2* length.
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


## Reasoning about Unsigned Integers

The `UInt.pf` file includes the definition of unsigned integers,
operations on them (e.g. addition), and proofs about those
operations. Also, Deduce automatically generates a summary of the
theorems and puts them in the file `UInt.thm`. Here is sample
of those theorems.

```
uint_add_zero: all n:UInt.  n + 0 = n
uint_add_commute: all n:UInt. all m:UInt.  n + m = m + n
uint_add_to_zero: all n:UInt. all m:UInt. if n + m = 0 then n = 0 and m = 0
uint_dist_mult_add: all a:UInt. all x:UInt, y:UInt. a * (x + y) = a * x + a * y
uint_mult_zero: all n:UInt. n * 0 = 0
uint_mult_one: all n:UInt. n * 1 = n
uint_mult_commute: all m:UInt. all n:UInt. m * n = n * m
uint_less_trans: all x:UInt, y:UInt, z:UInt. if (x < y and y < z) then x < z
```

You can use these theorems by instantiating them with particular
entities. For example, `uint_add_commute[a,b]` is a proof of `a + b = b + a`.
Some of these theorems (the ones declared `auto`)
are applied automatically by Deduce as it simplifies
a formula, such as `uint_add_zero`. The `commute` rules are not applied automatically
because that would trigger an infinite loop. 

We have not yet discussed how to use the `if`-`then` formula in
`uint_less_trans`, but we will get to that in the section below on
[Conditional Formulas (Implication)](#conditional-formulas-implication-and-applying-definitions-to-facts).

### Exercise

Prove the following using the theorems from `UInt.thm`.

```{.deduce^#uint_equation_ex}
theorem uint_equation_ex: 
  all x:UInt, y:UInt, z:UInt. x * z + y + x * z = (x + x) * z + y
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

It takes several uses of `uint_add_commute` to prove this.
To get started, we use `have` to give the label `step1` to a proof of
`x + y + z = x + z + y` (flipping the `y` and `z`).

```
theorem xyz_zyx: all x:UInt, y:UInt, z:UInt.
  x + y + z = z + y + x
proof
  arbitrary x:UInt, y:UInt, z:UInt
  have step1: x + y + z = x + z + y
    by replace uint_add_commute[y,z].
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
    by replace uint_add_commute[z,x].
  have step3: z + x + y = z + y + x
    by replace uint_add_commute[x,y].
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
theorem xyz_zyx: all x:UInt, y:UInt, z:UInt.
  x + y + z = z + y + x
proof
  arbitrary x:UInt, y:UInt, z:UInt
  have step1: x + y + z = x + z + y
    by replace uint_add_commute[y,z].
  have step2: x + z + y = z + x + y
    by replace uint_add_commute[z,x].
  have step3: z + x + y = z + y + x
    by replace uint_add_commute[x,y].
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
theorem xyz_zyx_eqn: all x:UInt, y:UInt, z:UInt.
  x + y + z = z + y + x
proof
  arbitrary x:UInt, y:UInt, z:UInt
  equations
    x + y + z = z + y + x      by ?
end
```

The first step is to commute `y + z` to `z + y`. If we're feeling
extra lazy, we can use `?` for the new right-hand side and the
error from Deduce will tell us what it needs to be.

```
  equations
    x + y + z = ?              by replace uint_add_commute[y,z] ?
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
theorem xyz_zyx_eqn: all x:UInt, y:UInt, z:UInt.
  x + y + z = z + y + x
proof
  arbitrary x:UInt, y:UInt, z:UInt
  equations
    x + y + z = x + z + y    by replace uint_add_commute[y,z].
          ... = z + x + y    by replace uint_add_commute[x,z].
          ... = z + y + x    by replace uint_add_commute[x,y].
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

But now we're stuck because append performs pattern matching
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
the argument. This is known as the **induction hypothesis**.
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
        ... = node(n, xs')            by ?
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
        ... = node(n, xs')         by ?
    }

Next, we see that the subterm `xs' ++ []` matches the
right-hand side of the induction hypothesis `IH`. We use the
`replace` statement to apply the `IH` equation to this subterm.

    case node(n, xs') assume IH: xs' ++ [] = xs' {
      equations
        node(n,xs') ++ []
            = node(n, xs' ++ [])   by expand operator++.
        ... = node(n, xs')         by replace IH.
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
      ... = node(n, xs')           by replace IH.
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
  have one_pos: 0 ≤ 1 by .
  have two_pos: 0 ≤ 2 by .
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

    theorem intro_dichotomy:  all x:UInt, y:UInt.  x ≤ y  or  y < x
    proof
      ?
    end

We can prove this using the `uint_trichotomy` theorem from `UInt.pf`,
which tells us that `x < y` or `x = y` or `y < x`.

    theorem intro_dichotomy:  all x:UInt, y:UInt.  x ≤ y  or  y < x
    proof
      arbitrary x:UInt, y:UInt
      have tri: x < y or x = y or y < x by uint_trichotomy[x][y]
      ?
    end

In Deduce, you can use an `or` fact by doing case analysis with the
`cases` statement. There is one `case` for each subformula of the
`or`.

    have tri: x < y or x = y or y < x by uint_trichotomy[x][y]
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
`uint_less_implies_less_equal` in `UInt.pf` tells us that `x ≤ y`.

    case x_l_y: x < y {
      have x_le_y: x ≤ y by apply uint_less_implies_less_equal[x][y] to x_l_y
      ?
    }

In Deduce, an `or` formula can be proved using a proof of either
subformula, so here we prove `x ≤ y or y < x` with `x ≤ y`.

    case x_l_y: x < y {
      have x_le_y: x ≤ y by apply uint_less_implies_less_equal[x][y] to x_l_y
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
theorem intro_dichotomy:  all x:UInt, y:UInt.  x ≤ y  or  y < x
proof
  arbitrary x:UInt, y:UInt
  have tri: x < y or x = y or y < x by uint_trichotomy[x][y]
  cases tri
  case x_l_y: x < y {
    have x_le_y: x ≤ y by apply uint_less_implies_less_equal[x][y] to x_l_y
    conclude x ≤ y or y < x by x_le_y
  }
  case x_eq_y: x = y {
    have x_le_y: x ≤ y by
        suffices y ≤ y  by replace x_eq_y.
        uint_less_equal_refl[y]
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

    theorem take_zero_empty: all E:type, xs:List<E>.
      take(xs, 0) = []
    proof
      ?
    end

We could proceed by induction, but it turns out we don't need the
induction hypothesis. In such situations, we can instead use `switch`.
Like induction, `switch` works on unions and there is one case for
each alternative of the union. Unlike induction, the goal formula does
not need to be an `all` formula. Instead, you indicate which entity to
switch on, as in `switch xs` below.

    arbitrary E:type, xs:List<E>
    switch xs {
      case [] {
        ?
      }
      case node(x, xs') {
        ?
      }
    }

Deduce responds that in the first case we need to prove the following.

    incomplete proof
    Goal:
        take(@[]<E>, 0) = []

So we expand `take`.

    case [] {
      expand take.
    }

In the second case, for `xs = node(x, xs')`, we need to prove the following.

    incomplete proof
    Goal:
        take(node(x, xs'), 0) = []

Again we conclude by expanding `take`.

    case node(x, xs') {
      expand take.
    }

Here is the completed proof that taking zero elements from a list
produces the empty list.


```{.deduce^#take_zero_empty}
theorem take_zero_empty: all E:type, xs:List<E>.
  take(xs, 0) = []
proof
  arbitrary E:type, xs:List<E>
  switch xs {
    case [] {
      expand take.
    }
    case node(x, xs') {
      expand take.
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
      have len_z3: 1 + length(xs') = 0
        by expand length in len_z2
      conclude false  by apply uint_not_one_add_zero to len_z3
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

Now from `UInt.pf` we have the following `if`-`then` fact.

```
uint_add_to_zero: all n:UInt. all m:UInt. if n + m = 0 then n = 0 and m = 0
```

Here is our first use of `apply`-`to` to obtain `length(xs) = 0` and
the same for `ys`. (Deduce can infer the arguments for the `all n` and `all m`
in `uint_add_to_zero`.)

```
  have len_xs: length(xs) = 0  by apply uint_add_to_zero to len_xs_len_ys
  have len_ys: length(ys) = 0  by apply uint_add_to_zero to len_xs_len_ys
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
  have len_xs: length(xs) = 0  by apply uint_add_to_zero to len_xs_len_ys
  have len_ys: length(ys) = 0  by apply uint_add_to_zero to len_xs_len_ys
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

Prove that `all x:UInt. if x ≤ 0 then x = 0`.

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
example, it is not true that every integer is equal to zero,
so the negation of that is true:
```
not (all n:UInt. n = 0)
```
Deduce treats `not` as syntactic sugar for a conditional formula with a
`false` conclusion. (This is a common thing to do in logic.)
So the above formula is equivalent to:
```
if (all n:UInt. n = 0) then false
```
We already know how to work with `if`-`then` formulas so we can use
that knowledge to work with `not`. For example, to prove that
a negated formula is true, we `assume` the formula and then
prove `false`. In the following, we instantiate the `all`
with a number that is not `0`, such as `1`, obtaining
`1 = 0`. We can then conclude `false` because Deduce recognizes
that the equality has two obviously different things on each side.

```{.deduce^#prove_not_example}
theorem prove_not_example: not (all n:UInt. n = 0)
proof
  assume prem: all n:UInt. n = 0
  have one_z: 1 = 0 by prem[1]
  conclude false by one_z
end
```

Next let us look at how to use a negated fact to prove something else.
The following theorem proves one direction of De Morgan's law,
that is, `not P or not Q` implies `not (P and Q)`.
So we assume that `P and Q` and our goal is to prove `false`.
Next we proceed by cases on the `or` so in the first case we know
that `not P`. Of course, from `P and Q` we have `P`,
which contradicts `not P`. So we use `contradict` to prove `false`.
The other case is similar. We have a contradiction between
`not Q` and `Q`.

```{.deduce^#use_not_example}
theorem use_not_example: all P:bool, Q:bool. if not P or not Q then not (P and Q)
proof
  arbitrary P:bool, Q:bool
  assume prem: not P or not Q
  assume pq: P and Q
  cases prem
  case np: not P {
    have p: P by pq
    conclude false      by contradict np, p  // !!
  }
  case nq: not Q {
    have q: Q by pq
    conclude false      by contradict nq, q  // !!
  }
end
```

To summarize this section:

* To expression that a formula is false, use `not`.
* Deduce treats the formula `not P` just like `if P then false`.
* Therefore, to prove a `not` formula, assume `P` then prove `false`.
* To use a formula like `not P`, use `contradict` with a proof of `P` to prove `false`.

## Replacing equals for equals in facts

In the section
[Replace equals for equals in goal](#replace-equals-for-equals-in-goal) 
we learned that the `replace` statement of Deduce applies an equation
to the current goal.  There is a second variant of `replace` that
applies an equation to a fact. As an example, we'll prove the
following theorem that is a straightforward use of `intro_less_irreflexive`.

```
theorem intro_less_not_equal: all x:UInt, y:UInt.
  if x < y then not (x = y)
proof
  arbitrary x:UInt, y:UInt
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

Here is the complete proof of `replace_in_example`.


```{.deduce^#replace_in_example}
theorem replace_in_example: all x:UInt, y:UInt.
  if x < y then not (x = y)
proof
  arbitrary x:UInt, y:UInt
  assume x_l_y: x < y
  assume x_y: x = y
  have y_l_y: y < y by replace x_y in x_l_y
  conclude false by apply uint_less_irreflexive[y] to y_l_y
end
```

### Exercise

Using the `replace`-`in` statement, prove the following variation on
the transitivity theorem for `≤`. Prove that if `x = y` and `y ≤ z`,
then `x ≤ z`.


```{.deduce^#equal_less_trans}
theorem equal_less_trans: all x:UInt, y:UInt, z:UInt.
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

    define Even = λ n:UInt { some m:UInt. n = 2 * m }

As an example of how to reason about `some` formulas, let us prove a
classic property of the even numbers, that the addition of two even
numbers is an even number. Here's the beginning of the proof.

    theorem intro_addition_of_evens:
      all x:UInt, y:UInt.
      if Even(x) and Even(y) then Even(x + y)
    proof
      arbitrary x:UInt, y:UInt
      assume even_xy: Even(x) and Even(y)
      have even_x: some m:UInt. x = 2 * m by expand Even in even_xy
      have even_y: some m:UInt. y = 2 * m by expand Even in even_xy
      ?
    end

The next step in the proof is to make use of the facts `even_x` and `even_y`.
We can ask Deduce for help in how to use a given with the `help` feature.

    help even_x
    
Deduce responds with
    
    Advice about using fact:
    some m:UInt. x = 2 * m

    Proceed with:
        obtain A where label: x = 2 * A from even_x
    where A is a new name of your choice

So we go ahead and write two `obtain` statements, one for `even_x` and
another for `even_y`, making different choices to replace the variable
`A` in the above advice.

    obtain a where x_2a: x = 2*a from even_x
    obtain b where y_2b: y = 2*b from even_y
    replace x_2a | y_2b

Deduce responds with

    available facts:
        y_2b: y = 2 * b,
        x_2a: x = 2 * a,

The `a` and `b` are new variables and the two facts `y_2b` and `x_2a`
are the subformulas of the `some`, but with `a` and `b` replacing `m`.

We still need to prove the following:

    incomplete proof:
        Even(2 * a + 2 * b)

So we use the definition of `Even` in an `expand` statement

    expand Even
    show some m:UInt. 2 * a + 2 * b = 2 * m
    ?

To prove a `some` formula, we use Deduce's `choose` statement.  This
requires some thinking on our part.  What number can we plug in for
`m` such that doubling it is equal to `2*a + 2*b`? Of course the
answer is `a + b`. We conclude the proof by using the distributivity
property of multiplication over addition (from `UInt.pf`).

    choose a + b
    replace x_2a | y_2b
    replate uint_dist_mult_add[2].

Here is the complete proof.


```{.deduce^#intro_addition_of_evens}
theorem intro_addition_of_evens:
  all x:UInt, y:UInt.
  if Even(x) and Even(y) then Even(x + y)
proof
  arbitrary x:UInt, y:UInt
  assume even_xy: Even(x) and Even(y)
  have even_x: some m:UInt. x = 2 * m by expand Even in even_xy
  have even_y: some m:UInt. y = 2 * m by expand Even in even_xy
  obtain a where x_2a: x = 2*a from even_x
  obtain b where y_2b: y = 2*b from even_y
  replace x_2a | y_2b
  expand Even
  show some m:UInt. 2 * a + 2 * b = 2 * m
  choose a + b
  replace uint_dist_mult_add[2].
end
```

### Exercise

Prove the following theorem, using a similar approach to the proof above
regardin ghte addition of even numbers.

```{.deduce^#intro_addition_of_odds}
theorem addition_of_odds: all x:UInt, y:UInt. 
  if Odd(x) and Odd(y) then Even(x + y)
proof
  ?
end
```

To summarize this section:

* The `some` formula expresses that a property is true for at least one entity.
* Deduce's `obtain` statement lets you make use of a fact that is a `some` formula.
* To prove a `some` formula, use Deduce's `choose` statement.

## Simplify the Goal

The `simplify` proof statement tells Deduce to simplify the goal
formula using all of the theorems that are marked `auto` as well as
additional built-in theorems regarding the logical operators.  For
example, in the following proof we use `simplify` to turn `2 + 3` and
`4 + 1` into `5`. However, the `simplify` statement does not know
about the commutativity of addition, so we complete the proof by
manually applying that theorem.

```{.deduce^#simplify_or_true}
theorem or_false_true: all x:UInt. 2 + 3 + x = x + 4 + 1
proof
  arbitrary x:UInt
  simplify
  conclude 5 + x = x + 5 by uint_add_commute
end
```  

<!--
```{.deduce^file=ProofIntro.pf}
<<import_uint_and_list>>

<<simplify_or_true>>
<<length_uint_empty>>
<<length_node42>>


theorem append_12: 
  node(1,empty) ++ node(2, empty) = node(1, node(2, empty))
proof
  expand 2* operator++.
end

<<length_uint_one>>
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
<<prove_not_example>>
<<use_not_example>>
<<replace_in_example>>

<<take_zero_empty>>
<<intro_addition_of_evens>>
```
-->
