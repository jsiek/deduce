Deduce is an automated proof checker meant for use in education. The
intended audience is students with (roughly) the following background
knowledge and skills:

* Basic programming skills in a mainstream language such as Java,
  Python, or C++, as one would learn in the introductory computer
  science course at a university.
* Some exposure to logic, as one would learn in a course on Discrete
  Mathematics (aka. Discrete Structures).

The primary goal of Deduce is to help students learn how to prove the
correctness of pure functional programs. The reason for the focus on
pure functional programs is because (1) those proofs are much more
straightforward to write than proofs of correctness of imperative
programs, so it serves as a better starting place educationally, and
(2) the technology for automatically checking those proofs is well
understood, so it's straightforward to build and maintain the Deduce
proof checker.

TODO: road map

# Functional Programming in Deduce

Deduce supports the following language features:
* unions
* natural numbers
* imports
* definitions
* recursive functions
* higher-order functions
* anonymous functions
* pairs
* booleans and conditional expressions
* switch

The following subsections describe each of these features.

## Unions

The `union` feature of Deduce is a tagged union.  A union declaration
provides the name for the union type.  The body of the union specifies
alternative ways to construct values of the union type. For example,
to represent a linked-list of natural numbers, we could define the
following union.

	union NatList {
	  empty;
	  node(Nat, NatList);
	}

We can then construct values of type `NatList` using the
alternatives. For example, `node(1, node(2, empty))` creates a
linked-list whose elements are the numbers `1` and `2`.

Unions may be recursive. An alternative within a union, such as `node`
above, may include a parameter whose type is again the same union
type, in this case `NatList`.

Deduce supports generic unions, that is, one can parameterize a union
with one or more type parameters. For example, we can generalize our
linked list to allow an arbitrary element type as follows.

	union List<T> {
	  empty;
	  node(T, List<T>);
	}

## The Natural Numbers

The natural numbers are not a builtin type in Deduce but instead they
are defined as a `union` type:

	union Nat {
	  zero;
	  suc(Nat);
	}

The file `Nat.pf` includes the above definition together with some
operations on natural numbers and theorems about them.

## Imports

The `import` declaration makes available the contents of another
Deduce file in the current file. For example, you can import the
contents of `Nat.pf` as follows

    import Nat

## Definitions

The `define` feature of Deduce associates a name with a value.  The
following two definitions associate the name `L23` with the
linked-list containing `2` and `3`, and the name `L13` with the
linked-list containing `1`, `2` and `3`.

	define L23 = node(2, node(3, empty))
	define L13 : List<Nat> = node(1, L23)

If desired, the type can be specified after the name, following a
colon.  In the above, `L13` is a list of natural numbers, so its type
is `List<Nat>`.


## Recursive Functions

The recursive functions of Deduce are somewhat special to make sure
they always terminate.

* The first parameter of the function must be a union.
* The function definition must include a clause for every
  alternative in the union.
* The first argument of every recursive call must be a sub-part of the
  current alternative of the union.

A recursive function begins with the `function` keyword, followed by
the name of the function, then the paramters types and the return
type. For example, here's the definition of a `length` function for
lists of natural numbers.

	function length(NatList) -> Nat {
	  length(empty) = 0;
	  length(node(n, next)) = 1 + length(next);
	}

There are two clauses in this definition, one for the `empty`
alternative and another for the `node` alternative.  One can think of
the clauses as pattern-matching on the union's alternatives.  In the
second clause, the pattern `node(n, next)` includes two pattern
variables `n` and `next` that bind the two sub-parts of the node.  The
expression after the `=` specifies the return value of the
function. The clause for `empty` says that its length is `0`.  The
clause for `node` says that its length is one more than the length of
the rest of the linked list.  Note that the recursive call
`length(next)` is allowed because `next` is a sub-part 
of `node(n,next)`.

Deduce supports generic functions, so we can generalize `length` to
work on lists with any element type as follows.

	function length<E>(List<E>) -> Nat {
	  length(empty) = 0;
	  length(node(n, next)) = 1 + length(next);
	}

Recursive functions may have more than one parameter but pattern
matching is only supported for the first parameter. For example, here
is the `append` function that combines two linked lists.

	function append<E>(List<E>, List<E>) -> List<E> {
	  append(empty, ys) = ys;
	  append(node(n, xs), ys) = node(n, append(xs, ys));
	}

## Higher-order Functions

Functions may be passed as parameters to a function and they may be
returned from a function. For example, the following function checks
whether every element of a list satisfies a predicate.

	function all_elements<T>(List<T>, fn (T) -> bool) -> bool {
	  all_elements(empty, P) = true;
	  all_elements(node(x, xs'), P) = P(x) and all_elements(xs', P);
	}

## Anonymous Functions

Anonymous functions can be created with a `λ` expression.  For
example, the following computes whether all the elements of the list
`L13` are positive.

    define L13_positive = all_elements(L13, λx{ 0 < x })

## Pairs

Pairs are defined as a `union` type:

	union Pair<T,U> {
	  pair(T,U);
	}

The file `Pair.pf` includes the above definition and several
operations on pairs, such as `first` and `second`.

## Booleans and Conditional Expressions

Deduce includes the values `true` and `false` of type `bool` and the
usual boolean operations such as `and`, `or`, and `not`.  Deduce also
provides an if-then-else expression that branches on the value of a
boolean. For example, the following expression

    if 0 ≤ 1 then 3+4 else 5+6

is equivalent to `7`. 

## Switch

One can also `switch` on a value of union type.  For example, the
following `zip` function combines two lists into a single list of pairs.
The `zip` function is recursive, pattern-matching on the first list, and
uses `switch` to pattern-match on the second list.

	function zip<T,U>(List<T>, List<U>) -> List< Pair<T, U> > {
	  zip(empty, ys) = empty;
	  zip(node(x, xs'), ys) =
		switch ys {
		  case empty { empty }
		  case node(y, ys') { node(pair(x,y), zip(xs', ys')) }
		};
	}

# Writing Proofs in Deduce

We consider a sequence of examples of increasing complexity,
introducing features of the Deduce proof language as we go.  Create a
file with a `.pf` suffix that contains all of the definitions from the
previous section. You will add these examples to that file.

## Working with Definitions

We begin with an simple example, proving that the length of an empty
list is `0`. Of course, this is a direct consequence of the definition
of `length`, so this first example is about how to use definitions.
To get started, we write down the theorem we would like to prove.  A
theorem starts with a label, followed by a colon, then the formula
followed by the proof. But intead of writing the proof, we'll simply
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
	  definition length;
	  ?
	end

Now Deduce responds with

	unfinished proof:
		true

Deduce expanded the definition of `length` in the currect goal,
changing `length(empty) = 0` to `0 = 0`. In particular, Deduce noticed
that `length(empty)` matches the first clause in the definition of
`length` and then replaced it with the right-hand side of the first
clause. Deduce then simplified `0 = 0` to `true`. In general, whenever
Deduce sees an equality with the same left and right-hand side, it
automatically simplies it to `true`.

To finish the proof, we just need to prove `true`, which is
accomplished with a period.

	theorem length_empty: length(empty) = 0
	proof
	  definition length;
	  .
	end

Run Deduce on the file to see it respond that the file is valid.

We can simplify the above proof by removing the semicolon, as
the `definition` statement is the last one in the proof.

	theorem length_empty: length(empty) = 0
	proof
	  definition length.
	end

Let's try a slightly more complex theorem, that the length
of a list with just a single node is indeed `1`. Based
on what we learned above, we better start by applying the
definition of `length`.

	theorem length_node42: length(node(42, empty)) = 1
	proof
	  definition length;
	  ?
	end

Deduce responds that we still need to prove the following obvious fact.

	unfinished proof:
		1 + 0 = 1

But that is just a consequence of the definition of addition, which
we can refer to as `operator +`.

	theorem length_node42: length(node(42, empty)) = 1
	proof
	  definition length, operator +;
	  ?
	end

Deduce responds with

	unfinished proof:
		true

so we can conclude the proof with a period.

	theorem length_node42: length(node(42, empty)) = 1
	proof
	  definition length, operator +.
	end

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
	  arbitrary x:Nat;
	  ?
	end

Deduce responds with

	unfinished proof:
		length(node(x,empty)) = 1

We don't know anything about this hypothetical `x` other than it being
a natural number. But as we previously observed, we don't need any
more information about `x` in this example.  We complete the proof as
before, using the definitions of `length` and addition.

	theorem length_one_nat: all x:Nat. length(node(x, empty)) = 1
	proof
	  arbitrary x:Nat;
	  definition length, operator +.
	end

Once we have proved that an `all` formula is true, we can use it by
supplying an entity of the appropriate type inside square brackets. In
the following we prove the `length_node42` theorem again, but this
time the proof makes use of `length_one_nat`.

	theorem length_node42_again: length(node(42, empty)) = 1
	proof
	  length_one_nat[42]
	end

We can generalize the theorem yet again by noticing that it does not
matter whether the element is a natural number. It could be a value of
any type. In Deduce we can also use the `all` statement to generalize
types. In the following, we add `U:type` to the `all` formula and to
the `arbitrary` statement.

	theorem length_one: all U:type, x:U. length(node(x, empty)) = 1
	proof
	  arbitrary U:type, x:U;
	  definition length, operator +.
	end

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
	  arbitrary U:type;
	  arbitrary xs:List<U>;
	  ?
	end

Deduce replies that we need to prove

	unfinished proof:
		append(xs,empty) = xs

We might try to expand the definition of `append` as follows.

	theorem append_empty: all U :type. all xs :List<U>.
	  append(xs, empty) = xs
	proof
	  arbitrary U:type;
	  arbitrary xs:List<U>;
	  definition append;
	  ?
	end

But Deduce replies with the same goal.

	unfinished proof:
		append(xs,empty) = xs

Deduce was unable to expand the definition of `append` because that
function pattern matches on its first argument, but we don't know
whether `xs` is an `empty` list or a `node`.

So instead of using `arbitrary xs:List<U>;` to prove the `all xs`, we
proceed by induction as follows.

	theorem append_empty: all U :type. all xs :List<U>.
	  append(xs, empty) = xs
	proof
	  arbitrary U:type;
	  induction List<U>
	  case empty {
		?
	  }
	  case node(n, xs') assume IH: append(xs',empty) = xs' {
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
	  show append(empty, empty) = empty  by definition append.
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

	case node(n, xs') assume IH: append(xs',empty) = xs' {
	  term append(node(n,xs'),empty) by definition append; ?;
	  ?
	}

Deduce responds with

	unfinished proof:
		node(n,append(xs',empty))

So we know that 

    append(node(n,xs'),empty) = node(n, append(xs',empty))        (1)

Next, we see that the subterm `append(xs',empty)` matches the
right-hand side of the induction hypothesis `IH`. So we have

    node(n, append(xs',empty)) = node(n, xs')                     (2)

To complete the proof, we need to string together equations (1) and (2).
We can do this in Deduce using an `equations` statement.

	case node(n, xs') assume IH: append(xs',empty) = xs' {
	  equations
		append(node(n,xs'),empty)
			= node(n, append(xs',empty))  by definition append.
		... = node(n,xs')                 by rewrite IH.
	}

