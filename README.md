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

## Functional Programming in Deduce

Deduce supports the following language features:
* unions
* definitions
* recursive functions

### Unions

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

### Definitions

The `define` feature of Deduce associates a name with a value.  The
following associates the name `L5` with the linked-list on the
right-hand side. The following definitions associate the name `L23`
with the linked list contains `2` and `3`, and then `L13` is the
linked list containing `1`, `2` and `3`.

	define L23 = node(2, node(3, empty))
	define L13 : List<Nat> = node(1, L23)

If desired, the type can be specified after the name, following a
colon.  In the above, `L13` is a list of natural numbers, so its type
is `List<Nat>`.


### Recursive Functions

The recursive functions of Deduce are somewhat special.
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
alternative and another for the `node` alternative.
The first clause says that length of an empty list is `0`.
The second clause says that the length of a list of the form
`node(n, next)` is one more than the length of `next`.
Note that the recursive call `length(next)` is allowed
because `next` is a sub-part of `node(n, next)`.

Deduce supports generic functions, so we can generalize `length` to
work on lists with any element type as follows.

	function length<E>(List<E>) -> Nat {
	  length(empty) = 0;
	  length(node(n, next)) = 1 + length(next);
	}


