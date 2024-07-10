# Functional Programming in Deduce

Deduce supports the following language features:
* [Unions](#unions)
* [Natural Numbers](#natural-numbers)
* [Imports](#imports)
* [Definitions](#definitions)
* [Printing Values](#printing-values)
* [Booleans and Conditional Expressions](#booleans-and-conditional-expressions)
* [Recursive Functions](#recursive-functions)
* [Higher-order Functions](#higher-order-functions)
* [Anonymous Functions (Lambda)](#anonymous-functions-lambda)
* [Pairs](#pairs)
* [Switch](#switch)

The following subsections describe each of these features.
There are several [exercises](#exercises) at the end 
that you can use to check your understanding.

## Unions

The `union` feature of Deduce is a tagged union.  A union declaration
provides the name for the union type.  The body of the union specifies
alternative ways to construct values of the union type. For example,
to represent a linked-list of natural numbers, we could define the
following union.

```{.deduce #NatList}
union NatList {
  nil
  cons(Nat, NatList)
}
```

We can then construct values of type `NatList` using the
alternatives. For example, `cons(1, cons(2, nil))` creates a
linked-list whose elements are the numbers `1` and `2`.

Unions may be recursive. An alternative within a union, such as `cons`
above, may include a parameter whose type is again the same union
type, in this case `NatList`.

Deduce supports generic unions, that is, one can parameterize a union
with one or more type parameters. For example, we can generalize our
linked list to allow an arbitrary element type as follows.

```{.deduce #List}
union List<T> {
  empty
  node(T, List<T>)
}
```

## Natural Numbers

Natural numbers are not a builtin type in Deduce but instead they
are defined as a `union` type:

```{.deduce #Nat}
union Nat {
  zero
  suc(Nat)
}
```

The file `Nat.pf` includes the above definition together with some
operations on natural numbers and theorems about them.  The numerals
`0`, `1`, `2`, etc. are shorthand for the natural numbers `zero`,
`suc(zero)`, `suc(suc(zero))`, etc.

## Imports

The `import` declaration makes available the contents of another
Deduce file in the current file. For example, you can import the
contents of `Nat.pf` as follows

```{.deduce #ImportNat}
import Nat
```

## Definitions

The `define` feature of Deduce associates a name with a value.  The
following definitions associate the name `L23` with the
linked-list containing `2` and `3`, and the name `L13` with the
linked-list containing `1`, `2` and `3`.

```{.deduce #List13}
define L23 = node(2, node(3, empty))
define L13 : List<Nat> = node(1, L23)
```

If desired, the type can be specified after the name, following a
colon.  In the above, `L13` is a list of natural numbers, so its type
is `List<Nat>`.

## Printing Values

You can ask Deduce to print a value to standard output using the
`print` statement.

```{.deduce #print_L13}
print L13
```

The output is

```
node(1,node(2,node(3,empty)))
```


## Booleans and Conditional Expressions

Deduce includes the values `true` and `false` of type `bool` and the
usual boolean operations such as `and`, `or`, and `not`.  Deduce also
provides an if-then-else expression that branches on the value of a
boolean. For example, the following if-then-else expression is
equivalent to `7`, so the `assert` succeeds.

```{.deduce #IfThenElse}
assert (if true then 7 else 5+6) = 7
```

## Recursive Functions

The recursive functions of Deduce are somewhat special to make sure
they always terminate.

* The first parameter of the function must be a union.
* The function definition must include a clause for every
  alternative in the union.
* The first argument of every recursive call must be a sub-part of the
  current alternative of the union.

A recursive function begins with the `function` keyword, followed by
the name of the function, then the parameters types and the return
type. For example, here's the definition of a `len` function for
lists of natural numbers.

```{.deduce #lenNatList}
function len(NatList) -> Nat {
  len(nil) = 0
  len(cons(n, next)) = 1 + len(next)
}
```

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

```{.deduce #length}
function length<E>(List<E>) -> Nat {
  length(empty) = 0
  length(node(n, next)) = 1 + length(next)
}
```

Recursive functions may have more than one parameter but pattern
matching is only supported for the first parameter. For example, here
is the `append` function that combines two linked lists.

```{.deduce #append}
function append<E>(List<E>, List<E>) -> List<E> {
  append(empty, ys) = ys
  append(node(n, xs), ys) = node(n, append(xs, ys))
}
```

## Higher-order Functions

Functions may be passed as parameters to a function and they may be
returned from a function. For example, the following function checks
whether every element of a list satisfies a predicate.

```{.deduce #all_elements}
function all_elements<T>(List<T>, fn (T) -> bool) -> bool {
  all_elements(empty, P) = true
  all_elements(node(x, xs'), P) = P(x) and all_elements(xs', P)
}
```

## Anonymous Functions (Lambda)

Anonymous functions can be created with a `λ` expression.  For
example, the following computes whether all the elements of the list
`L13` are positive.

```{.deduce #L13_pos}
define L13_positive = all_elements(L13, λx{ 0 < x })
```

## Pairs

Pairs are defined as a `union` type:

```{.deduce #Pair}
union Pair<T,U> {
  pair(T,U)
}
```

The file `Pair.pf` includes the above definition and several
operations on pairs, such as `first` and `second`.

## Switch

One can `switch` on a value of union type.  For example, the following
`zip` function combines two lists into a single list of pairs.  The
`zip` function is recursive, pattern-matching on the first list, and
uses `switch` to pattern-match on the second list.

```{.deduce #zip}
function zip<T,U>(List<T>, List<U>) -> List< Pair<T, U> > {
  zip(empty, ys) = empty
  zip(node(x, xs'), ys) =
	switch ys {
	  case empty { empty }
	  case node(y, ys') { node(pair(x,y), zip(xs', ys')) }
	}
}
```

## Exercises

### Sum the Elements in a List

Define a function named `sum` that adds up all the elements of a `List<Nat>`.

```{.deduce #test_sum}
assert sum(L13) = 6
```

### Inner Product

Define a function named `dot` that computes the inner product of two `List<Nat>`.

```{.deduce #test_dot}
define L46 = node(4, node(5, node(6, empty)))
assert dot(L13,L46) = 32
```

### Last Element in a List

Define a generic function named `last` that returns the last element
of a `List<E>`, if there is one. The return type should be `Option<E>`.
(`Option` is defined in the file `Option.pf`.)

```{.deduce #test_last}
assert last(L13) = just(3)
```

### Remove Elements from a List

Define a generic function named `remove_if` that removes elements
from a list if satisfy a predicate. So `remove_if` should have two
parameters: (1) a `List<E>` and (2) a function whose parameter is `E` 
and whose return type is `bool`.

```{.deduce #test_remove_if}
assert remove_if(L13, λx {x ≤ 1}) = node(2, node(3, empty))
```

### Non-empty Lists and Average

Define a `union` type named `NEList` for non-empty list.  Design the
alternatives in the `union` carefuly to make it impossible to create
an empty list.

Define a function named `average` that computes the mean of a
non-empty list and check that it works on a few inputs.

<!--
```{.deduce file=FunctionalProgramming.pf}
<<Nat>>
<<ImportNat>>
<<NatList>>
<<List>>
<<List13>>
<<print_L13>>
<<IfThenElse>>
<<lenNatList>>
<<length>>
<<append>>
<<all_elements>>
<<L13_pos>>
<<Pair>>
<<zip>>

function sum(List<Nat>) -> Nat {
  sum(empty) = 0
  sum(node(x, xs)) = x + sum(xs)
}
<<test_sum>>

function dot(List<Nat>,List<Nat>) -> Nat {
  dot(empty, ys) = 0
  dot(node(x, xs'), ys) =
    switch ys {
	  case empty {
	    0
	  }
	  case node(y, ys') {
	    x * y + dot(xs', ys')
	  }
    }
}

<<test_dot>>

import Option

function last<E>(List<E>) -> Option<E> {
  last(empty) = none
  last(node(x, xs')) = 
    switch xs' {
	  case empty {
	    just(x)
	  }
	  case node(y, ys) {
	    last(xs')
	  }
	}
}
<<test_last>>

function remove_if<E>(List<E>, fn (E)->bool) -> List<E> {
  remove_if(empty, P) = empty
  remove_if(node(x, ls), P) =
    if P(x) then remove_if(ls, P)
    else node(x, remove_if(ls, P))
}
<<test_remove_if>>

union NEList<T> {
  single(T)
  another(T, NEList<T>)
}

function len_ne<T>(NEList<T>) -> Nat {
  len_ne(single(x)) = 1
  len_ne(another(x, xs)) = suc(len_ne(xs))
}

function sum_ne(NEList<Nat>) -> Nat {
  sum_ne(single(x)) = x
  sum_ne(another(x, xs)) = x + sum_ne(xs)
}

define average : fn NEList<Nat> -> Nat = λ ne { sum_ne(ne) / len_ne(ne) }
assert average(another(3, another(2, single(1)))) = 2
assert average(another(4, another(5, single(6)))) = 5
```
-->
