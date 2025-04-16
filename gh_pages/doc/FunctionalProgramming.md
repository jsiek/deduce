# Programming in Deduce

Deduce supports the following language features:

* [Import](#import)
* [Definitions](#definitions)
* [Printing Values](#printing-values)
* [Functions](#function-statement)
* [Unions and Switch](#unions-and-switch)
* [Natural Numbers](#natural-numbers)
* [Lists](#lists)
* [Booleans, Conditionals, and Assert](#booleans-conditionals-and-assert)
* [Recursive Functions](#recursive-functions)
* [Generic Functions](#generic-functions)
* [Higher-order Functions](#higher-order-functions)
* [Pairs](#pairs)

The following subsections describe each of these features.
There are several [exercises](#exercises) at the end 
that you can use to check your understanding.

## Import

The `import` declaration makes available the contents of another
Deduce file in the current file. For example, you can import the
contents of `Nat.pf` as follows

```{.deduce^#ImportNat}
import Nat
```

## Definitions

The `define` feature of Deduce associates a name with a value.
The following definitions associate the name `five` with the
natural number `5`, and the name `six` with the natural
number `6`.

```{.deduce^#five_six}
define five = 2 + 3
define six : Nat = 1 + five
```

Optionally, the type can be specified after the name, following a
colon.  In the above, `six` holds a natural number, so its type is
`Nat`.

## Printing Values

You can ask Deduce to print a value to standard output using the
`print` statement.


```{.deduce^#print_five}
print five
```

The output is `5`.


## Function (Statement)

A function statement starts `fun`, followed by parameter names
and their types, then the body of the function enclosed in braces.
For example, the following creates a function for computing the area
of a rectangle.


```{.deduce^#area}
fun area(h:Nat, w:Nat) {
  h * w
}
```

To call a function, apply it to the appropriate number and type of
arguments.


```{.deduce^#print_area}
print area(3, 4)
```

The output is `12`.


## Unions and Switch

The `union` feature of Deduce defines a type whose values are created
by one or more constructors.  A union definition specifies a name for
the union type and its body specifies the name of each constructor and
its parameter types. For example, we define the following union to
represent a linked-list of natural numbers.

```{.deduce^#NatList}
union NatList {
  Empty
  Node(Nat, NatList)
}
```

We can then construct values of type `NatList` using the constructors
`Empty` and `Node`.  To create a linked-list whose elements are
`1` and `2`, write:

```{.deduce^#NL12}
define NL12 = Node(1, Node(2, Empty))
```

Unions may be recursive: a constructor may include a parameter type
that is the union type, e.g., the `NatList` parameter of `Node`. 

## Generic Unions

Unions may be generic: one can parameterize a union
with one or more type parameters. For example, we generalize linked
lists to any element types as follows.

```{.deduce^#List}
union List<T> {
  empty
  node(T, List<T>)
}
```

Constructing values of a generic union looks the same as for a regular
union. Deduce figures out the type for `T` from the types of
the constructor arguments.

```{.deduce^#L12}
define L12 = node(1, node(2, empty))
```

## Lists

The file `List.pf` includes the union type we defined
[above](#generic-unions) as well as operations on lists and theorems
about them. Deduce provides shorthand notation for lists where:

- `[]` is shorthand for `empty`
- `[1]` is shorthand for `node(1, empty)`
- `[1, 2]` is shorthand for `node(1, node(2, empty))`
- etc.

## Switch

You can branch on a value of union type using `switch`. For example,
the following `front` function returns the first element of a `NatList`. Here
we give an explicit type annotation for the `front` function. The type
of a function starts with `fn`, followed by the parameter types, then
`->`, and finally the return type.

```{.deduce^#front}
import Option
 
fun front(ls : NatList) {
  switch ls {
    case Empty { @none<Nat> }
    case Node(x, ls') { just(x) }
  }
}
```

The output of 

```{.deduce^#print_front}
print front(NL12)
```

is `just(1)`.

The `switch` compares the discriminated value with the
constructor pattern of each `case` and when it finds a match,
it initializes the pattern variables from the parts of the
discriminated value and then evaluates the branch associated with the
`case`.

If you forget a `case` in a `switch`, Deduce will tell
you. For example, if you try the following:

```{.deduce^#broken_front}
fun broken_front(ls : NatList) {
  switch ls { 
    case Empty { @none<Nat> } 
  }
}
```

Deduce responds with

```
this switch is missing a case for: Node(Nat,NatList)
```


## Natural Numbers

Natural numbers are not a builtin type in Deduce but instead they
are defined as a `union` type:

```{.deduce^#Nat}
union Nat {
  zero
  suc(Nat)
}
```

The file `Nat.pf` includes the above definition together with some
operations on natural numbers and theorems about them.  The numerals
`0`, `1`, `2`, etc. are shorthand for the natural numbers `zero`,
`suc(zero)`, `suc(suc(zero))`, etc.

## Booleans, Conditionals, and Assert

Deduce includes the values `true` and `false` of type
`bool` and the usual boolean operations such as `and`,
`or`, and `not`.  Deduce also provides an if-then-else
term that branches on the value of a boolean. For example, the
following if-then-else term is evaluates to `7`.

```{.deduce^#print7}
print (if true then 7 else 5+6)
```

The `assert` statement evaluates a term and reports an
error if the result is `false`. For example, the following
`assert` does nothing because the term evaluates to
`true`.

```{.deduce^#assert_if_true}
assert (if true then 7 else 5+6) = 7
```


## Recursive Functions

Recursive functions in Deduce are somewhat special to make sure they
always terminate.

* The first parameter of the function must be a union.
* The function definition must include a clause for every
  constructor in the union.
* The first argument of every recursive call must be a sub-part of the
  current constructor of the union.

A recursive function begins with the `recursive` keyword, followed by
the name of the function, then the parameters types and the return
type. For example, here's the definition of a `len` function for
lists of natural numbers.

```{.deduce^#lenNatList}
recursive len(NatList) -> Nat {
  len(Empty) = 0
  len(Node(n, next)) = 1 + len(next)
}
```

There are two clauses in the body. The clause for `Empty` says
that its length is `0`.  The clause for `Node` says that
its length is one more than the length of the rest of the linked list.
Deduce approves of the recursive call `len(next)` because
`next` is part of `Node(n, next)`.

Recursive functions may have more than one parameter but pattern
matching is only supported for the first parameter. For example, here
is the `app` function that combines two linked lists.

```{.deduce^#app}
recursive app(NatList, NatList) -> NatList {
  app(Empty, ys) = ys
  app(Node(n, xs), ys) = Node(n, app(xs, ys))
}
```

If you need to pattern match on a parameter that is not the first, you
can use a `switch` statement. For example, the following `zip`
function (defined in `List.pf`) combines two lists into a single list
of pairs. The function is defined by two clauses that pattern match on
the first parameter. However, `zip` also needs to match on the second
parameter `ys`, which is accomplished with a `switch` statement.

```{.deduce^#zip_example}
recursive zip<T,U>(List<T>, List<U>) -> List< Pair<T, U> > {
  zip(empty, ys) = []
  zip(node(x, xs'), ys) =
    switch ys {
      case empty { [] }
      case node(y, ys') { node(pair(x,y), zip(xs', ys')) }
    }
}
```


## Generic Functions

Deduce supports generic functions, both recursive and non-recursive.
For example, we can generalize the recursive `length` to work on lists
with any element type as follows.

```{.deduce^#length}
recursive length<E>(List<E>) -> Nat {
  length(empty) = 0
  length(node(n, next)) = 1 + length(next)
}
```

The following `head` function is an example of a generic non-recursive
function.

```{.deduce^#head}
fun head<T>(ls: List<T>) {
  switch ls {
    case empty { @none<T> }
    case node(x, ls') { just(x) }
  }
}
```

Calling a generic function is just like calling a normal function,
most of the time. For example, the following invokes the
generic `length` function on an argument of type `List<Nat>`
and Deduce figures out that the type parameter `E` must be `Nat`.

```{.deduce^#apply_length}
assert length([42]) = 1
```

However, there are times when there is not enough information for
Deduce to determine the type parameters of a generic. For example,
both the `length` function and the `empty` constructor are generic, so
Deduce cannot figure out what type of list is being constructed in the
following.


```{.deduce}
assert length([]) = 0
```

Deduce responds with the error:

```
Cannot infer type arguments for
	[]
Please make them explicit.
```

The solution is to explicitly instantiate either `empty` or `length`.
The syntax starts with `@`, followed by the generic entity, and finishes
with the type arguments surrounded by `<` and `>`. Here's the 
example again with the explicit instantiation.

```{.deduce^#apply_length_empty}
assert length(@[]<Nat>) = 0
```


## Higher-order Functions

Functions may be passed as parameters to a function and they may be
returned from a function. For example, the following function checks
whether every element of a list satisfies a predicate.

```{.deduce^#all_elements}
recursive all_elements<T>(List<T>, fn T->bool) -> bool {
  all_elements(empty, P) = true
  all_elements(node(x, xs'), P) = P(x) and all_elements(xs', P)
}
```

## Pairs

Pairs are defined as a `union` type:

```{.deduce^#Pair}
union Pair<T,U> {
  pair(T,U)
}
```

The file `Pair.pf` includes the above definition and several
operations on pairs, such as `first` and `second`.


## Exercises

### Sum the Elements in a List

Define a function named `sum` that adds up all the elements of a `List<Nat>`.

```{.deduce^#test_sum}
define L13 = [1, 2, 3]
assert sum(L13) = 6
```

### Inner Product

Define a function named `dot` that computes the inner product of two `List<Nat>`.

```{.deduce^#test_dot}
define L46 = [4, 5, 6]
assert dot(L13,L46) = 32
```

### Last Element in a List

Define a generic function named `last` that returns the last element
of a `List<E>`, if there is one. The return type should be `Option<E>`.
(`Option` is defined in the file `Option.pf`.)

```{.deduce^#test_last}
assert last(L13) = just(3)
```

### Remove Elements from a List

Define a generic function named `remove_if` that removes elements
from a list if they satisfy a predicate. So `remove_if` should have two
parameters: (1) a `List<E>` and (2) a function whose parameter is `E` 
and whose return type is `bool`.

```{.deduce^#test_remove_if}
assert remove_if(L13, fun x {x ≤ 1}) = [2, 3]
```

### Non-empty Lists and Average

Define a `union` type named `NEList` for non-empty list.  Design the
alternatives in the `union` carefully to make it impossible to create
an empty list.

Define a function named `average` that computes the mean of a
non-empty list and check that it works on a few inputs.
Note that the second parameter of the division operator `/` 
is of type `Pos`, which is defined in `Nat.pf`.

<!--
```{.deduce^file=FunctionalProgramming.pf}
<<ImportNat>>
<<five_six>>
<<print_five>>
<<area>>
<<print_area>>
<<NatList>>
<<NL12>>
<<List>>
<<L12>>
<<front>>
<<print_front>>
<<print7>>
<<assert_if_true>>
<<lenNatList>>
<<app>>
<<length>>
<<apply_length>>
<<apply_length_empty>>
<<head>>
<<all_elements>>
<<Pair>>
```
-->
