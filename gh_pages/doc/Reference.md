# Reference Manual

This is a comprehensive reference for Deduce. It describes each
feature in alphabetical order by keyword. It gives the grammar rule
(syntax) and describes its meaning and/or how it is used in a proof.

In the grammar rules, an unquoted asterisk means zero-or more
repetitions of the grammar item that it follows.
The symbol ε means the empty string.
A vertical bar separates alternatives right-hand sides in a grammar rule.


## Add

```
term ::= term "+" term
```

The addition function for natural numbers is defined in `Nat.pf`
as follows.

```
function operator +(Nat,Nat) -> Nat {
  operator +(0, m) = m
  operator +(suc(n), m) = suc(n + m)
}
```

Example:

```{.deduce^#add_example}
assert 2 + 3 = 5
```

## Add (Multiset)

```
term ::= term "⨄" term
term ::= term "[+]" term
```

Addition on multisets is defined in `MultiSet.pf`.  The main theorem
about multiset addition is `cnt_sum`, which says that the count for
each item in `A ⨄ B` is the sum of (1) the count for that item in `A`
and (2) the count for that item in `B`.

```
cnt_sum: all T:type. all A:MultiSet<T>, B:MultiSet<T>, x:T.
  cnt(A ⨄ B)(x) = cnt(A)(x) + cnt(B)(x)
```

Example:

```{.deduce^#add_multiset_example}
define X = m_one(5) ⨄ m_one(3) ⨄ m_one(5)
assert cnt(X)(3) = 1
assert cnt(X)(5) = 2
assert cnt(X)(7) = 0
```

## All (Universal Quantifier)

```
formula ::= "all" var_list "." formula
```

A formula of the form `all x1:T1,...,xn:Tn. P` is true
when `P` is true for all possible choices of `x1`...`xn`.

To prove an `all` formula, use `arbitrary` (see entry for
[Arbitrary](#arbitrary-forall-introduction)) or `induction` (see entry
for [Induction](#induction)). Induction is only allowed when the `all`
has a single variable, as in `all x:T. P`, and the type `T` must be a
union type.

```{.deduce^#all_example_bool}
theorem all_example_bool: all P:bool. P = true or P = false
proof
  arbitrary P:bool
  switch P {
    case true { . }
    case false { . }
  }
end
```

```{.deduce^#all_example_intro}
theorem all_example_intro: all x:Nat,y:Nat,z:Nat. x + y + z = z + y + x
proof
  arbitrary x:Nat, y:Nat, z:Nat
  equations
    x + y + z = y + x + z by replace add_commute[x,y].
          ... = z + y + x by add_commute[y+x,z]
end
```

A proof of `all x1:T1,...,xn:Tn. P` can be used to prove the
formula `P` where the `x1,...,xn` have been replaced by 
terms of your choice. Use square brackets to enclose your
comma-delimited choices.

```{.deduce^#all_example_elim}
theorem all_example_elim: 1 + 2 + 3 = 3 + 2 + 1
proof
  all_example_intro[1, 2, 3]
end
```

## And (logical conjunction)

```
formula ::= formula "and" formula
```

The formula `P and Q` is true when both `P` and `Q` are true.

Example:

```{.deduce^#and_example} 
assert true and true
assert not (true and false)
assert not (false and true)
assert not (false and false)
```

Use comma to combine a proof of `P` and a proof of `Q` into a proof of
`P and Q`.

```{.deduce^#and_example_intro}
theorem and_example_intro: (1 = 0 + 1) and (0 = 0 + 0)
proof
  have eq1: 1 = 0 + 1 by expand operator+.
  have eq2: 0 = 0 + 0 by expand operator+.
  conclude (1 = 0 + 1) and (0 = 0 + 0) by eq1, eq2
end
```

A proof of `P and Q` can be used implicitly to prove `P` and to prove `Q`.

```{.deduce^#and_example_elim}
theorem and_example_elim: all P:bool, Q:bool. if P and Q then Q and P
proof
  arbitrary P:bool, Q:bool
  assume prem: P and Q
  have p: P         by prem   // P and Q  used to prove  P
  have q: Q         by prem   // P and Q  used to prove  Q
  conclude Q and P  by p, q
end
```


## Append

```
term ::= term "++" term
```

The append function, i.e., `operator ++`, is defined in `List.pf` as follows.

```
function operator ++ <E>(List<E>, List<E>) -> List<E> {
  operator ++(empty, ys) = ys
  operator ++(node(n, xs), ys) = node(n, xs ++ ys)
}
```

Example:

```{.deduce^#append_example}
assert [1,2] ++ [3,4] = [1,2,3,4]
```

## Apply-To Proof (Modus Ponens)

```
conclusion ::= "apply" proof "to" proof
```

A proof of the form

```
apply X to Y
```

is a proof of formula `Q` if `X` is a proof of `(if P then Q)`
and `Y` is a proof of `P`.

Example:

```{.deduce^#apply_to_example}
theorem apply_to_example: all P:bool, Q:bool, R:bool.
  if (if P then Q) and (if Q then R) and P
  then R
proof
  arbitrary P:bool, Q:bool, R:bool
  assume prem: (if P then Q) and (if Q then R) and P
  have pq: if P then Q  by prem
  have p: P             by prem
  have q: Q             by apply pq to p
  have qr: if Q then R  by prem
  conclude R            by apply qr to q
end
```

## Arbitrary (Forall Introduction)

```
proof_stmt ::= "arbitrary" var_list
```

A proof of the form

```
arbitrary x1:T1, ..., xn:Tn
X
```

is a proof of the formula `all x1:T1, ..., xn:Tn. P` if `X` is a proof of `P`.
The variables `x1`, ..., `xn` may appear in the formula `P` and the proof `X`.

Example:

```{.deduce^#arbitrary_example}
theorem arbitrary_example: all x:Nat,y:Nat. if x = y then y = x
proof
  arbitrary x:Nat,y:Nat
  conclude if x = y then y = x by
    assume: x = y
    symmetric (recall x = y)
end
```

## Assert (Statement)

```
statement ::= "assert" term
```

The `assert` statement evaluates a term and reports an error if the
result is `false`. For example, the following `assert` does nothing
because the term evaluates to `true`.

```{.deduce^#assert_example}
assert (if true then 7 else 5+6) = 7
```


## Assume

```
proof_stmt ::= "assume" assumption
             | "suppose" assumption
```

A proof of the form

```
assume label: P
X
```

is a proof of the formula `if P then Q` if `X` is a proof of `Q`.
The proof `X` may use the `label` as a proof of `P`
and it may also refer to the proof of `P` by writing `recall P`.

```{.deduce^#assume_example}
theorem assume_example: all x:Nat,y:Nat. if (x = y) then (1 + x = 1 + y)
proof
  arbitrary x:Nat,y:Nat
  assume prem: x = y
  conclude 1 + x = 1 + y  by replace prem.
end
```

## Assumption and Assumption List

```
assumption ::= identifier
assumption ::= identifier ":" formula
assumption ::= ":" formula

assumption_list ::= assumption
assumption_list ::= assumption "," assumption_list
```

See the entry for [Assume](#assume) to see how assumptions are used.

## At Symbol `@`

See the entry for [Instantiation](#instantiation-term).

## Biconditional (if and only if)

```
formula ::= formula "⇔" formula
          | formula "<=>" formula
          | formula "iff" formula
```

The biconditional formula `P ⇔ Q` is syntactic sugar for
`(if P then Q) and (if Q then P)`.

## Bool (Type)

```
type ::= "bool"
```

The type `bool` classifies the values `true` and `false`.
A formula is a term of type `bool`.

## Braces (Proof)

```
proof ::= "{" proof "}"
```

A proof may be surrounded in curly braces.

## Call (Term)

```
term ::= term "(" term_list ")"
```

A term of the form `t0(t1, ..., tn)` calls the function indicated by
term `t0` on the arguments `t1`,...,`tn`.

```{.deduce^#call_example}
assert length(list_example) = 3
```

## Cases (Disjunction Elimination)

```
conclusion ::= "cases" proof case_list
case_list ::= case | case case_list
case ::= "case" identifier "{" proof "}"
       | "case" identifier ":" term "{" proof "}"
```

In Deduce, you can use an `or` fact by doing case analysis with the
`cases` statement. There is one `case` for each subformula of the
`or`. 

In the following example, we prove that `x ≤ y or y < x`
from the trichotomy law: `x < y or x = y or y < x`.

```
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
```



## Choose (Proof)

```
proof_stmt ::= "choose" term_list
```

A proof of the form

```
choose e1,...,en
X
```

is a proof of the formula `some x1,...xn. P`
if `X` is a proof of formula `P` where the `x`'s replaced by the `e`'s.

Example:

```{.deduce^#choose_example}
theorem choose_example: some x:Nat. 6 = 2 * x
proof
  choose 3
  conclude 6 = 2 * 3   by evaluate
end
```

## Comma (Logical And Introduction)

```
conclusion ::= proof "," proof
```

See the entry for And (logical conjunction).

## Compose (Functions)

```
term ::= term "∘" term | term "[o]" term
```

The composition of two functions `g ∘ f` is defined in `Maps.pf`
so that `(g ∘ f)(x) = g(f(x))`.

Example:

Applying the successor function `suc` (add 1) to `3` yields `5`.

```{.deduce^#compose_example}
assert (suc ∘ suc)(3) = 5
```

## Conclude (Proof)

```
conclusion ::= "conclude" formula "by" proof
```

This proof statement is useful when you wish to emphasize the end of a
proof by stating the formula that is being proved.

A proof of the form

```
conclude P by X
```

is a proof of formula `P` if `X` is a proof of `P`.

Example:

```{.deduce^#conclude_example}
theorem conclude_example: 1 + 1 = 2
proof
  conclude 1 + 1 = 2 by expand 2* operator+.
end
```

## Conclusion (Proof)

The last statement in a proof (the `conclusion` symbol in the grammar)
must be one of the following:

* [Cases](#cases-disjunction-elimination)
* [Comma (Logical-And Introduction)](#comma-logical-and-introduction)
* [Conclude](#conclude-proof)
* [Conjunct](#conjunct)
* [Expand-In](#expand-in-proof)
* [Equations](#equations)
* [Evaluate](#evaluate-proof)
* [Evaluate-In](#evaluate-in-proof)
* [Help](#help-proof)
* [Identifier](#identifier)
* [Induction](#induction)
* [Instantiation](#instantiation-proof)
* [Period](#period-proof-of-true)
* [Question Mark](#question-mark-proof)
* [Recall](#recall-proof)
* [Sorry](#sorry-proof)
* [Switch](#switch-proof)
* [Symmetric](#symmetric-proof)
* [Transitive](#transitive-proof)

## Conjunct

```
conclusion ::= "conjunct" number "of" proof 
```

A proof of the form

```
conjunct n of X
```

is a proof of `Pn` if `X` is a proof of `P1 and ... and Pk`
and 1 ≤ n ≤ k.

Example:

```{.deduce^#conjunct_example}
theorem conjunct_example: all P:bool, Q:bool. if P and Q then Q and P
proof
  arbitrary P:bool, Q:bool
  assume prem: P and Q
  have p: P         by conjunct 0 of prem
  have q: Q         by conjunct 1 of prem
  conclude Q and P  by p, q
end
```

## Contradiction

During a proof, one sometimes encounters assumptions that contradict
each other. In these situations, you can prove `false` and from that,
anything else (the Principle of Explosion). Here are two ways to prove
`false` from contradictions.

(1) If you have a proof `X` of an equality with different constructors
on the left and right-hand side, such as

```
have X: empty = node(3, empty) by ...
```

or

```
have X: 0 = 1 by ...
```

then you can implicitly use `X` to prove `false`:

```
conclude false by X
```

(2) If you have a proof `X` of `P` and a proof `Y` of `not P`,
then you can prove `false` using `apply`-`to`. (Because
`not P` is shorthand for `if P then false`.)

```
have X: P by ...
have Y: not P by ...
conclude false by apply Y to X
```

## Define (Statement)

```
statement ::= "define" ident ":" type "=" term
            | "define" ident "=" term
```

The `define` feature of Deduce associates a name with a value.  For
example, the following definitions associate the name `five` with the
natural number `5`, and the name `six` with the natural number `6`.

```{.deduce^#define_example}
define five = 2 + 3
define six : Nat = 1 + five
```

Optionally, the type can be specified after the name, following a
colon.  In the above, `six` holds a natural number, so its type is
`Nat`.

## Define (Term)

```
term ::= "define" identifier "=" term ";" term
```

This associates a name with a term for use in the term after the semicolon.

```{.deduce^#define_term_example}
assert 5 = (define x = 3; 2 + x)
```

## Define (Proof)

```
proof_stmt ::= "define" identifier "=" term  proof
```

This associates a name with a term for use in the following proof.
(Note: there is no semicolon after the term when using `define` in a proof.)

```{.deduce^#define_proof_example}
theorem define_proof_example: all x:Nat. 2 * (x + x + x) = (x + x + x) + (x + x + x)
proof
  arbitrary x:Nat
  define y = x + x + x
  suffices y + y + 0 = y + y  by expand 3* operator*.
  replace add_zero[y].
end
```

## Expand (Proof)

```
proof_stmt ::= "expand" identifier_list_bar
```

In the current goal formula, expand the occurrences of the specified
names with their definitions. If a definition is recursive, only one
expansion is performed per time the definition's name is mentioned in
the list. If one of the specified names does not appear in the goal
formula, Deduce signals an error.

```{.deduce^#expand_example}
theorem length_list2: length([0,1]) = 2
proof
  expand length
  show 1 + length([1]) = 2
  expand 2*length
  show 1 + (1 + 0) = 2
  evaluate
end
```

## Expand-In (Proof)

```
conclusion ::= "expand" identifier_list_bar "in" proof
```

In the formula of the given proof, expand the occurrences of the
specified names with their definitions, resulting in the formula that
is proved by this `expand`-`in` statement.  If a definition is
recursive, only one expansion is performed per time the definition's
name is mentioned in the list. If one of the specified names does not
appear in the formula, Deduce signals an error.

```{.deduce^#expand_in_example}
theorem expand_in_example: all ls:List<Nat>. if length(ls) = 0 then ls = []
proof
  arbitrary ls:List<Nat>
  switch ls {
    case [] {
      .
    }
    case node(x, ls') {
      assume A: length(node(x, ls')) = 0
      have B: 1 + length(ls') = 0  by expand length in A
      have C: suc(length(ls')) = 0 by expand operator+ in B
      conclude false by C
    }
  }
end
```

## Divide

```
term ::= term "/" term
```

The division function for `Nat` and `Pos` is defined in `Nat.pf`.
The main theorem is `division_remainder` which states that

```
(n / m) * pos2nat(m) + (n % m) = n
```

Example:

```{.deduce^#division_example}
assert 6 / 3 = 2
assert 7 / 3 = 2
assert 8 / 3 = 2
assert 9 / 3 = 3
```

## Empty Set

```
term ::= "∅"
```

The empty set `∅` does not contain any elements and is defined in
`Set.pf`.

## Equal

```
formula ::= term "=" term
```

The formula `a = b` is true when the left-hand side and right-hand are
the same. 

(In Deduce, there is no distinction between identity and deep equality
as there is in Java because there is no concept of identity in
Deduce.)

## Equations

```
conclusion ::= "equations" equation equation_list
equation ::= term "=" term "by" proof
half_equation ::= "..." "=" term "by" proof
equation_list ::= half_equation
equation_list ::= half_equation equation_list
equation_list ::= "$" equation equation_list
```

Combining a sequence of equations using `transitive` is quite common,
so Deduce provides `equations` to streamline this process.  After the
first equation, the left-hand side of each equation is written as
`...` because it is just a repetition of the right-hand side of the
previous equation.

When using `replace` for one of the reasoning steps in `equations`,
the replacement is, by default, applied to the left-hand side of the
equation (and not the right-hand side). However, if you would like to
apply a replacement to the right-hand side, use hash marks (`#`)
around the region of the right-hand side that you want to change.

Example:

```{.deduce^#equations_example}
theorem equations_example: all x:Nat, y:Nat, z:Nat.
  x + y + z = z + y + x
proof
  arbitrary x:Nat, y:Nat, z:Nat
  equations
    x + y + z = x + z + y      by replace add_commute[y].
          ... = #z + x# + y    by replace add_commute.
          ... = z + y + x      by replace add_commute[x].
end
```

The hash marks can also be used to control where Deduce applies a
`expand`. In the following example, the hash marks tell Deduce to
expand the definition of `length` in the right-hand side of the second
equation.

```{.deduce^#equations_expand_example}
theorem equations_expand_example: all x:Nat, y:Nat, xs:List<Nat>.
  length(node(x, xs)) = length(node(y, xs))
proof
  arbitrary x:Nat, y:Nat, xs:List<Nat>
  equations
    length(node(x,xs)) = 1 + length(xs)         by expand length.
                   ... = # length(node(y,xs)) # by expand length.
end
```


## Evaluate (Proof)

```
conclusion ::= "evaluate"
```

The `evaluate` proof method simplifies the goal formula by applying all
definitions. It succeeds if the formula is simplified to `true`.

## Evaluate-In (Proof)

```
conclusion ::= "evaluate" "in" proof
```

The `evaluate`-`in` proof method simplifies the formula of the given
proof by applying all definitions, producing a proof of the simplified
formula.

## Extensionality

```
proof_stmt ::= "extensionality"
```

To prove that two functions are equal, it is sufficient to prove that
they always produce equal outputs given equal inputs.

```{.deduce^#extensionality_example}
define inc = fun x:Nat { pred(suc(suc(x))) }

theorem extensionality_example: inc = suc
proof
  extensionality
  arbitrary x:Nat
  conclude inc(x) = suc(x) by expand inc | pred.
end
```


## False

```
formula ::= "false"
```

One can prove `false` when there are assumptions that contradict
each other, such as `x = 0` and `x = 1`, or `not P` and `P`.

A proof of `false` can be used to prove anything else!
(This is known as the Principle of Explosion.)


## Formula

A formula is any term of type `bool`.

```
formula ::= term
```

## Function (Term)

```
term ::= "fun" var_list "{" term "}"
         | "λ" var_list "{" term "}"
```

Functions are created with a `fun` expression.  Their syntax starts with
`fun`, followed by parameter names and their types, then the body of the
function enclosed in braces.  For example, the following defines a
function for computing the area of a rectangle.

```{.deduce^#function_term_example}
define area = fun h:Nat, w:Nat { h * w }
```

To call a function, apply it to the appropriate number and type of
arguments.

```{.deduce^#print_area}
print area(3, 4)
```

The output is `12`.

To add type parameters to a function (to make it generic), see
[Generic Function](#generic-function-term).

## Fun (Statement)

```
statement ::= "fun" ident type_params_opt "(" var_list ")" "{" term "}"
```

The `fun` statement is for defining a function (non-recursive).
The function begins with the `fun` keyword, followed by 
the type parameters enclosed in `<` and `>` (if generic),
then the parameter list enclosed in `(` and `)`, and finally
the body of the function enclosed in `{` and `}`.

```{.deduce^#fun_interchange_example}
fun interchange(p : Pair<Nat,Nat>) {
  pair(second(p), first(p))
}

assert interchange(pair(1,2)) = pair(2,1)
```

## Function Type

```
type ::= "fn" type_params_opt type_list "->" type
```

A function type classifies a function. This includes both recursive
functions (`function`) and anonymous functions (`fun` or `λ`).  If the
function is generic, its function type includes type parameters
enclosed in `<` and `>`.

## Generic (Formula)

```
formula ::= "<" identifier_list ">" formula
```

This parametrizes a formula by a list of type parameters.  For
example, the following formula states that if the length of a list is
0, then the list must be empty. The type parameter `<T>` means that
this formula applies to lists with any element type.

```
<T> all xs:List<T>. if length(xs) = 0 then xs = empty
```


## Generic (Term)

```
term ::= "generic" identifier_list "{" term "}"
```

A term of the form

```
generic T1, ..., Tn { X }
```

produces a generic function with type parameters 
`T1`, ..., `Tn`, if term `X` produces a function
(e.g., using `fun`).

An example use of `generic` is in `Maps.pf`, in the
definition of function composition.

```{.deduce^#generic_example}
define operator ∘ = generic T,U,V { fun g:fn U->V, f:fn T->U {
                        fun x:T { g(f(x)) } } }
```

Generic recursive functions can be defined using the `function`
statement (see [Function](#function-statement)).

## Generic Function (Term)

(This feature was added in Deduce version 1.1.)

```
term ::= "fun" type_params_opt var_list "{" term "}"
         | "λ" type_params_opt var_list "{" term "}"
```

To make a [Function](#function-term) generic, add type parameters surrounded
by `<` and `>`. For example, the following function declares two
type parameters with the syntax `<T, U>`.

```{.deduce^#generic_fun_example}
define swap = fun<T, U> p:Pair<T,U> { pair(second(p), first(p)) }

assert first(swap(pair(1,2))) = 2
assert second(swap(pair(1,2))) = 1
```

## Given

An assumption or fact that is already proved.

## Greater-Than

```
formula ::= term ">" term
```

The greater-than operator on natural numbers is defined in `Nat.pf`
and is defined in terms of less-than as follows

```
x > y = y < x
```


Example:

```{.deduce^#greater_example}
assert 2 > 1
assert not (1 > 1)
assert not (0 > 1)
```

## Greater-Than or Equal

```
formula ::= term "≥" term
formula ::= term ">=" term
```

The greater-than-or-equal operator on natural numbers is defined in `Nat.pf`
and is defined in terms of less-than-or-equal as follows

```
x ≥ y = y ≤ x
```

Example:

```{.deduce^#greater_equal_example}
assert 2 ≥ 1
assert 1 ≥ 1
assert not (0 ≥ 1)
```

## Have (Proof Statement)

```
proof_stmt ::= "have" identifier ":" term "by" proof 
             | "have" ":" term "by" proof 
```

Use `have` to prove a formula that may help you later to prove the
goal.

A proof of the form

```
have label: P by X
Y
```

is a proof of `Q` as long as `Y` is a proof of `Q` and `X` is a proof of `P`.

Inside the proof `X` the goal changes to `P`.

After the `have` statement, the formula `P` becomes a given and can be
used inside the proof `Y`.

## Help (Proof)

```
conclusion ::= "help" proof
```

This halts Deduce and prints advice regarding how to use the formula
of the supplied proof. Typically the supplied proof is the label for a
given.


## Identifier 

```
term ::= identifier
formula ::= identifier
conclusion ::= identifier
```

Identifiers are used in Deduce to give names to functions and values and
to label theorems and facts.

An identifier is a sequence of characters that starts with an upper or
lower-case letter or an underscore, and is followed by letters,
digits, or the special characters `!`, `?`, and `'`.  An identifier
can also be an operator, which starts with the keyword
`operator` and is then followed by one of the following operators:
`+`, `-`, `*`, `/`, `%`, `=`, `≠`, `/=`, `<`, `≤`, `<=`, `≥`, `>=`
`++`, `∩`, `&`, `∈`, `in`, `∪`, `|`, `⨄`, `.+.`, `⊆`, `(=`, `∘`, `.o.`.


## Identifier List

A comma-separated sequence of identifiers.

```
identifier_list ::= identifier
identifier_list ::= identifier "," identifier_list
```

## Identifier List Bar

A bar-separated sequence of identifiers. If an identifier is preceded
by a number and the multiplication sign, then the identifier is
repeated. (e.g. to make a definition expand recursively more than
once.)

```
identifier_list_bar ::= identifier
identifier_list_bar ::= natural_number "*" identifier
identifier_list_bar ::= identifier "|" identifier_list_bar
identifier_list_bar ::= natural_number "*" identifier "|" identifier_list_bar
```

## If and only if (iff)

See the entry for [Biconditional](#biconditional-if-and-only-if).

## If Then (Conditional Formula)

A formula `if P then Q` is true when both `P` and `Q` are true and it
is true when `P` is false.

To prove a conditional formula, use `assume`. (See the entry for [Assume](#assume).)

To use a given that is a conditional formula, use `apply`-`to`.
(See the entry for [Apply-To](#apply-to-proof-modus-ponens).)

## If Then Else (Term)

A term of the form

```
if a then b else c
```

is equal to `b` when `a` is true and equal to `c` when `a` is false.

Example:

```{.deduce^#if_then_else_example}
assert (if true then 1 else 2) = 1
assert (if false then 1 else 2) = 2

theorem if_then_else_example: all P:bool.
  (if P then 1 else 2) = (if not P then 2 else 1)
proof
  arbitrary P:bool
  switch P {
    case true { . }
    case false { . }
  }
end
```

## Import (Statement)

```
statement ::= "import" identifier
```

Import all of the definitions and theorems from the specified file
(without the file extension).


## In (Set Membership)

```
formula ::= term "∈" term
formula ::= term "in" term
```

The formula `x ∈ S` is true when element `x` is contained in the set `S`.

Example:

```{.deduce^#membership_example}
define S = single(1) ∪ single(2) ∪ single(3)
assert 1 ∈ S and 2 ∈ S and 3 ∈ S and not (4 ∈ S)
```

## Induction

```
conclusion ::= "induction" type ind_case*
ind_case ::= "case" pattern "{" proof "}"
           | "case" pattern "assume" assumption_list "{" proof "}"
```

A proof of the form

```
induction T
case c1(e11,...,e1k) assume IH1, ... { X1 }
...
case cn(en1,...,enj) assume IH1, ... { Xn }
```

is a proof of the formula `all x:T. P`
if each `Xi` is a proof of `P` where `x` is replaced
by `ci(ei1,...,eij)`. The type `T` must be a union type.
Each proof `Xi` may use its induction
hypotheses `IH1, ...`. For each term `ein` whose type is `T`
(so it is recursive), the induction hypothesis is
the formula `P` with `x` replaced by the constructor argument `ein`.

Example:

```{.deduce^#induction_example}
theorem induction_example: all n:Nat.
  n + 0 = n
proof
  induction Nat
  case 0 {
    conclude 0 + 0 = 0   by expand operator+.
  }
  case suc(n') assume IH: n' + 0 = n' {
    equations
      suc(n') + 0 = suc(n' + 0)  by expand operator+.
              ... = suc(n')      by replace IH.
  }
end
```

## Injective (Proof)

```
proof_stmt ::= "injective" term proof
```

The `injective` proof rule allows you to conclude that the inputs to a
constructor are equal if the outputs are equal. For example,
if `suc(x) = suc(y)` then `x = y`.

Example:

```{.deduce^#injective_example}
theorem injective_example: all x:Nat, y:Nat, z:Nat.
  if suc(x) = suc(y) and suc(y) = suc(z) then x = z
proof
  arbitrary x:Nat, y:Nat, z:Nat
  assume prem: suc(x) = suc(y) and suc(y) = suc(z)
  have: x = y by injective suc prem
  have: y = z by injective suc prem
  transitive (recall x = y) (recall y = z)
end
```


## Instantiation (Proof)

```
conclusion ::= proof '<' type_list '>'
             | proof '[' term_list ']'
```

Use square brackets `[` and `]` to instantiate an `all` formula with 
terms and use angle brackets `<` and `>` to instantiate an `all`
formula with types.

Example:

```{.deduce^#instantiate_proof_example}
theorem instantiate_proof_example: length(node(42, empty)) = 1
proof
  have X: all T:type. all x:T. length(node(x, empty)) = 1 by {
    arbitrary T:type arbitrary x:T
    expand 2* length | 2* operator+.
  }
  conclude length(node(42, empty)) = 1
    by X<Nat>[42]
end
```


## Instantiation (Term)

```
term ::= @ term '<' type_list '>'
```

Instantiates a generic function or constructor, replaces its type
parameters with the given type arguments.

```{.deduce^#instantiate_example}
define empty_nat_list = @empty<Nat>
```

## Intersection

```
term ::= term "∩" term
term ::= term "&" term
```

Set intersection is defined in `Set.pf`.
The intersection of sets `A` and `B`, written `A ∩ B`,
contains the items that occur both sets.

Example:

```{.deduce^#intersect_example}
define C = single(1) ∪ single(2)
define D = single(2) ∪ single(3)
assert 2 ∈ C ∩ D
assert not (1 ∈ C ∩ D)
assert not (3 ∈ C ∩ D)
```

## Less-Than

```
formula ::= term "<" term
```

The less-than operator on natural numbers is defined in `Nat.pf`
as follows.

```
x < y = suc(x) ≤ y
```

To find theorems about the less-than operator in `Nat.thm`, search for
theorems with `less` in the name.

Example:

```{.deduce^#less_than_example}
assert 1 < 2
assert not (1 < 1)
assert not (2 < 1)
```

## Less-Than or Equal

```
formula ::= term "≤" term
          | term "<=" term
```

The less-than-or-equal operator on natural numbers is defined in `Nat.pf`
as follows.

```
function operator ≤(Nat,Nat) -> bool {
  operator ≤(0, m) = true
  operator ≤(suc(n'), m) =
    switch m {
      case 0 { false }
      case suc(m') { n' ≤ m' }
    }
}
```

To find theorems about the less-than operator in `Nat.thm`, search for
theorems with `less_equal` in the name.

Example:

```{.deduce^#less_equal_example}
assert 1 ≤ 1
assert 1 ≤ 2
assert not (2 ≤ 1)
```

## List (Term)

```
term ::= "[" term_list "]"
```

Deduce treats `[t1,t2,...,tn]` as syntactic sugar for
`node(t1, node(t2, ... node(tn, empty)))`.


## List (Type)

The `List` type represents a singly-linked list of items and is
defined in `List.pf` as follows.

```
union List<T> {
  empty
  node(T, List<T>)
}
```

The sequence `3,8,4` can be represented as a `List` by creating three
nodes that are composed in the following way.

```{.deduce^#list_example}
define list_example = node(3, node(8, node(4, empty)))
```

## Mark 

```
term ::= "#" term "#"
```

Marking a subterm with hash symbols restricts a `replace` or `expand`
proof to only apply to that subterm.

The [`equations`](#equations) feature, by default, places marks around the entire
left-hand side of each equation. However, you can override this
default by placing explicit marks.

```{.deduce^#mark_example}
theorem mark_example: all x:Nat. if x = 1 then x + x + x = 3
proof
  arbitrary x:Nat
  assume: x = 1
  equations
    #x# + x + x = 1 + x + x   by replace recall x = 1.
  $ 1 + #x# + x = 1 + 1 + x   by replace recall x = 1.
  $ 1 + 1 + #x# = 1 + 1 + 1   by replace recall x = 1.
            ... = 1 + #x# + 1 by replace recall x = 1.
            ... = 1 + 1 + 1   by replace recall x = 1.
            ... = 3           by evaluate
end
```

## Modulo

```
term ::= term "%" term
```

The modulo operator is defined in `Nat.pf` as follows.  The first
argument is a natural number (of type `Nat`) and the second argument
is a positive number (of type `Pos`).

```
n % m = n - (n / m) * pos2nat(m)
```

Example:

```{.deduce^#mod_example}
assert 1 % 2 = 1
assert 2 % 2 = 0
assert 3 % 2 = 1
assert 4 % 2 = 0
```

## Modus Ponens

See the entry for [Apply-To](#apply-to-proof-modus-ponens).

## Multiply

```
term ::= term "*" term
```

Multiplication on natural numbers is defined in `Nat.pf` as follows.

```
function operator *(Nat,Nat) -> Nat {
  operator *(0, m) = 0
  operator *(suc(n), m) = m + (n * m)
}
```

To find theorems about multiplication, search for `mult` in `Nat.thm`.

Example:

```{.deduce^#multiply_example}
assert 2 * 3 = 6
```

## MultiSet (Type)

The `MultiSet<T>` type represents the standard mathematical notion of
a multiset, which is a set that may contain duplicates of an
element. The `MultiSet<T>` type is defined in `MultiSet.pf`.


## Natural Number

```
natural_number ::= [0-9]+
term ::= natural_number
```

A natural number literal is a sequence of one or more digits.


## Not

```
formula ::= "not" formula
```

The formula `not P` is true when `P` is false.
Deduce treats `not P` as syntactic sugar for `(if P then false)`.


## Not Equal

```
formula ::= term "≠" term
formula ::= term "/=" term
```

Deduce treats `x ≠ y` as syntactic sugar for `not (x = y)`.

## Obtain (Proof)

```
proof_stmt ::= "obtain" identifier_list "where" assumption "from" proof
```


A proof of the form

```
obtain x1,...,xn where label: P from X
Y
```

is a proof of formula `Q` if `Y` is a proof of `Q`.
The `X` must be a proof of the form `some x1:T1,...,xn:Tn. P`.
The proof `Y` may use the `label` as a proof of `P`
and it may also refer to the proof of `P` by writing `recall P`.

Example:

```{.deduce^#obtain_example}
theorem obtain_example: all n:Nat. 
  if (some x:Nat. n = 4 * x) then (some x:Nat. n = 2 * x)
proof
  arbitrary n:Nat
  assume prem: (some x:Nat. n = 4 * x)
  obtain x where m4: n = 4 * x from prem
  choose 2 * x
  equations
     n = 4 * x          by m4
   ... = (2 * 2) * x    by evaluate
   ... = 2 * 2 * x      by mult_assoc
end
```

## Or  (logical disjunction)

```
formula ::= formula "or" formula
```

The formula `P or Q` is true when either `P` is true or `Q` is true.

Example:

```{.deduce^#or_example}
assert true or true
assert true or false
assert false or true
assert not (false or false)
```

To prove `P or Q` it is enough to just prove `P` or to just prove `Q`.

```{.deduce^#or_example_intro1}
theorem or_example_intro1: all P:bool, Q:bool. if P then P or Q
proof
  arbitrary P:bool, Q:bool
  assume: P
  conclude P or Q by recall P
end
```

```{.deduce^#or_example_intro2}
theorem or_example_intro2: all P:bool, Q:bool. if Q then P or Q
proof
  arbitrary P:bool, Q:bool
  assume: Q
  conclude P or Q by recall Q
end
```

To use a given of the form `P or Q`, use
[Cases (Disjunction Elimination)](#cases-disjunction-elimination).


## Parentheses

```
term ::= "(" term ")"
formula ::= "(" formula ")"
proof ::= "(" proof ")"
```

A term, formula, or a proof may be surrounded in parentheses.

## Pattern

```
pattern ::= identifier | "0" | "true" | "false" | identifier "(" identifier_list ")"
```

This syntax is used in [Switch (Term)](#switch-term), [Switch (Proof)](#switch-proof),
and [Function (Statement)](#function-statement) via a Pattern List.


## Parameter List

```
param_list ::= ε | pattern | pattern "," identifier_list
```

A parameter list begins with a pattern (for the first function
parameter) and then continues with a comma-separated sequence of zero
or more identifiers (for the rest of the function parameters).

## Period (Proof of True)

```
conclusion ::= "."
```

A period is a proof of the formula `true` in Deduce.


## Pos (Positive Integers)

The type of positive integers `Pos` is defined in `Nat.pf`.


## Proof

```
proof ::= proof_stmt proof
        | conclusion
```

A proof is a sequence of zero or more [proof statements](#proof-statement)
that finishes with a [conclusion](#conclusion-proof).

## Proof List

```
proof_list :: proof 
proof_list ::= proof "|" proof_list
```

A list of proofs separated by vertical bars. This syntax is used
in [Replace (Proof)](#replace-proof).

## Proof Statement

The following are proof statements (`proof_stmt` symbol in the grammar).
A proof may begin with zero or more proof statements, but it must end
with a [Conclusion](#conclusion-proof) (not a proof statement).

* [Arbitrary](#arbitrary-forall-introduction)
* [Assume](#assume)
* [Choose](#choose-proof)
* [Define](#define-proof)
* [Expand](#expand-proof)
* [Extensionality](#extensionality)
* [Have](#have-proof-statement)
* [Injective](#injective-proof)
* [Obtain](#obtain-exists-elimination)
* [Replace](#replace-proof)
* [Show](#show-proof)
* [Suffices](#suffices-proof-statement)
* [Suppose](#suppose)

## Print (Statement)

```
statement ::= "print" term
```

You can ask Deduce to print a value to standard output using the
`print` statement.

```{.deduce^#print_example}
print five
```

The output is `5`.


## Question Mark `?` (Proof)

```
conclusion ::= "?"
```

A proof can be left incomplete by placing a `?` in the part that you
don't know. Deduce halts at the `?` and prints an error message with
the location of the `?` and the formula that needs to be proved, as
well as some advice about how to prove it.


## Recall (Proof)

```
conclusion ::= "recall" term_list
```


A proof of the form
```
recall P1, ..., Pn
```
is a proof of the formula `P1 and ... and Pn`. The formulas
`P1`,...,`Pn` must be in the givens at the current point in the proof.


## Recursive Function (Statement)

```
statement ::= "recursive" identifier type_params_opt "(" type_list ")" "->" type "{" fun_case* "}"
fun_case ::= identifier "(" pattern_list ")" "=" term
```

The `recursive` statement is for defining recursive functions that
operate on `union` types. Recursive functions in Deduce are somewhat
special to make sure they always terminate.

* The first parameter of the function must be a union.
* The function definition must include a clause for every
  constructor in the union.
* The first argument of every recursive call must be a sub-part of the
  current constructor of the union.

A recursive function begins with the `recursive` keyword (or `function` in version 1.0),
followed by the name of the function, then the parameters types and the return
type. The body of the function includes one equation for every
constructor in the union of its first parameter. For example, here's
the definition of a `length` function for lists of natural numbers.

```{.deduce^#function_length_example}
union NatList {
  Empty
  Node(Nat, NatList)
}

recursive length(NatList) -> Nat {
  length(Empty) = 0
  length(Node(n, next)) = 1 + length(next)
}
```

There are two clauses in the body of `length` because the `NatList` union
has two constructors. The clause for `Empty` says that its length is
`0`.  The clause for `Node` says that its length is one more than the
length of the rest of the linked list.  Deduce approves of the
recursive call `length(next)` because `next` is part of `Node(n, next)`.

Recursive functions may have more than one parameter but pattern
matching is only supported for the first parameter. 
If you need to pattern match on a parameter that is not the first, you
can use a `switch` statement. 


## Reflexive (Proof)

```
conclusion ::= reflexive
```

The proof `reflexive` proves that `a = a` for any term `a`.

## Replace (Proof)

```
proof_stmt ::= "replace" proof_list
```

Change the current goal formula according to the equalities proved by
the specified [Proof List](#proof-list). Each equality may be a
literal equality (has the form `LHS = RHS`) or it can be a generalized
equality (has the form `all x1:T1,...,xn:Tn. LHS = RHS`).

For each equality going left-to-right in the proof list, any subterm
in the goal formula that matches the left-hand side of the equality
(`LHS`) is replaced by the right-hand side of the equality
(`RHS`). Once a subterm is rewritten by an equality, the resulting
subterm is not rewritten further by the same equality. On the other
hand, rewriting with an equality may apply to multiple disjoint
locations in a formula.

```{.deduce^#replace_example}
theorem replace_example: all x:Nat,y:Nat. if (x = y) then (1 + x = 1 + y)
proof
  arbitrary x:Nat,y:Nat
  assume prem: x = y
  suffices 1 + y = 1 + y by replace prem.
  .
end
```

## Replace-In (Proof)

```
conclusion ::= "replace" proof_list "in" proof
```

In the formula of the given proof, replace according to the equalities
proved by the specified [Proof List](#proof-list), resulting in the
formula that is proved by this `replace`-`in` statement. 
The algorithm for rewriting described in the entry for
[Replace (Proof)](#replace-proof).

```{.deduce^#replace_in_example}
theorem replace_in_example: all x:Nat, y:Nat.
  if x < y then not (x = y)
proof
  arbitrary x:Nat, y:Nat
  assume: x < y
  assume: x = y
  have: y < y by replace (recall x = y) in (recall x < y)
  conclude false by apply less_irreflexive[y] to (recall y < y)
end
```

## Set (Type)

The `Set<T>` type defined in `Set.pf` represents the standard
mathematical notion of a set. The empty set is written `∅` and the
usual set operations such as union `∪`, intersection `∩`, membership
`∈`, and subset-or-equal `⊆` are all defined in `Set.pf`.  The
`Set.thm` file provides a summary of the many theorems about sets that
are proved in `Set.pf`.


## Show (Proof)

```
proof_stmt ::= "show" formula
```

Use `show` to document the current goal formula. Deduce checks to make
sure that the given formula matches the current goal.


## Some (Formula)

```
formula ::= "some" var_list "." formula
```

The formula `some x1:T1,...,xn:Tn. P` is true when there exists
a choice for `x1`,...,`xn` such that `P` is true.

To prove a `some` formula, see the entry for
[Choose](#choose-proof).

To use a `some` formula, see the entry for [Obtain](#obtain-exists-elimination)

## Sorry (Proof)

```
conclusion ::= "sorry"
```

`sorry` is the get-out-of-jail free card. It can prove anything.
However, it prints a warning message with the location of the `sorry`.

## Subset or Equal

```
formula ::= term "⊆" term
formula ::= term "(=" term
```

The formula `A ⊆ B` is true when every element of set `A` is
contained in set `B`. That is, given `A` and `B` of type `Set<T>`,
the definition of `A ⊆ B` is as follows.
```
A ⊆ B = (all x:T. if x ∈ A then x ∈ B)
```

Example:

```{.deduce^#subset_example}
define E = single(1)
define F = single(1) ∪ single(2)

theorem subset_example: E ⊆ F
proof
  expand E | F | operator ⊆
  arbitrary x:Nat
  assume x1: x ∈ single(1)
  apply union_member<Nat>[x, single(1), single(2)] to x1
end
```

## Subtract

```
term ::= term "-" term
```

Subtraction for natural numbers is defined in `Nat.pf` as follows

```
function operator -(Nat,Nat) -> Nat {
  operator -(0, m) = 0
  operator -(suc(n), m) =
    switch m {
      case 0 { suc(n) }
      case suc(m') { n - m' }
    }
}
```

Note that subtraction on natural numbers is different from subtraction
on integers, as they are no negative natural numbers. If you subtract
a larger natural number from a smaller natural number, the result is `0`.

```{.deduce^subtract_example}
assert 3 - 2 = 1
assert 3 - 3 = 0
assert 2 - 3 = 0
```

To search for theorems about subtraction in `Nat.thy`, search for
theorems with `sub` in the name.

## Suffices (Proof Statement)

```
proof_stmt ::= "suffices" formula "by" proof
```

A proof of the form

```
suffices P by X
Y
```

is a proof of the formula `Q` if `X` is a proof that `P` implies `Q`
and `Y` is a proof of `Q`.

Use `suffices` to transform the goal formula into a simpler formula.
Thus, the `suffices` feature enables reasoning backwards from the goal.

Example:

One often wants to transform the goal by using a definition or equation.
For example, in the following theorem we change the goal
from

```
length(node(3, empty)) = 1
```

into

```
1 + 0 = 1
```

by two uses of the definition of `length`.
We then prove the new goal with theorem `add_zero` from `Nat.thm`.

```{.deduce^#suffices_example}
theorem suffices_example:
  length(node(3, empty)) = 1
proof
  suffices 1 + 0 = 1  by expand 2*length.
  add_zero
end
```

## Suppose

See the entry for [Assume](#assume).

## Switch (Term)

```
term ::= "switch" term "{" switch_case* "}"
switch_case ::= "case" pattern "{" term "}"
```

(See the entry for [Pattern](#pattern) for the syntax of `pattern`.)

The subject of the `switch` must be of union type or `bool` (e.g., not
a function). The body of the `switch` must have one `case` for every
constructor in the `union`, or for `bool`, the cases are `true` and
`false`.  The body of each `case` is a term and they all must have the
same type.  The `switch` evaluates the subject and compares it to each
case, then evaluates the body of the case that matched.

```{.deduce^#switch_example}
define flip = fun x:bool {
  switch x {
    case true { false }
    case false { true }
  }
}
assert flip(false)
assert not flip(true)
```

## Switch (Proof)

```
conclusion ::= "switch" term "{" switch_proof_case* "}"
switch_proof_case ::= "case" pattern "{" proof "}"
switch_proof_case ::= "case" pattern assumptions "{" proof "}"
assumptions ::= "suppose" assumption_list | "assume" assumption_list
```

(See entry for Assumption List for the syntax of `assumption_list`.)

A proof of the form

```
switch t {
  case p1 assume eq1: t = p1 {
    X1
  }
  ...
  case pn assume eqn: t = pn {
    Xn
  }
}
```

is a proof of formula `R` if `X1`,...,`Xn` are all proofs of `R`.
The fact `t = p1` is a given that can be used in `X1`
and similarly for the other cases.

Example:

```{.deduce^#switch_proof_example}
theorem switch_proof_example: all x:Nat. x = 0 or 0 < x
proof
  arbitrary x:Nat
  switch x {
    case 0 assume xz: x = 0 {
      conclude true or 0 < 0 by .
    }
    case suc(x') assume xs: x = suc(x') {
      have z_l_sx: 0 < suc(x')
          by expand operator < | 2* operator ≤.
      conclude suc(x') = 0 or 0 < suc(x') by z_l_sx
    }
  }
end
```

## Symmetric (Proof)

```
conclusion ::= "symmetric" proof
```

If `X` is a proof of `a = b`, then `symmetric X` is a proof of `b = a`
for any terms `a` and `b`.


## Theorem (Statement)

```
statement ::= "theorem" IDENT ":" formula "proof" proof "end"
            | "lemma" IDENT ":" formula "proof" proof "end"
```

A theorem (or lemma) proves that a formula is true. The theorem's name
can then be used later when one needs to prove the formula again.

A theorem has the form

```
theorem label: P
proof
  X
end
```

The proof `X` must prove the formula `P`. After the theorem, the `label` can be used
as a proof of `P`.


## Term List

A term list is a comma-separated sequence of zero or more terms.

```
term_list ::= ε | term | term "," term_list
```

## Transitive (Proof)

```
conclusion ::= "transitive" proof proof
```

If `X` is a proof of `a = b` and `Y` is a proof of `b = c`,
then `transitive X Y` is a proof of `a = c`, for any
terms `a`, `b`, and `c`.

## True (Formula)

```
formula ::= "true"
```

There's not much to say about `true`. It's true!
Proving `true` is easy. Just use a period.

```{.deduce^#true_example}
theorem true_example: true
proof
  .
end
```

## Type

```
type ::= "bool"                                        // type of a Boolean
       | identifier                                    // type of a union
       | identifier "<" type_list ">"                  // type of a generic union
       | "fn" type_params_opt type_list "->" type      // type of a function 
       | "(" type ")"
```

## Type List

```
type_list ::= ε | type | type "," type_list
```

A type list is a comma-separated list of zero or more types.


## Type Parameters

```
type_params_opt ::= ε | "<" identifier_list ">"
```

Specifies the type parameters of a generic union or generic function.


## Union (Statement)

```
statement ::= "union" identifier type_params_opt "{" constructor* "}"
constructor ::= identifier | identifier "(" type_list ")"
```

The `union` statement defines a new type whose values are created by
invoking one of the constructors declared inside the union.

Example:

The following union statement defines a `Tree` type that has two kinds
of nodes, `Leaf` nodes with zero children and `Internal` nodes with
two children. We create a three-node tree `T3` by using the
constructors `Leaf` and `Internal` to create the nodes.

```{.deduce^#union_example}
union Tree {
  Leaf(Nat)
  Internal(Tree, Nat, Tree)
}

/*
            5
           / \
          4   7
*/
define T1 : Tree = Leaf(4)
define T2 : Tree = Leaf(7)
define T3 : Tree = Internal(T1, 5, T2)
```

## Union (Operator on Sets)

```
term ::= term "∪" term
term ::= term "|" term
```

Set union is defined in `Set.pf`.
The union of sets `A` and `B`, written `A ∪ B`,
contains the items that occur in either set.

Example:

```{.deduce^#set_union_example}
define C' = single(1) ∪ single(2)
define D' = single(2) ∪ single(3)
assert 1 ∈ C' ∪ D'
assert 2 ∈ C' ∪ D'
assert 3 ∈ C' ∪ D'
assert not (4 ∈ C' ∪ D')
```

## Variable List

```
var_list ::= ε | ident | ident ":" type
       | ident ":" type "," var_list
       | ident "," var_list
```

A comma-separated list of variable declarations. Each variable may
optionally be annotated with its type.

<!--
```{.deduce^file=Reference.pf} 
import Nat
import List
import Set
import MultiSet
import Maps
import Pair

<<function_length_example>>
<<add_example>>
<<add_multiset_example>>
<<all_example_bool>>
<<all_example_intro>>
<<all_example_elim>>
<<and_example>>
<<and_example_intro>>
<<and_example_elim>>
<<append_example>>
<<apply_to_example>>
<<arbitrary_example>>
<<assert_example>>
<<assume_example>>
<<list_example>>
<<call_example>>
<<choose_example>>
<<compose_example>>
<<conclude_example>>
<<conjunct_example>>
<<define_example>>
<<define_term_example>>
<<define_proof_example>>
<<expand_example>>
<<expand_in_example>>
<<division_example>>
<<equations_example>>
<<equations_expand_example>>
<<greater_example>>
<<greater_equal_example>>
<<if_then_else_example>>
<<membership_example>>
<<induction_example>>
<<instantiate_example>>
<<intersect_example>>
<<less_than_example>>
<<less_equal_example>>
<<mark_example>>
<<mod_example>>
<<obtain_example>>
<<or_example>>
<<or_example_intro1>>
<<or_example_intro2>>
<<print_example>>
<<replace_example>>
<<replace_in_example>>
<<switch_example>>
<<switch_proof_example>>
<<subset_example>>
<<suffices_example>>
<<true_example>>
<<union_example>>
<<fun_interchange_example>>
<<generic_fun_example>>
```
-->
