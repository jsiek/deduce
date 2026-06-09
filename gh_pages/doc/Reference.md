# Reference Manual

This is a comprehensive reference for Deduce. It describes each
feature in alphabetical order by keyword. It gives the grammar rule
(syntax) and describes its meaning and/or how it is used in a proof.

In the grammar rules, an unquoted asterisk means zero-or more
repetitions of the grammar item that it follows.
The symbol ε means the empty string.

<!--
Note to maintainers:
Grammar blocks marked `deduce-grammar` are checked against `Deduce.lark`
by CI. Unmarked grammar blocks may intentionally use a simplified
presentation while they are migrated to the strict check.
-->

## Contents

- [Add](#add)
- [Add (Multiset)](#add-multiset)
- [All (Universal Quantifier)](#all-universal-quantifier)
- [And (logical conjunction)](#and-logical-conjunction)
- [Append](#append)
- [Apply-To Proof (Modus Ponens)](#apply-to-proof-modus-ponens)
- [Arbitrary (Forall Introduction)](#arbitrary-forall-introduction)
- [Assert (Statement)](#assert-statement)
- [Assume](#assume)
- [Assumption and Assumption List](#assumption-and-assumption-list)
- [At Symbol `@`](#at-symbol)
- [Auto `auto` (Automatic Reduction)](#auto-auto-automatic-reduction)
- [Biconditional (if and only if)](#biconditional-if-and-only-if)
- [Bool (Type)](#bool-type)
- [Braces (Proof)](#braces-proof)
- [Call (Term)](#call-term)
- [Cases (Disjunction Elimination)](#cases-disjunction-elimination)
- [Choose (Proof)](#choose-proof)
- [Comma (Logical And Introduction)](#comma-logical-and-introduction)
- [Compose (Functions)](#compose-functions)
- [Conclude (Proof)](#conclude-proof)
- [Conclusion (Proof)](#conclusion-proof)
- [Conjunct](#conjunct)
- [Contradict (Proof)](#contradict-proof)
- [Contradiction](#contradiction)
- [Define (Statement)](#define-statement)
- [Define (Term)](#define-term)
- [Define (Proof)](#define-proof)
- [Divide](#divide)
- [GCD](#gcd)
- [Expand (Proof)](#expand-proof)
- [Expand-In (Proof)](#expand-in-proof)
- [Empty Set](#empty-set)
- [Equal](#equal)
- [Equations](#equations)
- [Evaluate (Proof)](#evaluate-proof)
- [Evaluate-In (Proof)](#evaluate-in-proof)
- [Extensionality](#extensionality)
- [False](#false)
- [Formula](#formula)
- [Function (Term)](#function-term)
- [Function (Statement)](#function-statement)
- [Function Type](#function-type)
- [Generic (Formula)](#generic-formula)
- [Generic (Term)](#generic-term)
- [Generic Function (Term)](#generic-function-term)
- [Given](#given)
- [Greater-Than](#greater-than)
- [Greater-Than or Equal](#greater-than-or-equal)
- [Have (Proof Statement)](#have-proof-statement)
- [Help (Proof)](#help-proof)
- [Identifier](#identifier)
- [Identifier List](#identifier-list)
- [Identifier List Bar](#identifier-list-bar)
- [If and only if (iff)](#if-and-only-if-iff)
- [If Then (Conditional Formula)](#if-then-conditional-formula)
- [If Then Else (Term)](#if-then-else-term)
- [Import (Statement)](#import-statement)
- [In (Set Membership)](#in-set-membership)
- [Induction](#induction)
- [Inductive (Statement)](#inductive-statement)
- [Injective (Proof)](#injective-proof)
- [Instantiation (Proof)](#instantiation-proof)
- [Instantiation (Term)](#instantiation-term)
- [Intersection](#intersection)
- [Less-Than](#less-than)
- [Less-Than or Equal](#less-than-or-equal)
- [List (Term)](#list-term)
- [List (Type)](#list-type)
- [Mark](#mark)
- [Modulo](#modulo)
- [Modus Ponens](#modus-ponens)
- [Multiply](#multiply)
- [MultiSet (Type)](#multiset-type)
- [Natural Number](#natural-number)
- [Not](#not)
- [Not Equal](#not-equal)
- [Obtain (Proof)](#obtain-proof)
- [Opaque (Visibility)](#opaque-visibility)
- [Operator Precedence](#operator-precedence)
- [Or  (logical disjunction)](#or-logical-disjunction)
- [Parentheses](#parentheses)
- [Pattern](#pattern)
- [Parameter List](#parameter-list)
- [Period (Proof of True)](#period-proof-of-true)
- [Private (Visibility)](#private-visibility)
- [Public (Visibility)](#public-visibility)
- [Proof](#proof)
- [Proof List](#proof-list)
- [Proof Statement](#proof-statement)
- [Predicate (Statement)](#predicate-statement)
- [Print (Statement)](#print-statement)
- [Question Mark `?` (Proof)](#question-mark-proof)
- [Reason](#reason)
- [Recall (Proof)](#recall-proof)
- [Recursive Function (Statement)](#recursive-function-statement)
- [Relation (Statement)](#relation-statement)
- [Reflexive (Proof)](#reflexive-proof)
- [Replace (Proof)](#replace-proof)
- [Replace-In (Proof)](#replace-in-proof)
- [Rule Induction (Proof)](#rule-induction-proof)
- [Rule Inversion (Proof)](#rule-inversion-proof)
- [Simplify (Proof)](#simplify-proof)
- [Set (Type)](#set-type)
- [Show (Proof)](#show-proof)
- [Some (Formula)](#some-formula)
- [Sorry (Proof)](#sorry-proof)
- [Subset or Equal](#subset-or-equal)
- [Subtract (Producing Integers)](#subtract-producing-integers)
- [Subtraction of Unsigned Integers (aka. monus or truncated subtraction)](#subtraction-of-unsigned-integers-aka-monus-or-truncated-subtraction)
- [Suffices (Proof Statement)](#suffices-proof-statement)
- [Suppose](#suppose)
- [Switch (Term)](#switch-term)
- [Switch (Proof)](#switch-proof)
- [Symmetric (Proof)](#symmetric-proof)
- [Theorem (Statement)](#theorem-statement)
- [Term List](#term-list)
- [Trace (Statement)](#trace-statement)
- [Transitive (Proof)](#transitive-proof)
- [True (Formula)](#true-formula)
- [Type](#type)
- [Type Alias (Statement)](#type-alias-statement)
- [Type List](#type-list)
- [Type Parameters](#type-parameters)
- [Union (Statement)](#union-statement)
- [Union (Operator on Sets)](#union-operator-on-sets)
- [Unsigned Integer](#unsigned-integer)
- [Variable List](#variable-list)
- [View (Statement)](#view-statement)
- [Visibility](#visibility)

## Add

```deduce-grammar
additive_term ::= additive_term "+" multiplicative_term
```

The addition operator for unsigned integers is defined in `UInt.pf`
and the one for integers is defined in `Int.pf`.

Example:

```{.deduce^#add_example}
assert 2 + 3 = 5
```

## Add (Multiset)

```deduce-grammar
additive_term ::= additive_term "⨄" multiplicative_term
additive_term ::= additive_term ".+." multiplicative_term
```

Addition on multisets is defined in `MultiSet.pf`.  The main theorem
about multiset addition is `cnt_sum`, which says that the count for
each item in `A ⨄ B` is the sum of (1) the count for that item in `A`
and (2) the count for that item in `B`.
The ASCII spelling `.+.` is equivalent to `⨄`.

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

```deduce-grammar
atomic_term ::= "all" type_annotation_list "." term
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
theorem all_example_intro: all x:UInt,y:UInt,z:UInt. x + y + z = z + y + x
proof
  arbitrary x:UInt, y:UInt, z:UInt
  equations
    x + y + z = y + x + z by replace uint_add_commute[x,y].
          ... = z + y + x by uint_add_commute[y+x,z]
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

```deduce-grammar
logical_term ::= logical_term "and" equality_term
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
define A1 = (1 = 0 + 1)
define B1 = (0 = 0 + 0)

theorem and_example_intro: A1 and B1
proof
  have A1_true: A1 by expand A1.
  have B1_true: B1 by expand B1.
  conclude A1 and B1 by A1_true, B1_true
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

```deduce-grammar
additive_term ::= additive_term "++" multiplicative_term
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

```deduce-grammar
conclusion ::= "apply" proof "to" proof
```

The proof `(apply X to Y)` proves formula `Q`
so long as 
* `X` proves `(if P then Q)`,
* `Y` proves `P`.

When matching `P` and `Q`, Deduce treats equivalent Nat and UInt
numeric literal spellings as the same value. For example, `zero`,
`lit(zero)`, and `ℕ0` can match each other in Nat formulas.

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

```deduce-grammar
proof_stmt ::= "arbitrary" type_annotation_list
```

A proof of the form

```
arbitrary x1:T1, ..., xn:Tn
X
```

is a proof of `all x1:T1, ..., xn:Tn. P` so long as
* `X` is a proof of `P`.
The variables `x1`, ..., `xn` may appear in the formula `P` and the proof `X`.

Example:

```{.deduce^#arbitrary_example}
theorem arbitrary_example: all x:UInt,y:UInt. if x = y then y = x
proof
  arbitrary x:UInt,y:UInt
  conclude if x = y then y = x by {
    assume: x = y
    symmetric (recall x = y)
  }
end
```

## Assert (Statement)

```deduce-grammar
statement ::= "assert" term
```

The `assert` statement evaluates a term and reports an error if the
result is `false`. For example, the following `assert` does nothing
because the term evaluates to `true`.

```{.deduce^#assert_example}
assert (if true then 7 else 5+6) = 7
```


## Assume

```deduce-grammar
proof_stmt ::= "assume" identifier
proof_stmt ::= "assume" identifier ":" term
proof_stmt ::= "assume" ":" term
proof_stmt ::= "suppose" identifier
proof_stmt ::= "suppose" identifier ":" term
proof_stmt ::= "suppose" ":" term
```

A proof of the form

```
assume label: P
X
```

is a proof of the formula `if P then Q`
so long as
* `X` is a proof of `Q`.
The proof `X` may use the given `label` as a proof of `P`
and it may also refer to the proof of `P` by writing `recall P`.

```{.deduce^#assume_example}
theorem assume_example: all x:UInt,y:UInt. if (x = y) then (1 + x = 1 + y)
proof
  arbitrary x:UInt,y:UInt
  assume prem: x = y
  conclude 1 + x = 1 + y  by replace prem.
end
```

## Assumption and Assumption List

```deduce-grammar
assumption_list ::= ε
assumption_list ::= identifier
assumption_list ::= identifier ":" term
assumption_list ::= ":" term
assumption_list ::= identifier "," assumption_list
assumption_list ::= identifier ":" term "," assumption_list
assumption_list ::= ":" term "," assumption_list
```

See the entry for [Assume](#assume) to see how assumptions are used.

## At Symbol `@`

See the entry for [Instantiation](#instantiation-term).

## Auto `auto` (Automatic Reduction)

```deduce-grammar
statement ::= "auto" atomic_proof
```

To tell Deduce to automatically apply an equation, left to right, use
the `auto` statement with the name of the theorem. For example, in
`UInt.pf` we prove that zero multiplied by anything is zero and follow
this `theorem` with an `auto` statement to register it for automatic
reduction.

```
theorem uint_zero_mult: all n:UInt. 0 * n = 0
proof
  ...
end

auto uint_zero_mult
```

From here on, anytime Deduce sees a term containing a `0` multiplied by
something, Deduce replaces it with `0`.

An `auto` theorem may also have premises:

```
theorem reduce_when_small: all x:Nat. if x < 5 then f(x) = 0
```

Deduce uses such a conditional equation only when each premise, after
substituting the matched terms, reduces to `true` using the unconditional
`auto` rules already in scope. Conditional `auto` rules are not used
while checking those premises.

Some care is needed when selecting equations for use with `auto`.  For
example, we do **not** register the `uint_mult_commute` theorem with
`auto` because that would cause Deduce to go into an infinite loop.

```
theorem uint_mult_commute: all m:UInt, n:UInt.
  m * n = n * m
```

## Biconditional (if and only if)

```deduce-grammar
iff_term ::= iff_term "⇔" logical_term
iff_term ::= iff_term "<=>" logical_term
iff_term ::= iff_term "iff" logical_term
```

The biconditional formula `P ⇔ Q` is syntactic sugar for
`(if P then Q) and (if Q then P)`.

## Bool (Type)

```deduce-grammar
type ::= "bool"
```

The type `bool` classifies the values `true` and `false`.
A *formula* is a term of type `bool`.

## Braces (Proof)

```
proof ::= "{" proof "}"
```

A proof may be surrounded in curly braces.

## Call (Term)

```deduce-grammar
atomic_term ::= atomic_term "(" term_list ")"
```

A term of the form `t0(t1, ..., tn)` calls the function indicated by
term `t0` on the arguments `t1`,...,`tn`.

```{.deduce^#call_example}
assert length(list_example) = 3
```

## Cases (Disjunction Elimination)

```deduce-grammar
conclusion ::= "cases" proof case_list
case_list ::= case
case_list ::= case case_list
case ::= "case" identifier "{" proof "}"
case ::= "case" identifier ":" term "{" proof "}"
case ::= "case" ":" term "{" proof "}"
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

```deduce-grammar
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
theorem choose_example: some x:UInt. 6 = 2 * x
proof
  choose 3
  conclude 6 = 2 * 3   by .
end
```

## Comma (Logical And Introduction)

```deduce-grammar
conclusion ::= proof "," proof
```

See the entry for [And](#and-logical-conjunction).

## Compose (Functions)

```deduce-grammar
multiplicative_term ::= multiplicative_term "∘" exponent_term
multiplicative_term ::= multiplicative_term ".o." exponent_term
```

The composition of two functions `g ∘ f` is defined in `Maps.pf`
so that `(g ∘ f)(x) = g(f(x))`.
The ASCII spelling `.o.` is equivalent to `∘`.

Example:

The composition of the `add1` with itself produces a function that
adds `2`. So applying that to `3` yields `5`.

```{.deduce^#compose_example}
fun add1(x : UInt) { 1 + x }

assert (add1 ∘ add1)(3) = 5
```

## Conclude (Proof)

```deduce-grammar
conclusion ::= "conclude" term reason
```

This proof statement is useful when you wish to emphasize the end of a
proof by stating the formula that is being proved.

A proof of the form

```
conclude P by X
```

is a proof of formula `P` so long as
* `X` is a proof of `P`.

Example:

```{.deduce^#conclude_example}
theorem conclude_example: 1 + 1 = 2
proof
  conclude 1 + 1 = 2 by evaluate
end
```

## Conclusion (Proof)

The last statement in a proof (the `conclusion` symbol in the grammar)
must be one of the following:

* [Cases](#cases-disjunction-elimination)
* [Comma (Logical-And Introduction)](#comma-logical-and-introduction)
* [Conclude](#conclude-proof)
* [Conjunct](#conjunct)
* [Contradict](#contradict-proof)
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

```deduce-grammar
conclusion ::= "conjunct" number "of" proof
```

A proof of the form

```
conjunct n of X
```

is a proof of `Pn` so long as
* `X` is a proof of `P1 and ... and Pk` and
* 1 ≤ n ≤ k.

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

## Contradict (Proof)

```deduce-grammar
conclusion ::= "contradict" proof
```

* The `contradict` proof expects a proof of a contradiction, such as `P and not P`.
* The result of `contradict` is a proof of `false`.

```{.deduce^#contradict_example}
theorem contradict_example: all P:bool, Q:bool. if P and not P then Q
proof
  arbitrary P:bool, Q:bool
  assume prem
  have p: P by prem
  have np: not P by prem
  conclude Q by contradict p, np
end
```


## Contradiction

During a proof, one sometimes encounters assumptions that contradict
each other. In these situations, you can prove `false` and from that,
anything else (the Principle of Explosion). Here are two ways to prove
`false` from contradictions.

(1) If you have a proof of an equality with different constructors
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

(2) If you have a proof of `P` and a proof of `not P`,
then you can prove `false` using [`contradict`](#contradict-proof).

```
have X: P by ...
have Y: not P by ...
conclude false by contradict Y, X
```

```{.deduce^#contradiction_example}
theorem contra_example: if length([1,2]) = length([1]) then length([1,2]) = length([2])
proof
  assume len_12_1: length([1,2]) = length([1])
  have: false by expand 3* length in len_12_1
  conclude length([1,2]) = length([2]) by recall false
end
```

## Define (Statement)

```deduce-grammar
definition ::= visibility "define" identifier "=" term
definition ::= visibility "define" identifier ":" type "=" term
```

The `define` feature of Deduce associates a name with a value.  For
example, the following definitions associate the name `five` with the
natural number `5`, and the name `six` with the natural number `6`.

```{.deduce^#define_example}
define five = 2 + 3
define six : UInt = 1 + five
```

Optionally, the type can be specified after the name, following a
colon.  In the above, `six` holds an unsigned integer, so its type is `UInt`.

## Define (Term)

```deduce-grammar
atomic_term ::= "define" identifier "=" term ";" term
```

This associates a name with a term for use in the term after the semicolon.

```{.deduce^#define_term_example}
assert 5 = (define x = 3; 2 + x)
```

## Define (Proof)

```deduce-grammar
proof_stmt ::= "define" identifier "=" term
```

This associates a name with a term for use in the following proof.
(Note: there is no semicolon after the term when using `define` in a proof.)

```{.deduce^#define_proof_example}
theorem define_proof_example: all x:UInt. 2 * (x + x + x) = (x + x + x) + (x + x + x)
proof
  arbitrary x:UInt
  define y = x + x + x
  show 2 * y = y + y
  uint_two_mult
end
```

## Divide

```deduce-grammar
multiplicative_term ::= multiplicative_term "/" exponent_term
```

The division function for `UInt` is defined in `UInt.pf`.  The main
theorem is `uint_div_mod` which states, assuming `m` is positive, that

```
(n / m) * m + (n % m) = n
```

Useful companion theorems include `uint_mult_div_inverse`,
`uint_mult_div_left_inverse`, `uint_mult_add_div`, `uint_add_mult_div`,
`uint_div_less_equal`, and `uint_div_less`.

Example:

```{.deduce^#division_example}
assert 6 / 3 = 2
assert 7 / 3 = 2
assert 8 / 3 = 2
assert 9 / 3 = 3
```

## GCD

The `UInt` library provides Euclid's algorithm as `gcd(a, b)`. It is
implemented over `UInt`, so it keeps the binary representation used by
unsigned integer arithmetic.

The theorem `uint_gcd_divides` proves that `gcd(a, b)` divides both
arguments. The helper theorems `uint_gcd_divides_left` and
`uint_gcd_divides_right` project the two sides. The theorem
`uint_gcd_greatest` proves that any common divisor divides the gcd.
The `divides(a, b)` predicate means there is some `k:UInt` with
`a * k = b`.

Example:

```{.deduce^#gcd_example}
assert gcd(12, 8) = 4
assert gcd(17, 13) = 1
```

## Expand (Proof)

```deduce-grammar
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
  .
end
```

## Expand-In (Proof)

```deduce-grammar
conclusion ::= "expand" identifier_list_bar "in" proof
```

In the formula of the given proof, expand the occurrences of the
specified names with their definitions, resulting in the formula that
is proved by this `expand`-`in` statement.  If a definition is
recursive, only one expansion is performed per time the definition's
name is mentioned in the list. If one of the specified names does not
appear in the formula, Deduce signals an error.

In the example below, we write `expand length in A` to
transform the formula
```
length(node(x, ls')) = 0
```
to
```
1 + length(ls') = 0
```

```{.deduce^#expand_in_example}
theorem expand_in_example: all ls:List<UInt>. if length(ls) = 0 then ls = []
proof
  arbitrary ls:List<UInt>
  switch ls {
    case [] {
      .
    }
    case node(x, ls') {
      assume A: length(node(x, ls')) = 0
      have B: 1 + length(ls') = 0  by expand length in A
      conclude false by B
    }
  }
end
```

## Empty Set

```deduce-grammar
atomic_term ::= "∅"
```

The empty set `∅` does not contain any elements and is defined in
`Set.pf`.

## Equal

```deduce-grammar
equality_term ::= equality_term "=" comparison_term
```

The formula `a = b` is true when the left-hand side and right-hand are
the same. 

(In Deduce, there is no distinction between identity and deep equality
as there is in Java because there is no concept of identity in
Deduce.)

## Equations

```deduce-grammar
conclusion ::= "equations" equation equation_list
```

```deduce-grammar
equation ::= equation_side "=" equation_side reason
half_equation ::= "..." "=" equation_side reason
equation_list ::= half_equation
equation_list ::= half_equation equation_list
equation_list ::= "$" equation equation_list
```

Combining a sequence of equations using `transitive` is quite common,
so Deduce provides `equations` to streamline this process.  After the
first equation, the left-hand side of each equation is written as
`...` because it is just a repetition of the right-hand side of the
previous equation.

Each `equation_side` may use the logical connectives `and`, `or`, and
`iff` without parentheses (for example, `P or Q = Q or P`); the `=`
that separates the two sides of a step still binds the whole step
together, even though the `=` operator normally binds more tightly than
those connectives.

When using `replace` or `expand` for one of the reasoning steps in
`equations`, the transformation is, by default, applied to the
left-hand side of the equation (and not the right-hand side). However,
if you would like to apply a transformation to the right-hand side,
use hash marks (`#`) around the region of the right-hand side that you
want to change.

Example:

```{.deduce^#equations_example}
theorem equations_example: all x:UInt, y:UInt, z:UInt.
  x + y + z = z + y + x
proof
  arbitrary x:UInt, y:UInt, z:UInt
  equations
    x + y + z = x + z + y      by replace uint_add_commute[y].
          ... = #z + x# + y    by replace uint_add_commute.
          ... = z + y + x      by replace uint_add_commute[x].
end
```

In the following example, the hash marks tell Deduce to `expand` the
definition of `length` in the right-hand side of the second equation.

```{.deduce^#equations_expand_example}
theorem equations_expand_example: all x:UInt, y:UInt, xs:List<UInt>.
  length(node(x, xs)) = length(node(y, xs))
proof
  arbitrary x:UInt, y:UInt, xs:List<UInt>
  equations
    length(node(x,xs)) = 1 + length(xs)         by expand length.
                   ... = # length(node(y,xs)) # by expand length.
end
```


## Evaluate (Proof)

```deduce-grammar
conclusion ::= "evaluate"
```

The `evaluate` proof method simplifies the goal formula by expanding
all definitions (except for opaque ones). It succeeds if the formula is
simplified to `true`.

## Evaluate-In (Proof)

```deduce-grammar
conclusion ::= "evaluate" "in" proof
```

The `evaluate`-`in` proof method simplifies the formula of the given
proof by expanding all definitions (except for opaque ones), producing
a proof of the simplified formula.

## Extensionality

```deduce-grammar
proof_stmt ::= "extensionality"
```

To prove that two functions are equal, it is sufficient to prove that
they always produce equal outputs given equal inputs.

```{.deduce^#extensionality_example}
define inc = fun x:UInt { pred(suc(suc(x))) }

theorem extensionality_example: inc = suc
proof
  extensionality
  arbitrary x:UInt
  conclude inc(x) = suc(x) by expand inc | pred.
end
```


## False

```deduce-grammar
atomic_term ::= "false"
```

One can prove `false` when there are assumptions that contradict
each other, such as `x = 0` and `x = 1`, or `not P` and `P`.

A proof of `false` can be used to prove anything else!
(This is known as the Principle of Explosion.)

See the entry for [Contradiction](#contradiction) for an example
of both proving `false` and using `false` to prove something else.


## Formula

A formula is any term of type `bool`.

```
formula ::= term
```

## Function (Term)

```deduce-grammar
atomic_term ::= "fun" type_params_opt variable_list "{" term "}"
atomic_term ::= "λ" type_params_opt variable_list "{" term "}"
```

Functions are created with a `fun` expression.  Their syntax starts with
`fun`, followed by parameter names and their types, then the body of the
function enclosed in braces.  For example, the following defines a
function for computing the area of a rectangle.

```{.deduce^#function_term_example}
define area = fun h:UInt, w:UInt { h * w }
```

To call a function, apply it to the appropriate number and type of
arguments.

```{.deduce^#print_area}
print area(3, 4)
```

The output is `12`.

To add type parameters to a function (to make it generic), see
[Generic Function](#generic-function-term).

## Function (Statement)

```deduce-grammar
statement ::= visibility "fun" identifier type_params_opt "(" variable_list ")" "{" term "}"
```

The `fun` statement is for defining a function (non-recursive).
The function statement begins with its [visibility](#visibility),
then the `fun` keyword, followed by 
the type parameters enclosed in `<` and `>` (if generic),
then the parameter list enclosed in `(` and `)`, and finally
the body of the function enclosed in `{` and `}`.

```{.deduce^#fun_interchange_example}
fun interchange(p : Pair<UInt,UInt>) {
  pair(second(p), first(p))
}

assert interchange(pair(1,2)) = pair(2,1)
```

## Function Type

```deduce-grammar
type ::= "fn" type_params_opt type_list "->" type
type ::= "fn" type_params_opt "(" type "," type_list ")" "->" type
```

A function type classifies a function. This includes both recursive
functions (`recursive`) and non-recursive functions (`fun` or `λ`).
If the function is generic, its function type includes type parameters
enclosed in `<` and `>`.

Multi-argument parameter lists may be written bare (`fn A, B -> C`) or
wrapped in parentheses (`fn (A, B) -> C`); both forms are equivalent.
The parenthesized spelling matches the parameter syntax used in
function declarations such as `recursive partition<T>(List<T>, fn (T)->bool) -> ...`.
A single-argument paren type (`fn (A) -> B`) was already accepted via
the existing parenthesized atomic type and continues to mean a unary
function from `A` to `B`.

## Generic (Formula)

```deduce-grammar
atomic_term ::= "<" identifier_list ">" term
```

This parametrizes a formula by a list of type parameters.  For
example, the following formula states that if the length of a list is
0, then the list must be empty. The type parameter `<T>` means that
this formula applies to lists with any element type.

```
<T> all xs:List<T>. if length(xs) = 0 then xs = empty
```


## Generic (Term)

```deduce-grammar
atomic_term ::= "generic" identifier_list "{" term "}"
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

Generic recursive functions can be defined using the `recursive`
statement (see [Recursive Function](#recursive-function-statement)).

## Generic Function (Term)

```deduce-grammar
atomic_term ::= "fun" type_params_opt variable_list "{" term "}"
atomic_term ::= "λ" type_params_opt variable_list "{" term "}"
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

An assumption or fact that is known to be true at a specific step
within a proof.

## Greater-Than

```deduce-grammar
comparison_term ::= comparison_term ">" additive_term
```

The greater-than operator on unsigned integers is defined in `UInt.pf`
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

```deduce-grammar
comparison_term ::= comparison_term "≥" additive_term
comparison_term ::= comparison_term ">=" additive_term
```

The greater-than-or-equal operator on unsigned integers is defined in `UInt.pf`
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

```deduce-grammar
proof_stmt ::= "have" identifier ":" term reason
proof_stmt ::= "have" ":" term reason
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

```deduce-grammar
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

An identifier is a sequence of characters that starts with a Unicode
letter or an underscore, and is followed by letters, digits, or the
special characters `!`, `?`, and `'`. Subscript digits (`₀`–`₉`) are
also allowed in continuation. The character `λ` is excluded because it
introduces a lambda expression; `ℕ` followed by a digit sequence is a
Nat literal rather than an identifier. An identifier can also be an
operator, which starts with the keyword `operator` and is then
followed by one of the following operators: `+`, `-`, `*`, `/`, `%`,
`=`, `≠`, `/=`, `<`, `≤`, `<=`, `≥`, `>=` `++`, `∩`, `&`, `∈`, `in`,
`∪`, `|`, `⨄`, `.+.`, `⊆`, `(=`, `∘`, `.o.`.


## Identifier List

A comma-separated sequence of identifiers.

```deduce-grammar
identifier_list ::= ε
identifier_list ::= identifier
identifier_list ::= identifier "," identifier_list
```

## Identifier List Bar

A bar-separated sequence of identifiers used in the syntax for
[Expand](#expand-proof) and [Expand-Int](#expand-in-proof) to specify
which definitions to expand.  To tell Deduce to expand a definition
multiple times (e.g. for a recursive function), preceed the identifier
by a number and the multiplication sign.

```deduce-grammar
identifier_list_bar ::= ε
identifier_list_bar ::= identifier
identifier_list_bar ::= number "*" identifier
identifier_list_bar ::= identifier "|" identifier_list_bar
identifier_list_bar ::= number "*" identifier "|" identifier_list_bar
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

```deduce-grammar
import ::= visibility "import" IDENT
import ::= visibility "import" IDENT "using" import_filter_list
import ::= visibility "import" IDENT "hiding" import_filter_list
import_filter_list ::= identifier ("|" identifier)*
```

Import all of the definitions and theorems from the specified file
(without the file extension).

The optional `using` clause restricts the import to a whitelist of
top-level names; `hiding` excludes a blacklist. The names are matched
against the primary name of each top-level statement in the imported
module, so `import M using U` brings the union `U` together with its
constructors. To filter an operator, use the `operator` form, e.g.
`import Nat using Nat | operator+`. A name in `using`/`hiding` that is
not exported by the module is reported as an error at the import.

If the import is `public`, the `using`/`hiding` filter also applies to
the re-exports.


## In (Set Membership)

```deduce-grammar
comparison_term ::= comparison_term "∈" additive_term
comparison_term ::= comparison_term "in" additive_term
```

The formula `x ∈ S` is true when element `x` is contained in the set `S`.

Example:

```{.deduce^#membership_example}
define S = single(1) ∪ single(2) ∪ single(3)
assert 1 ∈ S and 2 ∈ S and 3 ∈ S and not (4 ∈ S)
```

## Induction

```deduce-grammar
conclusion ::= "induction" type induction_case_list
induction_case_list ::= induction_case
induction_case_list ::= induction_case induction_case_list
induction_case ::= "case" pattern "{" proof "}"
induction_case ::= "case" pattern "suppose" assumption_list "{" proof "}"
induction_case ::= "case" pattern "assume" assumption_list "{" proof "}"
```

A proof of the form

```
induction T
case c_1(e_11,...,e_1k) assume IH_1, ... { X_1 }
...
case c_n(e_n1,...,e_nj) assume IH_n, ... { X_n }
```

is a proof of the formula `all x:T. P`
if each `X_i` is a proof of `P` where `x` is replaced
by `c_i(e_i1,...,e_ij)`. The type `T` must be a union type.
Each proof `X_i` may use its induction
hypotheses `IH_i`. For each term `e_in` whose type is `T`
(so it is recursive), the induction hypothesis is
the formula `P` with `x` replaced by the constructor argument `e_in`.

Example:

```{.deduce^#induction_example}
theorem induction_example: all ls:List<UInt>.
  ls ++ [] = ls
proof
  induction List<UInt>
  case [] {
    conclude @[]<UInt> ++ [] = []   by expand operator++.
  }
  case node(x, ls') assume IH: ls' ++ [] = ls' {
    equations
      node(x,ls') ++ [] = node(x, ls' ++ [])  by expand operator++.
                    ... = node(x, ls')        by replace IH.
  }
end
```

For induction over an inductively-defined predicate (rather than a
union type), see [`rule induction`](#rule-induction-proof).

## Inductive (Statement)
```deduce-grammar
statement ::= "inductive" type "by" atomic_proof
```

The `inductive` statement allows you to declare custom inductive structure
for any type in deduce, provided that the structure has been proved in a 
proof of the appropriate form. For example, the `UInt` library provides
the natural induction on positive integers, rather than requiring you to
do induction with the binary definition of the type.

Note: `inductive` is for installing a custom induction principle on
an *existing* type. To define an inductive predicate or relation —
i.e. a set characterized by a list of introduction rules — use
[`predicate`](#predicate-statement) or
[`relation`](#relation-statement) instead.

```
theorem uint_induction: all P:fn UInt -> bool.
  if P(0) and (all m:UInt. if P(m) then P(1 + m))
  then all n : UInt. P(n)
```

All theorems must be of a similar form to the one above,
including a function from the desired inductive type to bool, 
and a set of formulas that are either calls or if-thens that 
lead to the conclusion of the form `all n : T. P(n)`.

When performing induction on a type that has custom induction defined,
cases with free variables must use the "with" [pattern](#pattern) to
instantiate them. For example:
```
case with x. 1 + x assume IH { ... }
```

For `UInt`, this means `induction UInt` uses the public zero/successor
view constructors, not the private binary constructors. The library still
registers `uint_induction` as the supporting theorem that supplies the
recursive successor IH. The two public cases are:

```
case zero { ... }
case suc(n) assume IH { ... }
```

If a custom induction proof has the wrong number of cases, or if a
`with` pattern does not match the custom induction theorem, Deduce reports
the expected case shape in the error message.

## Injective (Proof)

```deduce-grammar
proof_stmt ::= "injective" term
```

The `injective` proof rule allows you to conclude that the inputs to a
constructor are equal if the outputs are equal. For example,
if `suc(x) = suc(y)` then `x = y`.

Example:

```{.deduce^#injective_example}
theorem injective_example: all x:List<UInt>, y:List<UInt>, z:List<UInt>.
  if node(1, x) = node(1, y) and node(1, y) = node(1, z) then x = z
proof
 arbitrary x:List<UInt>, y:List<UInt>, z:List<UInt>
 assume prem: node(1, x) = node(1, y) and node(1, y) = node(1, z)
 have nxy: node(1, x) = node(1, y) by prem
 have nyz: node(1, y) = node(1, z) by prem
 have: x = y by injective node nxy
 have: y = z by injective node nyz
 conclude x = z by transitive (recall x = y) (recall y = z)
end
```


## Instantiation (Proof)

```deduce-grammar
atomic_proof ::= atomic_proof "<" type_list ">"
atomic_proof ::= atomic_proof "[" term_list "]"
```

Use square brackets `[` and `]` to instantiate an `all` formula with 
terms and use angle brackets `<` and `>` to instantiate an `all`
formula with types. In the following example, at the bottom of the proof,
we instantiate `len_node_1` with the type `UInt` and then the term `42`,
with the syntax `len_node_1<UInt>[42]`.

Example:

```{.deduce^#instantiate_proof_example}
theorem instantiate_proof_example: length(node(42, empty)) = 1
proof
  have len_node_1: all T:type. all x:T. length(node(x, empty)) = 1 by {
    arbitrary T:type arbitrary x:T
    expand 2* length.
  }
  conclude length(node(42, empty)) = 1
    by len_node_1<UInt>[42]
end
```


## Instantiation (Term)

```deduce-grammar
atomic_term ::= "@" atomic_term "<" type_list ">"
```

Instantiates a generic function or constructor, replaces its type
parameters with the given type arguments.

```{.deduce^#instantiate_example}
define empty_nat_list = @empty<UInt>
```

## Intersection

```deduce-grammar
additive_term ::= additive_term "∩" multiplicative_term
additive_term ::= additive_term "&" multiplicative_term
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

```deduce-grammar
comparison_term ::= comparison_term "<" additive_term
```

The less-than operator on unsigned integers is defined in `UInt.pf`.
To find theorems about the less-than operator in `UInt.thm`, search for
theorems with `less` in the name.

Example:

```{.deduce^#less_than_example}
assert 1 < 2
assert not (1 < 1)
assert not (2 < 1)
```

## Less-Than or Equal

```deduce-grammar
comparison_term ::= comparison_term "≤" additive_term
comparison_term ::= comparison_term "<=" additive_term
```

The less-than-or-equal operator on unsigned integers is defined in `UInt.pf`.
To find theorems about the less-than operator in `UInt.thm`, search for
theorems with `less_equal` in the name.

Example:

```{.deduce^#less_equal_example}
assert 1 ≤ 1
assert 1 ≤ 2
assert not (2 ≤ 1)
```

## List (Term)

```deduce-grammar
atomic_term ::= "[" term_list "]"
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

```deduce-grammar
atomic_term ::= "#" term "#"
```

Marking a subterm with hash symbols restricts a `replace` or `expand`
proof to only apply to that subterm.

The [`equations`](#equations) feature, by default, places marks around the entire
left-hand side of each equation. However, you can override this
default by placing explicit marks.

```{.deduce^#mark_example}
theorem mark_example: all x:UInt. if x = 1 then x + x + x = 3
proof
  arbitrary x:UInt
  assume: x = 1
  equations
    #x# + x + x = 1 + x + x   by replace recall x = 1.
  $ 1 + #x# + x = 1 + 1 + x   by replace recall x = 1.
  $ 1 + 1 + #x# = 1 + 1 + 1   by replace recall x = 1.
            ... = 1 + #x# + 1 by replace recall x = 1.
            ... = 1 + 1 + 1   by replace recall x = 1.
            ... = 3           by .
end
```

## Modulo

```deduce-grammar
multiplicative_term ::= multiplicative_term "%" exponent_term
```

The modulo operator is defined in `UInt.pf` as follows. 

```
n % m = n ∸ (n / m) * m
```

Useful companion theorems include `uint_mod_less_divisor`,
`uint_mod_small`, `uint_mult_mod_right_zero`, `uint_mult_mod_left_zero`,
`uint_mult_add_mod`, `uint_add_mult_mod`, `uint_mod_mod`,
`uint_add_mod`, and `uint_mult_mod`.

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

```deduce-grammar
multiplicative_term ::= multiplicative_term "*" exponent_term
```

Multiplication on unsigned integers is defined in `UInt.pf`.
To find theorems about multiplication, search for `mult` in `UInt.thm`.

Example:

```{.deduce^#multiply_example}
assert 2 * 3 = 6
```

## MultiSet (Type)

The `MultiSet<T>` type represents the standard mathematical notion of
a multiset, which is a set that may contain duplicates of an
element. The `MultiSet<T>` type is defined in `MultiSet.pf`.


## Natural Number

```deduce-grammar
atomic_term ::= natural_number
```

An natural number literal is the symbol `ℕ` followed by a sequence of
one or more digits.

The operations on natural numbers and theorems about them are in `Nat.thm`.


## Not

```deduce-grammar
atomic_term ::= "not" atomic_term
```

The formula `not P` is true when `P` is false.
Deduce treats `not P` as syntactic sugar for `(if P then false)`.


## Not Equal

```deduce-grammar
equality_term ::= equality_term "≠" comparison_term
equality_term ::= equality_term "/=" comparison_term
```

Deduce treats `x ≠ y` as syntactic sugar for `not (x = y)`.

## Obtain (Proof)

```deduce-grammar
proof_stmt ::= "obtain" identifier_list "where" identifier "from" proof
proof_stmt ::= "obtain" identifier_list "where" identifier ":" term "from" proof
```


A proof of the form

```
obtain x1,...,xn where label: P from X
Y
```

is a proof of formula `Q` so long as
* `Y` proves `Q`.
* `X`proves `some x1:T1,...,xn:Tn. P`.
The proof `Y` may use the given `label` as a proof of `P`
and it may also refer to the proof of `P` by writing `recall P`.

Example:

```{.deduce^#obtain_example}
theorem obtain_example: all n:UInt. 
  if (some x:UInt. n = 4 * x) then (some x:UInt. n = 2 * x)
proof
  arbitrary n:UInt
  assume prem: (some x:UInt. n = 4 * x)
  obtain x where n_4x: n = 4 * x from prem
  choose 2 * x
  show n = 2 * (2 * x)
  replace n_4x.
end
```

## Opaque (Visibility)

```deduce-grammar
visibility ::= "opaque"
```

See [Visibility](#visibility).


## Operator Precedence

When parentheses are omitted, Deduce's terms group according to the
precedence levels below, listed from **tightest** (binds first) to
**loosest** (binds last). The `Deduce.lark` rule column names the
grammar rule that implements each level. The parser starts at the
loosest rule, `iff_term`, and each rule falls through toward the
tighter rule listed above it.

| Level | `Deduce.lark` rule     | Operators or forms                                                                 | Meaning                                                            |
|------:|------------------------|------------------------------------------------------------------------------------|--------------------------------------------------------------------|
|     0 | `atomic_term`          | literals, identifiers, parentheses, `f(...)`, `a[i]`, `@f<T>`, `not P`, `-n`       | primary and prefix forms                                           |
|     1 | `exponent_term`        | `^`                                                                                | exponent                                                           |
|     2 | `multiplicative_term`  | `*`  `/`  `%`  `∘` (also `.o.`)                                                    | multiply, divide, modulo, function composition                     |
|     3 | `additive_term`        | `+`  `-`  `∸` (also `.-.`)  `⊝`  `++`  `∪`  `∩`  `⨄` (also `.+.`)                  | add, subtract, monus, list append, set/multiset union/intersection |
|     4 | `comparison_term`      | `<`  `>`  `≤` (also `<=`)  `≥` (also `>=`)  `⊆` (also `(=`)  `∈` (also `in`)  `≲`  `≈` | comparisons, subset, membership                                |
|     5 | `equality_term`        | `=`  `≠` (also `/=`)                                                               | equality, inequality                                               |
|     6 | `logical_term`         | `and`  `or`  `:`                                                                   | logical conjunction, disjunction, type annotation                  |
|     7 | `iff_term`             | `iff` (also `<=>`, `⇔`)                                                            | biconditional                                                      |

The unary prefix forms `not P` and `-n` apply only to the immediately
following atom — for example, `not P and Q` means `(not P) and Q`, and
`-x * y` means `(-x) * y`. Type annotation `:` is part of
`logical_term`, so it is grouped left-to-right with `and` and `or`;
use parentheses when mixing annotations with logical connectives.

The ASCII aliases for `∪` and `∩` (the single characters used as the
table separator and HTML-attribute character) are documented at
[Union (Operator on Sets)](#union-operator-on-sets) and
[Intersection](#intersection).

The most common surprise is that **(in)equality binds tighter than the
logical connectives**, so

```
list_all(xs ++ ys, p) = list_all(xs, p) and list_all(ys, p)
```

groups as

```
(list_all(xs ++ ys, p) = list_all(xs, p)) and list_all(ys, p)
```

rather than the often-intended `... = (list_all(xs, p) and list_all(ys, p))`.
Parenthesize the right-hand side when the intent is the latter.

Binders — `all`, `some`, `λ`/`fun`, `generic`, `switch`, `if ... then ... else`,
`define ... ;`, and the mark form `# ... #` — extend their body as far to
the right as possible. For example,

```
all x:UInt. P(x) and Q(x)
```

means `all x:UInt. (P(x) and Q(x))`, not `(all x:UInt. P(x)) and Q(x)`.

Within a single precedence level, operators are read left to right;
chaining the same comparison (e.g. `a < b < c`) is unusual and is *not*
interpreted as a mathematical chained comparison — write it as
`a < b and b < c` instead.

The authoritative sources for precedence are `Deduce.lark` and
`rec_desc_parser.py`; the table above summarizes what those files
implement and names the corresponding public Lark rules.


## Or  (logical disjunction)

```deduce-grammar
logical_term ::= logical_term "or" equality_term
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

For the binding strength of the built-in operators when parentheses
are omitted, see [Operator Precedence](#operator-precedence).

## Pattern

```deduce-grammar
pattern ::= identifier
pattern ::= "0"
pattern ::= "true"
pattern ::= "false"
pattern ::= "[" "]"
pattern ::= identifier "(" identifier_list ")"
pattern ::= "with" identifier_list "." term
```

This syntax is used in [Switch (Term)](#switch-term), [Switch (Proof)](#switch-proof),
and [Recursive Function (Statement)](#function-statement) via a Parameter List.


## Parameter List

```deduce-grammar
pattern_list ::= ε
pattern_list ::= pattern
pattern_list ::= pattern "," identifier_list
```

A parameter list begins with a pattern (for the first function
parameter) and then continues with a comma-separated sequence of zero
or more identifiers (for the rest of the function parameters).

## Period (Proof of True)

```deduce-grammar
atomic_proof ::= "."
```

A period is a proof of the formula `true` in Deduce.


## Private (Visibility)

```deduce-grammar
visibility ::= "private"
```

See [Visibility](#visibility).


## Public (Visibility)

```deduce-grammar
visibility ::= "public"
```

See [Visibility](#visibility).


## Proof

```deduce-grammar
proof ::= conclusion
proof ::= proof_stmt proof?
```

A proof is a sequence of zero or more [proof statements](#proof-statement)
that finishes with a [conclusion](#conclusion-proof).

## Proof List

```deduce-grammar
proof_list ::= proof
proof_list ::= proof "|" proof_list
```

A list of proofs separated by vertical bars. This syntax is used
in [Replace (Proof)](#replace-proof).

## Proof Statement

The following are proof statements (`proof_stmt` symbol in the grammar).
A proof begins with zero or more proof statements, but it must end
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

## Predicate (Statement)

```deduce-grammar
statement ::= visibility "predicate" identifier type_params_opt ":" type "{" predicate_rule_list "}"
predicate_rule ::= IDENT ":" term
predicate_rule_list ::= ε
predicate_rule_list ::= predicate_rule predicate_rule_list
```

The `predicate` statement defines an inductively-defined set: the
predicate holds for some arguments exactly when one of the listed
introduction rules can produce a derivation showing it does. This is
the standard inductive-predicate construct from logic and PL
semantics; it is distinct from [`inductive`](#inductive-statement),
which declares a custom induction principle for an *existing* type.

The signature must end in `bool`, and each rule's conclusion must
apply the predicate being defined. Premises (in v1) must be a
conjunction of atoms — each atom is either a recursive call to the
predicate (giving the rule access to a sub-derivation) or a
non-recursive formula (a side condition).

The keyword [`relation`](#relation-statement) is an exact synonym;
each is preferred for its natural reading (a unary `predicate`, an
n-ary `relation`).

Example:

```
predicate even : fn UInt -> bool {
  ev0   : even(0)
  ev_ss : all n : UInt. if even(n) then even(n + 2)
}
```

Each `predicate` declaration auto-generates the following:

* **Intro lemmas.** Each rule name (here `ev0`, `ev_ss`) is usable
  as a proof-var of the rule's formula:
  ```
  theorem zero_is_even : even(0)
  proof
    ev0
  end
  ```
* **Rule-induction theorem.** A theorem named `<pred>_rule_induction`
  whose statement is the standard rule-induction principle:
  ```
  even_rule_induction :
    all M : fn UInt -> bool.
      if M(0) and (all n:UInt. if even(n) and M(n) then M(n + 2))
      then all n:UInt. if even(n) then M(n)
  ```
  Use it directly via `apply`, or via the
  [`rule induction`](#rule-induction-proof) proof form.
* **Rule-inversion theorem.** A theorem named `<pred>_rule_inversion`
  whose statement is the strictly-weaker companion (rule premises
  stay in their original form, with no induction hypothesis paired
  with recursive premises). See [`rule inversion`](#rule-inversion-proof).

### Strict positivity

The predicate may not occur in a *negative* position of any rule's
premise — under `not` or to the left of an inner `if/then`. This
restriction is necessary for the definition to be well-founded; the
diagnostic explicitly names the rule and the offending occurrence.

### Soft style hint

Declaring a `predicate` of arity ≥ 2 emits a non-blocking style hint
suggesting `relation`; the reverse hint fires for an arity-1
`relation`. Both keywords produce identical AST.

### Limitations (v1)

* Each rule's premise must be a conjunction of atoms. Disjunctive,
  implicational, or quantified premises produce a clear "supported
  in a later commit" diagnostic.
* Mutual `predicate ... and predicate ...` is not supported.

## Print (Statement)

```deduce-grammar
statement ::= "print" term
```

You can ask Deduce to print a value to standard output using the
`print` statement.

```{.deduce^#print_example}
print five
```

The output is `5`.


## Question Mark `?` (Proof)

```deduce-grammar
atomic_proof ::= "?"
               | NAMED_HOLE
```

A proof can be left incomplete by placing a `?` in the part that you
don't know. You can also name the hole with `?name`, where `name` uses
identifier characters. Deduce halts at the hole and prints an error
message with the location of the hole and the formula that needs to be
proved, as well as some advice about how to prove it. Named holes are
useful for editor and MCP tools because `?name` can be addressed by its
name even if nearby edits move the line and column.

## Reason

```deduce-grammar
reason ::= "by" proof
reason ::= "proof" proof "end"
```

## Recall (Proof)

```deduce-grammar
conclusion ::= "recall" term_list
```


A proof of the form
```
recall P1, ..., Pn
```
is a proof of the formula `P1 and ... and Pn`. The formulas
`P1`,...,`Pn` must be in the givens at the current point in the proof.


## Recursive Function (Statement)

```deduce-grammar
statement ::= visibility "recursive" identifier type_params_opt "(" type_list ")" "->" type "{" fun_case_list "}"
fun_case ::= identifier "(" pattern_list ")" "=" term
fun_case_list ::= fun_case
fun_case_list ::= fun_case fun_case_list
```

The `recursive` statement is for defining recursive functions that
operate on `union` types. Recursive functions in Deduce are somewhat
special to make sure they always terminate.

* The first parameter of the function must be a union.
* The function definition must include a clause for every constructor in the union.
* The first argument of every recursive call must be a sub-part of the current constructor of the union.

A recursive function begins with the `recursive` keyword,
followed by the name of the function, then the parameters types and the return
type. The body of the function includes one equation for every
constructor in the union of its first parameter. For example, here's
the definition of a `length` function for lists of unsigned integers.

```{.deduce^#function_length_example}
union UIntList {
  Empty
  Node(UInt, UIntList)
}

recursive length(UIntList) -> UInt {
  length(Empty) = 0
  length(Node(n, next)) = 1 + length(next)
}
```

There are two clauses in the body of `length` because the `UIntList` union
has two constructors. The clause for `Empty` says that its length is
`0`.  The clause for `Node` says that its length is one more than the
length of the rest of the linked list.  Deduce approves of the
recursive call `length(next)` because `next` is part of `Node(n, next)`.

Recursive functions may have more than one parameter but pattern
matching is only supported for the first parameter. 
If you need to pattern match on a parameter that is not the first, you
can use a `switch` statement. 


## Relation (Statement)

```deduce-grammar
statement ::= visibility "relation" identifier type_params_opt ":" type "{" predicate_rule_list "}"
```

`relation` is an exact synonym for [`predicate`](#predicate-statement).
The two keywords parse to the same AST and produce identical output;
the choice is purely stylistic. The convention is `predicate` for
unary properties and `relation` for n-ary relations:

```
relation reaches : fn Node, Node -> bool {
  refl : all n : Node. reaches(n, n)
  step : all a : Node, b : Node, c : Node.
            if edge(a, b) and reaches(b, c) then reaches(a, c)
}
```

Declaring a `predicate` whose arity is ≥ 2 — or a `relation` whose
arity is 1 — emits a non-blocking style hint suggesting the other
keyword.

See [`predicate`](#predicate-statement) for the full description of
the construct.


## Reflexive (Proof)

```deduce-grammar
conclusion ::= "reflexive"
```

The proof `reflexive` proves that `a = a` for any term `a`.

## Replace (Proof)

```deduce-grammar
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
theorem replace_example: all x:UInt,y:UInt. if (x = y) then (1 + x = 1 + y)
proof
  arbitrary x:UInt,y:UInt
  assume prem: x = y
  suffices 1 + y = 1 + y by replace prem.
  .
end
```

## Replace-In (Proof)

```deduce-grammar
conclusion ::= "replace" proof_list "in" proof
```

In the formula of the given proof, replace according to the equalities
proved by the specified [Proof List](#proof-list), resulting in the
formula that is proved by this `replace`-`in` statement. 
The algorithm for rewriting described in the entry for
[Replace (Proof)](#replace-proof).

```{.deduce^#replace_in_example}
theorem replace_in_example: all x:UInt, y:UInt.
  if x < y then not (x = y)
proof
  arbitrary x:UInt, y:UInt
  assume: x < y
  assume: x = y
  have: y < y by replace (recall x = y) in (recall x < y)
  conclude false by apply uint_less_irreflexive[y] to (recall y < y)
end
```

## Rule Induction (Proof)

```deduce-grammar
conclusion ::= "rule" "induction" identifier rule_induction_case_list
rule_induction_case ::= "case" identifier "{" proof "}"
rule_induction_case_list ::= rule_induction_case
rule_induction_case_list ::= rule_induction_case rule_induction_case_list
```

A proof of the form

```
rule induction P
case r_1 { X_1 }
...
case r_k { X_k }
```

is a proof of the formula

```
all x1:T1, ..., xn:Tn. if P(x1,...,xn) then Q(x1,...,xn)
```

where `P` is a [`predicate`](#predicate-statement) (or
[`relation`](#relation-statement)), and each `r_i` is one of `P`'s
rules. The motive `Q` is inferred from the goal. Each case proof
`X_i` proves the i-th rule's conjunct of the rule-induction
principle: with the rule's outer-quantified variables introduced via
`arbitrary`, and its premise — *augmented* with the motive's
induction hypothesis for each recursive premise — assumed.

The induction sits *before* any `arbitrary` / `assume` — the goal
must include the outer `all` and the `if P(...)` premise, so that
the motive can be inferred and the rule-induction theorem applied.

`rule induction P` desugars to applying the auto-generated
[`<P>_rule_induction`](#predicate-statement) theorem with the
inferred motive:

```
apply <P>_rule_induction[fun xs. Q(xs)] to (X_1, ..., X_k)
```

Example:

```
predicate even : fn UInt -> bool {
  ev0   : even(0)
  ev_ss : all n : UInt. if even(n) then even(n + 2)
}

theorem even_self : all n : UInt. if even(n) then even(n)
proof
  rule induction even
  case ev0 { ev0 }
  case ev_ss {
    arbitrary k : UInt
    assume hyp : even(k) and even(k)
    apply ev_ss[k] to (conjunct 0 of hyp)
  }
end
```

In the `ev_ss` case, the assumed hypothesis is `even(k) and even(k)`
— the rule's recursive premise `even(k)` is paired with the motive's
induction hypothesis `even(k)` (since the motive in this proof is
`even` itself).

If a case names a rule that doesn't belong to `P`, or omits a rule
that does, an error reports the offending rule and the predicate.

Compare with [`rule inversion`](#rule-inversion-proof), which uses
the same shape but does not pair recursive premises with an
induction hypothesis.

## Rule Inversion (Proof)

```deduce-grammar
conclusion ::= "rule" "inversion" identifier rule_induction_case_list
```

See [Rule Induction (Proof)](#rule-induction-proof) for the syntax of
`rule_induction_case` and `rule_induction_case_list`.

The structurally-identical companion to
[`rule induction`](#rule-induction-proof). It desugars to applying
the auto-generated [`<P>_rule_inversion`](#predicate-statement)
theorem, which is the strictly-weaker variant of the rule-induction
principle: rule premises stay in their *original* form, without the
motive's induction hypothesis paired with recursive premises.

Use `rule inversion` when each case needs only the rule's premises
"as given" — typical for one-step inversions of typing or reduction
judgments.

Example:

```
theorem even_self_via_inv : all n : UInt. if even(n) then even(n)
proof
  rule inversion even
  case ev0 { ev0 }
  case ev_ss {
    arbitrary k : UInt
    assume ev_k : even(k)
    apply ev_ss[k] to ev_k
  }
end
```

In the `ev_ss` case, the assumed hypothesis is `even(k)` alone — no
induction hypothesis paired. Compare with the
[`rule induction`](#rule-induction-proof) example above, where the
analogous case body assumes `even(k) and even(k)`.

## Simplify (Proof)

```deduce-grammar
proof_stmt ::= "simplify" optional_proof_list
conclusion ::= "simplify" optional_proof_list "in" proof
optional_proof_list ::= ε
optional_proof_list ::= "with" proof_list
```

Simplify the current goal formula using all of the built-in automatic
equations.

```{.deduce^#simplify_arith_if}
theorem simplify_arith_if: all x:UInt.
  if x + 0 = x then true else false
proof
  arbitrary x:UInt
  simplify.
end
```

The `simplify` statement also applies all the theorems and lemmas that
are declared to be `auto`.

```{.deduce^#simplify_auto}
fun make_true() { true }

theorem make_true_is_true: make_true() = true
proof
  expand make_true.
end

auto make_true_is_true

theorem simplify_auto: if make_true() then true else false
proof
  simplify.
end
```

Additionally, you can use givens to simplify the current goal by
adding `with` and the list of givens. If the given is of the form `not P`,
then `simplify` replaces occurences of `P` with `false`.
Otherwise `simplify` replaces occurences of the given `P` with `true`.

```{.deduce^#simplify_with_if}
theorem simplify_with_if: all P:bool, Q:bool.
  if P and not Q then   
  (if Q then false else P or Q)
proof
  arbitrary P:bool, Q:bool
  assume prem
  have p: P by prem
  have nq: not Q by prem
  simplify with p | nq.
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

```deduce-grammar
proof_stmt ::= "show" term
```

Use `show` to document the current goal formula. Deduce checks to make
sure that the given formula matches the current goal.


## Some (Formula)

```deduce-grammar
atomic_term ::= "some" type_annotation_list "." term
```

The formula `some x1:T1,...,xn:Tn. P` is true when there exists
a choice for `x1`,...,`xn` such that `P` is true.

To prove a `some` formula, see the entry for
[Choose](#choose-proof).

To use a `some` formula, see the entry for [Obtain](#obtain-exists-elimination)

## Sorry (Proof)

```deduce-grammar
atomic_proof ::= "sorry"
```

`sorry` is the get-out-of-jail free card. It can prove anything.
However, it prints a warning message with the location of the `sorry`.

## Subset or Equal

```deduce-grammar
comparison_term ::= comparison_term "⊆" additive_term
comparison_term ::= comparison_term "(=" additive_term
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
  arbitrary x:UInt
  assume x1: x ∈ single(1)
  x1
end
```

## Subtract (Producing Integers)

```deduce-grammar
additive_term ::= additive_term "-" multiplicative_term
```

```{.deduce^#subtract_example}
assert 3 - 2 = +1
assert 3 - 3 = +0
assert 2 - 3 = -1
```

## Subtraction of Unsigned Integers (aka. monus or truncated subtraction)

```deduce-grammar
additive_term ::= additive_term "∸" multiplicative_term
additive_term ::= additive_term ".-." multiplicative_term
```

The monus operator is different from ordanary subtraction on integers
because there are no negative unsigned integers. If you subtract a larger
unsigned integer from a smaller one, the result of monus is `0`.
The ASCII spelling `.-.` is equivalent to `∸`.

```{.deduce^#monus_example}
assert 3 ∸ 2 = 1
assert 3 ∸ 3 = 0
assert 2 ∸ 3 = 0
assert 3 .-. 2 = 1
```

To search for theorems about monus in `UInt.thy`, search for
theorems with `monus` in the name.

## Suffices (Proof Statement)

```deduce-grammar
proof_stmt ::= "suffices" term reason
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
We then prove the new goal with theorem `uint_add_zero` from `UInt.thm`.

```{.deduce^#suffices_example}
theorem suffices_example:
  length(node(3, empty)) = 1
proof
  suffices 1 + 0 = 1 by expand 2*length.
  uint_add_zero
end
```

## Suppose

See the entry for [Assume](#assume).

## Switch (Term)

```deduce-grammar
atomic_term ::= "switch" term "{" switch_list "}"
```

```deduce-grammar
switch_list ::= switch_case
switch_list ::= switch_case switch_list
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

```deduce-grammar
conclusion ::= "switch" term "{" switch_proof_case_list "}"
conclusion ::= "switch" term "for" identifier_list "{" switch_proof_case_list "}"
```

```deduce-grammar
switch_proof_case_list ::= switch_proof_case
switch_proof_case_list ::= switch_proof_case switch_proof_case_list
switch_proof_case ::= "case" pattern "{" proof "}"
switch_proof_case ::= "case" pattern "suppose" assumption_list "{" proof "}"
switch_proof_case ::= "case" pattern "assume" assumption_list "{" proof "}"
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
The goal `R` is automatically simplified using the assumption
for each case.

Example:

```{.deduce^#switch_proof_list_example}
theorem switch_proof_list: all ls:List<bool>.
  if length(ls) = 0 then ls = []
proof
  arbitrary ls:List<bool>
  switch ls {
    case [] assume: ls = [] {
      .
    }
    case node(b, ls') assume: ls = node(b, ls') {
      expand length.
    }
  }
end
```

If the subject `t` of the switch is a `bool`, then the assumptions for
the two cases are `t` and `not t`, respectively.

Example:

```{.deduce^#switch_proof_example}
theorem switch_proof_example: all x:bool. x or not x
proof
  arbitrary x:bool
  switch x {
    case true assume: x {
      .
    }
    case false assume: not x {
      .
    }
  }
end
```

For case analysis on a member of an inductively-defined predicate
(rather than a union value), see
[`rule inversion`](#rule-inversion-proof).

## Symmetric (Proof)

```deduce-grammar
conclusion ::= "symmetric" proof
```

If `X` is a proof of `a = b`, then `symmetric X` is a proof of `b = a`
for any terms `a` and `b`.


## Theorem (Statement)

```deduce-grammar
theorem ::= visibility "theorem" IDENT ":" term reason
theorem ::= visibility "lemma" IDENT ":" term reason
theorem ::= visibility "postulate" IDENT ":" term
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

A [`predicate`](#predicate-statement) declaration auto-generates
several theorems with predictable names: one per rule (the intro
lemma), plus `<pred>_rule_induction` and `<pred>_rule_inversion`.


## Term List

A term list is a comma-separated sequence of zero or more terms.

```deduce-grammar
term_list ::= ε
term_list ::= term
term_list ::= term "," term_list
```

## Trace (Statement)

```deduce-grammar
statement ::= "trace" identifier
```

You can ask Deduce to print the stack trace of functions as they get called or return a value using the `trace` statement. 

```{.deduce^#trace_example}
recursive sum(List<UInt>) -> UInt {
  sum([]) = 0
  sum(node(h, t)) = h + sum(t)
} 
trace sum
assert sum([1, 2, 3]) = 6
```

The output of this program will be:
```
> sum([1, 2, 3])
>> sum([2, 3])
>>> sum([3])
>>>> sum(@[]<UInt>)
<<<< bzero
<<< 3
<< 5
< 6
```

Where `bzero`, `3`, `5`, and `6` are the return values of `sum`.

## Transitive (Proof)

```deduce-grammar
conclusion ::= "transitive" proof proof
```

If `X` is a proof of `a = b` and `Y` is a proof of `b = c`,
then `transitive X Y` is a proof of `a = c`, for any
terms `a`, `b`, and `c`.

## True (Formula)

```deduce-grammar
atomic_term ::= "true"
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

```deduce-grammar
type ::= "bool"                                        // type of a Boolean
type ::= "type"                                        // the universe of types
type ::= identifier                                    // type of a union or type alias
type ::= identifier "<" type_list ">"                  // type of a generic union or type alias
type ::= "[" type "]"                                  // type of an array
type ::= "fn" type_params_opt type_list "->" type      // type of a function 
type ::= "fn" type_params_opt "(" type "," type_list ")" "->" type   // parenthesized multi-arg form
type ::= "(" type ")"
```

## Type Alias (Statement)

```deduce-grammar
statement ::= visibility "type" IDENT type_params_opt "=" type
```

The `type` statement defines a type alias. A type alias may be
parameterized, so aliases can also be used as type operators.

```{.deduce^#type_alias_example}
type Truth = bool

define id_truth : fn Truth -> Truth = fun x { x }

union Box<T> {
  box(T)
}

type Id<T> = T
type BoxOf<T> = Box<Id<T>>

define boxed_true : BoxOf<Truth> = box(true)
```

## Type List

```deduce-grammar
type_list ::= ε
type_list ::= type
type_list ::= type "," type_list
```

A type list is a comma-separated list of zero or more types.


## Type Parameters

```deduce-grammar
type_params_opt ::= ε
type_params_opt ::= "<" identifier_list ">"
```

Specifies the type parameters of a generic union, type alias, or generic
function.


## Union (Statement)

```deduce-grammar
statement ::= visibility "union" IDENT type_params_opt "{" constructor_list "}"
constructor_list ::= constructor
constructor_list ::= constructor constructor_list
constructor ::= IDENT
constructor ::= IDENT "(" type_list ")"
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
  Leaf(UInt)
  Internal(Tree, UInt, Tree)
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

```deduce-grammar
additive_term ::= additive_term "∪" multiplicative_term
additive_term ::= additive_term "|" multiplicative_term
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

## Unsigned Integer

```deduce-grammar
atomic_term ::= unsigned_integer
```

An unsigned integer literal is a sequence of one or more digits.

## Variable List

```deduce-grammar
variable_list ::= ε
variable_list ::= identifier
variable_list ::= identifier "," variable_list
variable_list ::= identifier ":" type
variable_list ::= identifier ":" type "," variable_list
```

A comma-separated list of variable declarations. Each variable may
optionally be annotated with its type.

## View (Statement)

```deduce-grammar
statement ::= visibility "view" IDENT type_params_opt "{" "source" type "target" type "into" identifier "out" identifier "roundtrip" identifier view_inverse_opt "}"
view_inverse_opt ::= ε
view_inverse_opt ::= "inverse" identifier
```

A `view` declaration describes how to pattern match on a value through
another union type. The `source` is the type being viewed, and the
`target` is the union type whose constructors may appear in the
recursive function cases. The `into` function converts from the source
type to the target type, and the `out` function converts a target value
back to a source value.

The `roundtrip` name must refer to a theorem that proves:

```
all v:Target. into(out(v)) = v
```

For a generic view, the theorem must quantify the type parameters
first:

```
all T:type, v:Target<T>. into(out(v)) = v
```

Deduce checks that the `into` and `out` functions have the expected
types, that the `roundtrip` theorem proves the expected formula, and,
when present, that the `inverse` theorem proves the reverse formula.
The optional `inverse` name must refer to a theorem that proves the
opposite direction:

```
all x:Source. out(into(x)) = x
```

For a generic view, the theorem must quantify the type parameters
first. If the `inverse` line is omitted, the opposite direction is not
required. This allows a view to forget representation details while
still presenting a complete pattern-matching interface.

The view name can be used wherever a type is expected. In ordinary type
positions it stands for the view's source type. When it appears as the
first parameter type of a `recursive` function, Deduce checks the cases
against the view's target constructors instead of the source
representation's constructors. If a view includes an `inverse` theorem,
ordinary term-level `switch` can also use the view's target constructors.
Proof-level `switch` and `induction` can use the same case shape when the
type's proof machinery supports it.

The following example defines a simple predecessor view for a unary
number type, then uses the normal `recursive` syntax to recurse
through that view.

```{.deduce^#view_example}
union Unary {
  UZero
  USucc(Unary)
}

union UnaryView {
  ViewZero
  ViewSucc(Unary)
}

fun unary_into(n:Unary) {
  switch n {
    case UZero { ViewZero }
    case USucc(p) { ViewSucc(p) }
  }
}

fun unary_out(v:UnaryView) {
  switch v {
    case ViewZero { UZero }
    case ViewSucc(p) { USucc(p) }
  }
}

theorem unary_roundtrip: all v:UnaryView. unary_into(unary_out(v)) = v
proof
  arbitrary v:UnaryView
  switch v {
    case ViewZero { evaluate }
    case ViewSucc(p) { evaluate }
  }
end

theorem unary_inverse: all n:Unary. unary_out(unary_into(n)) = n
proof
  arbitrary n:Unary
  switch n {
    case UZero { evaluate }
    case USucc(p) { evaluate }
  }
end

view UnaryPred {
  source Unary
  target UnaryView
  into unary_into
  out unary_out
  roundtrip unary_roundtrip
  inverse unary_inverse
}

recursive unary_length(UnaryPred) -> UInt {
  unary_length(ViewZero) = 0
  unary_length(ViewSucc(p)) = 1 + unary_length(p)
}
```

In the example above, `unary_length` has type `fn Unary -> UInt`, and
the recursive call
`unary_length(p)` is allowed because the `ViewSucc` case binds
`p : Unary`.

## Visibility

```deduce-grammar
visibility ::= ε
visibility ::= "public"
visibility ::= "private"
visibility ::= "opaque"
```

The visibility of a statement controls how the defined name can be
used outside of the current module.

* The default visibility is `public`, which means the name can be freely used outside the current module.
* A `private` name cannot be mentioned outside of the current module.
* An `opaque` name can be mentioned in other modules but it cannot be expanded (via the `expand` or `evaluate` statements). The constructors of an `opaque` union are always private.


<!--
```{.deduce^file=Reference.pf} 
import Nat
import UInt
import Int
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
<<gcd_example>>
<<equations_example>>
<<equations_expand_example>>
<<greater_example>>
<<greater_equal_example>>
<<if_then_else_example>>
<<membership_example>>
<<induction_example>>
<<injective_example>>
<<instantiate_proof_example>>
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
<<simplify_arith_if>>
<<simplify_with_if>>
<<simplify_auto>>
<<switch_example>>
<<switch_proof_list_example>>
<<switch_proof_example>>
<<subset_example>>
<<suffices_example>>
<<subtract_example>>
<<monus_example>>
<<multiply_example>>
<<true_example>>
<<union_example>>
<<view_example>>
<<fun_interchange_example>>
<<generic_fun_example>>
<<contradiction_example>>
<<set_union_example>>
<<contradict_example>>
```
-->
