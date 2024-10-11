
This is a comprehensive reference for Deduce. It describes each
feature in alphabetical order by keyword. It gives the grammar rule
(syntax) and describes its meaning and/or how it is used in a proof.
In the grammar rules, an unquoted astericks means zero-or more
repetitions of the grammar item that it follows.


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

### Example

```{.deduce #add_example}
assert 2 + 3 = 5
```

## Add (Multiset)

```
term ::= term "⨄" term
term ::= term "[+]" term
```

Addition on multisets is defined in `MultiSet.pf`.  The main theorem
about multiset addition is `cnt_sum`, which says that the count for
each item in `A ⨄ B` is the sum of the counts for that item in `A` and
the count for that item in `B`.

```
cnt_sum: all T:type. all A:MultiSet<T>, B:MultiSet<T>, x:T.
  cnt(A ⨄ B)(x) = cnt(A)(x) + cnt(B)(x)
```

### Example

```{.deduce #add_multiset_example}
define A = m_one(5) ⨄ m_one(3) ⨄ m_one(5)
assert cnt(A)(3) = 1
assert cnt(A)(5) = 2
assert cnt(A)(7) = 0
```

## And (logical conjunction)

```
term ::= term "and" term
```

A formula `P and Q` is true when both `P` and `Q` are true.

### Example

```{.deduce #and_example}
assert true and true
assert not (true and false)
assert not (false and true)
assert not (false and false)
```

### Prove `P and Q`

Use comma to combine a proof of `P` and a proof of `Q` into a proof of
`P and Q`.

```{.deduce #and_example_intro}
theorem and_example_intro: (1 = 0 + 1) and (0 = 0 + 0)
proof
  have eq1: 1 = 0 + 1 by definition operator+
  have eq2: 0 = 0 + 0 by definition operator+
  conclude (1 = 0 + 1) and (0 = 0 + 0) by eq1, eq2
end
```

### Use `P and Q`

A proof of `P and Q` can be used implicitly to prove `P` and to prove `Q`.

```{.deduce #and_example_elim}
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

### Example

```{.deduce #append_example}
assert [1,2] ++ [3,4] = [1,2,3,4]
```

## Apply-To Proof (Modus Ponens)

```
proof ::= "apply" proof "to" proof
```

### Meaning

A proof of the form
```
apply X to Y
```
is a proof of formula `Q` if `X` is a proof of `(if P then Q)`
and `Y` is a proof of `P`.

### Example

```{.deduce #apply_to_example}
theorem apply_to_example: all P:bool, Q:bool, R:bool.
  if (if P then Q) and (if Q then R) and P
  then R
proof
  arbitrary P:bool, Q:bool, R:bool
  suppose prem: (if P then Q) and (if Q then R) and P
  have pq: if P then Q  by prem
  have p: P             by prem
  have q: Q             by apply pq to p
  have qr: if Q then R  by prem
  conclude R            by apply qr to q
end
```

## Arbitrary (Forall Introduction)

```
proof ::= "arbitrary" var_decl_list  proof
```

### Meaning

A proof of the form
```
arbitrary x1:T1, ..., xn:Tn
X
```
is a proof of the formula `all x1:T1, ..., xn:Tn. P` if `X` is a proof of `P`.
The variables `x1`, ..., `xn` may appear in the formula `P` and the proof `X`.

### Example

```{.deduce #arbitrary_example}
theorem arbitrary_example: all x:Nat,y:Nat. if x = y then y = x
proof
  arbitrary x:Nat,y:Nat
  conclude if x = y then y = x by
    assume: x = y
    symmetric (recall x = y)
end
```


## Assume (aka. Suppose)

```
proof ::= "suppose" assumption proof
proof ::= "assume" assumption proof
```

### Meaning

A proof of the form
```
assume label: P
X
```
is a proof of the formula `if P then Q` if `X` is a proof of `Q`.

### Example

```{.deduce #assume_example}
theorem assume_example: all x:Nat,y:Nat. if (x = y) then (1 + x = 1 + y)
proof
  arbitrary x:Nat,y:Nat
  assume prem: x = y
  conclude 1 + x = 1 + y  by rewrite prem
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

See the entry for Assume to see how assumptions are used.


## Choose (Exists Elimination)

```
proof ::= "choose" term_list  proof
```

### Meaning

A proof of the form
```
choose e1,...,en
X
```
is a proof of the formula `some x1,...xn. P`
if `X` is a proof of formula `P` where the `x`'s replaced by the `e`'s.

### Example

```{.deduce #choose_example}
theorem choose_example: some x:Nat. 6 = 2 * x
proof
  choose 3
  enable {operator*, operator+, operator+, operator+}
  conclude 6 = 2 * 3   by .
end
```

## Comma (Conjunction/And Introduction)

```
term ::= term "," term
```

See the entry for And (logical conjunction).

## Compose (Functions)

```
term ::= term "∘" term
term ::= term "[o]" term
```

The composition of two functions `g ∘ f` is defined in `Maps.pf`
so that `(g ∘ f)(x) = g(f(x))`.

### Example

Applying the successor function `suc` (add 1) to `3` yields `5`.

```{.deduce #compose_example}
assert (suc ∘ suc)(3) = 5
```

## Conclude

```
proof ::= "conclude" formula "by" proof
```

This proof statement is useful when you wish to emphasize the end of a
proof by stating the formula that is being proved.

### Meaning

A proof of the form
```
conclude P by X
```
is a proof of formula `P` if `X` is a proof of `P`.

### Example

```{.deduce #conclude_example}
theorem conclude_example: 1 + 1 = 2
proof
  conclude 1 + 1 = 2 by definition {operator+,operator+}
end
```

## Conjunct

```
proof ::= "conjunct" number "of" proof 
```

### Meaning

A proof of the form
```
conjunct n of X
```
is a proof of `Pn` if `X` is a proof of `P1 and ... and Pk`
and 1 ≤ n ≤ k.

### Example

```{.deduce #conjunct_example}
theorem conjunct_example: all P:bool, Q:bool. if P and Q then Q and P
proof
  arbitrary P:bool, Q:bool
  assume prem: P and Q
  have p: P         by conjunct 0 of prem
  have q: Q         by conjunct 1 of prem
  conclude Q and P  by p, q
end
```


## Divide

```
term ::= term "/" term
```

## Enough

```
proof ::= "enough" formula "by" proof  proof
```

## Equal

```
term ::= term "=" term
```

## Equations

```
proof ::= "equations" equation equation_list
equation ::= term "=" term "by" proof
half_equation ::= "..." "=" term "by" proof
equation_list ::= half_equation
equation_list ::= half_equation equation_list
equation_list ::= "|" equation equation_list
```

## Formula

A formula is any term of type `bool`.

```
formula ::= term
```

## Greater-Than

```
term ::= term ">" term
```


## Greater-Than or Equal

```
term ::= term "≥" term
term ::= term ">=" term
```

## Identifier 

Identifiers are used in Deduce to give names functions and values and
to label theorems and facts.

An identifier is a sequence of characters that starts with an upper or
lower-case letter or an underscore, and is followed by letters,
digits, or the special characters `!`, `?`, and `'`.  An identifier
can also be an operator, which starts with the keyword
`operator` and is then followed by one of the following operators:
`+`, `-`, `*`, `/`, `%`, `=`, `≠`, `/=`, `<`, `≤`, `<=`, `≥`, `>=`
`++`, `∩`, `&`, `∈`, `in`, `∪`, `|`, `⨄`, `[+]`, `⊆`, `(=`, `∘`, `[o]`.



## Identifier List

A comma-separated sequence of identifiers.

```
identifier_list ::= identifier
identifier_list ::= identifier "," identifier_list
```

## If-Then (Conditional Formula)

A formula `if P then Q` is true when both `P` and `Q` are true and it
is true when `P` is false.

To prove a conditional formula, use `assume`. (See the entry for Assume.)

To use a given that is a conditional formula, use `apply`-`to`.
(See the entry for Apply-To.)

## If-Then-Else (Program Term)

A term of the form
```
if a then b else c
```
is equal to `b` when `a` is true and equal to `c` when `a` is false.

### Example

```{.deduce #if_then_else_example}
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

## In (Membership)

```
term ::= term "∈" term
term ::= term "in" term
```

The formula `x ∈ S` is true when element `x` is contained in the set `S`.

### Example

```{.deduce #membership_example}
define S = single(1) ∪ single(2) ∪ single(3)
assert 1 ∈ S and 2 ∈ S and 3 ∈ S and not (4 ∈ S)
```


## Induction

```
proof ::= "induction" type ind_case*
```

## Intersection

```
term ::= term "∩" term
term ::= term "&" term
```

## Less-Than

```
term ::= term "<" term
```

## Less-Than or Equal

```
term ::= term "≤" term
term ::= term "<=" term
```

## Modulo

```
term ::= term "%" term
```

## Multiply

```
term ::= term "*" term
```

## Not Equal

```
term ::= term "≠" term
term ::= term "/=" term
```

## Obtain

```
proof ::= "obtain" identifier_list "where" assumption "from" proof  proof
```

## Or

```
term ::= term "or" term
```

## Variable Declaration and Variable Declaration List

```
var_decl ::= identifier ":" type
var_decl_list ::= var_decl
var_decl_list ::= var_decl "," var_decl_list
```

## Pattern

```
pattern ::= identifier
pattern ::= "0"
pattern ::= "true"
pattern ::= "false"
pattern ::= identifier "(" identifier_list ")"
```

## Switch (Program Term)

```
term ::= "switch" term "{" switch_case* "}"
switch_case ::= "case" pattern "{" term "}"
```

(See the entry for Pattern for the syntax of `pattern`.)

## Switch (Proof)

```
proof ::= "switch" term "{" switch_proof_case* "}"
switch_proof_case ::= "case" pattern "{" proof "}"
switch_proof_case ::= "case" pattern "suppose" assumption_list "{" proof "}"
```

(See entry for Assumption List for the syntax of `assumption_list`.)


## Subset or Equal

```
term ::= term "⊆" term
term ::= term "(=" term
```

## Subtract

```
term ::= term "-" term
```

## Suffices

```
proof ::= "suffices" formula "by" suffices_proof  proof
suffices_proof ::= definition_clause 
suffices_proof ::= rewrite_clause 
suffices_proof ::= definition_clause "and" rewrite_clause 
```

## Suppose

See the entry for Assume.

## Term List

A term list is a comma-separated sequence of terms.

```
term_list ::= term
term_list ::= term "," term_list
```

## Union

```
term ::= term "∪" term
term ::= term "|" term
```


<!--
```{.deduce file=Reference.pf}
import Nat
import List

<<add_example>>
<<add_multiset_example>>
<<and_example>>
<<and_example_intro>>
<<and_example_elim>>
<<append_example>>
<<apply_to_example>>
<<arbitrary_example>>
<<assume_example>>
<<choose_example>>
<<compose_example>>
<<conclude_example>>
<<conjunct_example>>
<<if_then_else_example>>
<<membership_example>>
```
-->
