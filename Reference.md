
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


## Colon (Type Annnotation)

```
term ::= term ":" type
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

## Conclude

```
proof ::= "conclude" formula "by" proof
```

## Conjunct

```
proof ::= "conjunct" number "of" proof 
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

## If (Formula)

## If-Then (Program Term)

## In (Membership)

```
term ::= term "∈" term
term ::= term "in" term
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
<<and_example>>
<<and_example_intro>>
<<and_example_elim>>
<<append_example>>
<<apply_to_example>>
<<arbitrary_example>>
<<assume_example>>
<<choose_example>>
```
-->
