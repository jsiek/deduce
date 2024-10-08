
This is a comprehensive reference for Deduce. It describes each
feature in alphabetical order by keyword. It gives the grammar rule
(syntax) and describes its meaning and/or how it is used in a proof.
In the grammar rules, an unquoted astericks means zero-or more
repetitions of the grammar item that it follows.


## Add

```
term ::= term "+" term
```

## Add (Multiset)

```
term ::= term "⨄" term
term ::= term "[+]" term
```

## And

```
term ::= term "and" term
```

## Append

```
term ::= term "++" term
```

## Apply-To (Modus Ponens)

```
proof ::= "apply" proof "to" proof
```

## Arbitrary (Forall Introduction)

```
proof ::= "arbitrary" var_decl_list  proof
```



## Assume (aka. Suppose)

```
proof ::= "suppose" assumption proof
proof ::= "assume" assumption proof
```

## Assumption and Assumption List

```
assumption ::= identifier
assumption ::= identifier ":" formula

assumption_list ::= assumption
assumption_list ::= assumption "," assumption_list
```

## Choose (Exists Elimination)

```
proof ::= "choose" term_list  proof
```

## Colon (Type Annnotation)

```
term ::= term ":" type
```

## Comma (Conjunction/And Introduction)

```
term ::= term "," term
```

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
