# Associated types and same-type constraints (#1321 part 3)

This is the plan for part 3 of #1321 (concepts: local models, parameterized
models, associated types), following F^G §5 (Siek & Lumsdaine, PLDI 2005).

## The running example

```
concept Container<C> {
  type Elem
  fun get : fn (C, UInt) -> Elem
  fun size : fn C -> UInt
}

model Container<List<UInt>> {
  type Elem = UInt
  fun get = fun xs:List<UInt>, i:UInt { nth(xs, 0)(i) }
  fun size = length
}

model <T> Container<Array<T>> {
  type Elem = T
  ...
}

theorem same_first: all C:type, D:type
    where { Container<C>, Container<D>,
            @Container<C>.Elem = @Container<D>.Elem }.
  all c:C, d:D. if get(c, 0) = get(d, 0) then get(d, 0) = get(c, 0)
proof ... end

same_first<List<UInt>, Array<UInt>>   // OK: both Elem are UInt
same_first<List<UInt>, Array<bool>>   // error: UInt ≠ bool
```

## Syntax

| Where | Form |
|---|---|
| concept member | `type Elem` |
| model member | `type Elem = UInt` |
| type expression | `@Container<C>.Elem` |
| where clause | `{ Container<C>, @Container<C>.Elem = @Container<D>.Elem }` |

The projection takes an `@`, as qualified members of terms do
(`@Monoid<T>.zero`). Without it, `all x:List<T>.length(x) = 0` would read
as `all x:(List<T>.length)(x) = 0`, because a type followed by `.name`
would be a projection.

Inside the concept, `Elem` names the associated type of the concept's own
instance.

## The key design decision: types are normalized when checked

The type checker compares types with structural `==` in many places
(`type_match`, `alpha_equiv` on binder types, and dozens of `==` sites). The plan
does **not** change those. Instead it keeps this invariant:

> A checked type never contains a projection `@C<τ>.Elem`. Every projection
> is replaced by its normal form when the type is checked.

Under that invariant, structural `==` on checked types is equality modulo
the same-type constraints, because all equal types have the same normal
form.

Normal forms:

- **Projection on a model in scope with a `type Elem = σ` member:** `σ`,
  substituted for a parameterized model. Example:
  `@Container<Array<bool>>.Elem` becomes `bool`.
- **Projection on a where-clause model:** a fresh type variable, the
  *proxy*, created when the where clause is entered (as the where models'
  operation binders are now). Example: inside `same_first`,
  `@Container<C>.Elem` becomes the proxy `Elem₁`.
- **Same-type constraints** merge classes of a union-find over type terms.
  Each class has one representative, and normalizing a type replaces each
  subterm with its class's representative.

This is the F^G translation: an associated type becomes an extra type
parameter (the proxy) and a same-type constraint identifies two type
parameters. Because the translation happens when types are checked,
formulas never contain projections, and substituting into a formula can't
create one.

### Congruence closure

Within one where clause, the solver works on the clause's instances and
equations:

1. Create a proxy for each associated type of each instance in the clause's
   refinement closure.
2. For each equation `σ = τ`, normalize both sides and unify them:
   - variables merge classes;
   - `List<A> = List<B>` decomposes to `A = B`;
   - `List<A> = Pair<B, C>` is an error ("the same-type constraints of the
     where clause are inconsistent");
   - `T = List<T>` is an error (occurs check).
3. **Congruence:** after a merge, renormalize the instances. If two
   instances become equal, that is an error (decided): with
   `where { Container<C>, Container<D>, C = D }`, "the same-type
   constraints make Container<C> and Container<D> the same instance; list
   it once".
4. **Representative:** a constructor term if the class has one, else the
   variable bound outermost.

### Nested scopes

A where clause or local model inside a proof sees types normalized by the
outer scopes. To keep those normal, an inner where clause may only merge a
class with a variable it introduces itself (its own type variables and
proxies). Example: inside `same_first`'s proof,
`all E:type where { Container<E>, @Container<E>.Elem = @Container<C>.Elem }`
is allowed (the inner proxy joins the outer one, which stays the
representative). `where { @Container<C>.Elem = UInt }` is an error: "the
same-type constraint constrains @Container<C>.Elem, which is fixed outside
this where clause".

A local model changes only how projections resolve inside its proof.
Types checked outside the proof are already normal, so they don't mention
the projection.

## The translation of where formulas

Today `all T:type where { C<T> }. P` expands to `all T:type. all ops. if
axioms then P`. With associated types it becomes

```
all C:type, D:type where {...}. all Elem₁:type. all ops. if axioms then P'
```

There is one `all` per class that has no constructor term, and `P'` is `P`
with the normalized types. `_strip_operations` (`checker_concepts.py`)
strips these binders along with the operation binders.

## Instantiation

`instantiate_where`, `where_instances` (theorems) and the where-function
path in `type_check_call_funty` (functions) share one step,
`resolve_where`:

1. Match or take the explicit type arguments (`C := List<UInt>`,
   `D := Array<UInt>`).
2. Look up each instance's model, as `where_arguments` does now.
3. Each proxy's value is its model's `type` member, normalized in the
   caller's scope. If matching already bound the proxy (from an argument
   of type `Elem`), the two must be equal.
4. Check each same-type constraint by `==` on the normalized sides.
   Example: `same_first<List<UInt>, Array<bool>>` fails with

   ```
   the same-type constraint @Container<C>.Elem = @Container<D>.Elem
   does not hold at C := List<UInt>, D := Array<bool>:
     UInt ≠ bool
   ```

A where function's `FunctionType.where` records the proxies, so that
`first(xs)` with `xs:List<UInt>` gets return type `UInt`.

## Models

- `type Elem = σ` is checked in the model's scope, so a parameterized
  model's `σ` can mention its type parameters.
- `type Elem` may not be omitted. Binding by name would bind to a type
  called `Elem` in scope, which is rarely what's meant.
- `member_type` and `axiom` substitute `Elem ↦ @C<τ>.Elem` along with the
  concept's type parameters and then normalize. Example:
  `@Container<List<UInt>>.get` has type `fn (List<UInt>, UInt) -> UInt`.
- **Opaque models export their associated types.** Clients can't type
  check uses without them. An opaque model still hides its operations.

## C back end

Types are erased (`compiler/lower.py`), so associated types need nothing
beyond skipping `type` members when lowering a model.

## Steps

Each step lands with its fixtures under both parsers.

1. **AST and parsers:** `AssocType(ref, name)`, `type` members of concepts
   and models, equations in `WhereClause`. Both parsers, `Deduce.lark`,
   pretty printing, uniquify (`Elem` is bound in the concept body), and
   the files in `docs/knowledge-base/what-to-update.md`.
2. **Concrete projections:** `check_type` of `@C<τ>.Elem` through
   `find_model`; `type` members of models (top-level, local,
   parameterized); `member_type` and `axiom` substitution. Fixtures:
   should-validate `assoc_types.pf`; should-error missing `type` member,
   projection with no model, member with the wrong type.
   Done: a member lookup maps an associated type to the model's type, as
   it maps an operation to its body. The `FIELDACCESS` token may now be
   followed by `.` (so `all x:@C<τ>.Elem. P` lexes); only `.o.` is
   excluded. Where clauses on concepts with associated types and
   `require` on associated types report "not supported yet".
3. **Where clauses without equations:** proxies, the expansion's extra
   binders, `intro_where`, `resolve_where` for theorems and functions.
   C back end and a separate-compilation scenario.
   Done for theorems: `WhereClause.assoc` records a proxy per associated
   type (created by `bind`); the proxy where-models give them as their
   `type` members, so `@C<T>.Elem` resolves to the proxy; the expansion
   binds the proxies first and `_strip_operations` instantiates them with
   the models' types. Still to do, and rejected for now: where clauses of
   functions and parameterized models (`where_params`; the proxies must
   become extra type parameters of the `FunctionType`, matched at calls
   and filled from the models), and refining a concept with associated
   types.
4. **Same-type constraints:** the union-find with unification and
   congruence, the nested-scope rule, and the instantiation check. Fixtures:
   the `same_first` example, the inconsistent and occurs-check errors, the
   nested-scope error, and the failed instantiation.
5. **Docs:** `Reference.md` (Concept, Model, where clauses) and
   `TacticsCheatSheet.md`.
6. **`require` on associated types:** `require Regular<Elem>` in a
   concept. `require` is stored in the concept's `refines` where clause
   (step 1; `ConceptDecl.requires` only keeps the keyword for printing),
   so it already works on other types today. With associated types, a
   where clause gets proxy models of `Regular<Elem₁>`, and a model needs a
   model of `Regular<σ>` in scope.

## Open questions

1. **Implicit instantiation** (`replace same_first`): when a proxy is bound
   only through matching (the formula mentions `Elem₁` but not `C`),
   `C` can't be found. As with parameterized models, the user writes the
   types.
