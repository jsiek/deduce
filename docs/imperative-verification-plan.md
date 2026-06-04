# Imperative verification plan

Tracking issue: TBD.

**Status:** design draft. Nothing in this document is implemented yet. The
examples are proposed surface syntax and future acceptance tests.

## Goal

Extend Deduce with a controlled imperative programming layer for the data
structures and algorithms that show up in undergraduate computer science:
mutable arrays, stacks, queues, linked lists, trees, heaps, hash tables, graph
representations, and algorithm proofs over them.

The core design principle is:

> Pure Deduce stays pure. Imperative code lives in a separate computation
> layer with explicit specifications and explicit proof slots.

That gives students a familiar imperative programming style without making
ordinary Deduce terms silently effectful.

## Non-goals

- Do not turn `fun`, `recursive`, theorem statements, or normal terms into an
  effectful language.
- Do not require an SMT solver for the first implementation. Verification
  goals should be ordinary Deduce goals first; SMT automation can be a later
  acceleration path.
- Do not start with concurrency, IO, exceptions, pointer arithmetic, or manual
  memory management.
- Do not require separation logic for beginner array programs. Dynamic frames
  should be enough for the first tier.

## Design inspirations

This plan combines three compatible ideas:

- **Dijkstra or Hoare monads** provide the core semantics for stateful
  computations: a command has a precondition, a result type, and a postcondition.
- **Dynamic frames** provide the beginner-friendly surface discipline:
  `reads`, `modifies`, `old`, and ghost footprints.
- **Separation logic** provides the advanced assertion language for cyclic,
  aliased, pointer-rich structures such as circular doubly linked lists.

Useful reference systems include Dafny, Why3/WhyML, F*, Hoare Type Theory/Ynot,
Viper, CFML, and Iris.

## User-facing feature overview

### New top-level phrase: `proc`

A `proc` is an imperative procedure. It may read and update state, but it must
declare its contract.

```deduce
proc swap(a: MArray<UInt>, i: UInt, j: UInt)
  requires i < length(a)
  requires j < length(a)
  modifies a
  ensures a[i] = old(a[j])
  ensures a[j] = old(a[i])
{
  var tmp : UInt := a[i]
  a[i] := a[j]
  a[j] := tmp
}
```

The proposed spelling `MArray<T>` avoids changing the meaning of Deduce's
current pure array values. A future design pass may choose a different spelling,
but the semantic distinction should remain:

- pure arrays are ordinary values;
- mutable arrays are heap objects handled by `proc`.

Procedures that return values use `-> T` and refer to the return value as
`result` in postconditions.

```deduce
proc linear_search(a: MArray<UInt>, target: UInt) -> Option<UInt>
  reads a
  ensures result = none or
          some i:UInt. result = just(i) and i < length(a) and a[i] = target
{
  var i : UInt := 0
  while i < length(a)
    invariant i <= length(a)
    invariant all k:UInt. k < i -> a[k] != target
    decreases length(a) - i
  {
    if a[i] = target {
      return just(i)
    }
    i := i + 1
  }
  return none
}
```

### Statements inside `proc`

Initial statement set:

```deduce
var x : T := e
ghost var x : T := e
x := e
a[i] := e
if e { stmt* } else { stmt* }
while e invariant I* established by p preserved by q decreases d by r { stmt* }
assert P
assert P by p
assume P
call p(args)
call p(args) by q
call p(args) as h
return e
```

`ghost` variables and `assume` are proof-only. They are erased from compiled
code and should not affect runtime behavior. Procedure parameters may also be
marked `ghost` when they are needed only to state a contract.

### Specifications

Procedure specifications are written as repeated clauses. Repetition means
conjunction for `requires` and `ensures`, and union for `reads` and `modifies`.

```deduce
proc p(...)
  requires P
  requires Q
  reads frame1
  reads frame2
  modifies frame3
  ensures fact_r: R
  ensures fact_s: S
{
  ...
}
```

The first implementation should support:

- `requires P`: precondition.
- `ensures Q`: postcondition. Public procedures should label postconditions
  that clients may want to cite directly, as in `ensures model_post: Q`.
- `reads F`: heap locations whose values may be read by specifications or by
  pure observer functions used in specifications.
- `modifies F`: heap locations the procedure may update.
- `old(e)`: value of `e` in the procedure's entry state.
- `unchanged(F)`: shorthand for every location in frame `F` preserving its old
  value.
- `decreases d`: termination measure for loops and recursive procedures.

If a procedure has no `modifies` clause, its effective modifies frame is empty.
Allocating new heap objects is allowed, but newly allocated locations are not
part of the caller's old heap and must not let the procedure mutate locations
outside its frame.

### Frame expressions

Frame expressions denote sets of heap locations.

Proposed first tier:

```deduce
a              // every cell of mutable array a
a[i]           // one mutable array cell
p.f            // one mutable object field
footprint(x)   // ghost set of locations owned by an abstraction
{}             // empty frame
```

Commas in `reads` and `modifies` clauses form a union:

```deduce
modifies a[i], a[j]
```

The checker should reject writes outside the current modifies frame.

### Object and reference types

Arrays are enough for Phase 1, but linked structures need heap-allocated nodes.
This plan proposes an `object` declaration and a `Ref<T>` type.

```deduce
object Node<T> {
  var data : T
  var next : Option<Ref<Node<T>>>
}

object ListHead<T> {
  var first : Option<Ref<Node<T>>>
}

proc push_front<T>(h: Ref<ListHead<T>>, x: T)
  modifies h.first, footprint(h)
  ensures list_model(h) = node(x, old(list_model(h)))
{
  var n := new Node<T>(x, h.first)
  h.first := just(n)
}
```

Open questions for this surface:

- Whether Deduce wants `object`, `record`, or `struct`.
- Whether nullable links should be spelled with `Option<Ref<T>>` only, or with
  dedicated `null`.
- Whether references should be first-class pure values outside `proc`. The
  likely answer is yes, but field reads and writes stay effectful.

### Ghost models

Mutable structures should be specified by pure Deduce values.

Examples:

```deduce
observer array_model<T>(a: MArray<T>) -> List<T>
observer stack_model<T>(s: Ref<Stack<T>>) -> List<T>
observer set_model<T>(h: Ref<HashSet<T>>) -> Set<T>
```

A stack implementation can expose a clean contract:

```deduce
proc push<T>(s: Ref<Stack<T>>, x: T)
  requires StackValid(s)
  modifies footprint(s)
  ensures StackValid(s)
  ensures stack_model(s) = node(x, old(stack_model(s)))
{
  ...
}
```

The implementation may use mutable arrays, counters, or linked nodes. Clients
reason about the pure model.

## Core semantics

### One heap model

Dynamic frames and separation logic should not be separate state semantics.
They are two views over one heap model.

At the core, a state is:

```text
State = heap + local variables + allocation set
```

The allocation set is the set of heap identities that currently exist: object
ids for `Ref<T>` values and array ids for `MArray<T>` values. Reads and writes
must target allocated identities; `new` chooses a fresh identity not already in
the allocation set. In the first design, with no deallocation, the allocation
set only grows.

The heap maps locations to values. A location is an array cell or object field:

```text
Loc ::= array_cell(array_id, index)
      | object_field(object_id, field_name)
```

### Computation type

Internally, a procedure body elaborates to a computation type:

```text
ST<Result>(pre, post, reads, modifies)
```

This is a Dijkstra/Hoare-style computation. The checker computes weakest
preconditions for statements and checks the proof terms attached to
verification goals. Ordinary Deduce terms do not have this type.

### Verification Goals

For each procedure, the checker computes verification goals such as:

- preconditions imply the body is safe;
- all array accesses are in bounds;
- all field dereferences are initialized and allocated;
- every write is inside the effective modifies frame;
- the postcondition follows from the body;
- any location outside the modifies frame is unchanged;
- loop invariants hold initially;
- loop invariants are preserved by one iteration;
- loop exit plus invariant implies the continuation goal;
- loop decreases measures are well-founded and strictly decrease.

For a loop:

```deduce
while c
  invariant I
  modifies F
  established by init_proof
  preserved by step_proof
  decreases d by decreases_proof
{
  S
}
```

the essential goals are:

```text
entry:      current facts -> I
preserve:   I and c -> wp(S, I)
exit:       I and not c -> continuation
decreases:  I and c -> 0 <= d and d decreases after S
frame:      writes(S) subset F
```

The `by` clauses provide proof terms for the goals that are not discharged
automatically. A `by` clause can contain an ordinary proof expression, such as a
previous theorem, or a local proof-slot label whose body is supplied later in the
procedure's `proof` block.

### Proof Slot User Experience

The first implementation should make verification goals look and feel like
ordinary Deduce proof goals, without inventing stable generated names for them.
A goal is tied to the source annotation that needs proof.

A procedure may omit explicit proof terms when `auto` can discharge the goals:

```deduce
proc swap(...) ... {
  ...
}
```

If a goal is not automatic and no `by` clause is present, Deduce reports an
incomplete proof at the source construct that created the goal, with the usual
`Goal:` and `Givens:` display.

Short proof terms can be written inline:

```deduce
while i < length(a)
  invariant i <= length(a)
  invariant all k:UInt. k < i -> a[k] = 0
  established by fill_init[a]
  preserved by fill_step[a, i]
  decreases length(a) - i by fill_decreases[a, i]
{
  a[i] := 0
  i := i + 1
}
```

Long proof terms can be moved to the procedure's proof block. The point of
definition of a local proof-slot name is the `by label` annotation, not the
proof block entry.

```deduce
proc fill_zero(a: MArray<UInt>)
  modifies a
  ensures all k:UInt. k < length(a) -> a[k] = 0
{
  var i : UInt := 0
  while i < length(a)
    invariant i <= length(a)
    invariant all k:UInt. k < i -> a[k] = 0
    established by loop_init
    preserved by loop_step
    decreases length(a) - i by loop_decreases
  {
    a[i] := 0
    i := i + 1
  }
}
proof
  loop_init {
    ...
  }
  loop_step {
    ...
  }
  loop_decreases {
    ...
  }
end
```

The `proof` block is syntactic sugar for long inline proofs. Deduce should
reject a proof-block entry that does not correspond to a `by label` slot in the
procedure. If a bare `by name` could refer both to an in-scope theorem and to a
local proof-slot label, Deduce should report an ambiguity instead of guessing.

The LSP can later expose:

- "show verification goal for this proof slot";
- "jump to next missing proof";
- "insert proof skeleton";
- "explain why this frame is insufficient";
- "extract this proof slot as a theorem".

### Call Labels And Postconditions

After a verified imperative call, the callee's postconditions become facts in
the caller's symbolic proof context. Unlabeled postconditions are available to
`auto` and should appear in goal displays, but they are not convenient to cite
by hand.

When a later proof needs to refer to a specific postcondition, the call site can
introduce a local namespace with `as`.

```deduce
public proc push<T>(s: Ref<Stack<T>>, x: T)
  requires StackValid(s)
  modifies footprint(s)
  ensures valid_post: StackValid(s)
  ensures model_post: stack_model(s) = node(x, old(stack_model(s)))
{
  ...
}

proc client(s: Ref<Stack<UInt>>)
  requires StackValid(s)
  modifies footprint(s)
  ensures StackValid(s)
{
  ghost var before := stack_model(s)
  call push(s, 10) as hp
  assert StackValid(s) by hp.valid_post
  assert stack_model(s) = node(10, before) by hp.model_post
}
```

The call label is the point of definition for the instantiated postcondition
facts. In the example, `hp.valid_post` and `hp.model_post` are available only
after the call. They are the `push` postconditions specialized to this call.

For a call that returns a value, the returned value is substituted for `result`
in the labeled facts.

```deduce
var x := call pop(s) as hpop
assert StackValid(s) by hpop.valid_post
assert x = old_front by hpop.result_post
```

The `old(...)` in a callee postcondition is relative to the state immediately
before that call, not necessarily the beginning of the caller procedure. When a
later proof needs a readable name for that pre-call value, use a ghost variable
before the call, as in `before` above.

If a call has no `as` label, its postconditions remain available anonymously to
automation. Deduce should reject `hp.model_post` if `hp` is not a prior call
label, if `model_post` is not a labeled postcondition of the callee, or if the
call label is out of scope.

## Dynamic frames tier

Dynamic frames are the default user-facing discipline for arrays and simple
objects.

### Frame-preserving observer functions

Read-framed observer functions over mutable state are pure specification
functions. They may read the heap, but they cannot mutate it and they cannot be
called from runtime code.

```deduce
observer sorted(a: MArray<UInt>) -> bool
  reads a
{
  all i:UInt, j:UInt.
    i < j and j < length(a) -> a[i] <= a[j]
}
```

If a procedure modifies `b` but not `a`, then facts about `sorted(a)` remain
usable because `sorted` reads only `a`.

```deduce
proc touch_other(a: MArray<UInt>, b: MArray<UInt>)
  requires sorted(a)
  modifies b
  ensures sorted(a)
{
  if length(b) > 0 {
    b[0] := 0
  }
}
```

Without read frames, this kind of reasoning quickly becomes unmanageable.

### Ghost footprints

For heap objects, a valid data structure exposes a ghost footprint.

```deduce
predicate QueueValid<T>(q: Ref<Queue<T>>)
  reads footprint(q)

observer queue_model<T>(q: Ref<Queue<T>>) -> List<T>
  reads footprint(q)
```

Procedures use the footprint as the dynamic frame:

```deduce
proc enqueue<T>(q: Ref<Queue<T>>, x: T)
  requires QueueValid(q)
  modifies footprint(q)
  ensures QueueValid(q)
  ensures queue_model(q) = app(old(queue_model(q)), [x])
{
  ...
}
```

This is the beginner-friendly interface even if the internal proof later uses
separation logic.

## Separation logic tier

Separation logic is the advanced tier for alias-heavy structures and cycles.

### Resource assertions

This plan uses `resource` for user-defined separation predicates and `**` for
separating conjunction.

```deduce
resource cell<T>(p: Ref<Cell<T>>, v: T) {
  p.value |-> v
}

resource two_cells<T>(p: Ref<Cell<T>>, x: T,
                      q: Ref<Cell<T>>, y: T) {
  p.value |-> x ** q.value |-> y
}
```

Proposed primitive resource assertions:

```deduce
emp
P ** Q
p.f |-> v
acc(p.f)
acc(p.f, fraction)
array_cell(a, i) |-> v
```

The first implementation can skip fractional permissions and support only full
write ownership. Fractional permissions become useful when clients need
read-only sharing.

### Doubly linked and cyclic lists

A circular doubly linked list is best represented by a sentinel node. The
sentinel is always present; the logical list is the sequence of non-sentinel
nodes reached by following `next`.

```deduce
object DNode<T> {
  var data : Option<T>
  var next : Ref<DNode<T>>
  var prev : Ref<DNode<T>>
}
```

The resource predicate should describe both the heap shape and the pure model.

```deduce
resource dll_segment<T>(first: Ref<DNode<T>>,
                        left: Ref<DNode<T>>,
                        last: Ref<DNode<T>>,
                        right: Ref<DNode<T>>,
                        xs: List<T>)

resource dll<T>(sentinel: Ref<DNode<T>>, xs: List<T>) {
  sentinel.data |-> none **
  dll_segment(sentinel.next, sentinel, sentinel.prev, sentinel, xs)
}
```

The intended meaning of `dll_segment(first, left, last, right, xs)` is:

- the segment stores exactly the values `xs`;
- `first.prev = left`;
- `last.next = right`;
- every internal adjacent pair agrees on `next` and `prev`;
- the owned nodes are disjoint from the boundary nodes unless the segment is
  empty;
- for the full `dll`, the boundaries are the sentinel, so the structure may be
  cyclic.

Insertion after a node is a small local rewrite:

```deduce
proc insert_after<T>(p: Ref<DNode<T>>, x: T)
  requires sep node_linked_in_dll(p)
  modifies p.next, p.next.prev
  ensures sep node_linked_in_dll(p)
{
  var q := p.next
  var n := new DNode<T>(just(x), q, p)
  p.next := n
  q.prev := n
}
```

The public operation would usually expose the dynamic-frame model:

```deduce
proc push_front<T>(s: Ref<DNode<T>>, x: T)
  requires DllValid(s)
  modifies footprint(s)
  ensures DllValid(s)
  ensures dll_model(s) = node(x, old(dll_model(s)))
{
  call insert_after(s, x)
}
```

The implementation proof can use `dll` and `dll_segment`; clients only need
`DllValid`, `footprint`, and `dll_model`.

### Bridging dynamic frames and separation logic

Every resource predicate should have a footprint.

```deduce
observer footprint_of_dll<T>(s: Ref<DNode<T>>, xs: List<T>) -> Set<Loc>

theorem dll_footprint:
  all T:type, s:Ref<DNode<T>>, xs:List<T>.
    sep dll(s, xs) -> footprint(s) = footprint_of_dll(s, xs)
```

Bridge lemmas let a module use separation logic internally and export dynamic
frame contracts externally.

```deduce
theorem dll_valid_from_resource:
  all T:type, s:Ref<DNode<T>>, xs:List<T>.
    sep dll(s, xs) -> DllValid(s) and dll_model(s) = xs
```

This keeps the beginner interface small while preserving enough power for
cyclic structures.

## Modules, Visibility, And Abstraction

The imperative layer should reuse Deduce's existing module system:

- `public` exports a name.
- `private` keeps a name usable only inside the defining module.
- `opaque` exports a name but hides its implementation.
- `import M using ...` and `import M hiding ...` filter imperative names the
  same way they filter existing names.

The new declaration forms should all be declarations with visibility:

```deduce
public proc ...
private proc ...
opaque object ...
private resource ...
opaque observer ...
```

### Exported Contracts

An exported procedure's public contract must mention only names that are
available to importing modules. This should be checked at the module boundary.

Good:

```deduce
module Stack

opaque object Stack<T> {
  private var data : MArray<T>
  private ghost var Repr : Set<Loc>
}

opaque predicate StackValid<T>(s: Ref<Stack<T>>)
  reads footprint(s)

opaque observer stack_model<T>(s: Ref<Stack<T>>) -> List<T>
  reads footprint(s)

public proc push<T>(s: Ref<Stack<T>>, x: T)
  requires StackValid(s)
  modifies footprint(s)
  ensures valid_post: StackValid(s)
  ensures model_post: stack_model(s) = node(x, old(stack_model(s)))
{
  ...
}
```

Bad:

```deduce
module Stack

private resource stack_rep<T>(s: Ref<Stack<T>>, xs: List<T>)

public proc push<T>(s: Ref<Stack<T>>, x: T)
  requires sep stack_rep(s, xs)
  ensures sep stack_rep(s, node(x, xs))
{
  ...
}
```

The bad version exports a procedure whose contract mentions the private
resource `stack_rep`, so clients could not call it or use its postcondition.
Deduce should reject this as a visibility error.

### Opaque Objects

An `opaque object` exports the object type but hides its fields, constructor,
and allocation syntax outside the module.

Inside the module:

```deduce
var s := new Stack<T>(...)
s.data := ...
```

Outside the module:

```deduce
var s : Ref<Stack<UInt>> := call empty_stack<UInt>()
call push(s, 10)
```

Outside clients may hold references, compare references if that operation is
provided, pass references to exported procedures, and use exported observers.
They may not read or write hidden fields or allocate hidden objects directly.

This mirrors the current rule for `opaque union`: the type can be mentioned,
but constructors are hidden.

### Opaque Predicates, Observers, And Resources

Opaque specification declarations are the main way to hide invariants while
still letting clients reason abstractly.

- `opaque predicate StackValid(s)` lets clients assume, require, and preserve
  validity, but not unfold its definition.
- `opaque observer stack_model(s)` lets clients state contracts using the
  abstract model, but not expand the observer body.
- `private resource stack_rep(s, xs)` is used only by implementation proofs.
- `private theorem stack_rep_to_valid` bridges the internal resource to the
  public predicate and observer.

Example internal proof structure:

```deduce
module Stack

opaque object Stack<T> {
  private var data : MArray<T>
  private var size : UInt
  private ghost var Repr : Set<Loc>
}

opaque predicate StackValid<T>(s: Ref<Stack<T>>)
  reads footprint(s)

opaque observer stack_model<T>(s: Ref<Stack<T>>) -> List<T>
  reads footprint(s)

private resource stack_rep<T>(s: Ref<Stack<T>>, xs: List<T>)

private theorem stack_rep_exposes_api:
  all T:type, s:Ref<Stack<T>>, xs:List<T>.
    sep stack_rep(s, xs) -> StackValid(s) and stack_model(s) = xs
proof
  ...
end

public proc push<T>(s: Ref<Stack<T>>, x: T)
  requires StackValid(s)
  modifies footprint(s)
  ensures valid_post: StackValid(s)
  ensures model_post: stack_model(s) = node(x, old(stack_model(s)))
{
  ghost var before := stack_model(s)
  ...
  assert StackValid(s) and stack_model(s) = node(x, before)
    by implementation
}
proof
  implementation {
    // Open stack_rep internally, update fields, close stack_rep again,
    // then use stack_rep_exposes_api to re-establish the public contract.
    ...
  }
end
```

Clients importing `Stack` see `Stack`, `StackValid`, `stack_model`, and `push`.
They do not see `data`, `size`, `Repr`, `stack_rep`, or
`stack_rep_exposes_api`.

### Procedure Bodies And Proofs

Procedure bodies and local proof slots are implementation details across a
module boundary.

- A public procedure exports its callable name and its public contract.
- A private procedure is available only inside the module.
- Procedure bodies are not unfolded by client proofs.
- Procedure proof-block entries are private unless their proof is exported as
  an ordinary theorem.

This is intentionally stricter than public pure functions, whose definitions may
currently be expanded unless they are marked `opaque`. For imperative code, the
contract is the proof interface; the body is the implementation.

### Public Constructors

Opaque mutable objects need exported constructor procedures instead of public
allocation syntax.

```deduce
public proc empty_stack<T>() -> Ref<Stack<T>>
  ensures valid_post: StackValid(result)
  ensures model_post: stack_model(result) = []
{
  var s := new Stack<T>(...)
  return s
}
```

This keeps allocation and representation initialization inside the module.

### Re-exporting Imperative APIs

Library umbrella modules should re-export imperative APIs with existing
`public import` syntax.

```deduce
module MutableCollections

public import Stack using Stack | StackValid | stack_model | empty_stack | push | pop
public import Queue using Queue | QueueValid | queue_model | empty_queue | enqueue | dequeue
```

The `using` names match top-level declaration names. Hidden fields, private
resources, and local proof-slot labels are not top-level exports and should not
be selectable.

## Proposed grammar sketch

This is intentionally a sketch, not a parser-ready grammar.

```text
statement ::=
    ...
  | visibility proc_decl
  | visibility observer_decl
  | visibility object_decl
  | visibility resource_decl

visibility ::= "public" | "private" | "opaque" | empty

proc_decl ::=
  "proc" id type_params? "(" params? ")" return_type?
    spec_clause*
    block
    proc_proof?

observer_decl ::=
  "observer" id type_params? "(" params? ")" "->" type
    "reads" frame_list observer_body?

observer_body ::= "{" term "}"

object_decl ::=
  "object" id type_params? object_body?

object_body ::= "{" object_field* "}"

object_field ::=
  visibility "ghost"? "var" id ":" type

params ::= param ("," param)*

param ::= "ghost"? id ":" type

return_type ::= "->" type

spec_clause ::=
    "requires" spec_label? formula
  | "requires" "sep" spec_label? resource_formula
  | "ensures" spec_label? formula
  | "ensures" "sep" spec_label? resource_formula
  | "reads" frame_list
  | "modifies" frame_list
  | "decreases" term

spec_label ::= id ":"

block ::= "{" imp_stmt* "}"

imp_stmt ::=
    "var" id type_ann? ":=" imp_rhs
  | "ghost" "var" id type_ann? ":=" term
  | lvalue ":=" imp_rhs
  | "if" term block "else" block
  | "while" term loop_spec* block
  | "assert" formula proof_clause?
  | "assume" formula
  | call_expr
  | "return" term

imp_rhs ::= term | call_expr

call_expr ::= "call" id type_args? "(" term_list? ")" call_label? proof_clause?

call_label ::= "as" id

type_args ::= "<" type_list ">"

loop_spec ::=
    "invariant" formula
  | "established" "by" proof_ref
  | "preserved" "by" proof_ref
  | "modifies" frame_list
  | "decreases" term proof_clause?

proof_clause ::= "by" proof_ref

proof_ref ::= proof | id | id "." id

lvalue ::=
    id
  | term "[" term "]"
  | term "." id

proc_proof ::=
  "proof" proof_slot* "end"

proof_slot ::=
  id "{" proof "}"

resource_decl ::=
  "resource" id type_params? "(" params? ")" resource_body?

resource_body ::=
  "{" resource_formula "}"
```

Allocation expressions such as `new Node<T>(...)` are effectful and should be
accepted only in procedure statement right-hand sides, not in ordinary Deduce
terms.

## Implementation phases

### Phase 1: Imperative AST and parser, no verifier

- Add AST nodes for `Proc`, imperative statements, spec clauses, frame
  expressions, observer declarations, object declarations, and resource
  declarations.
- Parser accepts the proposed syntax under a feature flag, for example
  `--experimental-imperative`.
- Type checker rejects procedure calls from pure terms.
- Pretty-printer and symbol outline include procedures, observers, objects, and
  resources.
- Import filters accept the new top-level declaration names.

Acceptance:

- parser fixtures for each new syntactic form;
- type checker confirms pure `fun` cannot write mutable state;
- LSP symbols include `proc`, `observer`, `object`, and `resource`
  declarations;
- `import M using p` can import an exported procedure `p`;
- a public procedure whose contract mentions a private name is rejected.

### Phase 2: Mutable arrays and local variables

- Add `MArray<T>` handles and operations: length, read, write, allocation from
  a list.
- Implement local variable assignment.
- Implement `requires`, `ensures`, `modifies`, `old`, `while invariant`, and
  `decreases`.
- Check inline `by` proof terms and out-of-line proof-slot entries against the
  verification goals computed from procedure annotations.

Acceptance:

- `swap`, `fill`, `linear_search`, and `binary_search` verify using explicit
  proof slots where automation is insufficient;
- writing outside `modifies` is rejected;
- missing loop invariant produces a clear verification failure;
- invalid array access requires a bound proof.

### Phase 3: Dynamic-frame objects and ghost models

- Add `object` and `Ref<T>`.
- Add `new`, field read, and field write.
- Add ghost footprints and read-frame checking for observer functions.
- Implement `opaque object` field hiding and allocation hiding.
- Verify mutable stack and queue implementations against pure list models.

Acceptance:

- stack `push` and `pop` preserve `StackValid`;
- queue `enqueue` and `dequeue` preserve `QueueValid`;
- modifying one object does not invalidate facts about an object with a
  disjoint footprint;
- aliasing errors produce frame or invariant failures;
- clients cannot access fields of an imported `opaque object`;
- clients can call exported constructor procedures for opaque objects.

### Phase 4: Separation logic resources

- Add resource assertions: `emp`, `**`, `|->`, and user-defined `resource`
  predicates.
- Add proof rules for frame, consequence, open/fold of resources, and local
  heap updates.
- Keep full write permissions only at first.
- Keep private resource predicates hidden across module boundaries.

Acceptance:

- verify a two-cell swap with `p.value |-> x ** q.value |-> y`;
- verify singly linked list segment append;
- verify circular doubly linked list insertion and removal around a sentinel;
- importing modules cannot mention private resource predicates.

### Phase 5: Bridges and library data structures

- Define standard resource predicates and dynamic-frame interfaces for:
  mutable arrays, stacks, queues, singly linked lists, circular doubly linked
  lists, binary search trees, heaps, and hash tables.
- Provide bridge lemmas from resources to footprints and pure models.
- Prefer public specs in dynamic-frame style; use separation logic internally
  where it earns its keep.

Acceptance:

- clients can use `push_front` and `remove` through `DllValid` and `dll_model`
  without seeing the internal `dll_segment` proof;
- advanced users can open the resource predicate and prove local pointer
  rewrites directly inside the implementation module;
- umbrella modules can `public import ... using ...` only the intended public
  API.

### Phase 6: Compilation and runtime

- Extend the existing compiler pipeline to imperative procedures.
- Map `MArray` and objects to runtime heap structures.
- Erase ghost code and proofs.
- Preserve runtime checks only for conditions that are not statically proved
  in the executable fragment, if any.

Acceptance:

- verified array algorithms compile and run;
- ghost-only code produces no runtime behavior;
- compiled output agrees with interpreter behavior on executable examples.

## Test case catalog

These are proposed fixtures. They should not be added to the active test suite
until the corresponding syntax is implemented. The array-level fixtures are
intended to be copied directly into `test/imperative/should-validate/` and
`test/imperative/should-error/` once Phase 2 lands. Later object and separation
logic fixtures are sketches whose exact helper predicates should be finalized
with the library implementation.

### `should-validate/local_counter.pf`

Purpose: local variables, while invariant, and decreases.

```deduce
import UInt

proc count_to(n: UInt) -> UInt
  ensures result = n
{
  var i : UInt := 0
  while i < n
    invariant i <= n
    decreases n - i
  {
    i := i + 1
  }
  return i
}
```

Expected: validates.

### `should-validate/array_swap.pf`

Purpose: array reads/writes, `old`, and narrow modifies frame.

```deduce
import UInt
import List

proc swap(a: MArray<UInt>, i: UInt, j: UInt)
  requires i < length(a)
  requires j < length(a)
  modifies a[i], a[j]
  ensures a[i] = old(a[j])
  ensures a[j] = old(a[i])
  ensures all k:UInt. k < length(a) and k != i and k != j ->
            a[k] = old(a[k])
{
  var tmp : UInt := a[i]
  a[i] := a[j]
  a[j] := tmp
}
```

Expected: validates.

### `should-error/array_swap_missing_modifies.pf`

Purpose: reject writes outside the declared frame.

```deduce
import UInt

proc bad_swap(a: MArray<UInt>, i: UInt, j: UInt)
  requires i < length(a)
  requires j < length(a)
  modifies a[i]
{
  var tmp : UInt := a[i]
  a[i] := a[j]
  a[j] := tmp
}
```

Expected: error at `a[j] := tmp`, because `a[j]` is not in the modifies frame.

### `should-validate/array_fill_zero.pf`

Purpose: loop writes across an array with an invariant over prefix and suffix.

```deduce
import UInt

proc fill_zero(a: MArray<UInt>)
  modifies a
  ensures all k:UInt. k < length(a) -> a[k] = 0
{
  var i : UInt := 0
  while i < length(a)
    invariant i <= length(a)
    invariant all k:UInt. k < i -> a[k] = 0
    invariant all k:UInt. i <= k and k < length(a) -> a[k] = old(a[k])
    decreases length(a) - i
  {
    a[i] := 0
    i := i + 1
  }
}
```

Expected: validates.

### `should-error/array_fill_missing_invariant.pf`

Purpose: show that postconditions after loops need invariants.

```deduce
import UInt

proc fill_zero_bad(a: MArray<UInt>)
  modifies a
  ensures all k:UInt. k < length(a) -> a[k] = 0
{
  var i : UInt := 0
  while i < length(a)
    invariant i <= length(a)
    decreases length(a) - i
  {
    a[i] := 0
    i := i + 1
  }
}
```

Expected: incomplete proof goal for the postcondition.

### `should-validate/linear_search.pf`

Purpose: return values, early return, existential postcondition.

```deduce
import UInt
import Option

proc linear_search(a: MArray<UInt>, target: UInt) -> Option<UInt>
  reads a
  ensures result = none or
          some i:UInt. result = just(i) and i < length(a) and a[i] = target
  ensures result = none ->
          all k:UInt. k < length(a) -> a[k] != target
{
  var i : UInt := 0
  while i < length(a)
    invariant i <= length(a)
    invariant all k:UInt. k < i -> a[k] != target
    decreases length(a) - i
  {
    if a[i] = target {
      return just(i)
    } else {
      i := i + 1
    }
  }
  return none
}
```

Expected: validates.

### `should-validate/frame_preserves_sorted.pf`

Purpose: read frames preserve facts about untouched state.

```deduce
import UInt

observer sorted(a: MArray<UInt>) -> bool
  reads a
{
  all i:UInt, j:UInt.
    i < j and j < length(a) -> a[i] <= a[j]
}

proc modify_other(a: MArray<UInt>, b: MArray<UInt>)
  requires sorted(a)
  modifies b
  ensures sorted(a)
{
  if length(b) > 0 {
    b[0] := 0
  }
}
```

Expected: validates because `sorted` reads only `a`.

### `should-error/bad_decreases.pf`

Purpose: reject non-decreasing loops.

```deduce
import UInt

proc diverge_shape(n: UInt)
{
  var i : UInt := 0
  while i < n
    invariant i <= n
    decreases i
  {
    i := i + 1
  }
}
```

Expected: incomplete proof goal showing that `i` does not decrease.

### `should-validate/two_cell_swap_sep.pf`

Purpose: smallest separation-logic local update.

```deduce
object Cell<T> {
  var value : T
}

proc cell_swap<T>(p: Ref<Cell<T>>, q: Ref<Cell<T>>,
                  ghost x: T, ghost y: T)
  requires sep p.value |-> x ** q.value |-> y
  ensures sep p.value |-> y ** q.value |-> x
{
  var tmp : T := p.value
  p.value := q.value
  q.value := tmp
}
```

Expected: validates, with a side condition that `p.value` and `q.value` are
distinct resources supplied by `**`.

### `should-error/duplicate_resource.pf`

Purpose: demonstrate that separation ownership cannot be duplicated.

```deduce
object Cell<T> {
  var value : T
}

proc duplicate_resource<T>(p: Ref<Cell<T>>, ghost x: T)
  requires sep p.value |-> x
  ensures sep p.value |-> x ** p.value |-> x
{
}
```

Expected: incomplete proof goal for the postcondition, because exclusive
ownership of `p.value` cannot be copied.

### `should-validate/stack_push_model.pf`

Purpose: dynamic-frame ADT proof with a pure list model.

```deduce
import List

object Stack<T> {
  var data : MArray<T>
  var size : UInt
  ghost var model : List<T>
  ghost var Repr : Set<Loc>
}

predicate StackValid<T>(s: Ref<Stack<T>>)
  reads s.Repr

observer stack_model<T>(s: Ref<Stack<T>>) -> List<T>
  reads s.Repr

proc push<T>(s: Ref<Stack<T>>, x: T)
  requires StackValid(s)
  modifies s.Repr
  ensures StackValid(s)
  ensures stack_model(s) = node(x, old(stack_model(s)))
{
  ...
}
```

Expected: validates once arrays, objects, ghost fields, and frames exist.

### `should-validate/dll_push_front_public.pf`

Purpose: public dynamic-frame interface for a cyclic doubly linked list.

```deduce
import List
import Option

object DNode<T> {
  var data : Option<T>
  var next : Ref<DNode<T>>
  var prev : Ref<DNode<T>>
}

predicate DllValid<T>(s: Ref<DNode<T>>)
  reads footprint(s)

observer dll_model<T>(s: Ref<DNode<T>>) -> List<T>
  reads footprint(s)

proc push_front<T>(s: Ref<DNode<T>>, x: T)
  requires DllValid(s)
  modifies footprint(s)
  ensures DllValid(s)
  ensures dll_model(s) = node(x, old(dll_model(s)))
{
  var q := s.next
  var n := new DNode<T>(just(x), q, s)
  s.next := n
  q.prev := n
}
```

Expected: validates after object and dynamic-frame support. Internal proof may
need resource predicates, but clients should see only `DllValid` and
`dll_model`.

### `should-validate/dll_insert_after_sep.pf`

Purpose: direct separation-logic proof for cyclic doubly linked list surgery.

```deduce
import List
import Option

object DNode<T> {
  var data : Option<T>
  var next : Ref<DNode<T>>
  var prev : Ref<DNode<T>>
}

resource dll_segment<T>(first: Ref<DNode<T>>,
                        left: Ref<DNode<T>>,
                        last: Ref<DNode<T>>,
                        right: Ref<DNode<T>>,
                        xs: List<T>)

proc insert_after<T>(p: Ref<DNode<T>>, x: T)
  requires sep local_dll_gap(p, q, xs_left, xs_right)
  modifies p.next, q.prev
  ensures sep local_dll_gap_with_inserted(p, x, q, xs_left, xs_right)
{
  var q := p.next
  var n := new DNode<T>(just(x), q, p)
  p.next := n
  q.prev := n
}
```

Expected: validates after separation resources exist. The exact helper
resources should be refined when implementing the library.

### `should-error/dll_breaks_back_pointer.pf`

Purpose: demonstrate that cyclic doubly linked invariants catch one-sided
updates.

```deduce
import Option

object DNode<T> {
  var data : Option<T>
  var next : Ref<DNode<T>>
  var prev : Ref<DNode<T>>
}

proc bad_insert_after<T>(p: Ref<DNode<T>>, x: T)
  requires DllValid(owner_of(p))
  modifies footprint(owner_of(p))
  ensures DllValid(owner_of(p))
{
  var q := p.next
  var n := new DNode<T>(just(x), q, p)
  p.next := n
  // Missing q.prev := n
}
```

Expected: incomplete proof goal for `DllValid(owner_of(p))`.

### `modules/Stack.pf`

Purpose: implementation module exports an abstract imperative API while hiding
fields, resources, and bridge theorems.

```deduce
module Stack

import UInt
import List

opaque object Stack<T> {
  private var data : MArray<T>
  private var size : UInt
  private ghost var Repr : Set<Loc>
}

opaque predicate StackValid<T>(s: Ref<Stack<T>>)
  reads footprint(s)

opaque observer stack_model<T>(s: Ref<Stack<T>>) -> List<T>
  reads footprint(s)

private resource stack_rep<T>(s: Ref<Stack<T>>, xs: List<T>)

private theorem stack_rep_exposes_api:
  all T:type, s:Ref<Stack<T>>, xs:List<T>.
    sep stack_rep(s, xs) -> StackValid(s) and stack_model(s) = xs
proof
  ...
end

public proc empty_stack<T>() -> Ref<Stack<T>>
  ensures valid_post: StackValid(result)
  ensures model_post: stack_model(result) = []
{
  ...
}

public proc push<T>(s: Ref<Stack<T>>, x: T)
  requires StackValid(s)
  modifies footprint(s)
  ensures valid_post: StackValid(s)
  ensures model_post: stack_model(s) = node(x, old(stack_model(s)))
{
  ...
}
```

Expected: validates inside the implementation module.

### `should-validate/import_abstract_stack.pf`

Purpose: client can use the public abstract stack API without seeing the
representation.

```deduce
import Stack using Stack | StackValid | stack_model | empty_stack | push
import UInt
import List

proc run_stack_example() -> Ref<Stack<UInt>>
{
  var s := call empty_stack<UInt>() as hempty
  assert StackValid(s) by hempty.valid_post
  assert stack_model(s) = [] by hempty.model_post
  ghost var before_push1 := stack_model(s)
  call push(s, 10) as hpush1
  assert StackValid(s) by hpush1.valid_post
  assert stack_model(s) = node(10, before_push1) by hpush1.model_post
  ghost var before_push2 := stack_model(s)
  call push(s, 20) as hpush2
  assert StackValid(s) by hpush2.valid_post
  assert stack_model(s) = node(20, before_push2) by hpush2.model_post
  return s
}
```

Expected: validates. The client mentions only exported names.

### `should-error/call_label_unknown_postcondition.pf`

Purpose: reject references to postcondition labels that the callee did not
export.

```deduce
import Stack using Stack | StackValid | empty_stack
import UInt

proc bad_call_label()
{
  var s := call empty_stack<UInt>() as hempty
  assert StackValid(s) by hempty.no_such_post
}
```

Expected: error at `hempty.no_such_post`, because `empty_stack` has no
postcondition with that label.

### `should-error/export_private_resource_contract.pf`

Purpose: reject exported procedure specs that leak private representation names.

```deduce
module BadStack

opaque object Stack<T> {
  private var data : MArray<T>
}

private resource stack_rep<T>(s: Ref<Stack<T>>, xs: List<T>)

public proc bad_push<T>(s: Ref<Stack<T>>, x: T, ghost xs: List<T>)
  requires sep stack_rep(s, xs)
  ensures sep stack_rep(s, node(x, xs))
{
  ...
}
```

Expected: visibility error at `bad_push`, because a public contract mentions
the private resource `stack_rep`.

### `should-error/opaque_object_field_access.pf`

Purpose: clients cannot access fields of an imported opaque object.

```deduce
import Stack using Stack | empty_stack
import UInt

proc bad_client()
{
  var s := call empty_stack<UInt>()
  s.size := 0
}
```

Expected: visibility error at `s.size`, because `size` is a hidden field of
opaque object `Stack`.

## Diagnostics requirements

Good errors matter as much as soundness for this feature. Target diagnostics:

- "assignment writes `a[j]`, but the current modifies frame is `a[i]`";
- "loop invariant is not known after one iteration";
- "postcondition may fail because the loop invariant does not mention ...";
- "array access `a[i]` needs proof of `i < length(a)`";
- "observer `sorted(a)` may change because its read frame overlaps the
  modifies frame";
- "resource `p.next |-> v` is required but not available";
- "cannot split resource assertion; try opening `dll_segment` first".
- "public procedure `bad_push` exposes private name `stack_rep` in its
  contract";
- "field `size` of opaque object `Stack` is not visible here".
- "unknown call label `hp`";
- "procedure `push` has no labeled postcondition `model_post`".

## Open design questions

- Should the top-level keyword be `proc`, `method`, or `imperative`?
- Should mutable arrays be spelled `MArray<T>`, `Array<T>`, or reuse `[T]` in
  procedure contexts?
- Should the first implementation include object references, or should Phase 1
  stay arrays-only until the proof-slot machinery is solid?
- Should procedure proof slots accept arbitrary proof expressions inline, or
  should the first implementation require bare labels plus `proof ... end`
  entries?
- Should separation formulas use `sep` clauses, a distinct formula type, or
  ordinary formulas with resource connectives?
- Should object fields have their own `public`/`private` visibility, or should
  opaque objects always hide all fields outside the defining module?
- Should `opaque proc` mean anything beyond the default rule that procedure
  bodies are hidden across module boundaries?
- How much automation should be built into `auto` before adding optional SMT
  support?
- Should partial correctness be available via `decreases *`, or should Deduce
  require termination for all checked procedures at first?

## Recommended first slice

The smallest useful implementation slice is:

1. Add `proc` with local variables, `if`, `while`, and returns.
2. Add `MArray<T>` reads/writes, `length`, and `new_array`.
3. Support `requires`, `ensures`, `modifies`, `old`, loop `invariant`, and
   loop `decreases`.
4. Check `by` proof terms and proof-block entries as ordinary Deduce proofs.
5. Validate `local_counter`, `array_swap`, `array_fill_zero`, and
   `linear_search`.

This slice already supports a meaningful set of undergraduate algorithms while
keeping the advanced heap story out of the initial parser/checker work.
