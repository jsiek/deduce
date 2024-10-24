Here is some advice about what to do next in a proof. Options 1, 3,
and 4 make use of the table below.

1. Prove the goal by decomposing it into sub-goals. In the table
  below, look in the `Prove` column for the current goal. The table
  entry suggests the proof statement to use next.

2. Work backwards from the goal using a
  [`suffices`](./Reference.md#suffices) statement. After the `by`
  keyword, write the reason, often
  [`definition`](./Reference.md#definition) and/or
  [`rewrite`](./Reference.md#rewrite), which transform the goal
  formula.

3. Work forwards from a [given](./Reference.md#given) with a
  [`have`](./Reference.md#have-proof) statement. Look at the formula
  of the given and cross reference the `Use` column in the table
  below. The table entry suggests what to write for the reason after
  the `by` keyword of your `have` statement.

4. For `conclude`, write the reason after the `by` keyword, typically
   using a given according to the `Use` column in the table below.


| Formula        |  Prove        | Use      |
| -------------- | ------------- | -------- |
| `true`         | `.`           | No uses  |
| `false`        | [Contradiction](./Reference.md#contradiction) | implicit as anything |
| `P and Q`      |  `,` [Comma](./Reference.md#comma-conjunction-and-introduction) | (1) implicit as `P`, (2) implicit as `Q` |
| `P or Q`      | (1) implicit from `P`, (2) implicit from `Q` | [`cases`](./Reference.md#cases-disjunction-elimination) |
| `if P then Q` | [`assume`](./Reference.md#assume) | [`apply`-`to`](./Reference.md#apply-to-proof-modus-ponens) |
| `all x:T. P`  | [`arbitrary`](./Reference.md#arbitrary-forall-introduction), [`induction`](./Reference.md#induction) | [brackets](./Reference.md#instantiation-proof) |
| `some x:T. P` | [`choose`](./Reference.md#choose-exists-introduction) | [`obtain`](./Reference.md#obtain-exists-elimination) |
| `x = y`    | Many options including [`symmetric`](./Reference.md#symmetric-proof), [`transitive`](./Reference.md#transitive-proof), [`equations`](./Reference.md#equations), [`definition`](./Reference.md#definition-proof) | Many options including [`symmetric`](./Reference.md#symmetric-proof), [`transitive`](./Reference.md#transitive-proof), [`rewrite`](./Reference.md#rewrite-proof), [`rewrite`-`in`](./Reference.md#rewrite-in-proof) |


