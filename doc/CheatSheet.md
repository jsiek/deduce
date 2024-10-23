At any step in a proof, the next step can either
1. prove the goal formula by decomposing into one or more sub-goals
   using a formula-specific statement,
2. work backwards from the goal formula using a `suffices` statement,
3. work forwards by proving some new fact from the current givens (previously-prove facts)
  with a `have` statement, or
4. `conclude` by giving a proof of the goal formula.

Here is some advice about each of those options. Options 1, 3, and 4
make use of the table below.

1. To prove the goal by decomposing it into sub-goals, cross reference
  the goal formula with the `Prove` column of the below table. The
  table entry will provide guidance regarding which proof statement to
  use next.

2. To work backwards from the goal using a
  [`suffices`](./Reference.md#suffices) statement, use one or both of
  [`definition`](./Reference.md#definition) and
  [`rewrite`](./Reference.md#rewrite) to transform the goal formula.

3. To work forwards with a `have` statement, look at the formula of
  the given that you are using and cross reference that formula with
  the `Use` column in the following table. The table entry provides
  guidance regarding what to write for the reason after the `by`
  keyword of your `have` statement.

4. For `conclude`, to write the reason after by `by` keywork, look at
  given that you want to use and cross reference it with the `Use`
  column.



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


