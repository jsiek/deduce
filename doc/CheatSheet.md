

| Formula        |  Prove        | Use      |
| -------------- | ------------- | -------- |
| `true`         | `.`           | No uses  |
| `false`        | [Contradiction](./Reference.md#contradiction) | implicit as anything |
| `P and Q`      |  `,` [Comma](./Reference.md#comma-conjunction-and-introduction) | (1) implicit as `P`, (2) implicit as `Q` |
| `P or Q`      | (1) implicit from `P`, (2) implicit from `Q` | 
| `if P then Q` | [`assume`](./Reference.md#assume) | [`apply`-`to`](./Reference.md#apply-to-proof-modus-ponens) |
| `all x:T. P`  | [`arbitrary`](./Reference.md#arbitrary-forall-introduction) | [square brackets](./Reference.md#instantiation-proof)


