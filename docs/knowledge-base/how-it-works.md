# How it works

This file contains a detailed explanation of how Deduce *actually* works. This file will explain the source code and how Deduce goes from a text file to the glorious `file.pf is valid` message.

## TODO: Entry point, `deduce.py`, `deduce_file`, `deduce_directory`

## Lexing and Parsing

Deduce starts by building an AST

- Uses lark to lex
- Either recursive descent parser or lark parser
- `Deduce.lark` is maintained for lexing and documentation of the grammar, as well as allowing for the use of lark's parser.

See [`Abstract Syntax`](./abstract-syntax.md) for documentation of the various ast nodes.



## TODO: `check_deduce`

The checking process for programs & proofs has three steps:

1. `process_declarations`:
   Collects the type environment for the top-level statements, usually
   from their declared types. (Except for define's without types.)
2. `type_check_stmt`:
   Type check the bodies of functions using the type environment.
   Perform overload resolution using the types.
3. `collect_env`:
   Collects the proofs (mapping proof labels to their formulas
             and runtime environment mapping variables to values)
   and the values (mapping names to their values, for defines a functions)
   into an environment.
4. `check_proofs`:
   Check that the proofs follow the rules of logic
   and run the print and assert statements.


Explain bidirectional