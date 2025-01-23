# Getting Started

## Installation

You will need [Python](https://www.python.org/) version 3.10 or later. Here are some [instructions](https://wiki.python.org/moin/BeginnersGuide/Download) and links to the download for various systems.

You will also need to install the [Lark](https://github.com/lark-parser/lark) parsing library, which you can do by running the following command in the same directory as `deduce.py`

```
python -m pip install lark
```

## Source Code

The source code for Deduce can be obtained from the following GitHub repository.

[https://github.com/jsiek/deduce](https://github.com/jsiek/deduce)

## Deduce Introduction

This introduction to Deduce has two parts. The first part gives a tutorial on how to write programs in Deduce. The second part shows how to write proofs in Deduce.

* [Programming in Deduce](./FunctionalProgramming.md)
* [Writing Proofs in Deduce](./ProofIntro.md)

I recommend that you work through the examples in this introduction. Create a file named `examples.pf` in the top `deduce` directory and add the examples one at a time. To check the file, run the `deduce.py` script on the file from the `deduce` directory.

You can also download one of these extensions for programming in Deduce in some common text editors.

* VSCode ([deduce-mode](https://github.com/HalflingHelper/deduce-mode)). You can also install it from the extensions tab in VSCode
* Emacs ([deduce-mode](https://github.com/mateidragony/deduce-mode))
* Vim (not now, not ever)

The Deduce Reference manual is linked below. It provides an alphabetical list of all the features in Deduce. The Cheat Sheet gives some advice regarding proof strategy and which Deduce keyword to use next in a proof. The Syntax Overview page provides a brief overview of the syntax structure of deduce.

* [Reference Manual](./Reference.md)
* [Cheat Sheet](./CheatSheet.md)
* [Syntax Overview](./SyntaxGrammar.md)

## Command Line Arguments

The `deduce.py` script supports certain command line arguments which
are documented below. If an argument is not preceded by one of the
keywords listed below, then it is treated as the name of a file or
directory and will be processed by Deduce.

`--dir directory-name`

Tells Deduce to include the given `directory-name` in the list of
directories to search when importing a file. For example, if `test.pf`
imports `Curry`, and `Curry.pf` resides in a folder named `howard`,
then `--dir howard` will allow `test.pf` to import `Church`. Note that
`--dir` expects a directory name, not an individual file.

`--no-stdlib`

Deduce, by default, will locate and link the standard library (in
`/lib` of the Deduce repository). However if this argument is
supplied, it will not do so.

`--lalr`

Deduce normally uses a custom recursive descent parser to parse any
input files, however this argument will make Deduce instead use lark's
LALR parser. This argument exists solely for checking that
`Deduce.lark` maintains parity with the recursive descent parser.

`--recursive-descent`

Tells Deduce to use the recursive descent (default) parser. If
`--lalr` is also supplied, then only the recursive descent parser will
be used.

`--recursive-directories` or `-r`

Instead of only processing files in the specified directories, Deduce
will also descend into any subdirectories.

`--traceback`

Prints out the exception if processing a file triggers an error.

`--unique-names`

Prints out all variables and types with an unique name. For example,
if a program defines a variable `x` in several different scopes, `x`
would instead be printed out as `x.1` in one scope and printed as
`x.2` in a different scope.

`--verbose`

Makes Deduce print out the debug logs. It is generally recommended to
use `--traceback` instead, as this argument can make Deduce print out
thousands of lines.

`--error`

Deduce will expect all files that it processes to contain an error. If
there is a file that does not contain an error, Deduce will exit with
a return code of 255.