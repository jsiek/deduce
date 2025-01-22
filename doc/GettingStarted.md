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

The Deduce Reference manual is linked below. It provides an alphabetical list of all the features in Deduce. The Cheat Sheet gives some advice regarding proof strategy and which Deduce keyword to use next in a proof. The Syntax Overview page provides a brief overview of the syntax structure of deduce.

* [Reference Manual](./Reference.md)
* [Cheat Sheet](./CheatSheet.md)
* [Syntax Overview](./SyntaxGrammar.md)
