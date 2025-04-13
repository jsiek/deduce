# Getting Started

Here are some resources to help you get started with Deduce.

* [Installing Deduce](#installation)
* [Running Programs](#running-deduce-programs)
* [Learning Deduce](#deduce-introduction)

## Installation

To get started with Deduce, follow these steps:

1. [Install Prerequisites](#install-prerequisites)
2. [Install Deduce](#install-deduce)
3. [Choose a Text Editor](#install-and-configure-a-text-editor)

### Install Prerequisites

You will need [Python](https://www.python.org/) version 3.10 or later. Here are some [instructions](https://wiki.python.org/moin/BeginnersGuide/Download) and links to download Python for many computer systems.

You will also need the [Lark](https://github.com/lark-parser/lark) parsing library, which you can install by running the following command in the same directory as `deduce.py`

```
python -m pip install lark
```

### Install Deduce

You can find the stable releases of Deduce on
[github](https://github.com/jsiek/deduce/releases). Download the zip
file and unpack it. To check that Deduce is working, go into the top
`deduce` directory, and run `python` on the `deduce.py` script and the
provided example file.  (There is no executable for Deduce.)

```
python ./deduce.py ./example.pf
```

You should see the following response from Deduce.

```
example.pf is valid
```

This response means that all the proofs in `example.pf` are complete and flawless!
Most of the time you will be working on incomplete or flawed proofs and
Deduce will try to give you helpful feedback. For example, if you replace
the proof in `example.pf` with a `?` as follows

```
theorem one_x: 1 = x
proof
  ?
end
```

and run Deduce again, you will see the following response.

```
example.pf:8.3-8.4: incomplete proof
Goal:
	1 = x
Advice:
	To prove this equality, one of these statements might help:
		definition
		rewrite
		equations
```

The latest development branch of Deduce (not stable) is available
[here](https://github.com/jsiek/deduce) on github. It includes the
source code for Deduce and for the Deduce web site.


### Install and Configure a Text Editor

You can write Deduce in any text editor you want, and run Deduce through
the terminal.

For the following editors, we have developed extensions that improve
the experience of writing Deduce code.

* VSCode ([deduce-mode](https://github.com/HalflingHelper/deduce-mode))
* Emacs ([deduce-mode](https://github.com/mateidragony/deduce-mode))


## Running Deduce Programs

As mentioned above, Deduce is run by providing the `deduce.py` script
with a `*.pf` file.

Suppose you have written thew following program in a file named `hello.pf`.

```{.deduce^#hello_starting_example}
// hello.pf
union Greeting {
  hello
}

define world : Greeting = hello

print world
```

This program defines a new union type called `Greeting`, defines a
variable `world`, and prints it out.

To run it, type the following command from within the `deduce`
directory, or use the run functionality provided by your deduce
editor.

```
python deduce.py hello.pf
```

You should see the output

```
hello
hello.pf is valid
```



## Deduce Introduction

This introduction to Deduce has two parts. The first part gives a tutorial on how to write programs in Deduce. The second part shows how to write proofs in Deduce.

* [Programming in Deduce](./FunctionalProgramming.md)
* [Writing Proofs in Deduce](./ProofIntro.md)

I recommend that you work through the examples in this introduction. Create a file named `examples.pf` in the top `deduce` directory and add the examples one at a time. To check the file, run the `deduce.py` script on the file from the `deduce` directory.

The Deduce Reference manual is linked below. It provides an alphabetical list of all the features in Deduce. The Cheat Sheet gives some advice regarding proof strategy and which Deduce keyword to use next in a proof. The Syntax Overview page provides a brief overview of the syntax structure of deduce.

* [Reference Manual](./Reference.md)
* [Cheat Sheet](./CheatSheet.md)
* [Syntax Overview](./SyntaxGrammar.md)

### Command Line Arguments

The `deduce.py` script supports command line arguments which are
documented below. If an argument is not preceded by one of the
keywords listed below, then it is treated as the name of a file or
directory and will be processed by Deduce.

`--dir directory-name`

Tells Deduce to include the given `directory-name` in the list of
directories to search when importing a file. For example, if `test.pf`
imports `Curry`, and `Curry.pf` resides in a folder named `howard`,
then `--dir howard` will allow `test.pf` to import `Church`. Note that
`--dir` expects a directory name, not an individual file.

The rest of the command line arguments are useful primarily for the
authors of Deduce. Users of Deduce can ignore them.

`--no-stdlib`

Deduce, by default, will include the directory of the standard library
(in `/lib` of the Deduce repository) in the list of directories to
search when importing a file. However if this argument is supplied, it
will not do so.

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

`--suppress-theorems`

When a file contains one or more proof declarations inside of it, Deduce will create a `.thm` file. However, this argument makes it such that Deduce never creates such files.

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

By default, `--verbose` only prints debug logs for the current file.
If ran as `--verbose full` it also prints debug logs for all imported
files as well.

`--error`

Deduce will expect all files that it processes to contain an error. If
there is a file that does not contain an error, Deduce will exit with
a return code of 255.

