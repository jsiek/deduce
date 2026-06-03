# [Deduce](https://jsiek.github.io/deduce/)

![Blue Hippo next to the word Deduce.](/logos/Main-Logo.svg)

A proof checker and small functional language for teaching logic.

## Quick start

Deduce needs Python 3.12+ and the [Lark](https://github.com/lark-parser/lark)
parsing library. From a fresh clone:

```sh
python3 -m pip install lark
python3 deduce.py example.pf
```

(Use `python` if your system aliases that to Python 3; recent macOS and
some Linux distros ship only `python3`. On Windows the bundled launcher
is `py`.)

You should see:

```
example.pf is valid
```

For installation details, editor integrations, AI-assisted proof
completion, and the language introduction, see
[Getting Started](gh_pages/doc/GettingStarted.md) or the
[Deduce website](https://jsiek.github.io/deduce/).

More worked examples live in [`examples/`](examples).

## Repo layout

* `/compiler` Deduce-to-C compiler ([user guide](https://jsiek.github.io/deduce/pages/compiler.html))
* `/docs` Documentation for contributing to Deduce
* `/editor` Editor integrations (Emacs, VS Code)
* `/examples` Worked example proofs
* `/gh_pages` Source code for the [Deduce website](https://jsiek.github.io/deduce/)
* `/lib` Deduce library files. This includes Nat, List, etc.
* `/live_code_vercel_api` Source code for [Deduce live code](https://jsiek.github.io/deduce/sandbox.html)
* `/logos` The Hippopotamus logo and other images.
* `/test` Deduce files used for testing Deduce.
