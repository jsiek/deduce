# Contributing code

This section guides you through how to start contributing code to Deduce. Following these guidelines is required for your changes to be merged into Deduce.

## Table of contents
- [Get started](#get-started)
- [Contribution outline](#contribution-outline)
- [Contribution expectations](#contribution-expectations)
    - [Testing](#testing)
        - [How to use the Deduce test script](#how-to-use-the-deduce-test-script)
    - [Coding style, readability, and maintainability](#coding-style-readability-and-maintainability)
- [Pull requests](#pull-requests)

## Get started

To get started with contributing code to Deduce, please make sure to complete the following steps:

1. Read the documentation for Deduce found on the [Deduce site](https://jsiek.github.io/deduce/).
2. Review the contributing documentation in the Deduce [knowledge-base](./knowledge-base/). 
    - [`how-it-works.md`](./knowledge-base/how-it-works.md) contains internal Deduce documentation.
    - [`site-maintenance.md`](./knowledge-base/site-maintenance.md) contains Deduce site maintenance documentation.
3. Create a personal fork from `main` to make your contributions.

## Contribution outline

1. Create a branch from `main`, preferably with a descriptive name (e.g. `site/stdlib-generation`).
2. Make your changes.
3. Open a pull request to `main`.
4. Wait for the automated checks to pass and for a team member to review your PR.
5. Work on requested changes, or discuss the feedback with the reviewer.
6. Review [`what-to-update.md`](./knowledge-base/what-to-update.md) to check what internal (and potentially external) Deduce parts need to be updated to to your change. If any external Deduce tools need to be updated, please tag the developers of those tools in your PR.
7. Once approved, your PR will be merged to `main` by a Deduce team member.

## Contribution Expectations

What you must provide other than your source code to have a PR merged:

### Testing

Deduce tests are automatically ran whenever a PR is created, but it is recommended that you run tests locally before creating a PR. All core functionality must be tested and "pass" before being merged to `main`.

#### How to use the Deduce test script

All Deduce test programs are found within the `/test` directory and are ran by the `test-deduce.py` file. Test files are separated into two categories:

- `should-validate`: Deduce test programs which should run with no error.
- `should-error`: Deduce test programs which should error and output a specific error message. The test script checks that the error message is the same as the expected error message stored in a `*.err` file in the `/test/should-error` directory.

To generate a `.err` file for your new test program, you can run the `test-deduce.py` file  with the name of your file along with the `--generate-error` flag. For example:

```shell
python test-deduce.py --generate-error ./test/should-error/test-error.pf
```

Generates a `test-error.pf.err` file which contains the expected error message of running `test.error.pf`. You can also regenerate **ALL** `.err` files by passing the `regenerate-errors` flag.

Running `test-deduce.py` with no arguments will test all of the deduce `/lib/`, `/test/should-pass` and `/test/should-error` files. You can also specify which types of tests you want to run via command line arguments:
- `--lib`: tests `/lib`
- `--passable`: tests `/test/should-validate`
- `--errors`: tests `/test/should-error`
- `--site`: tests Deduce codeblocks found on the site


### Coding style, readability, and maintainability

General tips highly encouraged, but not strictly enforced.

- **Use proper function and variable names:** names should reflect what (not how) a function does something and what a variable holds. Avoid abbreviations and single-letter names.
- **Comments:** consider refactoring *before* adding comments (see above). But if it's still not clear why a code block exists, having a comment is better than nothing.
- **Use keywords arguments:** prefer `write_thing(thing=thing, file=file_name)` over `write_thing(file_name, thing)`. It's trivial to accidentally swap the order of arguments with a weakly typed language like Python.
- **Code type hints:** they (really) help with editor auto-completion and making public functions easier to use.
- **Doc-strings:** especially for public functions and classes.

## Pull requests

+ "Feature PR" model: a pull request should have all code related to deliver a single feature.
+ If a pull request has more features, consider breaking it into more PRs by splitting the code into more branches to facilitate reviews.