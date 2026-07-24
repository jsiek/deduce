#!/usr/bin/env python3
"""Deduce test harness.

Replaces the older subprocess-per-file harness with an in-process
multiprocessing runner. The parent pays the ~2.3s prelude bootstrap
once; workers fork from the populated ``uniquified_modules`` cache
via copy-on-write and run ``lsp.library.check_file`` directly.

Modes
-----
Default (no flags): runs ``--cli + --lib + --passable + --prelude +
--errors + --warns + --equiv``.

Per-category flags (combinable):
    --cli          One subprocess invocation of ``deduce.py`` on a tiny
                   no-stdlib proof to sanity-check the CLI entry point
                   itself.
    --lib          ``lib/`` with both parsers, no shared cache.
    --passable     ``test/should-validate`` + ``example.pf`` with both
                   parsers (uses the cheap ``prewarm`` bootstrap).
    --prelude      ``test/prelude`` with both parsers. Separate from
                   ``--passable`` because it needs the full ``prelude=``
                   bootstrap (checks the stdlib, ~100s cold on CI); keeping
                   it its own leg lets should-validate shards stay cheap.
    --errors       ``test/should-error`` (RD only, ``.err`` diff).
    --warns        ``test/should-warn`` (RD only, ``.warn`` diff): files
                   that must validate AND emit specific warning text.
    --equiv        Parse a grammar-coverage corpus with both parsers and
                   compare structural ASTs. The corpus is a curated stdlib /
                   accepted / warning selection plus every ``test/should-error``
                   fixture both parsers accept at parse time. Known historical
                   divergences and parse-time-rejected fixtures are allowlisted
                   so CI catches new drift. Also round-trip representative ASTs
                   through the pretty-printer and both parsers.

Standalone modes (mutually exclusive with the above):
    --site             Generate ``doc_*.pf`` from ``gh_pages/doc/``
                       and check them with both parsers.
    --parser           ``test/parse`` parser-error fixtures (RD only).
                       These stay RD-only because RD diagnostics are the
                       user-facing diagnostics; LALR is checked for accepted
                       syntax and AST shape by ``--equiv`` instead.
    --examples         ``examples/`` worked-example proofs (RD only).
                       LALR/RD parity is already covered by ``--equiv`` for a
                       representative grammar corpus; here we just need to
                       catch regressions in the examples themselves.
    --equiv-full       Pretty-print → reparse round-trip over EVERY
                       accepted-syntax ``.pf`` file (``lib/``,
                       ``test/should-validate``, ``example.pf``,
                       ``test/should-warn``, ``test/prelude``, ``examples/``,
                       ``test/test-imports``, ``test/compile``, the
                       ``tools/claude_fill_hole/examples`` hole fixtures, and
                       the ``test/should-error`` fixtures both parsers accept
                       at parse time) with both parsers. This is the opt-in
                       full-corpus audit
                       from issue #931 -- broader than the curated
                       ``PARSER_ROUND_TRIP_FILES`` set that ``--equiv`` runs in
                       CI, and intentionally NOT part of the default sweep so
                       CI stays fast.
    --regenerate-errors      Regenerate every ``test/should-error/*.err``.
    --generate-error <path>  Regenerate one ``.err`` fixture.
    --regenerate-warns       Regenerate every ``test/should-warn/*.warn``.
    --generate-warn <path>   Regenerate one ``.warn`` fixture.
    --gen-parse              Regenerate every ``test/parse/*.err``.

Pool sizing:
    --workers N         Worker count (default ``os.cpu_count()``).
    --max-threads N     Alias for ``--workers`` (legacy).
    --serial            Equivalent to ``--workers 1``.

Sharding:
    --shard i/n         Process only stride ``i`` of ``n`` of each selected
                        category's work list (``i`` is 1-based). Every item
                        lands in exactly one shard, so running all ``n`` shards
                        covers the whole corpus with no loss -- this is how CI
                        fans the long categories (should-validate, lib, equiv)
                        across parallel matrix legs. Corpus-wide invariant
                        checks in ``--equiv`` run only on shard 1.
"""

from __future__ import annotations

import contextlib
import io
import multiprocessing as mp
import os
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ProcessPoolExecutor
from dataclasses import fields as dc_fields, is_dataclass
from pathlib import Path
from signal import signal, SIGINT
from typing import Callable, Iterable, Optional, TypeVar, TypedDict, cast
from lark import Token

# Work around macOS sandbox profiles (notably Claude Code's seatbelt
# sandbox) that deny ``sysconf(_SC_SEM_NSEMS_MAX)``. Python's
# ``concurrent.futures.process._check_system_limits`` calls that
# sysconf to verify enough POSIX semaphores are available; it catches
# ``AttributeError``/``ValueError`` but lets ``PermissionError``
# propagate, which would crash the pool before any worker spawns.
# The check is purely advisory -- if the sysconf is denied we wrap it
# and treat the limit as undetermined (matching the existing -1 path).
import concurrent.futures.process as _ppmod

_orig_check_system_limits = _ppmod._check_system_limits


def _patched_check_system_limits() -> None:
    try:
        _orig_check_system_limits()
    except PermissionError:
        pass


_ppmod._check_system_limits = _patched_check_system_limits


REPO_ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(REPO_ROOT))

# ``lsp.library`` derives the location of ``Deduce.lark`` from
# ``os.path.dirname(sys.argv[0])``. When this script is invoked as
# ``python test-deduce.py`` from the repo root that's an empty string,
# which produces ``/Deduce.lark`` -- a non-existent absolute path.
# Spoof argv[0] to a real ``deduce.py`` path so the lookup works
# regardless of how the script was invoked.
sys.argv = [str(REPO_ROOT / "deduce.py")] + sys.argv[1:]

from abstract_syntax import add_import_directory, init_import_directories
from flags import (
    RECURSION_LIMIT,
    set_experimental_imperative,
    set_quiet_mode,
    set_recursive_descent,
)

sys.setrecursionlimit(RECURSION_LIMIT)
from lsp.library import check_file, reset_prelude_cache
import parser as _equiv_lark_parser
import rec_desc_parser as _equiv_rd_parser


# Keep these as relative paths -- ``deduce.py``'s error messages
# encode the filename as given to the checker, and the ``.err``
# fixtures were captured against relative-path invocations.
LIB_DIR = Path("lib")
PASS_DIR = Path("test/should-validate")
ERROR_DIR = Path("test/should-error")
WARN_DIR = Path("test/should-warn")
PRELUDE_DIR = Path("test/prelude")
IMPORTS_DIR = Path("test/test-imports")
PARSE_DIR = Path("test/parse")
EXAMPLES_DIR = Path("examples")
COMPILE_DIR = Path("test/compile")
HOLE_FILL_EXAMPLES_DIR = Path("tools/claude_fill_hole/examples")
EXAMPLE_FILE = Path("example.pf")

IMPERATIVE_SYNTAX_SOURCE = """\
module ImperativeSyntax

union List<T> {
  empty
  node(T, List<T>)
}

type MutableArrayFixture<T> = [T]!
type NestedMutableArrayFixture<T> = [List<T>]!

proc touch<T>(a: [T]!, xs: [List<T>]!, i: T, ghost p: T) -> [T]!
  reads a, a[i], p.f, footprint(p), {}
  modifies a[i]
{
}

proc give<T>(v: T) -> T
  ensures result_post: result = result
{
  return v
}

proc body_forms<T>(a: [T]!, i: T, n: T, ghost g: T) -> T
  requires n = n
  modifies a
{
  var x : T := n
  var y := a[i]
  ghost var z : T := g
  ghost var w := g
  x := n
  a[i] := a[n]
  a.header := x
  if x = x {
    x := y
  }
  if x = y {
    x := n
  } else {
    while x = x
      invariant x = x
      invariant y = y
      modifies a, a[i]
      established by loop_init
      preserved by loop_step[a, i]
      decreases n by loop_dec
    {
      x := y
      call touch(a, a, i, g)
    }
  }
  assert x = x by loop_exit
  assert y = y by .
  assume y = y
  call touch(a, a, i, g)
  call touch(a, a, i, g) as h
  call touch(a, a, i, g) by touch_pre
  call touch(a, a, i, g) as h2 by h.valid_post
  var r := call give(n) as hr
  x := call give(g)
  assert x = x by hr.result_post
  return x
}
proof
  loop_init {
    .
  }
  loop_step {
    arbitrary p:T
    .
  }
  loop_dec {
    .
  }
  loop_exit {
    .
  }
  touch_pre {
    .
  }
end
"""

EXPERIMENTAL_IMPERATIVE_FILES = frozenset({
    "./test/should-validate/proc_declarations.pf",
    "./test/should-validate/observer_declarations.pf",
    "./test/should-validate/imperative_import.pf",
    "./test/should-error/resource_declarations.pf",
    "./test/should-error/imperative_import_unknown.pf",
    "./test/should-error/imperative_import_field.pf",
    "./test/should-error/imperative_export_private_contract.pf",
    "./test/test-imports/ImpExports.pf",
})


def _uses_experimental_imperative(path: str) -> bool:
    return path in EXPERIMENTAL_IMPERATIVE_FILES


# Current parser-equivalence baseline. These files parse successfully with
# both parsers but produce structurally different ASTs today. Keeping the
# baseline explicit makes any new drift fail CI, and also fails when a listed
# file becomes equivalent so the list gets smaller over time.
PARSER_EQUIV_EXPECTED_DIVERGENCES: frozenset[str] = frozenset()


# Most ``test/should-error`` files fail in later phases (type-check,
# proof-check) and parse cleanly under both parsers; comparing their ASTs
# gives us 180+ extra surface-syntax samples for drift detection. The files
# below are excluded because at least one parser rejects them at parse time
# today -- either as an intentional parser-error fixture or because the two
# parsers diverge on a tolerated form (e.g. RD currently accepts ``conclude
# ... by`` with a hole where LALR does not). If a listed file ever starts to
# parse cleanly with both parsers, the staleness check downgrades it to a
# failure so the baseline shrinks over time.
SHOULD_ERROR_PARSER_EQUIV_SKIP = frozenset({
    "./test/should-error/all5.pf",
    "./test/should-error/apply_to_error.pf",
    "./test/should-error/call_trailing_comma.pf",
    "./test/should-error/cases_error.pf",
    "./test/should-error/conjunct.pf",
    "./test/should-error/constructor_type_trailing_comma.pf",
    "./test/should-error/deep_error.pf",
    "./test/should-error/define_missing_semi.pf",
    "./test/should-error/define_proof_missing_term.pf",
    "./test/should-error/define_type.pf",
    "./test/should-error/define_with_type_params.pf",
    "./test/should-error/double_private.pf",
    "./test/should-error/fn_missing_arrow.pf",
    "./test/should-error/fun_params_trailing_comma.pf",
    "./test/should-error/function_case_missing_equal.pf",
    "./test/should-error/lambda_empty_params.pf",
    "./test/should-error/literal_too_large.pf",
    "./test/should-error/missing-colon-in-have.pf",
    "./test/should-error/paren_term.pf",
    "./test/should-error/quantifier_binding_trailing_comma.pf",
    "./test/should-error/private_opaque.pf",
    "./test/should-error/suffices_misspell.pf",
    "./test/should-error/switch_case_close.pf",
    "./test/should-error/switch_case_empty.pf",
    "./test/should-error/switch_case_open.pf",
    "./test/should-error/switch_case_pattern.pf",
    "./test/should-error/theorem_implies8.pf",
    "./test/should-error/theorem_misspelled.pf",
    "./test/should-error/type_params_trailing_comma.pf",
    "./test/should-error/unclosed_comment.pf",
    "./test/should-error/union_bad_constructor.pf",
    "./test/should-error/union_missing_name.pf",
})


# Pretty-printer/parser round-trip coverage for accepted syntax. This is also
# the backbone of the parser-equivalence CI corpus below; keep it curated by
# grammar construct instead of letting runtime grow with every checked-in proof.
PARSER_ROUND_TRIP_FILES = (
    "./test/should-validate/theorem_true.pf",
    "./test/should-validate/function1.pf",
    "./test/should-validate/generic-fun.pf",
    "./test/should-validate/bintree.pf",
    "./test/should-validate/uint_viewrec.pf",
    "./lib/Option.pf",
    # Broaden coverage to additional small files that already
    # round-trip cleanly under today's pretty-printer. Each one
    # exercises a distinct surface construct so a regression in
    # any of these forms is caught here too.
    "./test/should-validate/empty_file.pf",        # empty input
    "./test/should-validate/bicond1.pf",           # biconditional <=>
    "./test/should-validate/conditional1.pf",      # if-then-else term
    "./test/should-validate/array1.pf",            # array literal + indexing
    "./test/should-validate/some1.pf",             # existential + `choose`
    "./test/should-validate/inst1.pf",             # all-elim by application
    "./test/should-validate/switch_term.pf",       # switch in a term position
    "./test/should-validate/predicate_basic.pf",   # `predicate` declaration
    "./test/should-validate/relation_basic.pf",    # `relation` declaration
    "./test/should-validate/opaque_define.pf",     # `opaque` visibility
    "./test/should-validate/import_using.pf",      # `import ... using ...`
    "./test/should-validate/public_import_roundtrip.pf",  # `public import` prefix
    "./test/should-validate/auto_conditional.pf",  # `auto` + `postulate` decl
    "./test/should-validate/recall1.pf",           # `recall` proof
    "./test/should-validate/simplify1.pf",         # `simplify` proof
    "./test/should-validate/trace_recursive.pf",   # `trace` decl + `print`
    "./test/should-validate/union_positive_nested.pf",  # nested generic union
    "./test/should-validate/mark2.pf",             # `#`-mark term + `expand a | b`
    "./test/should-validate/nat_literals.pf",      # `ℕn` Nat literals + `lit`
    "./test/should-validate/fun_zero_param.pf",    # zero-parameter `fun`
    "./test/should-validate/some-intro-tlet.pf",   # `define ... ; ...` term-let
    "./test/should-validate/int1.pf",              # Int negation / literals
    "./test/should-validate/theorem_let.pf",       # inline `apply ... to ...`
    # Coverage added with the issue #931 round of pretty-printer fixes.
    # Each one exercises a fix landed in that pass:
    "./test/should-validate/all1.pf",              # `arbitrary x:T` (no `;`)
    "./test/should-validate/all2.pf",              # multi-`arbitrary` list
    "./test/should-validate/all3.pf",              # arbitrary + apply chain
    "./test/should-validate/bicond3.pf",           # `switch ... case … assume`
    "./test/should-validate/bicond4.pf",           # nested case-assume
    "./test/should-validate/not_equal.pf",         # `x /= y` surface form
    "./test/should-validate/private_define.pf",    # `private define : T = …`
    "./test/should-validate/private_function.pf",  # `private fun …`
    "./test/should-validate/private_union.pf",     # `private union` + `/=`
    "./test/should-validate/simplify3.pf",         # `simplify with q.`
    "./test/should-validate/simplify4.pf",         # `simplify with` + body
    "./test/should-validate/TestUIntDiv.pf",       # numeric literal sugar
    "./test/should-validate/rewrite_with_all.pf",  # `replace x.` finishing form
    "./test/should-validate/type_alias.pf",        # `type Foo = Bar` round-trip
    "./test/should-validate/predicate_opaque.pf",  # `opaque predicate`
    # Coverage added with the follow-up pretty-printer round (#931 again):
    # `suffices ... by { ... }` block, `cases <subject> case ... { ... }`,
    # and `induction T case <pat> { ... }` (no induction-hypothesis clause).
    "./test/should-validate/suffices1.pf",         # `suffices ... by ...`
    "./test/should-validate/suffices_def.pf",      # `suffices` with `define`
    "./test/should-validate/suffices_omitted.pf",  # `suffices ... by` then proof
    "./test/should-validate/suffices_rewrite.pf",  # `suffices ... by replace ...`
    "./test/should-validate/cases-tlet.pf",        # `cases prem` with `case <l>: <t>`
    "./test/should-validate/induction-tlet.pf",    # `induction T case A { . }`
    "./test/should-validate/induction_auto_assume.pf",  # induction + suffices body
    "./test/should-validate/private_roundtrip.pf", # `private type` + `private fun`
    # `private theorem` / `private lemma` / `private postulate` visibility
    # round-trip (Theorem.__str__ / Postulate.__str__ visibility prefix).
    "./test/should-validate/private_theorem.pf",
    # `recfun ... measure n of T { body } terminates { proof }` — both
    # the `of <measure_ty>` clause and the `terminates` proof block were
    # silently dropped by `GenRecFun.pretty_print`; covers both shapes.
    "./test/should-validate/recfun_roundtrip.pf",
    # Coverage added with the issue #945 fix for `mkEqual` emitting
    # `Var('=')` from the parser (so `equations`-block `=` matches the
    # ordinary infix-`=` parsing shape):
    "./test/should-validate/assoc1.pf",            # `equations` + `replace`
    "./test/should-validate/assoc2.pf",            # `equations` chain
    "./test/should-validate/induction1.pf",        # `equations` under induction
    "./test/should-validate/postulate1.pf",        # `equations` + `postulate`
    "./test/should-validate/mark3.pf",             # `equations` + `#`-marks
    "./test/should-validate/ListTests.pf",         # operator-call rator: `(f ∘ g)(x)`
    "./test/should-validate/function_type_paren.pf",  # multi-arg `fn` types
    "./test/should-validate/relation_operator_name.pf",  # `relation operator <op>`
    "./test/should-validate/object_syntax.pf",    # object decls + fields
    # `Omitted.__str__` previously returned `--`, which neither parser
    # accepts; the surface form is `__` (or `─`). Covers `suffices __ by …`.
    "./test/should-validate/suffices_implies_omitted.pf",
    # RD parser now chains `(...)` and `[...]` postfix in any order
    # (matching LALR), so `array(l)[0]` and `f(a)[0]` re-parse the
    # same way the pretty-printer emits them.
    "./test/should-validate/array4.pf",            # `array(...)` + `[i]`
    "./test/should-validate/array5.pf",            # nested `(array(...))[i]`
    "./test/should-validate/postfix_chain_roundtrip.pf",  # synthetic chain
    # `opaque define name : T = body` — `Define.pretty_print` used to
    # short-circuit to header-only when `visibility == 'opaque'`, dropping
    # the `= body`. Covers both an annotated `opaque define : T = fun ...`
    # and the visibility coexisting with the broader Define pretty-print.
    "./test/should-validate/ImportTests.pf",
    # `op_arg_str` now parenthesizes `TAnnote` args of operator Calls --
    # `:` binds looser than every operator, so the printed
    # `subject:type ^ ...` previously reparsed as `subject : (type ^ ...)`
    # and the leftover operator tripped the next statement.
    "./test/should-validate/int_pow.pf",
    # LALR's `all_elim_types` transformer was passing the Lark `Tree`
    # instead of the loop index `i` as the first slot of `AllElimTypes.pos`,
    # so the canonical AST drifted (and `__str__` would `TypeError` on a
    # `Tree + 1` comparison). Each of these files exercises `proof<T>` /
    # `proof<T1, T2>` in some surface context.
    "./test/should-validate/inst3.pf",                # `prem<UInt>[...]`
    "./test/should-validate/bicond2.pf",              # `empty_iff_0<E>` inside `apply`
    "./test/should-validate/expand-repeat.pf",        # `reverse_append<U>` chain
    "./test/should-validate/all-elim-types-tlet.pf",  # `bleh<T>` term-let
    "./test/should-validate/map_append_cross_type.pf",  # multi-arg `proof<UInt, bool>`
    # TLet's `define ...; ...` binds looser than operators/connectives, so
    # term-let operands must be parenthesized when pretty-printed in those
    # contexts.
    "./test/should-validate/contradict-tlet.pf",      # term-let under `and`
    "./test/should-validate/define_cases.pf",         # term-let under `and`/`or`
    "./test/should-validate/extensionality-tlet.pf",  # term-let equality args
    # Remaining issue #931 AST-drift fixes:
    "./test/should-validate/custom_induction.pf",     # `with xs. term` pattern
    "./test/should-validate/theorem_false2.pf",       # `replace p | q in ...`
    # `Associative.__str__` must preserve the grammar's `in` keyword and
    # operator identifier spelling.
    "./test/should-validate/associative_roundtrip.pf",
    # Proof arguments with statement bodies must not be flattened by
    # ModusPonens pretty-printing (`arbitrary ... assume ...` needs
    # separators/braces when used after `apply ... to`).
    "./test/should-validate/apply_to_intro_roundtrip.pf",
    # `PRecall`'s textual tail (`recall <fact1>, <fact2>, ...`) is
    # greedy at the term parser level. When it appears as an element
    # of a `|`-separated proof list (`simplify with`, `replace`), a
    # `,`-separated proof tuple (`apply ... to A, B`), or just before
    # an `in` keyword (`replace ... in ...`), it must be parenthesized
    # so the outer separator/keyword isn't consumed by the inner
    # `parse_nonempty_term_list` / `parse_term`. Also covers proofs
    # that delegate to a trailing `PRecall` (`symmetric recall ...`).
    # Adds the four `lib/` files that round-tripped after the fix:
    "./lib/IntAddSub.pf",
    "./lib/Maps.pf",
    "./lib/NatLess.pf",
    "./lib/UIntLess.pf",
    "./test/should-validate/recall_list_roundtrip.pf",
    # `Cases.__str__` was missing (the dataclass repr leaked through any
    # `__str__`-cascading body chain — `simplify ... \n` + `str(body)`,
    # `expand ... ` + `str(body)`, `replace ... \n` + `str(body)`).
    # `SimplifyGoal` was also missing `pretty_print`, so the cascade kicked
    # in even for a top-level `simplify` whose body needed indentation.
    "./lib/IntMult.pf",
    "./test/should-validate/cases_in_simplify_roundtrip.pf",
    # `not X` (`IfThen(_, _, _, Bool false)`) had no entry in
    # `precedence`, so an outer infix operator like `=` would print
    # `(not (P and Q)) = (not P or not Q)` as `not (P and Q) = ...`,
    # which reparses with `=` inside `not` (since the parser's `NOT`
    # branch consumes `parse_term_equal`). Covers De Morgan's laws
    # which were the original lib/Base.pf drift.
    "./test/should-validate/not_paren_roundtrip.pf",
    # lib/Base.pf round-trips cleanly once the `not X` precedence
    # case is added (`not_and`, `not_or`, `double_neg` were the three
    # drift sites).
    "./lib/Base.pf",
    # `Call.__str__` used to re-sugar `Call(char_fun, [Lambda(_, false)])`
    # back to `∅` (`isEmptySet` matched the expanded `empty_set` body),
    # but both parsers desugar `∅` to `Call(Var('empty_set'), [])`. So the
    # `char_fun(λx{false})` shape drifted whenever it appeared as the body
    # of `empty_set` itself or in `@char_fun<T>(λ_{false})` witnesses.
    # Refs #988 category (c).
    "./test/should-validate/empty_set_roundtrip.pf",
    # `_proof_list_item_str` used to parenthesize only the ``PRecall``
    # trailing-term-list shape and its ``symmetric`` / ``transitive`` /
    # ``help`` recursion. But every proof whose parse rule ends with a
    # ``parse_proof()`` call is comma-greedy at the tail: ``apply I to
    # A``, ``conjunct N of P``, ``expand D in P``, ``replace E in P``,
    # ``simplify with G in P``, ``evaluate in P``, ``conclude C by P``.
    # ``PTuple([ModusPonens, ModusPonens])`` therefore drifted to one
    # ``ModusPonens`` whose arg is a ``PTuple``, and same for
    # ``PAndElim`` etc.  Symmetrically, ``AllElim`` / ``AllElimTypes``
    # printed their ``univ`` unparenthesized so the postfix ``[...]`` /
    # ``<...>`` nested inside a trailing sub-proof instead of wrapping
    # the ``univ``. Refs #988 categories (b) and (d).
    "./test/should-validate/apply_tuple_postfix_roundtrip.pf",
    # lib/ modules now round-trip once (b), (c), (d) are all fixed.
    # ``Set.pf`` exercises the ``∅`` and ``(conjunct N of P)[x]`` shapes;
    # ``UIntAdd.pf`` exercises the ``apply f to a, apply g to b`` tuple.
    "./lib/Set.pf",
    "./lib/UIntAdd.pf",
    # Imperative procedure declarations (recognized in Phase 1i, #968; bodies
    # not verified). Both parsers must agree on the AST and the pretty-printer
    # must preserve the header and repeated specification clauses.
    "./test/should-validate/proc_declarations.pf",
    # Imperative observer declarations. Both parsers must agree on the AST and
    # the pretty-printer must preserve repeated `reads` clauses and the optional
    # body.
    "./test/should-validate/observer_declarations.pf",
    # Separation-resource declarations (#854 Phase 1h). The declarations are
    # recognized (Phase 1i) but the file stays in should-error because resource
    # formulas have no term semantics; both parsers must agree on the AST and
    # the pretty-printer must round-trip the `emp`, `**`, and `|->` connectives
    # and the `p.f` field-access address form.
    "./test/should-error/resource_declarations.pf",
    # `import M using ... | operator≲` stored the operator name bare (`≲`),
    # but a using/hiding list only accepts an operator behind the `operator`
    # keyword, so `Import._filter_clause_str` must print `operator ≲`.
    "./test/prelude/import_using_prelude.pf",
    # A user constructor named `empty` (here `Tree.empty(bool)`) shares the
    # base name of `List`'s nil, so the `empty` -> `[]` display sugar fired
    # even in applied positions: `empty(b)` printed `[](b)`, which does not
    # reparse. Covers the pattern (`size(empty(b)) = ...`) and term
    # (`flip(empty(b)) = empty(b)`) occurrences.
    "./test/should-error/induction2.pf",
    # A bodyless `object` with no type parameters, as the final statement of
    # the file, hit EOF inside `parse_type_parameters`, which called
    # `current_token()` with no end-of-file guard. RD raised "Expected a
    # token, got end of file" while LALR accepted it, so the pretty-printed
    # `object Empty` at EOF did not reparse under RD. Fixed by guarding the
    # `LESSTHAN` lookahead with `not end_of_file()`.
    "./test/should-validate/object_bodyless_eof.pf",
    # A bare `if ... then ...` implication (no `else`) as the final term of the
    # file hit the same EOF hazard: the `IF` branch checked for an optional
    # `else` with `current_token()`, which raised "Expected a token, got end of
    # file" under RD while LALR accepted the `"if" term "then" term` form.
    # Fixed by guarding the `else` lookahead with `not end_of_file()`.
    # Refs #1073, #473.
    "./test/should-validate/if_then_no_else_eof.pf",
    # The experimental-imperative keyword vocabulary (`call`, `return`,
    # `while`, `emp`, `reads`, ...) is only reserved with
    # `--experimental-imperative` on. RD tokenizes with lark's
    # non-contextual lexer, so it used to reserve those words globally and
    # reject them as ordinary identifiers, diverging from the LALR parser
    # (which accepts them as identifiers when the flag is off). RD now
    # demotes them to `IDENT` in that mode. Refs #473.
    "./test/should-validate/experimental_imperative_keywords_as_identifiers.pf",
    # RD used to make `not` bind looser than `=` (its `NOT` branch consumed
    # `parse_term_equal`), parse `=`/comparison operators right-associatively,
    # and recurse rightward on `and`/`or` (making `or` bind tighter than
    # `and`) while handling the `:` annotation only after that loop, all
    # diverging from the LALR grammar and Reference.md, which put `and`/`or`/`:`
    # at one left-associative level. `not P = false`, `a = b = c`,
    # `a and b or c`, and `P or Q : bool and false` now group as
    # `(not P) = false` / `(a = b) = c` / `(a and b) or c` /
    # `((P or Q):bool) and false` under both.
    "./test/should-validate/operator_precedence_rd_lalr.pf",
    # An empty (uninhabited) `union { }` body. RD documents the body as
    # `constructor*` and accepted zero constructors, but the LALR
    # `constructor_list` rule required at least one, so the pretty-printed
    # empty union did not reparse under LALR. Fixed by admitting the empty
    # production in `constructor_list`. Refs #473.
    "./test/should-validate/empty_union.pf",
    # Chained proof instantiation `h[x]<Nat>` (term then type). RD used to
    # consume all `<...>` type instantiations before any `[...]` term
    # instantiations in two separate loops, so a `<...>` following a `[...]`
    # was rejected -- diverging from the interleaving LALR `atomic_proof`
    # rules. A single dispatching loop now accepts both orders. Refs #473.
    "./test/should-validate/proof_instantiation_order_rd_lalr.pf",
    # RD handled the `:` type annotation only as a trailing step after the
    # `and`/`or` chain (and redundantly above `iff`), so a stacked annotation
    # such as `P : bool : bool` was split, with the second colon leaking up a
    # precedence level. `:` now folds into the same left-associative
    # `logical_term` loop as `and`/`or`, matching LALR. Refs #473.
    "./test/should-validate/annotation_precedence_rd_lalr.pf",
    # `operator ≠` (and its ASCII synonym `operator /=`) produce a bare
    # `Var('≠')`, but `≠` has no infix/prefix precedence entry (it is sugar
    # for `not (x = y)`), so `is_operator_name` reported False and the term
    # pretty-printed to a bare `≠` that no longer reparses. `≠` is now
    # recognized as an operator name, so the `operator` prefix is preserved.
    # Refs #931, #473.
    "./test/should-error/operator_not_equal_synonym.pf",
    # `rule induction <pred>` / `rule inversion <pred>` proofs (`RuleInduction`,
    # `RuleInductionCase`, `RuleInversion` AST nodes). No prior round-trip fixture
    # exercised these tactics, so a pretty-printer regression on the `rule
    # induction`/`rule inversion` header or its `case <rule> { ... }` list would
    # have passed CI silently. Refs #931, #473.
    "./test/should-validate/predicate_rule_induction_sugar.pf",
    "./test/should-validate/predicate_rule_inversion.pf",
    # A `view` declaration (`ViewDecl` node) with its `source`/`target`/`into`/
    # `out`/`roundtrip`/`inverse` clauses, plus a `recursive f(<view>) -> ...`
    # function keyed on the view. No prior round-trip fixture covered `view`, so
    # the pretty-printer's reproduction of the clause block was unverified.
    # Refs #931, #473.
    "./test/should-validate/view_inverse_decl.pf",
    # A bare `export <name>` re-export statement (`Export` node). Only stdlib
    # modules exercised it before, none of them in the round-trip corpus, so the
    # pretty-printer's `export IDENT` form was unverified. Refs #931, #473.
    "./test/should-validate/export_decl.pf",
)


PARSER_EQUIV_FILES = PARSER_ROUND_TRIP_FILES + (
    # Small representative stdlib modules. Avoid large semantic proof corpora
    # such as BigO; parser equivalence only needs surface-syntax coverage.
    "./lib/List.pf",
    "./lib/Nat.pf",
    "./lib/UInt.pf",
    "./lib/Int.pf",
    # Warning fixtures add syntax that is not always present in validating
    # examples. The ``test/should-error`` corpus is folded in wholesale by
    # ``should_error_equiv_files`` below (everything both parsers accept at
    # parse time), so individual should-error paths are not listed here.
    "./test/should-warn/replace_auto_handled_922.pf",
)


def should_error_equiv_files() -> tuple[str, ...]:
    """``test/should-error`` fixtures both parsers accept at parse time.

    Most should-error files fail in a *later* phase (type-check/proof-check)
    while parsing cleanly under both parsers, so their surface syntax is a
    legitimate RD-vs-LALR drift sample -- and exercises constructs the
    validating corpus may not. Everything except the
    ``SHOULD_ERROR_PARSER_EQUIV_SKIP`` baseline (fixtures at least one parser
    rejects at parse time) participates; that baseline shrinks over time via
    ``_check_should_error_skip_set``.
    """
    return tuple(p for p in list_pf(ERROR_DIR)
                 if p not in SHOULD_ERROR_PARSER_EQUIV_SKIP)


class ParsedFlags(TypedDict):
    cli: bool
    lib: bool
    passable: bool
    prelude: bool
    errors: bool
    warns: bool
    equiv: bool
    equiv_full: bool
    site: bool
    parser: bool
    examples: bool
    regen_all: bool
    regen_files: list[str]
    regen_all_warns: bool
    regen_warn_files: list[str]
    gen_parse: bool
    workers: int
    shard: Optional[tuple[int, int]]


T = TypeVar("T")
R = TypeVar("R")
S = TypeVar("S")


# Module-level globals consumed by worker functions. The parent
# populates these before forking the pool; workers inherit them via
# copy-on-write. Avoids pickling a 32-entry tuple per task.
_WORKER_PREWARM: tuple[str, ...] = ()
_WORKER_PRELUDE: tuple[str, ...] = ()

# When set by ``--shard i/n`` the run functions process only their stride of
# the work list, so CI can fan a long category (e.g. should-validate) across n
# parallel matrix legs without any coverage loss -- every item lands in exactly
# one shard. ``None`` means "run everything" (the default / local behaviour).
_SHARD: tuple[int, int] | None = None


def shard(items: list[T]) -> list[T]:
    """Return this shard's slice of ``items`` (round-robin by stride).

    Striding rather than contiguous chunks keeps the shards balanced even
    when per-item cost is uneven across the (sorted) list."""
    if _SHARD is None:
        return items
    idx, count = _SHARD
    return items[idx::count]


def handle_sigint(signum: int, frame: object) -> None:
    print('SIGINT caught, exiting...')
    sys.exit(137)


def discover_lib_modules() -> tuple[str, ...]:
    return tuple(sorted(p.stem for p in LIB_DIR.glob("*.pf")))


def setup_paths() -> None:
    # Run from the repo root so the relative paths above resolve and so
    # error messages match the existing ``.err`` fixtures. The import
    # directories must be ``./``-prefixed because the legacy harness
    # invoked ``deduce.py --dir ./lib --dir ./test/test-imports`` and
    # that prefix ends up in some error messages (the "declared as
    # `lemma` in module X (<file>:<line>)" hint, in particular).
    os.chdir(REPO_ROOT)
    init_import_directories()
    add_import_directory("./" + LIB_DIR.as_posix())
    add_import_directory("./" + IMPORTS_DIR.as_posix())


def list_pf(d: Path) -> list[str]:
    # Return ``./test/<...>/foo.pf``-style paths to match how the
    # ``.err`` fixtures were captured.
    return sorted(
        f"./{d.as_posix()}/{p.name}" for p in d.iterdir() if p.suffix == ".pf"
    )


# ---------------------------------------------------------------------------
# Worker functions (must be picklable for multiprocessing).
# ---------------------------------------------------------------------------


def _worker_validate(task: tuple[str, bool]) -> tuple[str, bool, str, str]:
    f, recursive_descent = task
    set_recursive_descent(recursive_descent)
    label = "recursive-descent" if recursive_descent else "lalr"
    set_experimental_imperative(_uses_experimental_imperative(f))
    try:
        result = check_file(f, prewarm_modules=_WORKER_PREWARM)
    finally:
        set_experimental_imperative(False)
    return (f, result.ok, label, result.error_message or "")


def _worker_lib(task: tuple[str, bool]) -> tuple[str, bool, str, str]:
    """Each lib file is checked with no prewarm so the file (and its
    transitive imports of other lib modules) is freshly parsed --
    otherwise we'd just typecheck a cached AST that was parsed once by
    the parent and never exercise the LALR parser on lib code.
    """
    f, recursive_descent = task
    set_recursive_descent(recursive_descent)
    label = "recursive-descent" if recursive_descent else "lalr"
    result = check_file(f)
    return (f, result.ok, label, result.error_message or "")


def _worker_prelude(task: tuple[str, bool]) -> tuple[str, bool, str, str]:
    """``test/prelude`` worker. Uses ``prelude=`` (injected imports),
    not ``prewarm=``."""
    f, recursive_descent = task
    set_recursive_descent(recursive_descent)
    label = "recursive-descent" if recursive_descent else "lalr"
    result = check_file(f, prelude=_WORKER_PRELUDE)
    return (f, result.ok, label, result.error_message or "")


def _check_against_err(f: str) -> tuple[str, bool, str]:
    """Run ``f`` and diff its captured stdout against ``f + '.err'``.

    Shared between ``--errors`` (``test/should-error``) and
    ``--parser`` (``test/parse``); both use the same fixture format.
    Reproduces the CLI's full stdout (warnings + ``error_message``)
    and runs ``diff --ignore-space-change`` to match the historical
    matching semantics exactly.
    """
    err_file = f + ".err"
    if not os.path.isfile(err_file):
        return (f, False, "missing .pf.err fixture")
    set_recursive_descent(True)
    set_experimental_imperative(_uses_experimental_imperative(f))
    set_quiet_mode(True)
    buf = io.StringIO()
    try:
        with contextlib.redirect_stdout(buf):
            result = check_file(f, prewarm_modules=_WORKER_PREWARM)
            if not result.ok:
                print(result.error_message)
    finally:
        set_experimental_imperative(False)
    if result.ok:
        return (f, False, "expected error but file was valid")
    actual = buf.getvalue()
    with tempfile.NamedTemporaryFile(
        "w", suffix=".tmp", delete=False, encoding="utf-8"
    ) as tf:
        tf.write(actual)
        tmp_path = tf.name
    try:
        cp = subprocess.run(
            ["diff", "--ignore-space-change", err_file, tmp_path],
            capture_output=True, text=True,
        )
        if cp.returncode != 0:
            return (f, False, f"error message diverged:\n{cp.stdout[:500]}")
        return (f, True, "")
    finally:
        os.unlink(tmp_path)


def _check_against_warn(f: str) -> tuple[str, bool, str]:
    """Run ``f`` and diff its captured stdout against ``f + '.warn'``.

    Counterpart to ``_check_against_err`` for ``test/should-warn``:
    the file must validate (``result.ok``) AND the warnings printed
    via ``error.warning`` must match the ``.warn`` fixture line-for-
    line (modulo whitespace, like ``--errors``).
    """
    warn_file = f + ".warn"
    if not os.path.isfile(warn_file):
        return (f, False, "missing .pf.warn fixture")
    set_recursive_descent(True)
    set_quiet_mode(True)
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        result = check_file(f, prewarm_modules=_WORKER_PREWARM)
    if not result.ok:
        return (f, False, f"expected valid + warnings but file errored:\n"
                          f"{(result.error_message or '')[:500]}")
    actual = buf.getvalue()
    with tempfile.NamedTemporaryFile(
        "w", suffix=".tmp", delete=False, encoding="utf-8"
    ) as tf:
        tf.write(actual)
        tmp_path = tf.name
    try:
        cp = subprocess.run(
            ["diff", "--ignore-space-change", warn_file, tmp_path],
            capture_output=True, text=True,
        )
        if cp.returncode != 0:
            return (f, False, f"warning output diverged:\n{cp.stdout[:500]}")
        return (f, True, "")
    finally:
        os.unlink(tmp_path)


# ---------------------------------------------------------------------------
# Orchestration.
# ---------------------------------------------------------------------------


def _make_fork_pool(workers: int) -> ProcessPoolExecutor:
    """Fork-based ``ProcessPoolExecutor``: children inherit the
    parent's populated AST cache via copy-on-write. macOS Python
    defaults to ``spawn``; we override.
    """
    fork_ctx = mp.get_context("fork")
    return ProcessPoolExecutor(max_workers=workers, mp_context=fork_ctx)


def bootstrap_prewarm(lib_modules: tuple[str, ...]) -> None:
    """Pay the prelude bootstrap once in the parent (prewarm flavour)."""
    global _WORKER_PREWARM
    _WORKER_PREWARM = lib_modules
    set_recursive_descent(True)
    # ``content=""`` runs the pipeline on an empty buffer -- cheapest
    # valid trigger for ``_prepare_state``'s bootstrap path.
    check_file("__warmup__.pf", content="", prewarm_modules=lib_modules)


def bootstrap_prelude(lib_modules: tuple[str, ...]) -> None:
    """Bootstrap with ``prelude=`` (implicit imports) for prelude tests."""
    global _WORKER_PRELUDE
    _WORKER_PRELUDE = lib_modules
    set_recursive_descent(True)
    check_file("__warmup__.pf", content="", prelude=lib_modules)


def _map_or_serial(
    workers: int,
    fn: Callable[[T], R],
    tasks: Iterable[T],
    chunksize: int = 4,
) -> list[R]:
    """Run ``fn(task)`` over ``tasks`` in a pool, or in-line when
    ``workers <= 1`` (handy for debugging and the ``--serial`` flag)."""
    if workers <= 1:
        return [fn(t) for t in tasks]
    with _make_fork_pool(workers) as ex:
        return list(ex.map(fn, tasks, chunksize=chunksize))


def _parser_workers(workers: int, task_count: int) -> int:
    return min(workers, task_count, 8)


def run_lib_parallel(workers: int) -> list[tuple[str, str, str]]:
    """``lib/*.pf`` × both parsers with no shared cache."""
    files = list_pf(LIB_DIR)
    tasks = shard([(f, p) for f in files for p in (True, False)])
    failures: list[tuple[str, str, str]] = []
    for f, ok, label, msg in _map_or_serial(workers, _worker_lib, tasks, 2):
        if not ok:
            failures.append((f, label, msg))
    return failures


def run_validate_parallel(workers: int) -> list[tuple[str, str, str]]:
    """``test/should-validate`` + ``example.pf`` × both parsers."""
    files = list_pf(PASS_DIR) + [f"./{EXAMPLE_FILE.as_posix()}"]
    tasks = shard([(f, p) for f in files for p in (True, False)])
    failures: list[tuple[str, str, str]] = []
    for f, ok, label, msg in _map_or_serial(workers, _worker_validate, tasks, 4):
        if not ok:
            failures.append((f, label, msg))
    return failures


def run_prelude_parallel(workers: int) -> list[tuple[str, str, str]]:
    """``test/prelude`` × both parsers (uses ``prelude=`` bootstrap)."""
    files = list_pf(PRELUDE_DIR)
    tasks = shard([(f, p) for f in files for p in (True, False)])
    failures: list[tuple[str, str, str]] = []
    for f, ok, label, msg in _map_or_serial(workers, _worker_prelude, tasks, 2):
        if not ok:
            failures.append((f, label, msg))
    return failures


def run_err_diff_parallel(directory: Path, label: str,
                          workers: int) -> list[tuple[str, str, str]]:
    """Run ``.err``-fixture tests in ``directory`` (RD only)."""
    files = shard(list_pf(directory))
    failures: list[tuple[str, str, str]] = []
    for f, ok, msg in _map_or_serial(workers, _check_against_err, files, 4):
        if not ok:
            failures.append((f, label, msg))
    return failures


def run_warn_diff_parallel(workers: int) -> list[tuple[str, str, str]]:
    """Run ``.warn``-fixture tests in ``test/should-warn`` (RD only)."""
    files = shard(list_pf(WARN_DIR))
    failures: list[tuple[str, str, str]] = []
    for f, ok, msg in _map_or_serial(workers, _check_against_warn, files, 4):
        if not ok:
            failures.append((f, "recursive-descent", msg))
    return failures


def _canonical_ast(
    value: object,
    *,
    parent_class: str | None = None,
    field_name: str | None = None,
) -> object:
    """Canonical structural form for comparing parser ASTs.

    Source locations are intentionally ignored. Lark ``Token`` values are
    converted to plain strings because the RD parser usually emits strings for
    the same identifier/operator leaves. The RD parser also preserves the
    historical ``default`` visibility sentinel; normalize it to the LALR
    parser's concrete visibility for this comparison.
    """
    if isinstance(value, Token):
        return str(value)
    if field_name == "visibility" and value == "default":
        value = "private" if parent_class == "Import" else "public"
    if is_dataclass(value):
        cls_name = type(value).__name__
        return (
            cls_name,
            tuple(
                (fld.name, _canonical_ast(
                    getattr(value, fld.name),
                    parent_class=cls_name,
                    field_name=fld.name,
                ))
                for fld in dc_fields(value)
                if fld.name != "location"
            ),
        )
    if isinstance(value, list):
        return [_canonical_ast(v) for v in value]
    if isinstance(value, tuple):
        return tuple(_canonical_ast(v) for v in value)
    return value


def _canonical_equal(a: object, b: object) -> bool:
    """Structural equality for ``_canonical_ast`` results, iteratively.

    A canonical AST for a large unary numeric literal is nested thousands of
    levels deep; comparing two of them with plain ``==`` recurses in C and
    trips CPython 3.12's fixed C-recursion guard -- which ``setrecursionlimit``
    does not raise -- aborting the whole ``--equiv-full`` run on files like
    ``test/should-validate/large_numeric_literals.pf``. This explicit worklist
    keeps the comparison iterative; leaf values (str/int/bool/None) are the
    only ones handed to ``==``.
    """
    stack: list[tuple[object, object]] = [(a, b)]
    while stack:
        x, y = stack.pop()
        x_seq = isinstance(x, (list, tuple))
        y_seq = isinstance(y, (list, tuple))
        if x_seq != y_seq or isinstance(x, list) != isinstance(y, list):
            return False
        if x_seq:
            x_seq_v = cast("list[object] | tuple[object, ...]", x)
            y_seq_v = cast("list[object] | tuple[object, ...]", y)
            if len(x_seq_v) != len(y_seq_v):
                return False
            stack.extend(zip(x_seq_v, y_seq_v))
        elif x != y:
            return False
    return True


def _parse_for_equivalence(
    path: str, *, recursive_descent: bool
) -> list[object]:
    with open(path, encoding="utf-8") as f:
        return _parse_text_for_equivalence(
            path, f.read(), recursive_descent=recursive_descent,
            experimental_imperative=_uses_experimental_imperative(path),
        )


def _parse_text_for_equivalence(path: str, source: str, *,
                                recursive_descent: bool,
                                experimental_imperative: bool = False
                                ) -> list[object]:
    parser_mod = _equiv_rd_parser if recursive_descent else _equiv_lark_parser
    parser_mod.set_deduce_directory(str(REPO_ROOT))
    parser_mod.set_filename(path)
    parser_mod.init_parser()
    return cast(list[object], parser_mod.parse(
        source, experimental_imperative=experimental_imperative,
    ))


def _pretty_print_program(ast: Iterable[object]) -> str:
    chunks = []
    for stmt in ast:
        printer = getattr(stmt, "pretty_print", None)
        text = (
            cast(Callable[[int], str], printer)(0)
            if callable(printer)
            else str(stmt)
        )
        chunks.append(text if text.endswith("\n") else text + "\n")
    return "".join(chunks)


def _worker_parser_equivalence(
    path: str,
) -> tuple[str, bool, str, bool]:
    try:
        rd_ast = _canonical_ast(
            _parse_for_equivalence(path, recursive_descent=True)
        )
        lalr_ast = _canonical_ast(
            _parse_for_equivalence(path, recursive_descent=False)
        )
    except Exception as exc:
        return path, False, f"{type(exc).__name__}: {exc}", False

    if _canonical_equal(rd_ast, lalr_ast):
        if path in PARSER_EQUIV_EXPECTED_DIVERGENCES:
            return path, False, "listed as a divergence but now matches", False
        return path, True, "", False

    if path in PARSER_EQUIV_EXPECTED_DIVERGENCES:
        return path, True, "", True
    return path, False, "RD and LALR ASTs differ", False


# Reserved keywords must not be usable as identifiers in name/binding
# positions under either parser (issue #1032). RD lexes non-contextually so it
# always rejected these; the LALR parser used to lex a keyword as IDENT
# whenever the keyword terminal was not expected in the current state, letting
# it slip through until `parser.reject_reserved_identifiers` closed the gap.
# One representative keyword per binding position from the issue's table is
# enough to catch a regression of that fix.
KEYWORD_NAME_REJECTION_CASES = (
    "define if = true",                 # define name
    "theorem if: true proof . end",     # theorem name
    "fun and(x:bool) { x }",            # fun name
    "union theorem { foo }",            # union name
    "fun f(then:bool) { then }",        # fun parameter
    "define d = all if:bool. true",     # all-bound variable
)

# The LALR grammar once had an `atomic_term: "%" type` production that leaked a
# bare Type node into a term position (crashing later in `type_synth_term`),
# which RD never accepted (issue #1077). One `%<type>` per type shape guards
# against reintroducing that LALR-only divergence.
PERCENT_TYPE_REJECTION_CASES = (
    "define d = %bool",                 # atomic type
    "define d = %[bool]",               # array type
    "define d = %U<bool>",              # instantiated type
)


def _expect_both_parsers_reject(
    cases: tuple[str, ...], marker: str, why: str,
) -> list[tuple[str, str, str]]:
    """Every case must fail to parse under both parsers."""
    failures: list[tuple[str, str, str]] = []
    for src in cases:
        for recursive_descent in (True, False):
            label = "recursive-descent" if recursive_descent else "lalr"
            try:
                _parse_text_for_equivalence(
                    marker, src, recursive_descent=recursive_descent,
                )
                failures.append((src, "parser-equivalence",
                                 f"{label} accepted input both parsers must "
                                 f"reject: {why}"))
            except Exception:
                pass
    return failures


# Operator-grouping forms that both parsers must group identically (refs #473,
# #931). These belong here rather than in a ``should-validate`` fixture because
# the approximate operators ``≈``/``≲`` only apply to ``fn UInt -> UInt`` while
# the comparison/equality operators apply to numbers, so a mixed expression like
# ``a ≈ b < c`` never type-checks -- yet both parsers must still parse it to the
# same AST. ``≈`` sits at the ``comparison_term``
# level in ``Deduce.lark`` and the Reference.md precedence table (level 4), but
# RD used to group it with the looser equality operators, so ``a ≈ b < c``
# diverged (``a ≈ (b < c)`` under RD vs ``(a ≈ b) < c`` under LALR).
OPERATOR_GROUPING_EQUIV_CASES = (
    "define t = a ≈ b < c",
    "define t = a = b ≈ c",
    "define t = a ≠ b ≈ c",
    "define t = a ≈ b ≲ c",
    "define t = a ≲ b ≈ c",
    # ASCII synonyms (~~ for ≈, <~ for ≲, ~- for ⊝) must group exactly like
    # their Unicode counterparts under both parsers (issue #1069).
    "define t = a ~~ b < c",
    "define t = a <~ b ~~ c",
    "define t = a ~- b + c",
    "define t = a ~~ b ~- c",
)


def _check_operator_grouping_equivalence() -> list[tuple[str, str, str]]:
    """Both parsers must group mixed operator forms identically."""
    failures: list[tuple[str, str, str]] = []
    for src in OPERATOR_GROUPING_EQUIV_CASES:
        try:
            rd = _canonical_ast(_parse_text_for_equivalence(
                "<operator-grouping>", src, recursive_descent=True))
            lalr = _canonical_ast(_parse_text_for_equivalence(
                "<operator-grouping>", src, recursive_descent=False))
        except Exception as exc:
            failures.append((src, "parser-equivalence",
                             f"{type(exc).__name__}: {exc}"))
            continue
        if not _canonical_equal(rd, lalr):
            failures.append((src, "parser-equivalence",
                             "RD and LALR group this form differently"))
    return failures


# Each ASCII operator spelling must parse to the *same* AST as its Unicode
# counterpart -- both as an infix operator and in an `operator` declaration --
# under both parsers (issue #1069). This guards the synonym wiring in
# Deduce.lark / rec_desc_parser.py / parser.py against silent drift.
ASCII_OPERATOR_SYNONYM_PAIRS = (
    ("define t = a ~~ b", "define t = a ≈ b"),
    ("define t = a <~ b", "define t = a ≲ b"),
    ("define t = a ~- b", "define t = a ⊝ b"),
    ("define f = operator ~~", "define f = operator ≈"),
    ("define f = operator <~", "define f = operator ≲"),
    ("define f = operator ~-", "define f = operator ⊝"),
)


def _check_ascii_operator_synonyms() -> list[tuple[str, str, str]]:
    """ASCII operator spellings must parse identically to their Unicode forms."""
    failures: list[tuple[str, str, str]] = []
    for ascii_src, unicode_src in ASCII_OPERATOR_SYNONYM_PAIRS:
        for rd in (True, False):
            parser = "RD" if rd else "LALR"
            try:
                a = _canonical_ast(_parse_text_for_equivalence(
                    "<ascii-synonym>", ascii_src, recursive_descent=rd))
                u = _canonical_ast(_parse_text_for_equivalence(
                    "<ascii-synonym>", unicode_src, recursive_descent=rd))
            except Exception as exc:
                failures.append((ascii_src, "ascii-synonym",
                                 f"{parser}: {type(exc).__name__}: {exc}"))
                continue
            if not _canonical_equal(a, u):
                failures.append((ascii_src, "ascii-synonym",
                                 f"{parser}: parses differently from {unicode_src!r}"))
    return failures


def _check_keyword_name_rejection() -> list[tuple[str, str, str]]:
    """Both parsers must reject reserved keywords in name/binding positions."""
    return _expect_both_parsers_reject(
        KEYWORD_NAME_REJECTION_CASES, "<keyword-name-rejection>",
        "reserved keyword used as an identifier")


def _check_percent_type_rejection() -> list[tuple[str, str, str]]:
    """Both parsers must reject `%<type>` in term position (issue #1077)."""
    return _expect_both_parsers_reject(
        PERCENT_TYPE_REJECTION_CASES, "<percent-type-rejection>",
        "`%<type>` is not a term")


def run_parser_equivalence(workers: int) -> list[tuple[str, str, str]]:
    """Compare RD and LALR ASTs for parseable syntax.

    Covers a curated corpus spanning stdlib, accepted, and warning fixtures,
    plus the entire ``test/should-error`` directory: those files fail in a
    later phase but parse cleanly under both parsers, so their ASTs are still
    meaningful surface-syntax samples. The ``SHOULD_ERROR_PARSER_EQUIV_SKIP``
    baseline excludes only the fixtures where at least one parser rejects at
    parse time today.

    ``test/parse`` remains RD-only because those fixtures intentionally lock
    down beginner-facing RD diagnostics, while the LALR parser is kept as an
    executable grammar spec.
    """
    all_files = tuple(dict.fromkeys(
        PARSER_EQUIV_FILES
        + should_error_equiv_files()
        + tuple(sorted(PARSER_EQUIV_EXPECTED_DIVERGENCES))
    ))
    files = shard(list(all_files))
    failures: list[tuple[str, str, str]] = []
    seen_divergences: set[str] = set()
    for path, ok, msg, expected_diverged in _map_or_serial(
        _parser_workers(workers, len(files)),
        _worker_parser_equivalence,
        files,
        1,
    ):
        if expected_diverged:
            seen_divergences.add(path)
        if not ok:
            failures.append((path, "parser-equivalence",
                             msg))

    # Global invariant checks are corpus-wide, not per-file: run them once
    # (on the sole/first shard) so a fan-out neither duplicates their failures
    # nor trips the staleness check on paths another shard owns.
    if _SHARD is None or _SHARD[0] == 0:
        failures.extend(_check_should_error_skip_set())
        failures.extend(_check_keyword_name_rejection())
        failures.extend(_check_operator_grouping_equivalence())
        failures.extend(_check_ascii_operator_synonyms())
        failures.extend(_check_percent_type_rejection())
        stale = (PARSER_EQUIV_EXPECTED_DIVERGENCES
                 - seen_divergences - set(all_files))
        for path in sorted(stale):
            failures.append((path, "parser-equivalence",
                             "expected divergence path no longer exists"))
    return failures


def _worker_parser_round_trip(path: str) -> list[tuple[str, str, str]]:
    failures: list[tuple[str, str, str]] = []
    pretty_by_source: dict[str, str] = {}
    for source_rd in (True, False):
        source_label = "RD" if source_rd else "LALR"
        try:
            original = _parse_for_equivalence(
                path, recursive_descent=source_rd
            )
            pretty_source = _pretty_print_program(original)
            original_ast = _canonical_ast(original)
        except Exception as exc:
            failures.append((path, "parser-roundtrip",
                             f"{source_label} source parse/print: "
                             f"{type(exc).__name__}: {exc}"))
            continue
        pretty_by_source[source_label] = pretty_source

        for roundtrip_rd in (True, False):
            roundtrip_label = "RD" if roundtrip_rd else "LALR"
            try:
                reparsed = _parse_text_for_equivalence(
                    path + f"<{source_label}-roundtrip-{roundtrip_label}>",
                    pretty_source,
                    recursive_descent=roundtrip_rd,
                    experimental_imperative=_uses_experimental_imperative(path),
                )
            except Exception as exc:
                failures.append((path, "parser-roundtrip",
                                 f"{source_label} pretty source failed "
                                 f"with {roundtrip_label}: "
                                 f"{type(exc).__name__}: {exc}"))
                continue

            if not _canonical_equal(_canonical_ast(reparsed), original_ast):
                failures.append((path, "parser-roundtrip",
                                 f"{source_label} pretty source changed "
                                 f"when parsed with {roundtrip_label}"))
                continue

            # Idempotence: the pretty-printer is meant to be a canonical
            # fixpoint, so re-printing the reparsed AST must reproduce the
            # exact same text. A drift here means the printed output depends
            # on something the canonical-AST check normalizes away (source
            # locations, Token-vs-str leaves, the ``default`` visibility
            # sentinel) -- a latent formatting bug masked by that comparison.
            if _pretty_print_program(reparsed) != pretty_source:
                failures.append((path, "parser-roundtrip",
                                 f"{source_label} pretty source is not "
                                 f"idempotent under {roundtrip_label} "
                                 f"(reprint differs)"))

    # Cross-parser agreement: RD and LALR must pretty-print a file to byte
    # identical text. They already produce canonically equal ASTs (checked by
    # ``run_parser_equivalence``), so any text difference is the printer
    # reading a field the canonical comparison ignores.
    if ("RD" in pretty_by_source and "LALR" in pretty_by_source
            and pretty_by_source["RD"] != pretty_by_source["LALR"]):
        failures.append((path, "parser-roundtrip",
                         "RD and LALR pretty-print to different text"))
    return failures


def _check_should_error_skip_set() -> list[tuple[str, str, str]]:
    """Verify each ``SHOULD_ERROR_PARSER_EQUIV_SKIP`` entry still needs skipping.

    A file belongs in the skip set only as long as at least one parser
    rejects it at parse time. Once both parsers accept it, it should be
    promoted into the main equivalence sweep so we get drift coverage there
    too.
    """
    failures: list[tuple[str, str, str]] = []
    existing_error_files = set(list_pf(ERROR_DIR))
    for path in sorted(SHOULD_ERROR_PARSER_EQUIV_SKIP):
        if path not in existing_error_files:
            failures.append((path, "parser-equivalence",
                             "skip-set path no longer exists"))
            continue
        try:
            _parse_for_equivalence(path, recursive_descent=True)
            rd_ok = True
        except Exception:
            rd_ok = False
        try:
            _parse_for_equivalence(path, recursive_descent=False)
            lalr_ok = True
        except Exception:
            lalr_ok = False
        if rd_ok and lalr_ok:
            failures.append((path, "parser-equivalence",
                             "skip-set entry now parses with both parsers; "
                             "remove from SHOULD_ERROR_PARSER_EQUIV_SKIP"))
    return failures


def run_parser_round_trip(workers: int) -> list[tuple[str, str, str]]:
    """Pretty-print representative ASTs and re-parse with both parsers."""
    files = shard(list(PARSER_ROUND_TRIP_FILES))
    failures: list[tuple[str, str, str]] = []
    for file_failures in _map_or_serial(
        _parser_workers(workers, len(files)),
        _worker_parser_round_trip,
        files,
        1,
    ):
        failures.extend(file_failures)
    return failures


# Accepted-syntax directories swept by the opt-in ``--equiv-full`` audit.
# ``test/parse`` is excluded on purpose: those fixtures are deliberately
# malformed and RD-only, so round-tripping them is not meaningful. Everything
# else with ``.pf`` files is in scope so the audit lives up to its "every
# accepted-syntax file" promise (issues #931, #473):
#
#   * ``test/test-imports`` -- auxiliary modules the ``should-validate`` /
#     ``should-error`` suites import as ``--dir`` inputs (cross-module import,
#     export, and visibility forms); accepted modules in their own right even
#     though no top-level test checks them directly.
#   * ``test/compile`` -- the compilation-test inputs (nested subdirectories),
#     which must parse and check to be compiled.
#   * ``tools/claude_fill_hole/examples`` -- hole-fill fixtures exercising the
#     ``?`` / ``help`` hole syntax.
#
# ``test/should-error`` files are meant to fail, but most fail in a *later*
# phase (type/proof check) while parsing cleanly under both parsers -- their
# surface syntax is a legitimate round-trip subject and exercises constructs
# the validating corpus may not. Those are folded in by ``full_round_trip_files``
# below; the ones that at least one parser rejects at parse time are the
# ``SHOULD_ERROR_PARSER_EQUIV_SKIP`` baseline and stay out (the ``--equiv``
# staleness check shrinks that set as parsers converge). This is the full-corpus
# counterpart to the curated ``PARSER_ROUND_TRIP_FILES`` set.
FULL_ROUND_TRIP_DIRS = (LIB_DIR, PASS_DIR, WARN_DIR, PRELUDE_DIR, EXAMPLES_DIR,
                        IMPORTS_DIR, COMPILE_DIR, HOLE_FILL_EXAMPLES_DIR)


def list_pf_recursive(d: Path) -> list[str]:
    """Like ``list_pf`` but descends into subdirectories (e.g. ``test/compile``)."""
    return sorted(f"./{p.as_posix()}" for p in d.rglob("*.pf"))


def full_round_trip_files() -> tuple[str, ...]:
    """Every accepted-syntax ``.pf`` file, deduped and order-preserving.

    Includes ``test/should-error`` fixtures that both parsers accept at parse
    time (i.e. everything except the ``SHOULD_ERROR_PARSER_EQUIV_SKIP``
    baseline), since those round-trip meaningfully even though they fail a
    later semantic phase.
    """
    files: list[str] = []
    for d in FULL_ROUND_TRIP_DIRS:
        files.extend(list_pf_recursive(d))
    files.extend(p for p in list_pf(ERROR_DIR)
                 if p not in SHOULD_ERROR_PARSER_EQUIV_SKIP)
    files.append(f"./{EXAMPLE_FILE.as_posix()}")
    return tuple(dict.fromkeys(files))


def run_parser_round_trip_full(workers: int) -> list[tuple[str, str, str]]:
    """Round-trip every accepted-syntax ``.pf`` file (opt-in, non-CI)."""
    files = full_round_trip_files()
    failures: list[tuple[str, str, str]] = []
    for file_failures in _map_or_serial(
        _parser_workers(workers, len(files)),
        _worker_parser_round_trip,
        files,
        1,
    ):
        failures.extend(file_failures)
    return failures


def run_cli_test() -> list[tuple[str, str, str]]:
    """Sanity-check that ``python deduce.py`` works end-to-end.

    The in-process runner exercises ``lsp.library.check_file``; this
    one subprocess invocation makes sure the ``deduce.py`` CLI wrapper
    itself (arg parsing, no-stdlib mode, exit codes, success output)
    hasn't drifted. A tiny no-stdlib file is enough -- we're testing
    the CLI shape without paying for a full stdlib bootstrap.
    """
    cli_path = "./test/should-validate/theorem_true.pf"
    cp = subprocess.run(
        [sys.executable, "deduce.py", "--no-stdlib", cli_path],
        capture_output=True, text=True,
    )
    failures: list[tuple[str, str, str]] = []
    if cp.returncode != 0:
        failures.append((
            cli_path, "cli",
            f"exit {cp.returncode}\nstderr: {cp.stderr[:500]}\n"
            f"stdout: {cp.stdout[:500]}",
        ))
    elif "theorem_true.pf is valid" not in cp.stdout:
        failures.append((
            cli_path, "cli",
            f"unexpected stdout:\n{cp.stdout[:500]}",
        ))
    help_cp = subprocess.run(
        [sys.executable, "deduce.py", "--help"],
        capture_output=True, text=True,
    )
    if help_cp.returncode != 0:
        failures.append((
            "deduce.py --help", "cli",
            f"exit {help_cp.returncode}\nstderr: {help_cp.stderr[:500]}\n"
            f"stdout: {help_cp.stdout[:500]}",
        ))
    elif "--experimental-imperative" not in help_cp.stdout:
        failures.append((
            "deduce.py --help", "cli",
            "--experimental-imperative missing from help output",
        ))
    return failures


def run_experimental_imperative_parser_test() -> list[tuple[str, str, str]]:
    pure_new_source = "module Test\ndefine x = new Node()\n"
    failures: list[tuple[str, str, str]] = []
    path = "__experimental_imperative__.pf"
    try:
        for recursive_descent in (True, False):
            label = "recursive-descent" if recursive_descent else "lalr"
            try:
                _parse_text_for_equivalence(
                    path, IMPERATIVE_SYNTAX_SOURCE,
                    recursive_descent=recursive_descent,
                )
                failures.append((
                    path, label,
                    "imperative syntax parsed with the flag disabled",
                ))
            except Exception:
                pass

        rd_ast = _parse_text_for_equivalence(
            path, IMPERATIVE_SYNTAX_SOURCE,
            recursive_descent=True,
            experimental_imperative=True,
        )
        lalr_ast = _parse_text_for_equivalence(
            path, IMPERATIVE_SYNTAX_SOURCE,
            recursive_descent=False,
            experimental_imperative=True,
        )
        canonical = _canonical_ast(rd_ast)
        if not _canonical_equal(_canonical_ast(lalr_ast), canonical):
            failures.append((
                path, "experimental-imperative",
                "RD and LALR ASTs differ",
            ))

        pretty_source = _pretty_print_program(rd_ast)
        for recursive_descent in (True, False):
            label = "recursive-descent" if recursive_descent else "lalr"
            reparsed = _parse_text_for_equivalence(
                path + f"<roundtrip-{label}>",
                pretty_source,
                recursive_descent=recursive_descent,
                experimental_imperative=True,
            )
            if not _canonical_equal(_canonical_ast(reparsed), canonical):
                failures.append((
                    path, label,
                    "pretty-printer round-trip changed the AST",
                ))

        for recursive_descent in (True, False):
            label = "recursive-descent" if recursive_descent else "lalr"
            set_recursive_descent(recursive_descent)
            set_experimental_imperative(True)
            # Phase 1i (issue #968): proc/observer/resource declarations are
            # recognized as first-class for module boundaries and tooling.
            # Their bodies and specs are not verified yet (Phase 2+), so a file
            # that only declares them checks successfully.
            checked = check_file(path, content=IMPERATIVE_SYNTAX_SOURCE,
                                 prelude=())
            if not checked.ok:
                failures.append((
                    path, label,
                    "imperative declarations should now be recognized, "
                    f"but checking failed:\n{(checked.error_message or '')[:500]}",
                ))

            pure_new = check_file(
                "__experimental_new__.pf", content=pure_new_source,
                prelude=(),
            )
            if pure_new.ok:
                failures.append((
                    "__experimental_new__.pf", label,
                    "`new` unexpectedly parsed as a pure term",
                ))
            elif "allocation syntax is only available" not in (
                pure_new.error_message or ""
            ):
                failures.append((
                    "__experimental_new__.pf", label,
                    "`new` pure-term rejection had unexpected diagnostic:\n"
                    f"{(pure_new.error_message or '')[:500]}",
                ))
    finally:
        set_experimental_imperative(False)
        set_recursive_descent(True)
    return failures


def run_examples_parallel(workers: int) -> list[tuple[str, str, str]]:
    """``examples/*.pf`` × RD parser only.

    Examples are end-user-facing proofs that rely on the auto-prelude
    (``import UInt`` etc. is not written out); use the prelude-injection
    worker so the stdlib is implicitly available, the same way
    ``deduce.py`` runs them.
    """
    files = list_pf(EXAMPLES_DIR)
    tasks = shard([(f, True) for f in files])
    failures: list[tuple[str, str, str]] = []
    for f, ok, label, msg in _map_or_serial(workers, _worker_prelude, tasks, 4):
        if not ok:
            failures.append((f, label, msg))
    return failures


def run_site(workers: int) -> list[tuple[str, str, str]]:
    """Generate ``doc_*.pf`` from ``gh_pages/doc/`` and check them."""
    from gh_pages.scripts.convert import convert_dir as convert_dir_raw
    convert_dir = cast(Callable[[str, bool], None], convert_dir_raw)
    convert_dir("./gh_pages/doc/", False)
    files: list[str] = []
    for name in sorted(os.listdir(PASS_DIR)):
        if name.startswith("doc_") and name.endswith(".pf"):
            files.append(f"./{PASS_DIR.as_posix()}/{name}")
    tasks = [(f, p) for f in files for p in (True, False)]
    failures: list[tuple[str, str, str]] = []
    for f, ok, label, msg in _map_or_serial(workers, _worker_validate, tasks, 2):
        if not ok:
            failures.append((f, label, msg))
    return failures


# ---------------------------------------------------------------------------
# Regeneration of .err fixtures.
# ---------------------------------------------------------------------------


def _capture_err_output(path: str) -> str:
    """Run ``check_file`` on ``path`` and return the captured stdout.

    Mirrors what ``deduce.py`` would have printed on a failing run:
    interleaved warnings emitted via ``print()`` followed by the
    final ``result.error_message`` line.
    """
    set_recursive_descent(True)
    set_experimental_imperative(_uses_experimental_imperative(path))
    set_quiet_mode(True)
    buf = io.StringIO()
    try:
        with contextlib.redirect_stdout(buf):
            result = check_file(path, prewarm_modules=_WORKER_PREWARM)
            if not result.ok:
                print(result.error_message)
    finally:
        set_experimental_imperative(False)
    return buf.getvalue()


def regenerate_one(path: str, suffix: str = ".err") -> None:
    out = _capture_err_output(path)
    with open(path + suffix, "w", encoding="utf-8") as f:
        f.write(out)
    print(f"  wrote {path}{suffix}")


def regenerate_dir(directory: Path, suffix: str = ".err") -> None:
    for f in list_pf(directory):
        regenerate_one(f, suffix)


# ---------------------------------------------------------------------------
# CLI.
# ---------------------------------------------------------------------------


def time_section(label: str, fn: Callable[[], S]) -> tuple[float, S]:
    t0 = time.perf_counter()
    result = fn()
    dt = time.perf_counter() - t0
    print(f"  {label:32s}  {dt:6.2f}s")
    return dt, result


def _parse_shard(spec: str) -> tuple[int, int]:
    """Parse a ``--shard i/n`` spec into a 0-based ``(index, count)``.

    ``i`` is 1-based on the command line (``1/6`` .. ``6/6``) to read
    naturally in CI matrix definitions."""
    try:
        i_str, n_str = spec.split("/", 1)
        index, count = int(i_str), int(n_str)
    except ValueError:
        print(f"invalid --shard spec {spec!r} (expected i/n, e.g. 2/6)",
              file=sys.stderr)
        sys.exit(2)
    if count < 1 or not (1 <= index <= count):
        print(f"invalid --shard {spec}: need 1 <= i <= n and n >= 1",
              file=sys.stderr)
        sys.exit(2)
    return (index - 1, count)


def parse_args(argv: list[str]) -> ParsedFlags:
    """Return a dict of flag → value. Tolerates the legacy long-form
    arguments still in scripts / muscle memory."""
    flags: ParsedFlags = {
        "cli": False, "lib": False, "passable": False, "prelude": False,
        "errors": False,
        "warns": False, "equiv": False, "equiv_full": False, "site": False,
        "parser": False,
        "examples": False, "regen_all": False, "regen_files": [],
        "regen_all_warns": False, "regen_warn_files": [],
        "gen_parse": False, "workers": max(1, (os.cpu_count() or 4)),
        "shard": None,
    }
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == "--cli": flags["cli"] = True
        elif a == "--lib": flags["lib"] = True
        elif a == "--passable": flags["passable"] = True
        elif a == "--prelude": flags["prelude"] = True
        elif a == "--errors": flags["errors"] = True
        elif a == "--warns": flags["warns"] = True
        elif a == "--equiv": flags["equiv"] = True
        elif a == "--equiv-full": flags["equiv_full"] = True
        elif a == "--site": flags["site"] = True
        elif a == "--parser": flags["parser"] = True
        elif a == "--examples": flags["examples"] = True
        elif a == "--regenerate-errors": flags["regen_all"] = True
        elif a == "--generate-error":
            flags["regen_files"].append(argv[i + 1])
            i += 1
        elif a == "--regenerate-warns": flags["regen_all_warns"] = True
        elif a == "--generate-warn":
            flags["regen_warn_files"].append(argv[i + 1])
            i += 1
        elif a == "--gen-parse": flags["gen_parse"] = True
        elif a == "--serial": flags["workers"] = 1
        elif a in ("--workers", "--max-threads"):
            flags["workers"] = max(1, int(argv[i + 1]))
            i += 1
        elif a == "--shard":
            flags["shard"] = _parse_shard(argv[i + 1])
            i += 1
        else:
            print(f"unknown argument: {a}", file=sys.stderr)
            sys.exit(2)
        i += 1

    # If no flags at all, default to the per-PR regression sweep.
    if not (
        flags["cli"] or flags["lib"] or flags["passable"] or flags["prelude"]
        or flags["errors"]
        or flags["warns"] or flags["site"] or flags["parser"]
        or flags["examples"] or flags["equiv"] or flags["equiv_full"]
        or flags["regen_all"]
        or flags["regen_all_warns"] or flags["gen_parse"]
        or flags["regen_files"] or flags["regen_warn_files"]
    ):
        flags["cli"] = flags["lib"] = flags["passable"] = True
        flags["prelude"] = True
        flags["errors"] = flags["warns"] = flags["equiv"] = True

    # Standalone modes are mutually exclusive with everything else.
    category_flags = (
        ("cli", flags["cli"]),
        ("lib", flags["lib"]),
        ("passable", flags["passable"]),
        ("prelude", flags["prelude"]),
        ("errors", flags["errors"]),
        ("warns", flags["warns"]),
        ("equiv", flags["equiv"]),
    )
    standalone_flags = (
        ("site", flags["site"]),
        ("parser", flags["parser"]),
        ("examples", flags["examples"]),
        ("equiv-full", flags["equiv_full"]),
        ("regen_all", flags["regen_all"]),
        ("regen_files", bool(flags["regen_files"])),
        ("regen_all_warns", flags["regen_all_warns"]),
        ("regen_warn_files", bool(flags["regen_warn_files"])),
        ("gen_parse", flags["gen_parse"]),
    )
    if any(active for _, active in standalone_flags):
        active_categories = [name for name, active in category_flags if active]
        active_standalone = [
            name for name, active in standalone_flags if active
        ]
        if active_categories and active_standalone:
            print(
                f"--{active_standalone[0]} is standalone; cannot combine with "
                f"--{active_categories[0]}", file=sys.stderr,
            )
            sys.exit(2)
        if len(active_standalone) > 1:
            print(
                f"these flags are mutually exclusive: "
                f"{', '.join('--' + s for s in active_standalone)}",
                file=sys.stderr,
            )
            sys.exit(2)

    return flags


def main(argv: list[str]) -> int:
    flags = parse_args(argv)
    setup_paths()
    lib_modules = discover_lib_modules()
    workers = flags["workers"]

    global _SHARD
    _SHARD = flags["shard"]
    if _SHARD is not None:
        print(f"[shard {_SHARD[0] + 1}/{_SHARD[1]}] "
              "processing this stride of each category's work list")

    total_failures: list[tuple[str, str, str]] = []
    total_t0 = time.perf_counter()

    # Standalone: regen / site / parser. Each owns the run.
    if flags["regen_all"]:
        print(f"Regenerating ALL errors in {ERROR_DIR}")
        bootstrap_prewarm(lib_modules)
        regenerate_dir(ERROR_DIR)
        return 0
    if flags["regen_files"]:
        bootstrap_prewarm(lib_modules)
        for path in flags["regen_files"]:
            print(f"Generating error for: {path}")
            regenerate_one(path)
        return 0
    if flags["regen_all_warns"]:
        print(f"Regenerating ALL warnings in {WARN_DIR}")
        bootstrap_prewarm(lib_modules)
        regenerate_dir(WARN_DIR, ".warn")
        return 0
    if flags["regen_warn_files"]:
        bootstrap_prewarm(lib_modules)
        for path in flags["regen_warn_files"]:
            print(f"Generating warning fixture for: {path}")
            regenerate_one(path, ".warn")
        return 0
    if flags["gen_parse"]:
        print(f"Regenerating ALL parser errors in {PARSE_DIR}")
        bootstrap_prewarm(lib_modules)
        regenerate_dir(PARSE_DIR)
        return 0
    if flags["site"]:
        print("=== --site: generate doc_*.pf and check (parallel) ===")
        bootstrap_prewarm(lib_modules)
        _, fails = time_section("site doc files × 2 parsers",
                                lambda: run_site(workers))
        total_failures.extend(fails)
        return _report(total_failures, total_t0)
    if flags["parser"]:
        print(f"=== --parser: {PARSE_DIR} (RD only, parallel) ===")
        bootstrap_prewarm(lib_modules)
        _, fails = time_section("test/parse",
                                lambda: run_err_diff_parallel(
                                    PARSE_DIR, "parser", workers))
        total_failures.extend(fails)
        return _report(total_failures, total_t0)
    if flags["examples"]:
        print(f"=== --examples: {EXAMPLES_DIR} (RD only, parallel) ===")
        bootstrap_prelude(lib_modules)
        _, fails = time_section("examples",
                                lambda: run_examples_parallel(workers))
        total_failures.extend(fails)
        return _report(total_failures, total_t0)
    if flags["equiv_full"]:
        corpus = full_round_trip_files()
        print(f"=== --equiv-full: pretty-print round trip over "
              f"{len(corpus)} accepted-syntax files (both parsers) ===")
        _, fails = time_section("full-corpus round trip",
                                lambda: run_parser_round_trip_full(workers))
        total_failures.extend(fails)
        return _report(total_failures, total_t0)

    # Combinable per-category sweep.
    print(f"Discovered {len(lib_modules)} lib modules; workers={workers}")

    if flags["cli"]:
        print("\n=== --cli: deduce.py CLI sanity check ===")
        _, fails = time_section(
            "deduce.py --no-stdlib theorem_true.pf", run_cli_test
        )
        total_failures.extend(fails)
        _, fails = time_section(
            "experimental imperative parser",
            run_experimental_imperative_parser_test,
        )
        total_failures.extend(fails)

    # Lib pool: clean state (no shared cache).
    if flags["lib"]:
        reset_prelude_cache()
        print("\n=== lib (both parsers, parallel) ===")
        _, fails = time_section("lib × 2 parsers",
                                lambda: run_lib_parallel(workers))
        total_failures.extend(fails)

    # Prelude pool: prelude-injection bootstrap. This is a separate leg from
    # ``--passable`` because the ``prelude=`` bootstrap fully checks the stdlib
    # (~100s cold on CI), whereas should-validate needs only the cheap
    # ``prewarm`` bootstrap -- bundling them made every should-validate shard
    # pay the expensive bootstrap. See issue #1049.
    if flags["prelude"]:
        reset_prelude_cache()
        t0 = time.perf_counter()
        bootstrap_prelude(lib_modules)
        print(f"\n  {'bootstrap prelude (parent)':32s}  "
              f"{time.perf_counter() - t0:6.2f}s")
        print("=== test/prelude (both parsers, parallel) ===")
        _, fails = time_section("test/prelude × 2 parsers",
                                lambda: run_prelude_parallel(workers))
        total_failures.extend(fails)

    # Combined pool: should-validate + should-error + should-warn share a
    # prewarm bootstrap.
    if flags["passable"] or flags["errors"] or flags["warns"]:
        reset_prelude_cache()
        t0 = time.perf_counter()
        bootstrap_prewarm(lib_modules)
        print(f"\n  {'bootstrap prewarm (parent)':32s}  "
              f"{time.perf_counter() - t0:6.2f}s")

    if flags["passable"]:
        print("=== should-validate (both parsers, parallel) ===")
        _, fails = time_section("should-validate × 2 parsers",
                                lambda: run_validate_parallel(workers))
        total_failures.extend(fails)

    if flags["errors"]:
        print("\n=== should-error (RD only, parallel) ===")
        _, fails = time_section("should-error",
                                lambda: run_err_diff_parallel(
                                    ERROR_DIR, "recursive-descent", workers))
        total_failures.extend(fails)

    if flags["warns"]:
        print("\n=== should-warn (RD only, parallel) ===")
        _, fails = time_section("should-warn",
                                lambda: run_warn_diff_parallel(workers))
        total_failures.extend(fails)

    if flags["equiv"]:
        print("\n=== parser equivalence (RD vs LALR ASTs) ===")
        _, fails = time_section("grammar + should-error corpus",
                                lambda: run_parser_equivalence(workers))
        total_failures.extend(fails)
        _, fails = time_section("pretty-print round trip",
                                lambda: run_parser_round_trip(workers))
        total_failures.extend(fails)

    return _report(total_failures, total_t0)


def _report(failures: list[tuple[str, str, str]], t0: float) -> int:
    print(f"\nTotal wall time: {time.perf_counter() - t0:.2f}s")
    if failures:
        print(f"\n{len(failures)} FAILURE(s):")
        for fpath, label, msg in failures[:20]:
            print(f"  [{label}] {fpath}")
            for line in str(msg).splitlines()[:3]:
                print(f"      {line}")
        if len(failures) > 20:
            print(f"  ... and {len(failures) - 20} more")
        return 1
    print("\nAll tests passed.")
    return 0


if __name__ == "__main__":
    signal(SIGINT, handle_sigint)
    sys.exit(main(sys.argv[1:]))
