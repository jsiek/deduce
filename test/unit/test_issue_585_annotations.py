from __future__ import annotations

import inspect
from collections.abc import Callable
from typing import Any

import abstract_syntax as ast


def _assert_params_annotated(
    func: Callable[..., Any],
    expected_params: set[str],
) -> None:
    signature = inspect.signature(func)
    missing = {
        name
        for name in expected_params
        if signature.parameters[name].annotation is inspect.Parameter.empty
    }
    assert missing == set()


def test_issue_585_statement_method_parameters_are_annotated() -> None:
    methods: list[tuple[Callable[..., Any], set[str]]] = [
        (ast.Module.pretty_print, {"indent"}),
        (ast.Module.uniquify, {"env", "ctx"}),
        (ast.Module.collect_exports, {"export_env", "importing_module"}),
        (ast.Export.pretty_print, {"indent"}),
        (ast.Export.uniquify, {"env", "ctx"}),
        (ast.Export.collect_exports, {"export_env", "importing_module"}),
        (ast.Associative.uniquify, {"env", "ctx"}),
        (ast.Associative.collect_exports, {"export_env", "importing_module"}),
        (ast.Trace.reduce, {"env"}),
    ]

    for method, expected_params in methods:
        _assert_params_annotated(method, expected_params)


def test_issue_585_helper_parameters_are_annotated() -> None:
    functions: list[tuple[Callable[..., Any], set[str]]] = [
        (ast.mkEqual, {"loc", "arg1", "arg2"}),
        (ast.is_equation, {"formula"}),
        (ast.isBZero, {"t"}),
        (ast.isDubInc, {"t"}),
        (ast.isIncDub, {"t"}),
        (ast.get_arg, {"t"}),
        (ast.mkBZero, {"loc", "zname", "ty"}),
        (ast.mkIncDub, {"loc", "arg", "cname", "ty"}),
        (ast.mkDubInc, {"loc", "arg", "cname", "ty"}),
        (ast.uint_inc, {"loc", "x"}),
        (ast.isSuc, {"t"}),
        (ast._array_index_predecessor, {"pos", "env"}),
        (ast._try_match_one_plus, {"t"}),
        (ast._uint_double, {"loc", "x", "env"}),
        (ast.intToUInt, {"loc", "n", "bzero", "dubinc", "incdub", "uint_ty"}),
        (ast.isLitNat, {"t"}),
        (ast.isLitUInt, {"t"}),
        (ast.isInt, {"t"}),
    ]

    for func, expected_params in functions:
        _assert_params_annotated(func, expected_params)
