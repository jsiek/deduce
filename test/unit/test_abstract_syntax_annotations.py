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


def test_issue_586_abstract_syntax_function_parameters_are_annotated() -> None:
    functions: list[tuple[Callable[..., Any], set[str]]] = [
        (ast.mkUIntLit, {"loc", "num"}),
        (ast.mkPos, {"loc", "arg"}),
        (ast.mkNeg, {"loc", "arg"}),
        (ast.mkIntLit, {"loc", "n", "sign"}),
        (ast.is_constructor, {"constr_name", "env"}),
        (ast.is_constr_term, {"term", "env"}),
        (ast.constr_name, {"term"}),
        (ast.constructor_conflict, {"term1", "term2", "env"}),
        (ast._is_named, {"node", "base"}),
        (ast.isNodeList, {"t"}),
        (ast.nodeListToList, {"t"}),
        (ast.nodeListToString, {"t"}),
        (ast.mkEmpty, {"loc"}),
        (ast.mkNode, {"loc", "arg", "ls"}),
        (ast.listToNodeList, {"loc", "lst"}),
        (ast.type_params_str, {"type_params"}),
    ]

    for func, expected_params in functions:
        _assert_params_annotated(func, expected_params)


def test_issue_586_env_method_parameters_are_annotated() -> None:
    methods: list[tuple[Callable[..., Any], set[str]]] = [
        (ast.Env.base_to_unique, {"name"}),
        (ast.Env.base_to_overloads, {"name"}),
        (ast.Env.__contains__, {"item"}),
        (ast.Env.declare_type, {"loc", "name", "vis"}),
        (ast.Env.declare_type_vars, {"loc", "type_vars"}),
        (ast.Env.define_type, {"loc", "name", "defn", "visibility"}),
        (ast.Env.declare_view, {"loc", "view", "visibility"}),
        (ast.Env.declare_term_var,
         {"loc", "name", "typ", "local", "visibility"}),
        (ast.Env.declare_assoc, {"loc", "opname", "typarams", "typ"}),
        (ast.Env.declare_auto_rewrite, {"loc", "equation"}),
    ]

    for method, expected_params in methods:
        _assert_params_annotated(method, expected_params)
