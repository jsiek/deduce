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


def test_issue_587_env_method_parameters_are_annotated() -> None:
    methods: list[tuple[Callable[..., Any], set[str]]] = [
        (ast.Env.declare_inductive, {"loc", "ind_dict", "thm"}),
        (ast.Env.get_inductive, {"typ"}),
        (ast.Env.declare_term_vars, {"loc", "xty_pairs", "local"}),
        (ast.Env.define_term_var, {"loc", "name", "typ", "val", "visibility"}),
        (ast.Env.define_term_vars, {"loc", "xv_pairs"}),
        (ast.Env.declare_proof_var, {"loc", "name", "frm"}),
        (ast.Env.declare_local_proof_var, {"loc", "name", "frm"}),
        (ast.Env.declare_module, {"module"}),
        (ast.Env._def_of_type_var, {"curr", "name"}),
        (ast.Env._type_of_term_var, {"curr", "name"}),
        (ast.Env._term_var_defined, {"curr", "name"}),
        (ast.Env._value_of_term_var, {"curr", "name"}),
        (ast.Env._formula_of_proof_var, {"curr", "name"}),
        (ast.Env.type_var_is_defined, {"tyname"}),
        (ast.Env.term_var_is_defined, {"tvar"}),
        (ast.Env.proof_var_is_defined, {"pvar"}),
        (ast.Env.get_def_of_type_var, {"var"}),
        (ast.Env.get_view, {"name"}),
        (ast.Env.get_formula_of_proof_var, {"pvar"}),
        (ast.Env.get_type_of_term_var, {"tvar"}),
        (ast.Env.get_value_of_term_var, {"tvar"}),
    ]

    for method, expected_params in methods:
        _assert_params_annotated(method, expected_params)


def test_issue_587_helper_parameters_are_annotated() -> None:
    functions: list[tuple[Callable[..., Any], set[str]]] = [
        (ast.set_default_mark_LHS, {"b"}),
        (ast.extract_and, {"frm"}),
        (ast.extract_or, {"frm"}),
        (ast.check_post_typecheck_invariants, {"ast_list"}),
        (ast.make_switch_for, {"meta", "defs", "subject", "cases"}),
    ]

    for func, expected_params in functions:
        _assert_params_annotated(func, expected_params)


def test_issue_587_nested_loc_prefix_parameter_is_annotated() -> None:
    source = inspect.getsource(ast.check_post_typecheck_invariants)
    assert "def loc_prefix(loc:" in source
