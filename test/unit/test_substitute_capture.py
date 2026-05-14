"""Focused substitution capture-avoidance fixtures for issue #475."""

from __future__ import annotations

from lark.tree import Meta

import abstract_syntax as ast


def _m() -> Meta:
    return Meta()


def _var(name: str) -> ast.Var:
    return ast.Var(_m(), None, name)


def _call_with_bound_and_free(bound_name: str) -> ast.Call:
    return ast.Call(
        _m(),
        None,
        _var("pair"),
        [_var(bound_name), _var("free")],
    )


def _and_with_bound_and_free(bound_name: str) -> ast.And:
    return ast.And(_m(), None, [_var(bound_name), _var("free")])


def _env() -> dict[str, object]:
    return {
        "no overload": {},
        "free": ["free.seed"],
        "pair": ["pair.seed"],
        "Cons": ["Cons.seed"],
        "x": ["x.outer"],
        "T": ["T.outer"],
    }


def _uniquify(node: ast.AST) -> ast.AST:
    return node.uniquify(_env(), ast.UniquifyContext())


def _substitute_free_with_source_x(node: ast.AST) -> ast.AST:
    return node.substitute({"free.seed": _var("x")})


def _assert_bound_and_replacement_args(call: ast.Call, bound_name: str) -> None:
    bound_arg, replacement_arg = call.args
    assert isinstance(bound_arg, ast.OverloadedVar)
    assert bound_arg.resolved_names == [bound_name]
    assert isinstance(replacement_arg, ast.Var)
    assert replacement_arg.name == "x"
    assert replacement_arg.name != bound_name


def _assert_bound_and_replacement_formula_args(
    formula: ast.And, bound_name: str
) -> None:
    bound_arg, replacement_arg = formula.args
    assert isinstance(bound_arg, ast.OverloadedVar)
    assert bound_arg.resolved_names == [bound_name]
    assert isinstance(replacement_arg, ast.Var)
    assert replacement_arg.name == "x"
    assert replacement_arg.name != bound_name


def test_lambda_substitution_does_not_capture_shadowed_source_name() -> None:
    term = ast.Lambda(_m(), None, [("x", None)], _call_with_bound_and_free("x"))

    out = _substitute_free_with_source_x(_uniquify(term))

    assert isinstance(out, ast.Lambda)
    bound_name = out.vars[0][0]
    assert bound_name == "x.0"
    _assert_bound_and_replacement_args(out.body, bound_name)


def test_tlet_substitution_does_not_capture_shadowed_source_name() -> None:
    term = ast.TLet(
        _m(),
        None,
        "x",
        _var("free"),
        _call_with_bound_and_free("x"),
    )

    out = _substitute_free_with_source_x(_uniquify(term))

    assert isinstance(out, ast.TLet)
    assert out.var == "x.0"
    assert isinstance(out.rhs, ast.Var)
    assert out.rhs.name == "x"
    _assert_bound_and_replacement_args(out.body, out.var)


def test_all_substitution_does_not_capture_shadowed_source_name() -> None:
    formula = ast.All(
        _m(),
        None,
        ("x", ast.IntType(_m())),
        (0, 1),
        _and_with_bound_and_free("x"),
    )

    out = _substitute_free_with_source_x(_uniquify(formula))

    assert isinstance(out, ast.All)
    bound_name = out.var[0]
    assert bound_name == "x.0"
    _assert_bound_and_replacement_formula_args(out.body, bound_name)


def test_some_substitution_does_not_capture_shadowed_source_name() -> None:
    formula = ast.Some(
        _m(),
        None,
        [("x", ast.IntType(_m()))],
        _and_with_bound_and_free("x"),
    )

    out = _substitute_free_with_source_x(_uniquify(formula))

    assert isinstance(out, ast.Some)
    bound_name = out.vars[0][0]
    assert bound_name == "x.0"
    _assert_bound_and_replacement_formula_args(out.body, bound_name)


def test_generic_substitution_does_not_capture_shadowed_type_param_name() -> None:
    term = ast.Generic(_m(), None, ["T"], _call_with_bound_and_free("T"))

    out = _substitute_free_with_source_x(_uniquify(term))

    assert isinstance(out, ast.Generic)
    bound_name = out.type_params[0]
    assert bound_name == "T.0"
    _assert_bound_and_replacement_args(out.body, bound_name)


def test_switch_case_substitution_does_not_capture_pattern_binding() -> None:
    case = ast.SwitchCase(
        _m(),
        ast.PatternCons(_m(), _var("Cons"), ["x"]),
        _call_with_bound_and_free("x"),
    )

    out = _substitute_free_with_source_x(_uniquify(case))

    assert isinstance(out, ast.SwitchCase)
    assert isinstance(out.pattern, ast.PatternCons)
    bound_name = out.pattern.parameters[0]
    assert bound_name == "x.0"
    _assert_bound_and_replacement_args(out.body, bound_name)


def test_ind_case_substitution_does_not_capture_pattern_or_hypothesis_bindings() -> None:
    case = ast.IndCase(
        _m(),
        ast.PatternCons(_m(), _var("Cons"), ["x"]),
        [("h", _and_with_bound_and_free("x"))],
        ast.PVar(_m(), "h"),
    )

    out = _substitute_free_with_source_x(_uniquify(case))

    assert isinstance(out, ast.IndCase)
    assert isinstance(out.pattern, ast.PatternCons)
    pattern_name = out.pattern.parameters[0]
    hypothesis_name, hypothesis_formula = out.induction_hypotheses[0]
    assert pattern_name == "x.0"
    assert hypothesis_name == "h.1"
    _assert_bound_and_replacement_formula_args(hypothesis_formula, pattern_name)
    assert isinstance(out.body, ast.PVar)
    assert out.body.name == hypothesis_name


def test_switch_proof_case_substitution_does_not_capture_case_bindings() -> None:
    case = ast.SwitchProofCase(
        _m(),
        ast.PatternCons(_m(), _var("Cons"), ["x"]),
        [("h", _and_with_bound_and_free("x"))],
        ast.PVar(_m(), "h"),
    )

    out = _substitute_free_with_source_x(_uniquify(case))

    assert isinstance(out, ast.SwitchProofCase)
    assert isinstance(out.pattern, ast.PatternCons)
    pattern_name = out.pattern.parameters[0]
    assumption_name, assumption_formula = out.assumptions[0]
    assert pattern_name == "x.0"
    assert assumption_name == "h.1"
    _assert_bound_and_replacement_formula_args(assumption_formula, pattern_name)
    assert isinstance(out.body, ast.PVar)
    assert out.body.name == assumption_name


def test_fun_case_substitution_does_not_capture_pattern_or_parameter_bindings() -> None:
    case = ast.FunCase(
        _m(),
        _var("f"),
        ast.PatternCons(_m(), _var("Cons"), ["x"]),
        ["T"],
        ast.Call(_m(), None, _var("pair"), [_var("x"), _var("T"), _var("free")]),
    )
    env = _env()
    env["f"] = ["f.seed"]

    out = case.uniquify(env, "f", ast.UniquifyContext()).substitute(
        {"free.seed": _var("x")}
    )

    assert isinstance(out, ast.FunCase)
    assert isinstance(out.pattern, ast.PatternCons)
    pattern_name = out.pattern.parameters[0]
    parameter_name = out.parameters[0]
    assert pattern_name == "x.0"
    assert parameter_name == "T.1"

    pattern_arg, parameter_arg, replacement_arg = out.body.args
    assert isinstance(pattern_arg, ast.OverloadedVar)
    assert pattern_arg.resolved_names == [pattern_name]
    assert isinstance(parameter_arg, ast.OverloadedVar)
    assert parameter_arg.resolved_names == [parameter_name]
    assert isinstance(replacement_arg, ast.Var)
    assert replacement_arg.name == "x"
    assert replacement_arg.name not in {pattern_name, parameter_name}
