from __future__ import annotations

from lark.tree import Meta

import abstract_syntax as ast


def _meta() -> Meta:
    return Meta()


def test_callable_name_distinguishes_anonymous_callable() -> None:
    lam = ast.Lambda(_meta(), None, [("x", ast.IntType(_meta()))],
                     ast.Var(_meta(), None, "x"))

    assert ast.callable_name(ast.Var(_meta(), None, "f")) == "f"
    assert ast.callable_name(ast.TermInst(_meta(), None,
                                          ast.Var(_meta(), None, "f"),
                                          [ast.IntType(_meta())],
                                          True)) == "f"
    assert ast.callable_name(lam) is None


def test_auto_rewrite_fallback_bucket_is_explicit() -> None:
    fallback = ast.Bool(_meta(), None, False)
    direct = ast.Bool(_meta(), None, True)
    fallback_rule = ast.AutoRewriteRule(fallback, [], [], fallback, fallback)
    direct_rule = ast.AutoRewriteRule(direct, [], [], direct, direct)
    env = ast.Env({
        "__auto__": ast.AutoEquationBinding(
            location=_meta(),
            module="M",
            equations={"f": [direct_rule]},
            fallback_equations=[fallback_rule],
        )
    })

    assert env.get_auto_rewrites("f") == [direct_rule]
    assert env.get_auto_rewrites("missing") == [fallback_rule]
    assert env.get_auto_rewrites(None) == [fallback_rule]
