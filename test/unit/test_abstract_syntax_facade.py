import abstract_syntax as ast
from abstract_syntax import Env, Theorem, Var, uniquify_deduce


def test_abstract_syntax_facade_preserves_common_import_styles() -> None:
    assert ast.Var is Var
    assert ast.Theorem is Theorem
    assert ast.Env is Env
    assert ast.uniquify_deduce is uniquify_deduce


def test_abstract_syntax_facade_exports_state_from_split_modules() -> None:
    ast.reset_reduced_defs()
    ast.add_reduced_def("Example.f")
    assert ast.get_reduced_defs() == {"Example.f"}
    assert ast.reduced_defs == {"Example.f"}
