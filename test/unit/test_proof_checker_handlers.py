"""Unit tests for the goal-directed proof handler dispatch table."""

from lark.tree import Meta

import abstract_syntax as ast
import proof_checker


def _meta() -> Meta:
    return Meta()


def test_check_proof_of_registers_extracted_goal_handlers() -> None:
    expected = {
        ast.PHole,
        ast.PSorry,
        ast.PReflexive,
        ast.PSymmetric,
        ast.PTransitive,
        ast.PExtensionality,
        ast.EvaluateGoal,
        ast.RewriteGoal,
        ast.SimplifyGoal,
        ast.ApplyDefsGoal,
    }

    assert expected <= set(proof_checker._CHECK_PROOF_OF_HANDLERS)


def test_check_proof_of_dispatches_registered_handler(monkeypatch) -> None:
    proof = ast.PSorry(_meta())
    calls = []

    def fake_handler(proof_arg, formula_arg, env_arg):
        calls.append((proof_arg, formula_arg, env_arg))
        return "handled"

    monkeypatch.setitem(
        proof_checker._CHECK_PROOF_OF_HANDLERS,
        ast.PSorry,
        fake_handler,
    )

    formula = object()
    env = object()

    assert proof_checker.check_proof_of(proof, formula, env) == "handled"
    assert calls == [(proof, formula, env)]


def test_sorry_handler_preserves_warning_behavior(monkeypatch) -> None:
    proof = ast.PSorry(_meta())
    calls = []

    def fake_warning(location, message):
        calls.append((location, message))

    monkeypatch.setattr(proof_checker, "warning", fake_warning)

    proof_checker._check_proof_of_sorry(proof, object(), object())

    assert calls == [(proof.location, "unfinished proof")]
