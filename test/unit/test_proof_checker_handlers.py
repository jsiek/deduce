"""Unit tests for proof handler dispatch tables."""

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
        ast.AllIntro,
        ast.SomeIntro,
        ast.SomeElim,
        ast.ImpIntro,
        ast.PTLetNew,
        ast.PLet,
        ast.PAnnot,
        ast.PTuple,
        ast.Cases,
        ast.Induction,
        ast.SwitchProof,
        ast.Suffices,
        ast.RuleInduction,
        ast.RuleInversion,
    }

    assert expected <= set(proof_checker._CHECK_PROOF_OF_HANDLERS)


def test_check_proof_of_registers_extracted_intro_and_local_handlers() -> None:
    expected = {
        ast.AllIntro: proof_checker._check_proof_of_all_intro,
        ast.SomeIntro: proof_checker._check_proof_of_some_intro,
        ast.SomeElim: proof_checker._check_proof_of_some_elim,
        ast.ImpIntro: proof_checker._check_proof_of_imp_intro,
        ast.PTLetNew: proof_checker._check_proof_of_tlet_new,
        ast.PLet: proof_checker._check_proof_of_let,
        ast.PAnnot: proof_checker._check_proof_of_annot,
        ast.PTuple: proof_checker._check_proof_of_tuple,
        ast.Cases: proof_checker._check_proof_of_cases,
        ast.Induction: proof_checker._check_proof_of_induction,
        ast.SwitchProof: proof_checker._check_proof_of_switch,
        ast.Suffices: proof_checker._check_proof_of_suffices,
        ast.RuleInduction: proof_checker._check_rule_induction,
        ast.RuleInversion: proof_checker._check_rule_inversion,
    }

    for proof_type, handler in expected.items():
        assert proof_checker._CHECK_PROOF_OF_HANDLERS[proof_type] is handler


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


def test_check_proof_registers_extracted_synthesis_handlers() -> None:
    expected = {
        ast.PRecall: proof_checker._check_proof_recall,
        ast.PVar: proof_checker._check_proof_var,
        ast.PTrue: proof_checker._check_proof_true,
        ast.PAndElim: proof_checker._check_proof_and_elim,
        ast.EvaluateFact: proof_checker._check_proof_evaluate_fact,
        ast.ApplyDefsFact: proof_checker._check_proof_apply_defs_fact,
        ast.RewriteFact: proof_checker._check_proof_rewrite_fact,
        ast.SimplifyFact: proof_checker._check_proof_simplify_fact,
        ast.PHole: proof_checker._check_proof_hole,
        ast.PSorry: proof_checker._check_proof_sorry,
        ast.PHelpUse: proof_checker._check_proof_help_use,
        ast.PTLetNew: proof_checker._check_proof_tlet_new,
        ast.PLet: proof_checker._check_proof_let,
        ast.PAnnot: proof_checker._check_proof_annot,
        ast.PTuple: proof_checker._check_proof_tuple,
        ast.ImpIntro: proof_checker._check_proof_imp_intro,
        ast.AllIntro: proof_checker._check_proof_all_intro,
    }

    for proof_type, handler in expected.items():
        assert proof_checker._CHECK_PROOF_HANDLERS[proof_type] is handler


def test_check_proof_dispatches_registered_handler(monkeypatch) -> None:
    proof = ast.PTrue(_meta())
    calls = []

    def fake_handler(proof_arg, env_arg):
        calls.append((proof_arg, env_arg))
        return "handled"

    monkeypatch.setitem(
        proof_checker._CHECK_PROOF_HANDLERS,
        ast.PTrue,
        fake_handler,
    )

    env = object()

    assert proof_checker.check_proof(proof, env) == "handled"
    assert calls == [(proof, env)]
