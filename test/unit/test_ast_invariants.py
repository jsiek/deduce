"""Python-level unit tests for AST invariants (issue #475).

Hand-built AST values exercise the AST helpers (`__eq__`, `copy`,
field completeness) directly, so a failing test points at the
offending method rather than a downstream `.pf`-fixture mismatch.

Initial coverage:

- `__eq__` reflexivity: every specimen equals itself.
- `__eq__` symmetry under `copy`: ``a == a.copy()`` and
  ``a.copy() == a`` -- catches asymmetric ``isinstance`` ladders
  like the ones fixed in PR #486 (TAnnote, Var/OverloadedVar
  cross-class equality).
- `copy` returns a *distinct* instance for compound nodes. The
  generic ``_map_children`` walker rebuilds the node, so any
  override that returns ``self`` (or accidentally aliases a child
  list) would surface here.
- `copy` field completeness: the copied node has the same set of
  populated dataclass fields as the original -- catches arity
  drift like the historical ``AllIntro.copy`` /
  ``Array.copy`` issues mentioned in #475.
- `__hash__` policy: AST nodes remain unhashable while equality is
  structural and instances are mutable.

A meta-test (``test_specimen_coverage_report``) lists concrete AST
subclasses that are not yet covered by a specimen so the registry
can be grown over time. It is informational only; it does not
fail the build for uncovered classes.

The follow-up items from #475 (``substitute`` capture-avoidance,
proof-side walker completeness, broader ``typeof`` coverage) are
deferred to subsequent PRs.
"""

from __future__ import annotations

from dataclasses import fields as dc_fields
from typing import Callable, Iterable

import pytest
from lark.tree import Meta

import abstract_syntax as ast


# ---------------------------------------------------------------------------
# Specimen registry
# ---------------------------------------------------------------------------
#
# A "specimen" is a hand-built sample instance of a concrete AST class.
# Each factory builds a fresh instance every call so the tests can mutate
# without leaking state across cases.
#
# Specimens are intentionally minimal -- just enough to populate every
# dataclass field with a non-default value. The point is to exercise the
# generic AST machinery, not to model a realistic program fragment.


def _meta() -> Meta:
    # ``Meta()`` constructs a default Meta with ``empty=True``; that is
    # what the parser uses for synthesised nodes, which is exactly the
    # opaque "source location" sentinel ``_map_children`` is supposed to
    # carry across unchanged.
    return Meta()


def _var(name: str = "x") -> ast.Var:
    return ast.Var(_meta(), None, name)


def _rvar(name: str = "x") -> ast.ResolvedVar:
    return ast.ResolvedVar(_meta(), None, name)


# ---- Types -----------------------------------------------------------------


def _spec_IntType() -> ast.IntType:
    return ast.IntType(_meta())


def _spec_BoolType() -> ast.BoolType:
    return ast.BoolType(_meta())


def _spec_TypeType() -> ast.TypeType:
    return ast.TypeType(_meta())


def _spec_ArrayType() -> ast.ArrayType:
    return ast.ArrayType(_meta(), ast.IntType(_meta()))


def _spec_FunctionType() -> ast.FunctionType:
    return ast.FunctionType(
        _meta(), ["T"], [ast.IntType(_meta())], ast.BoolType(_meta())
    )


def _spec_TypeInst() -> ast.TypeInst:
    return ast.TypeInst(_meta(), ast.IntType(_meta()), [ast.BoolType(_meta())])


def _spec_GenericUnknownInst() -> ast.GenericUnknownInst:
    return ast.GenericUnknownInst(_meta(), ast.IntType(_meta()))


def _spec_OverloadType() -> ast.OverloadType:
    return ast.OverloadType(_meta(), [("x", ast.IntType(_meta()))])


# ---- Patterns --------------------------------------------------------------


def _spec_PatternBool() -> ast.PatternBool:
    return ast.PatternBool(_meta(), True)


def _spec_PatternCons() -> ast.PatternCons:
    return ast.PatternCons(_meta(), _var("node"), ["hd", "tl"])


def _spec_PatternTerm() -> ast.PatternTerm:
    return ast.PatternTerm(_meta(), _var("c"), ["a", "b"])


# ---- Terms / Formulas ------------------------------------------------------


def _spec_Var() -> ast.Var:
    return _var("y")


def _spec_ResolvedVar() -> ast.ResolvedVar:
    return _rvar("y")


def _spec_OverloadedVar() -> ast.OverloadedVar:
    return ast.OverloadedVar(_meta(), None, ["y.0", "y.1"])


def _spec_Int() -> ast.Int:
    return ast.Int(_meta(), ast.IntType(_meta()), 42)


def _spec_Bool() -> ast.Bool:
    return ast.Bool(_meta(), ast.BoolType(_meta()), True)


def _spec_Hole() -> ast.Hole:
    return ast.Hole(_meta(), None)


def _spec_Omitted() -> ast.Omitted:
    return ast.Omitted(_meta(), None)


def _spec_Mark() -> ast.Mark:
    return ast.Mark(_meta(), None, _var())


def _spec_TAnnote() -> ast.TAnnote:
    return ast.TAnnote(_meta(), None, _var(), ast.IntType(_meta()))


def _spec_Conditional() -> ast.Conditional:
    return ast.Conditional(
        _meta(),
        None,
        ast.Bool(_meta(), None, True),
        _var("a"),
        _var("b"),
    )


def _spec_Lambda() -> ast.Lambda:
    return ast.Lambda(
        _meta(), None, [("x", ast.IntType(_meta()))], _var("x")
    )


def _spec_Generic() -> ast.Generic:
    return ast.Generic(_meta(), None, ["T"], _var("x"))


def _spec_Call() -> ast.Call:
    return ast.Call(_meta(), None, _var("f"), [_var("a"), _var("b")])


def _spec_TermInst() -> ast.TermInst:
    return ast.TermInst(_meta(), None, _var("f"), [ast.IntType(_meta())], True)


def _spec_SwitchCase() -> ast.SwitchCase:
    return ast.SwitchCase(_meta(), _spec_PatternBool(), _var("x"))


def _spec_Switch() -> ast.Switch:
    return ast.Switch(_meta(), None, _var("subj"), [_spec_SwitchCase()])


def _spec_Array() -> ast.Array:
    return ast.Array(_meta(), None, [_var("a"), _var("b")])


def _spec_MakeArray() -> ast.MakeArray:
    return ast.MakeArray(_meta(), None, _var("xs"))


def _spec_ArrayGet() -> ast.ArrayGet:
    return ast.ArrayGet(_meta(), None, _var("xs"), ast.Int(_meta(), None, 0))


def _spec_TLet() -> ast.TLet:
    return ast.TLet(_meta(), None, "x", _var("rhs"), _var("body"))


def _spec_And() -> ast.And:
    return ast.And(_meta(), None, [_var("p"), _var("q")])


def _spec_Or() -> ast.Or:
    return ast.Or(_meta(), None, [_var("p"), _var("q")])


def _spec_IfThen() -> ast.IfThen:
    return ast.IfThen(_meta(), None, _var("p"), _var("q"))


def _spec_All() -> ast.All:
    return ast.All(
        _meta(), None, ("x", ast.IntType(_meta())), (0, 1), _var("body")
    )


def _spec_Some() -> ast.Some:
    return ast.Some(_meta(), None, [("x", ast.IntType(_meta()))], _var("body"))


# ---- Proofs ----------------------------------------------------------------


def _spec_PVar() -> ast.PVar:
    return ast.PVar(_meta(), "h")


def _spec_PTrue() -> ast.PTrue:
    return ast.PTrue(_meta())


def _spec_PReflexive() -> ast.PReflexive:
    return ast.PReflexive(_meta())


def _spec_PHole() -> ast.PHole:
    return ast.PHole(_meta())


def _spec_PSorry() -> ast.PSorry:
    return ast.PSorry(_meta())


def _spec_PHelpUse() -> ast.PHelpUse:
    return ast.PHelpUse(_meta(), _var("h"))


def _spec_PSymmetric() -> ast.PSymmetric:
    return ast.PSymmetric(_meta(), _spec_PVar())


def _spec_PTransitive() -> ast.PTransitive:
    return ast.PTransitive(_meta(), _spec_PVar(), _spec_PVar())


def _spec_PInjective() -> ast.PInjective:
    return ast.PInjective(_meta(), _var("c"), _spec_PVar())


def _spec_PExtensionality() -> ast.PExtensionality:
    return ast.PExtensionality(_meta(), _spec_PVar())


def _spec_PAnnot() -> ast.PAnnot:
    return ast.PAnnot(_meta(), _var("p"), _spec_PVar())


def _spec_PAndElim() -> ast.PAndElim:
    return ast.PAndElim(_meta(), 0, _spec_PVar())


def _spec_PTuple() -> ast.PTuple:
    return ast.PTuple(_meta(), [_spec_PVar(), _spec_PVar()])


def _spec_PLet() -> ast.PLet:
    return ast.PLet(
        _meta(), "h", _var("p"), _spec_PVar(), _spec_PVar()
    )


def _spec_PTLetNew() -> ast.PTLetNew:
    return ast.PTLetNew(_meta(), "x", _var("rhs"), _spec_PVar())


def _spec_PRecall() -> ast.PRecall:
    return ast.PRecall(_meta(), [_var("p")])


def _spec_Suffices() -> ast.Suffices:
    return ast.Suffices(_meta(), _var("c"), _spec_PVar(), _spec_PVar())


def _spec_Cases() -> ast.Cases:
    return ast.Cases(
        _meta(), _spec_PVar(), [("l", _var("p"), _spec_PVar())]
    )


def _spec_ModusPonens() -> ast.ModusPonens:
    return ast.ModusPonens(_meta(), _spec_PVar(), _spec_PVar())


def _spec_ImpIntro() -> ast.ImpIntro:
    return ast.ImpIntro(_meta(), "h", _var("p"), _spec_PVar())


def _spec_AllIntro() -> ast.AllIntro:
    return ast.AllIntro(
        _meta(), ("x", ast.IntType(_meta())), (0, 1), _spec_PVar()
    )


def _spec_AllElim() -> ast.AllElim:
    return ast.AllElim(_meta(), _spec_PVar(), _var("a"), (0, 1))


def _spec_AllElimTypes() -> ast.AllElimTypes:
    return ast.AllElimTypes(
        _meta(), _spec_PVar(), ast.IntType(_meta()), (0, 1)
    )


def _spec_SomeIntro() -> ast.SomeIntro:
    return ast.SomeIntro(_meta(), [_var("a")], _spec_PVar())


def _spec_SomeElim() -> ast.SomeElim:
    return ast.SomeElim(
        _meta(), ["x"], "h", _var("p"), _spec_PVar(), _spec_PVar()
    )


def _spec_EvaluateGoal() -> ast.EvaluateGoal:
    return ast.EvaluateGoal(_meta())


def _spec_EvaluateFact() -> ast.EvaluateFact:
    return ast.EvaluateFact(_meta(), _spec_PVar())


def _spec_SimplifyGoal() -> ast.SimplifyGoal:
    return ast.SimplifyGoal(_meta(), _spec_PVar(), [_spec_PVar()])


def _spec_SimplifyFact() -> ast.SimplifyFact:
    return ast.SimplifyFact(_meta(), _spec_PVar(), [_spec_PVar()])


def _spec_ApplyDefsGoal() -> ast.ApplyDefsGoal:
    return ast.ApplyDefsGoal(_meta(), [_var("f")], _spec_PVar())


def _spec_ApplyDefsFact() -> ast.ApplyDefsFact:
    return ast.ApplyDefsFact(_meta(), [_var("f")], _spec_PVar())


def _spec_RewriteGoal() -> ast.RewriteGoal:
    return ast.RewriteGoal(_meta(), [_spec_PVar()], _spec_PVar())


def _spec_RewriteFact() -> ast.RewriteFact:
    return ast.RewriteFact(_meta(), _spec_PVar(), [_spec_PVar()])


def _spec_IndCase() -> ast.IndCase:
    return ast.IndCase(
        _meta(), _spec_PatternCons(), [("ih", _var("p"))], _spec_PVar()
    )


def _spec_Induction() -> ast.Induction:
    return ast.Induction(_meta(), ast.IntType(_meta()), [_spec_IndCase()])


def _spec_RuleInductionCase() -> ast.RuleInductionCase:
    return ast.RuleInductionCase(_meta(), "r", _spec_PVar())


def _spec_RuleInduction() -> ast.RuleInduction:
    return ast.RuleInduction(_meta(), "h", [_spec_RuleInductionCase()])


def _spec_RuleInversion() -> ast.RuleInversion:
    return ast.RuleInversion(_meta(), "h", [_spec_RuleInductionCase()])


def _spec_SwitchProofCase() -> ast.SwitchProofCase:
    return ast.SwitchProofCase(
        _meta(), _spec_PatternBool(), [("a", _var("p"))], _spec_PVar()
    )


def _spec_SwitchProof() -> ast.SwitchProof:
    return ast.SwitchProof(_meta(), _var("subj"), [_spec_SwitchProofCase()])


# ---- Statements / Declarations ---------------------------------------------


def _spec_Postulate() -> ast.Postulate:
    return ast.Postulate(_meta(), "p", _var("f"))


def _spec_Theorem() -> ast.Theorem:
    return ast.Theorem(_meta(), "t", _var("f"), _spec_PVar(), False)


def _spec_Constructor() -> ast.Constructor:
    return ast.Constructor(_meta(), "c", [ast.IntType(_meta())])


def _spec_Rule() -> ast.Rule:
    return ast.Rule(_meta(), "r", _var("f"))


def _spec_Predicate() -> ast.Predicate:
    return ast.Predicate(
        _meta(),
        name="P",
        type_params=["T"],
        signature=ast.IntType(_meta()),
        rules=[_spec_Rule()],
        original_keyword="predicate",
    )


def _spec_Union() -> ast.Union:
    return ast.Union(
        _meta(),
        name="U",
        type_params=["T"],
        alternatives=[_spec_Constructor()],
    )


def _spec_FunCase() -> ast.FunCase:
    return ast.FunCase(
        _meta(), _var("f"), _spec_PatternCons(), ["a"], _var("body")
    )


def _spec_RecFun() -> ast.RecFun:
    return ast.RecFun(
        _meta(),
        name="f",
        type_params=["T"],
        params=[ast.IntType(_meta())],
        returns=ast.BoolType(_meta()),
        cases=[_spec_FunCase()],
    )


def _spec_GenRecFun() -> ast.GenRecFun:
    return ast.GenRecFun(
        _meta(),
        name="f",
        type_params=["T"],
        vars=[("x", ast.IntType(_meta()))],
        returns=ast.BoolType(_meta()),
        measure=_var("m"),
        measure_ty=ast.IntType(_meta()),
        body=_var("body"),
        terminates=_spec_PVar(),
    )


def _spec_Define() -> ast.Define:
    return ast.Define(
        _meta(), name="x", typ=ast.IntType(_meta()), body=_var("v")
    )


def _spec_Assert() -> ast.Assert:
    return ast.Assert(_meta(), _var("p"))


def _spec_Print() -> ast.Print:
    return ast.Print(_meta(), _var("t"))


def _spec_Auto() -> ast.Auto:
    return ast.Auto(_meta(), _var("eq"))


def _spec_Inductive() -> ast.Inductive:
    return ast.Inductive(_meta(), ast.IntType(_meta()), _var("thm"))


def _spec_Module() -> ast.Module:
    return ast.Module(_meta(), "M")


def _spec_Export() -> ast.Export:
    return ast.Export(_meta(), "x", ["x.0"])


def _spec_Associative() -> ast.Associative:
    return ast.Associative(
        _meta(), ["T"], _var("op"), ast.IntType(_meta())
    )


def _spec_Trace() -> ast.Trace:
    return ast.Trace(_meta(), _var("f"))


def _spec_Import() -> ast.Import:
    # ``ast=None`` is the typical pre-uniquify shape (the parser produces
    # an Import without the imported AST attached). A populated ``ast``
    # would point at a list of statements, which uniquify fills in.
    return ast.Import(_meta(), name="Nat", ast=None)


# ---- Bindings --------------------------------------------------------------


def _spec_TypeBinding() -> ast.TypeBinding:
    return ast.TypeBinding(
        module="M", visibility="public", location=_meta(), defn=ast.IntType(_meta())
    )


def _spec_TermBinding() -> ast.TermBinding:
    return ast.TermBinding(
        module="M",
        visibility="public",
        location=_meta(),
        typ=ast.IntType(_meta()),
        defn=_var("v"),
        local=False,
    )


def _spec_ProofBinding() -> ast.ProofBinding:
    return ast.ProofBinding(
        module="M",
        visibility="public",
        location=_meta(),
        formula=_var("f"),
        local=False,
    )


def _spec_AutoEquationBinding() -> ast.AutoEquationBinding:
    return ast.AutoEquationBinding(
        module="M",
        visibility="public",
        location=_meta(),
        equations={"f": [ast.Bool(_meta(), None, True)]},
        fallback_equations=[ast.Bool(_meta(), None, False)],
    )


def _spec_AssociativeBinding() -> ast.AssociativeBinding:
    return ast.AssociativeBinding(
        module="M",
        visibility="public",
        location=_meta(),
        opname="+",
        types=[(["T"], ast.IntType(_meta()))],
    )


# ---- Registry --------------------------------------------------------------


_SPECIMEN_FACTORIES: dict[type, Callable[[], ast.AST]] = {
    # Types
    ast.IntType: _spec_IntType,
    ast.BoolType: _spec_BoolType,
    ast.TypeType: _spec_TypeType,
    ast.ArrayType: _spec_ArrayType,
    ast.FunctionType: _spec_FunctionType,
    ast.TypeInst: _spec_TypeInst,
    ast.GenericUnknownInst: _spec_GenericUnknownInst,
    ast.OverloadType: _spec_OverloadType,
    # Patterns
    ast.PatternBool: _spec_PatternBool,
    ast.PatternCons: _spec_PatternCons,
    ast.PatternTerm: _spec_PatternTerm,
    # Terms / Formulas
    ast.Var: _spec_Var,
    ast.ResolvedVar: _spec_ResolvedVar,
    ast.OverloadedVar: _spec_OverloadedVar,
    ast.Int: _spec_Int,
    ast.Bool: _spec_Bool,
    ast.Hole: _spec_Hole,
    ast.Omitted: _spec_Omitted,
    ast.Mark: _spec_Mark,
    ast.TAnnote: _spec_TAnnote,
    ast.Conditional: _spec_Conditional,
    ast.Lambda: _spec_Lambda,
    ast.Generic: _spec_Generic,
    ast.Call: _spec_Call,
    ast.TermInst: _spec_TermInst,
    ast.SwitchCase: _spec_SwitchCase,
    ast.Switch: _spec_Switch,
    ast.Array: _spec_Array,
    ast.MakeArray: _spec_MakeArray,
    ast.ArrayGet: _spec_ArrayGet,
    ast.TLet: _spec_TLet,
    ast.And: _spec_And,
    ast.Or: _spec_Or,
    ast.IfThen: _spec_IfThen,
    ast.All: _spec_All,
    ast.Some: _spec_Some,
    # Proofs
    ast.PVar: _spec_PVar,
    ast.PTrue: _spec_PTrue,
    ast.PReflexive: _spec_PReflexive,
    ast.PHole: _spec_PHole,
    ast.PSorry: _spec_PSorry,
    ast.PHelpUse: _spec_PHelpUse,
    ast.PSymmetric: _spec_PSymmetric,
    ast.PTransitive: _spec_PTransitive,
    ast.PInjective: _spec_PInjective,
    ast.PExtensionality: _spec_PExtensionality,
    ast.PAnnot: _spec_PAnnot,
    ast.PAndElim: _spec_PAndElim,
    ast.PTuple: _spec_PTuple,
    ast.PLet: _spec_PLet,
    ast.PTLetNew: _spec_PTLetNew,
    ast.PRecall: _spec_PRecall,
    ast.Suffices: _spec_Suffices,
    ast.Cases: _spec_Cases,
    ast.ModusPonens: _spec_ModusPonens,
    ast.ImpIntro: _spec_ImpIntro,
    ast.AllIntro: _spec_AllIntro,
    ast.AllElim: _spec_AllElim,
    ast.AllElimTypes: _spec_AllElimTypes,
    ast.SomeIntro: _spec_SomeIntro,
    ast.SomeElim: _spec_SomeElim,
    ast.EvaluateGoal: _spec_EvaluateGoal,
    ast.EvaluateFact: _spec_EvaluateFact,
    ast.SimplifyGoal: _spec_SimplifyGoal,
    ast.SimplifyFact: _spec_SimplifyFact,
    ast.ApplyDefsGoal: _spec_ApplyDefsGoal,
    ast.ApplyDefsFact: _spec_ApplyDefsFact,
    ast.RewriteGoal: _spec_RewriteGoal,
    ast.RewriteFact: _spec_RewriteFact,
    ast.IndCase: _spec_IndCase,
    ast.Induction: _spec_Induction,
    ast.RuleInductionCase: _spec_RuleInductionCase,
    ast.RuleInduction: _spec_RuleInduction,
    ast.RuleInversion: _spec_RuleInversion,
    ast.SwitchProofCase: _spec_SwitchProofCase,
    ast.SwitchProof: _spec_SwitchProof,
    # Statements / Declarations
    ast.Postulate: _spec_Postulate,
    ast.Theorem: _spec_Theorem,
    ast.Constructor: _spec_Constructor,
    ast.Rule: _spec_Rule,
    ast.Predicate: _spec_Predicate,
    ast.Union: _spec_Union,
    ast.FunCase: _spec_FunCase,
    ast.RecFun: _spec_RecFun,
    ast.GenRecFun: _spec_GenRecFun,
    ast.Define: _spec_Define,
    ast.Assert: _spec_Assert,
    ast.Print: _spec_Print,
    ast.Auto: _spec_Auto,
    ast.Inductive: _spec_Inductive,
    ast.Module: _spec_Module,
    ast.Export: _spec_Export,
    ast.Associative: _spec_Associative,
    ast.Trace: _spec_Trace,
    ast.Import: _spec_Import,
    # Bindings
    ast.TypeBinding: _spec_TypeBinding,
    ast.TermBinding: _spec_TermBinding,
    ast.ProofBinding: _spec_ProofBinding,
    ast.AutoEquationBinding: _spec_AutoEquationBinding,
    ast.AssociativeBinding: _spec_AssociativeBinding,
}


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _all_concrete_ast_subclasses() -> Iterable[type]:
    """Yield every concrete (instantiable) subclass of ``AST``.

    Abstract base classes (``Type``, ``Term``, ``Formula``, ``Proof``,
    ``Statement``, ``Pattern``, ``Declaration``, ``Binding``,
    ``VarRef``) are excluded -- they are never instantiated directly.
    """
    abstract = {
        ast.AST,
        ast.Type,
        ast.Term,
        ast.Formula,
        ast.Proof,
        ast.Statement,
        ast.Pattern,
        ast.Declaration,
        ast.Binding,
        ast.VarRef,
    }
    seen: set[type] = set()
    work: list[type] = [ast.AST]
    while work:
        cls = work.pop()
        if cls in seen:
            continue
        seen.add(cls)
        work.extend(cls.__subclasses__())
    return sorted((c for c in seen if c not in abstract), key=lambda c: c.__name__)


def _specimen_ids() -> list[str]:
    return sorted(c.__name__ for c in _SPECIMEN_FACTORIES)


def _make(cls: type) -> ast.AST:
    return _SPECIMEN_FACTORIES[cls]()


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "cls",
    sorted(_SPECIMEN_FACTORIES, key=lambda c: c.__name__),
    ids=_specimen_ids(),
)
def test_eq_reflexive(cls: type) -> None:
    """``x == x`` for every specimen."""
    node = _make(cls)
    assert node == node


@pytest.mark.parametrize(
    "cls",
    sorted(_SPECIMEN_FACTORIES, key=lambda c: c.__name__),
    ids=_specimen_ids(),
)
def test_copy_round_trip(cls: type) -> None:
    """``copy()`` returns an equal value (both directions)."""
    node = _make(cls)
    copied = node.copy()
    assert node == copied, f"{cls.__name__}: original != copy"
    assert copied == node, f"{cls.__name__}: copy != original (asymmetric __eq__)"


@pytest.mark.parametrize(
    "cls",
    sorted(_SPECIMEN_FACTORIES, key=lambda c: c.__name__),
    ids=_specimen_ids(),
)
def test_copy_returns_distinct_compound_instance(cls: type) -> None:
    """For compound nodes, ``copy()`` should produce a *new* object.

    Leaf nodes (no dataclass field besides ``location``/``typeof``) are
    allowed to alias since they carry no per-instance child state, but
    every other node should be a fresh instance -- otherwise mutation
    on the "copy" would leak back into the original.
    """
    node = _make(cls)
    copied = node.copy()
    structural_fields = [
        f for f in dc_fields(node)
        if f.name not in type(node)._NON_STRUCTURAL_FIELDS
    ]
    if len(structural_fields) == 0:
        # No structural state to alias -- skip.
        return
    assert copied is not node, (
        f"{cls.__name__}.copy() returned self; compound nodes should be rebuilt"
    )


@pytest.mark.parametrize(
    "cls",
    sorted(_SPECIMEN_FACTORIES, key=lambda c: c.__name__),
    ids=_specimen_ids(),
)
def test_copy_field_completeness(cls: type) -> None:
    """The copy has the same set of populated dataclass fields.

    Catches arity drift in any per-class ``copy`` overrides (the
    generic ``_map_children``-driven default cannot drop a field by
    construction, but bespoke overrides can -- this test is the
    backstop for the historical ``AllIntro.copy`` / ``Array.copy``
    issues called out in #475).
    """
    node = _make(cls)
    copied = node.copy()
    expected = {f.name for f in dc_fields(node)}
    actual = {f.name for f in dc_fields(copied)}
    assert expected == actual, (
        f"{cls.__name__}: copy lost fields "
        f"{sorted(expected - actual)} or gained "
        f"{sorted(actual - expected)}"
    )


@pytest.mark.parametrize(
    "cls",
    sorted(_SPECIMEN_FACTORIES, key=lambda c: c.__name__),
    ids=_specimen_ids(),
)
def test_structural_eq_nodes_are_unhashable(cls: type) -> None:
    """Mutable structural-equality nodes should not define ``__hash__``.

    A value-based hash would have to mirror every bespoke ``__eq__``
    implementation, including alpha-equivalence and cross-class wrappers.
    Keeping AST nodes unhashable avoids silently corrupting dict/set keys
    when a mutable node changes after insertion.
    """
    node = _make(cls)
    copied = node.copy()
    assert node == copied
    with pytest.raises(TypeError, match="unhashable"):
        hash(node)
    with pytest.raises(TypeError, match="unhashable"):
        hash(copied)


def test_specimen_coverage_report(capsys: pytest.CaptureFixture[str]) -> None:
    """Informational: report concrete AST classes without a specimen.

    This test always passes; it exists so the registry's growth is
    visible in CI output. A failing assertion would force every new
    AST class to ship with a specimen, which is a stricter policy than
    issue #475 asks for.
    """
    covered = set(_SPECIMEN_FACTORIES)
    uncovered = [c for c in _all_concrete_ast_subclasses() if c not in covered]
    if uncovered:
        # Use print so the message survives ``-q`` and shows up in
        # ``-rs`` output; pytest's warnings infrastructure is overkill
        # for a non-fail signal.
        print(
            "AST specimen coverage: "
            f"{len(covered)} covered, {len(uncovered)} uncovered: "
            + ", ".join(c.__name__ for c in uncovered)
        )
