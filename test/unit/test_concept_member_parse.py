"""Both parsers read `@C<τ>.m` as a concept member (#1264), and only that:
a field access on any other instantiated term is ordinary field access,
gated behind --experimental-imperative. The LALR parser used to crash
with an AttributeError on such terms (Codex review on #1274)."""

from pathlib import Path

import pytest

import parser as lalr_parser
import rec_desc_parser
from abstract_syntax import ConceptMember, Define
from error import ParseError

PARSERS = [lalr_parser, rec_desc_parser]


def _parse_define(parser_module, term):
    parser_module.set_deduce_directory(str(Path.cwd()))
    parser_module.set_filename("<concept-member-parse-test>")
    parser_module.init_parser()
    ast = parser_module.parse(f"define y = {term}\n")
    return next(stmt for stmt in ast if isinstance(stmt, Define)).body


@pytest.mark.parametrize("parser_module", PARSERS)
def test_concept_member(parser_module):
    member = _parse_define(parser_module, "@Monoid<T>.zero")
    assert isinstance(member, ConceptMember)
    assert member.ref.concept == "Monoid"
    assert member.member == "zero"


@pytest.mark.parametrize("parser_module", PARSERS)
def test_field_access_on_other_instantiation_is_gated(parser_module):
    with pytest.raises(ParseError, match="experimental imperative"):
        _parse_define(parser_module, "@(f(true))<bool>.x")
