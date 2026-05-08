"""Tests for prompt.py.

Regression-focused: the original SCAFFOLD body contained the literal
substring ``{ok: bool, error?: str}`` describing the validate_proof
tool's return shape, and the system-prompt builder used
``str.format`` -- which threw ``KeyError: 'ok'`` at runtime.  These
tests pin the actual production call (``build_system_prompt`` with
a small int) and the substitution behaviour.
"""

from __future__ import annotations

import pytest

from tools.claude_fill_hole.prompt import (
    SCAFFOLD,
    build_system_prompt,
    build_user_message,
    slice_around_hole,
)
from tools.claude_fill_hole.schema import Given, LemmaInfo


def test_build_system_prompt_does_not_raise_on_braces_in_scaffold():
    """The original SCAFFOLD has ``{ok: bool, error?: str}`` describing
    the validate_proof tool's return shape; under ``str.format`` this
    threw ``KeyError: 'ok'``.  Pinning the call so a future SCAFFOLD
    edit reintroducing ``str.format`` (or unescaped braces) breaks
    here, not in production."""
    out = build_system_prompt(max_attempts=5)
    assert isinstance(out, str)
    assert "{ok: bool, error?: str}" in out


def test_build_system_prompt_substitutes_max_attempts():
    out = build_system_prompt(max_attempts=7)
    assert "up to 7 times" in out
    # The placeholder sentinel itself shouldn't survive into output.
    assert "__MAX_ATTEMPTS__" not in out


def test_build_system_prompt_embeds_cheatsheets_when_available():
    """Both cheatsheets should be inlined under recognisable XML-ish
    markers so a downstream consumer can find them."""
    out = build_system_prompt(max_attempts=3)
    assert "<tactics_cheatsheet>" in out
    assert "</tactics_cheatsheet>" in out
    assert "<cheatsheet>" in out
    assert "</cheatsheet>" in out


def test_build_user_message_shape():
    out = build_user_message(
        goal="P = P",
        givens=(Given(label="pP", formula="P"),),
        lemmas_in_scope=(
            LemmaInfo(name="h", kind="lemma", signature="h: true"),
        ),
        surrounding_excerpt="  ?",
    )
    assert "Goal:" in out
    assert "P = P" in out
    assert "pP: P" in out
    # Lemma section format: "[<kind>] <signature>"
    assert "[lemma] h: true" in out
    assert "  ?" in out


def test_slice_around_hole_returns_context():
    content = "line0\nline1\nline2\nline3\nline4\nline5\n"
    # Hole at offset 12 (start of "line2") — context_lines defaults to 15
    # so the whole file fits.
    out = slice_around_hole(content, 12, 13)
    assert "line0" in out
    assert "line5" in out


def test_slice_around_hole_empty_content():
    assert slice_around_hole("", 0, 1) == ""
