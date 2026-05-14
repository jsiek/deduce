"""Tests for prompt.py.

Regression-focused: the original SCAFFOLD body contained the literal
substring ``{ok: bool, error?: str}`` describing the validate_proof
tool's return shape, and the system-prompt builder used
``str.format`` -- which threw ``KeyError: 'ok'`` at runtime.  These
tests pin the actual production call (``build_system_prompt`` with
a small int) and the substitution behaviour.
"""

from __future__ import annotations


from tools.claude_fill_hole.prompt import (
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
    # The substitution lands; tolerate any whitespace between number
    # and the next word (the SCAFFOLD wraps mid-sentence).
    assert "up to 7" in out
    # The placeholder sentinel itself shouldn't survive into output.
    assert "__MAX_ATTEMPTS__" not in out


def test_build_system_prompt_embeds_docs_when_available():
    """The worked-examples doc and tactics cheatsheet should both be
    inlined under recognisable XML-ish markers so a downstream
    consumer can find them.  CheatSheet.md was deliberately dropped
    -- its strategy-by-goal-shape content is subsumed by the
    goal-shape-organised worked examples."""
    out = build_system_prompt(max_attempts=3)
    assert "<worked_examples>" in out
    assert "</worked_examples>" in out
    assert "<tactics_cheatsheet>" in out
    assert "</tactics_cheatsheet>" in out
    # The standalone strategy cheatsheet is intentionally NOT embedded.
    assert "<cheatsheet>" not in out


def test_worked_examples_appear_before_tactics_cheatsheet():
    """Worked examples lead because models pattern-match on concrete
    code more reliably than they read strategy prose; the tactics
    cheatsheet is the lookup-table fallback."""
    out = build_system_prompt(max_attempts=3)
    we_pos = out.index("<worked_examples>")
    tc_pos = out.index("<tactics_cheatsheet>")
    assert we_pos < tc_pos


def test_build_user_message_shape():
    out = build_user_message(
        goal="P = P",
        givens=(Given(label="pP", formula="P"),),
        lemmas_in_scope=(
            LemmaInfo(name="h", kind="lemma", signature="h: true"),
            LemmaInfo(
                name="add",
                kind="function",
                signature=(
                    "recursive add(Nat,Nat) -> Nat{\n"
                    "  add(zero, m) = m\n"
                    "  add(suc(n), m) = suc(add(n, m))\n"
                    "}"
                ),
            ),
        ),
        surrounding_excerpt="  ?",
    )
    assert "Goal:" in out
    assert "P = P" in out
    assert "pP: P" in out
    # New format: each declaration's signature is emitted raw
    # (matching the .thm file format), not prefixed with `[kind]`.
    assert "h: true" in out
    assert "recursive add(Nat,Nat) -> Nat{" in out
    assert "add(zero, m) = m" in out
    assert "  ?" in out


def test_system_prompt_warns_not_to_fill_neighbor_holes():
    out = build_system_prompt(max_attempts=5)
    assert "<<<TARGET_HOLE>>>?" in out
    assert "Other ``?`` holes" in out
    assert "valid" in out
    assert "``proof_text``" in out
    assert "exactly ``.``" in out


def test_slice_around_hole_returns_context():
    content = "line0\nline1\nline2\nline3\nline4\nline5\n"
    # Hole at offset 12 (start of "line2") — context_lines defaults to 15
    # so the whole file fits.
    out = slice_around_hole(content, 12, 13)
    assert "line0" in out
    assert "line5" in out
    assert "<<<TARGET_HOLE>>>l<<<END_TARGET_HOLE>>>ine2" in out


def test_slice_around_hole_marks_only_target_question_mark():
    content = (
        "theorem t1: true\n"
        "proof\n"
        "  ?\n"
        "end\n"
        "\n"
        "theorem t2: true\n"
        "proof\n"
        "  ?\n"
        "end\n"
        "\n"
        "theorem t3: true\n"
        "proof\n"
        "  ?\n"
        "end\n"
    )
    target = content.rindex("?")
    out = slice_around_hole(content, target, target + 1)
    assert out.count("<<<TARGET_HOLE>>>") == 1
    assert out.count("<<<END_TARGET_HOLE>>>") == 1
    assert out.count("?") == 3
    assert "<<<TARGET_HOLE>>>?<<<END_TARGET_HOLE>>>" in out


def test_slice_around_hole_empty_content():
    assert slice_around_hole("", 0, 1) == ""
