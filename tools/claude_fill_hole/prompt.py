"""System prompt + user message assembly for the hole-fill agent loop.

Two cheatsheet files (``gh_pages/doc/TacticsCheatSheet.md`` and
``gh_pages/doc/CheatSheet.md``) carry most of the model-facing
context. They are embedded in the system prompt with prompt
caching enabled, so the cost of sending them is paid once per
5-minute window rather than once per attempt.

The user message carries the per-request bits: the goal, the
givens, the lemmas in scope, and a small excerpt of the source
around the hole.
"""

from __future__ import annotations

from pathlib import Path
from typing import Sequence

from .schema import Given, LemmaInfo


# Repo root is two parents up from this file: tools/claude_fill_hole/prompt.py
# -> tools/claude_fill_hole/ -> tools/ -> <repo>/.
_REPO_ROOT = Path(__file__).resolve().parents[2]
_TACTICS_CHEATSHEET = _REPO_ROOT / "gh_pages" / "doc" / "TacticsCheatSheet.md"
_CHEATSHEET = _REPO_ROOT / "gh_pages" / "doc" / "CheatSheet.md"


SCAFFOLD = """\
You are a Deduce proof-completion agent.

Deduce is a small functional language and proof checker for teaching
logic. Source files have ``.pf`` extension; ``?`` marks an
incomplete proof (a "hole"). Your job is to fill in one hole.

You have one tool: ``validate_proof(proof_text)``. It splices
``proof_text`` into the source at the hole's range, runs the
checker, and returns ``{ok: bool, error?: str}``. You can call it
up to {max_attempts} times; the first valid proof wins. After each
failed attempt, the error message comes back to you and you can
refine.

Rules:
- Emit raw Deduce text in ``proof_text``. Do not wrap it in code
  fences. Do not include English commentary in the proof itself.
- Keep edits to the hole only. Do not modify anything outside it.
- Prefer existing givens and the listed lemmas over postulates.
- If the goal reduces trivially (e.g. ``true``, reflexive
  equalities), the simplest valid proof is best.
"""


def _read_cheatsheet(path: Path) -> str:
    """Return the cheatsheet's contents, or an empty string if missing.

    The sidecar is expected to be invoked from a Deduce checkout
    where the cheatsheets exist; missing-file is unusual but we
    don't fail the whole run over it -- the model still has the
    SCAFFOLD instructions.
    """
    try:
        return path.read_text(encoding="utf-8")
    except OSError:
        return ""


def build_system_prompt(max_attempts: int) -> list[dict]:
    """Return the system block for ``messages.create``, with prompt
    caching enabled on the cheatsheet content.

    Render order in the API is ``tools`` -> ``system`` -> ``messages``;
    putting the breakpoint on the last system block caches both the
    tool definition and the cheatsheets together. Subsequent
    attempts on the same hole pay only for the per-attempt
    tool-result chain.
    """
    tactics = _read_cheatsheet(_TACTICS_CHEATSHEET)
    cheats = _read_cheatsheet(_CHEATSHEET)

    body = (
        SCAFFOLD.format(max_attempts=max_attempts)
        + "\n\n<tactics_cheatsheet>\n"
        + tactics
        + "\n</tactics_cheatsheet>\n\n<cheatsheet>\n"
        + cheats
        + "\n</cheatsheet>\n"
    )
    return [
        {
            "type": "text",
            "text": body,
            "cache_control": {"type": "ephemeral"},
        }
    ]


def build_user_message(
    goal: str,
    givens: Sequence[Given],
    lemmas_in_scope: Sequence[LemmaInfo],
    surrounding_excerpt: str,
) -> str:
    """Assemble the per-request user message.

    Compact text format -- the model parses it well enough without
    XML or JSON, and saves tokens. Lemmas are listed by name +
    signature so the model can pick by name without us having to
    serialize their proofs.
    """
    parts: list[str] = []

    parts.append("Goal:")
    parts.append(f"  {goal}")
    parts.append("")

    if givens:
        parts.append("Givens:")
        for g in givens:
            label = g.label or "_"
            parts.append(f"  {label}: {g.formula}")
        parts.append("")
    else:
        parts.append("Givens: (none)")
        parts.append("")

    if lemmas_in_scope:
        parts.append("Lemmas in scope:")
        for lemma in lemmas_in_scope:
            parts.append(f"  [{lemma.kind}] {lemma.signature}")
        parts.append("")

    if surrounding_excerpt:
        parts.append("Source around the hole:")
        parts.append("```")
        parts.append(surrounding_excerpt)
        parts.append("```")
        parts.append("")

    parts.append(
        "Call ``validate_proof`` with a candidate. If it fails, "
        "read the error and try again. First valid proof wins."
    )

    return "\n".join(parts)


def slice_around_hole(
    content: str,
    hole_start_offset: int,
    hole_end_offset: int,
    context_lines: int = 15,
) -> str:
    """Return ~``context_lines`` lines on each side of the hole.

    Used to populate ``surrounding_excerpt`` when the request didn't
    include one. The excerpt is for the model's situational
    awareness only; the splice itself uses the hole's exact range
    from the request.
    """
    if not content:
        return ""

    # Find the line containing each offset.
    lines = content.splitlines(keepends=True)
    cumulative = 0
    line_starts: list[int] = []
    for line in lines:
        line_starts.append(cumulative)
        cumulative += len(line)
    line_starts.append(cumulative)  # sentinel for past-EOF offsets

    def _line_for_offset(offset: int) -> int:
        # Linear search is fine for the kind of files the user is
        # editing; sources rarely exceed a few thousand lines.
        for i in range(len(line_starts) - 1):
            if line_starts[i] <= offset < line_starts[i + 1]:
                return i
        return len(lines) - 1

    start_line = _line_for_offset(hole_start_offset)
    end_line = _line_for_offset(max(hole_end_offset - 1, hole_start_offset))

    first = max(0, start_line - context_lines)
    last = min(len(lines), end_line + context_lines + 1)
    return "".join(lines[first:last]).rstrip("\n")
