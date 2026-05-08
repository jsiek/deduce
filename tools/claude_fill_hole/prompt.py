"""System prompt + user message assembly for the hole-fill agent loop.

Two model-facing reference docs are embedded in the system prompt:

  - ``gh_pages/doc/WorkedExamples.md`` -- short proof snippets that
    demonstrate each tactic concept (one per goal-shape and per
    non-shape-keyed tactic). Models pattern-match on concrete
    examples much more reliably than they parse strategy prose,
    so this leads.

  - ``gh_pages/doc/TacticsCheatSheet.md`` -- dense reference: every
    tactic with a one-line meaning, plus a "Common pitfalls"
    section. Used as the look-up table when the worked examples
    don't cover a specific construct.

The third doc, ``CheatSheet.md``, is intentionally NOT included --
its strategy-by-goal-shape table is subsumed by the goal-shape-
indexed worked examples, and including it adds noise without
adding new information.

The two embedded docs are wrapped in XML-ish tags
(``<worked_examples>`` and ``<tactics_cheatsheet>``) so the model
can refer to them in its reasoning. Prompt caching on the Anthropic
backend amortises the cost across attempts; OpenAI-compat servers
re-tokenise each attempt (no breakpoints).

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
_WORKED_EXAMPLES = _REPO_ROOT / "gh_pages" / "doc" / "WorkedExamples.md"
_TACTICS_CHEATSHEET = _REPO_ROOT / "gh_pages" / "doc" / "TacticsCheatSheet.md"


# Single literal placeholder, replaced via ``str.replace`` rather than
# ``str.format`` so the surrounding documentation can use ``{...}``
# freely (e.g. to describe the tool's ``{ok, error}`` return shape)
# without each pair tripping a KeyError.
_MAX_ATTEMPTS_PLACEHOLDER = "__MAX_ATTEMPTS__"


SCAFFOLD = """\
You are a Deduce proof-completion agent.

Deduce is a small functional language and proof checker for teaching
logic. Source files have ``.pf`` extension; ``?`` marks an
incomplete proof (a "hole"). Your job is to fill in one hole.

You have two tools:

  - ``validate_proof(proof_text)`` -- splice ``proof_text`` into the
    source at the hole and run the checker.  Returns
    ``{ok: bool, error?: str}``.  Call this when you're ready to
    commit a complete proof.  You can call it up to __MAX_ATTEMPTS__
    times; the first valid proof wins.  Counts toward your budget.

  - ``query_goal(proof_text)`` -- splice a PARTIAL ``proof_text``
    that itself contains a ``?'' marker, and return the goal +
    in-scope givens at that ``?'' as a JSON object with ``{goal,
    givens}'' (or ``{error}'' if the splice didn't reach the
    marker).  Does NOT count toward your validate budget -- call it
    freely to inspect intermediate goals.

Use ``query_goal`` to plan multi-step proofs.  For an induction proof:
write the skeleton ``induction T case ctor1 { ? } case ctor2(n')
suppose IH: ... { ? }`` and call ``query_goal`` to see what each
``?'' has to prove.  Refine each case with progressively-smaller
holes until you can fill the whole thing, then ``validate_proof''
the complete result.

Rules:
- Emit raw Deduce text in ``proof_text``. Do not wrap it in code
  fences. Do not include English commentary in the proof itself.
- ``proof_text`` is spliced verbatim where the ``?'' was -- emit
  ONLY the proof body that fills the hole. Do NOT include the
  surrounding ``theorem``, ``proof``, or ``end`` keywords; those
  are already in the source.  A trailing ``end'' in your
  ``proof_text'' will produce a parse error ("expected a
  statement, not end") because the source already has its own.
- Keep edits to the hole only. Do not modify anything outside it.
- Prefer existing givens and the listed lemmas over postulates.
- If the goal reduces trivially (e.g. ``true``, reflexive
  equalities), the simplest valid proof is best.
"""


def _read_doc(path: Path) -> str:
    """Return the doc's contents, or an empty string if missing.

    The sidecar is expected to be invoked from a Deduce checkout
    where the docs exist; missing-file is unusual but we don't fail
    the whole run over it -- the model still has the SCAFFOLD
    instructions.
    """
    try:
        return path.read_text(encoding="utf-8")
    except OSError:
        return ""


def build_system_prompt(max_attempts: int) -> str:
    """Return the rendered system prompt as a plain string.

    Backend-agnostic.  The Anthropic backend wraps this in a
    text-block list with ``cache_control``; the OpenAI-compat
    backend uses it as the content of a leading ``system`` message.

    The prompt embeds two docs:

    - ``gh_pages/doc/WorkedExamples.md`` (concrete proof snippets)
    - ``gh_pages/doc/TacticsCheatSheet.md`` (dense tactic reference)

    Worked examples come first because models pattern-match on
    concrete code more reliably than they parse strategy prose.
    The tactics cheatsheet follows as a look-up table.
    """
    worked = _read_doc(_WORKED_EXAMPLES)
    tactics = _read_doc(_TACTICS_CHEATSHEET)

    return (
        SCAFFOLD.replace(_MAX_ATTEMPTS_PLACEHOLDER, str(max_attempts))
        + "\n\n<worked_examples>\n"
        + worked
        + "\n</worked_examples>\n\n<tactics_cheatsheet>\n"
        + tactics
        + "\n</tactics_cheatsheet>\n"
    )


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
        parts.append("Declarations in scope (same content as `.thm` files --")
        parts.append("theorem signatures, function bodies, union")
        parts.append("constructors, predicate rules, and auto-rewrite rules):")
        parts.append("```")
        for lemma in lemmas_in_scope:
            parts.append(lemma.signature)
            parts.append("")
        parts.append("```")
        parts.append("")

    if surrounding_excerpt:
        parts.append(
            "Source around the hole (for context only -- "
            "your proof_text REPLACES the `?', so do NOT echo "
            "back the surrounding `theorem'/`proof'/`end' "
            "keywords):"
        )
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
