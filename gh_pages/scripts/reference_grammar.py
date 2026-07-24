#!/usr/bin/env python3
"""Check strict Reference.md grammar fragments against Deduce.lark.

Reference.md and ImperativeReference.md contain many small, user-facing
syntax snippets. Only fenced blocks marked ``deduce-grammar`` are part of
this strict check; unmarked blocks may stay simplified while they are
migrated.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
import sys


REPO_ROOT = Path(__file__).resolve().parents[2]
REFERENCE_MDS = (
    REPO_ROOT / "gh_pages" / "doc" / "Reference.md",
    REPO_ROOT / "gh_pages" / "doc" / "ImperativeReference.md",
)
DEDUCE_LARK = REPO_ROOT / "Deduce.lark"

RULE_RE = re.compile(r"^\s*\??([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(.*)$")
ALT_RE = re.compile(r"^\s*\|\s*(.*)$")
DOC_RULE_RE = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s*::=\s*(.*)$")
DOC_ALT_RE = re.compile(r"^\s*\|\s*(.*)$")
FENCE_RE = re.compile(r"^```(?P<info>.*)$")

TOKEN_ALIASES = {
    "identifier": "IDENT",
    "identifier_list": "identifier_list",
    "natural_number": "NAT",
    "number": "INT",
    "unsigned_integer": "INT",
}
PASSTHROUGH_RULES = {"atomic_type"}
# Many Reference entries document one syntax form at a time. For these
# categories, every documented alternative must exist in Deduce.lark, but the
# entry does not have to repeat the full rule.
SUBSET_RULES = {
    "additive_term",
    "atomic_term",
    "atomic_proof",
    "conclusion",
    "comparison_term",
    "equality_term",
    "iff_term",
    "logical_term",
    "multiplicative_term",
    "proof_stmt",
    "statement",
    "type",
    "visibility",
}


@dataclass(frozen=True)
class GrammarBlock:
    line: int
    productions: dict[str, set[str]]


def strip_comment(line: str) -> str:
    quote: str | None = None
    i = 0
    while i < len(line):
        ch = line[i]
        if ch in {'"', "'"}:
            quote = None if quote == ch else ch if quote is None else quote
        elif ch == "/" and i + 1 < len(line) and line[i + 1] == "/" and quote is None:
            return line[:i]
        i += 1
    return line


def normalize_rhs(rhs: str) -> str:
    rhs = strip_comment(rhs).strip()
    if rhs == "ε":
        rhs = ""
    rhs = re.sub(r"\s*->\s*[A-Za-z_][A-Za-z0-9_]*\s*$", "", rhs).strip()
    rhs = rhs.replace("'", '"')
    for old, new in TOKEN_ALIASES.items():
        rhs = re.sub(rf"\b{re.escape(old)}\b", new, rhs)
    rhs = re.sub(r"\s+", " ", rhs)
    return rhs


def parse_lark_rules(path: Path) -> dict[str, set[str]]:
    rules: dict[str, set[str]] = {}
    current: str | None = None

    for raw in path.read_text(encoding="utf-8").splitlines():
        line = strip_comment(raw).rstrip()
        if not line.strip() or line.lstrip().startswith("%"):
            continue
        match = RULE_RE.match(line)
        if match:
            current = match.group(1)
            if current.isupper():
                current = None
                continue
            rhs = normalize_rhs(match.group(2))
            rules.setdefault(current, set()).add(rhs)
            continue
        match = ALT_RE.match(line)
        if match and current is not None:
            rhs = normalize_rhs(match.group(1))
            rules.setdefault(current, set()).add(rhs)

    return rules


def expand_passthrough_alternatives(rules: dict[str, set[str]]) -> dict[str, set[str]]:
    """Inline alternatives that are exactly another rule name.

    The public reference often presents helper rules such as ``atomic_type`` as
    alternatives of the user-facing ``type`` nonterminal. Deduce.lark keeps
    those helper rules separate for precedence and AST construction.
    """
    expanded: dict[str, set[str]] = {}
    rule_names = set(rules)
    for name, alternatives in rules.items():
        result: set[str] = set()
        pending = list(alternatives)
        seen: set[str] = set()
        while pending:
            alt = pending.pop()
            if alt in seen:
                continue
            seen.add(alt)
            if alt in rule_names and alt in PASSTHROUGH_RULES:
                pending.extend(rules[alt])
            else:
                result.add(alt)
        expanded[name] = result
    return expanded


def parse_doc_productions(lines: list[str]) -> dict[str, set[str]]:
    productions: dict[str, set[str]] = {}
    current: str | None = None
    for raw in lines:
        line = strip_comment(raw).rstrip()
        if not line.strip():
            continue
        match = DOC_RULE_RE.match(line)
        if match:
            current = match.group(1)
            productions.setdefault(current, set()).add(normalize_rhs(match.group(2)))
            continue
        match = DOC_ALT_RE.match(line)
        if match and current is not None:
            productions.setdefault(current, set()).add(normalize_rhs(match.group(1)))
            continue
        raise ValueError(f"not a grammar production: {raw}")
    return productions


def extract_marked_blocks(path: Path) -> list[GrammarBlock]:
    blocks: list[GrammarBlock] = []
    in_block = False
    block_start = 0
    block_lines: list[str] = []

    for line_no, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        fence = FENCE_RE.match(raw)
        if fence and not in_block:
            info = fence.group("info").strip()
            if info == "deduce-grammar" or "deduce-grammar" in info.split():
                in_block = True
                block_start = line_no
                block_lines = []
            continue
        if fence and in_block:
            blocks.append(GrammarBlock(block_start, parse_doc_productions(block_lines)))
            in_block = False
            continue
        if in_block:
            block_lines.append(raw)

    if in_block:
        raise ValueError(f"unterminated deduce-grammar block starting at {block_start}")
    return blocks


def format_alternatives(alternatives: set[str]) -> str:
    return "\n".join(f"      {alt or 'ε'}" for alt in sorted(alternatives))


# --- Operator-precedence table check ---------------------------------------
#
# The "Operator Precedence" section of Reference.md documents the term
# grammar's precedence levels as a Markdown table: each row names a
# ``Deduce.lark`` rule and the operators it introduces. Nothing else checks
# that table, so it can silently drift when operators are added, moved, or
# renamed in the grammar. The checks below pin it to Deduce.lark:
#
#   * every named rule exists,
#   * the levels form a fall-through chain (each looser rule reaches the next
#     tighter rule, transitively -- the table intentionally skips the
#     experimental ``sep_term``/``pointsto_term`` levels), and
#   * every operator listed at a level (including ``(also ...)`` ASCII
#     aliases) is actually an operator of that rule in Deduce.lark.
#
# Level 0 (``atomic_term``) lists descriptive primary/prefix *forms*
# (``f(...)``, ``@f<T>``, ``not P``, ...) rather than plain operators, so its
# operator membership is not checked -- only that the rule exists and anchors
# the chain.

TERMINAL_RE = re.compile(r'^\s*(_[A-Z0-9_]+)\s*:\s*"([^"]*)"\s*$')
BARE_RULE_RE = re.compile(r"^[a-z_][A-Za-z0-9_]*$")
ARROW_RE = re.compile(r"\s*->\s*\w+\s*$")
LITERAL_RE = re.compile(r'"([^"]*)"')
TERM_REF_RE = re.compile(r"\b(_[A-Z0-9_]+)\b")
BACKTICK_RE = re.compile(r"`([^`]*)`")


def parse_lark_terminals(text: str) -> dict[str, str]:
    """Map simple single-literal terminal names (e.g. ``_APPROXEQ``) to their
    literal spelling (``~~``). Multi-alternative or regex terminals are
    ignored -- the precedence table only references the literal ones."""
    terminals: dict[str, str] = {}
    for raw in text.splitlines():
        match = TERMINAL_RE.match(strip_comment(raw))
        if match:
            terminals[match.group(1)] = match.group(2)
    return terminals


def parse_lark_alternatives(text: str) -> dict[str, list[str]]:
    """Return each lowercase rule's raw right-hand-side alternatives, with
    comments and the ``-> name`` tree-shaping suffix removed."""
    alternatives: dict[str, list[str]] = {}
    current: str | None = None

    def record(name: str, rhs: str) -> None:
        alternatives.setdefault(name, []).append(ARROW_RE.sub("", rhs).strip())

    for raw in text.splitlines():
        line = strip_comment(raw).strip()
        if not line or line.startswith("%"):
            continue
        match = RULE_RE.match(line)
        if match:
            current = match.group(1)
            if current.isupper():
                current = None
                continue
            record(current, match.group(2))
            continue
        match = ALT_RE.match(line)
        if match and current is not None:
            record(current, match.group(1))
    return alternatives


def rule_operators(
    rhs_list: list[str], terminals: dict[str, str]
) -> set[str]:
    """Operator spellings introduced by a rule: every quoted string literal
    plus every referenced literal terminal, resolved to its spelling."""
    operators: set[str] = set()
    for rhs in rhs_list:
        operators.update(LITERAL_RE.findall(rhs))
        for term_name in TERM_REF_RE.findall(rhs):
            if term_name in terminals:
                operators.add(terminals[term_name])
    return operators


def fall_through_targets(rhs_list: list[str]) -> set[str]:
    """Rules this rule falls through to: alternatives that are exactly a bare
    rule name (no operators, no other symbols)."""
    return {rhs for rhs in rhs_list if BARE_RULE_RE.match(rhs)}


def reaches(source: str, target: str, edges: dict[str, set[str]]) -> bool:
    seen: set[str] = set()
    stack = [source]
    while stack:
        node = stack.pop()
        if node == target:
            return True
        if node in seen:
            continue
        seen.add(node)
        stack.extend(edges.get(node, set()))
    return False


@dataclass(frozen=True)
class PrecedenceRow:
    line: int
    level: int
    rule: str
    operators: tuple[str, ...]


def extract_precedence_table(path: Path) -> list[PrecedenceRow]:
    lines = path.read_text(encoding="utf-8").splitlines()
    start = next(
        (i for i, l in enumerate(lines) if l.strip() == "## Operator Precedence"),
        None,
    )
    if start is None:
        raise ValueError(f"{path.name}: no '## Operator Precedence' section")

    i = start + 1
    while i < len(lines) and not lines[i].lstrip().startswith("|"):
        if lines[i].startswith("## "):
            raise ValueError(f"{path.name}: Operator Precedence section has no table")
        i += 1

    table: list[str] = []
    table_start = i
    while i < len(lines) and lines[i].lstrip().startswith("|"):
        table.append(lines[i])
        i += 1

    rows: list[PrecedenceRow] = []
    # Skip the header row and the |---| separator row.
    for offset, raw in enumerate(table[2:], start=2):
        cells = [c.strip() for c in raw.strip().strip("|").split("|")]
        if len(cells) < 3:
            continue
        rule_names = BACKTICK_RE.findall(cells[1])
        if not rule_names:
            raise ValueError(f"{path.name}: precedence row has no rule name: {raw!r}")
        rows.append(
            PrecedenceRow(
                line=table_start + offset + 1,
                level=int(cells[0]),
                rule=rule_names[0],
                operators=tuple(BACKTICK_RE.findall(cells[2])),
            )
        )
    return rows


def check_precedence_table(path: Path) -> tuple[list[str], int]:
    text = DEDUCE_LARK.read_text(encoding="utf-8")
    terminals = parse_lark_terminals(text)
    alternatives = parse_lark_alternatives(text)
    edges = {r: fall_through_targets(rhs) for r, rhs in alternatives.items()}
    operators = {r: rule_operators(rhs, terminals) for r, rhs in alternatives.items()}

    rows = extract_precedence_table(path)
    failures: list[str] = []
    checked = 0

    for row in rows:
        loc = f"{path}:{row.line}"
        if row.rule not in alternatives:
            failures.append(f"{loc}: rule {row.rule!r} is not in Deduce.lark")
            continue
        # Level 0 lists descriptive forms, not plain operators.
        if row.level == 0:
            continue
        for op in row.operators:
            checked += 1
            if op not in operators[row.rule]:
                failures.append(
                    f"{loc}: operator {op!r} is documented at level {row.level} "
                    f"({row.rule}) but is not an operator of {row.rule} in Deduce.lark"
                )

    # Verify the precedence chain: each looser rule falls through (transitively)
    # to the next tighter rule.
    ordered = [r for r in sorted(rows, key=lambda r: r.level)]
    for tighter, looser in zip(ordered, ordered[1:]):
        checked += 1
        if looser.rule in alternatives and tighter.rule in alternatives:
            if not reaches(looser.rule, tighter.rule, edges):
                failures.append(
                    f"{path}:{looser.line}: level {looser.level} ({looser.rule}) "
                    f"does not fall through to level {tighter.level} "
                    f"({tighter.rule}) in Deduce.lark"
                )
    return failures, checked


def main() -> int:
    lark_rules = expand_passthrough_alternatives(parse_lark_rules(DEDUCE_LARK))
    failures: list[str] = []
    total_checked = 0

    for ref_md in REFERENCE_MDS:
        blocks = extract_marked_blocks(ref_md)
        if not blocks:
            failures.append(f"{ref_md.name} has no ```deduce-grammar blocks to check")
            continue
        for block in blocks:
            for rule, documented in block.productions.items():
                total_checked += 1
                expected = lark_rules.get(rule)
                if expected is None:
                    failures.append(
                        f"{ref_md}:{block.line}: rule {rule!r} is not in Deduce.lark"
                    )
                    continue
                if rule in SUBSET_RULES:
                    matches = documented <= expected
                else:
                    matches = documented == expected
                if not matches:
                    missing = expected - documented
                    extra = documented - expected
                    parts = [f"{ref_md}:{block.line}: rule {rule!r} differs"]
                    if missing and rule not in SUBSET_RULES:
                        parts.append(f"  Missing from {ref_md.name}:\n" + format_alternatives(missing))
                    if extra:
                        parts.append("  Not present in Deduce.lark:\n" + format_alternatives(extra))
                    failures.append("\n".join(parts))

    table_failures, table_checked = check_precedence_table(REFERENCE_MDS[0])
    failures.extend(table_failures)

    if failures:
        print("\n\n".join(failures), file=sys.stderr)
        return 1

    print(
        f"Checked {total_checked} reference grammar rule(s) and "
        f"{table_checked} operator-precedence entr(y/ies) against Deduce.lark."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
