#!/usr/bin/env python3
"""Check strict Reference.md grammar fragments against Deduce.lark.

Reference.md contains many small, user-facing syntax snippets. Only fenced
blocks marked ``deduce-grammar`` are part of this strict check; unmarked
blocks may stay simplified while they are migrated.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
import sys


REPO_ROOT = Path(__file__).resolve().parents[2]
REFERENCE_MD = REPO_ROOT / "gh_pages" / "doc" / "Reference.md"
DEDUCE_LARK = REPO_ROOT / "Deduce.lark"

RULE_RE = re.compile(r"^\s*\??([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(.*)$")
ALT_RE = re.compile(r"^\s*\|\s*(.*)$")
DOC_RULE_RE = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s*::=\s*(.*)$")
DOC_ALT_RE = re.compile(r"^\s*\|\s*(.*)$")
FENCE_RE = re.compile(r"^```(?P<info>.*)$")

TOKEN_ALIASES = {
    "identifier": "IDENT",
    "identifier_list": "ident_list",
    "natural_number": "NAT",
    "number": "INT",
    "unsigned_integer": "INT",
}
PASSTHROUGH_RULES = {"type_hi"}


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

    The public reference often presents helper rules such as ``type_hi`` as
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


def main() -> int:
    lark_rules = expand_passthrough_alternatives(parse_lark_rules(DEDUCE_LARK))
    blocks = extract_marked_blocks(REFERENCE_MD)
    failures: list[str] = []

    if not blocks:
        failures.append("Reference.md has no ```deduce-grammar blocks to check")

    for block in blocks:
        for rule, documented in block.productions.items():
            expected = lark_rules.get(rule)
            if expected is None:
                failures.append(
                    f"{REFERENCE_MD}:{block.line}: rule {rule!r} is not in Deduce.lark"
                )
                continue
            if documented != expected:
                missing = expected - documented
                extra = documented - expected
                parts = [f"{REFERENCE_MD}:{block.line}: rule {rule!r} differs"]
                if missing:
                    parts.append("  Missing from Reference.md:\n" + format_alternatives(missing))
                if extra:
                    parts.append("  Not present in Deduce.lark:\n" + format_alternatives(extra))
                failures.append("\n".join(parts))

    if failures:
        print("\n\n".join(failures), file=sys.stderr)
        return 1

    checked = sum(len(block.productions) for block in blocks)
    print(f"Checked {checked} Reference.md grammar rule(s) against Deduce.lark.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
