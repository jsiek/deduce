import re

from lark.tree import Meta

from error import ParseError


_PROC_DECL_RE = re.compile(
    r"(?m)^[ \t]*(?:(?:public|private|opaque)[ \t]+)?(?P<keyword>proc)\b"
)


def _meta_for_span(program_text: str, filename: str, start: int, end: int) -> Meta:
    meta = Meta()  # type: ignore[no-untyped-call,unused-ignore]
    meta.empty = False
    setattr(meta, "filename", filename)
    meta.line = program_text.count("\n", 0, start) + 1
    line_start = program_text.rfind("\n", 0, start) + 1
    meta.column = start - line_start + 1
    meta.start_pos = start
    meta.end_line = meta.line
    meta.end_column = meta.column + max(1, end - start)
    meta.end_pos = end
    return meta


def reject_unimplemented_imperative_syntax(
    program_text: str, filename: str
) -> None:
    """Recognize gated imperative syntax before full parser support lands."""
    match = _PROC_DECL_RE.search(program_text)
    if match is None:
        return

    start, end = match.span("keyword")
    raise ParseError(
        _meta_for_span(program_text, filename, start, end),
        "experimental imperative parser path reached for `proc`; "
        "`proc` declarations are not implemented yet",
    )
