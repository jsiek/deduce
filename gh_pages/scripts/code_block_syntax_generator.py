import os

from keywords import get_pattern_types

# The site matches these regexes against HTML-escaped source, so the same
# entity substitution codeUtils.js applies to the code must be baked into the
# patterns (``=`` in a pattern has to become ``&equals;`` to match ``&equals;``
# in the escaped code, and so on).
HTML_ENTITIES = {
    ';': '&semi;',
    '&': '&amp;',
    '=': '&equals;',
    '/': '&sol;',
    '<': '&lt;',
    '>': '&gt;',
}


def escape_pattern(regex):
    """HTML-escape a regex the way the site escapes code, but never inside a
    ``[...]`` character class.

    A character class can only ever match a single character, so rewriting
    ``=`` to the multi-character entity ``&equals;`` inside one does not make
    the class match escaped code -- it injects the letters ``e q u a l s`` as
    literal class members. That is what caused single-letter identifiers to be
    highlighted as keywords (issue #1004). No class needs the substitution to
    match anyway, so we simply leave class contents alone.
    """
    out = []
    in_class = False
    i, n = 0, len(regex)
    while i < n:
        c = regex[i]
        if c == '\\' and i + 1 < n:
            # A backslash escapes the next character; it never opens or closes
            # a class. Outside a class the escaped char is still entity-mapped
            # (e.g. ``\/`` -> ``\&sol;`` in the comment patterns).
            nxt = regex[i + 1]
            out.append('\\')
            out.append(nxt if in_class else HTML_ENTITIES.get(nxt, nxt))
            i += 2
            continue
        if c == '[':
            in_class = True
        elif c == ']':
            in_class = False
        out.append(c if in_class else HTML_ENTITIES.get(c, c))
        i += 1
    return ''.join(out)


if __name__ == '__main__':
    pattern_types = get_pattern_types()

    with open('./gh_pages/js/codeKeywords.js', 'w') as f:

        for pt, ps in pattern_types.items():
            patterns = '[' + ', '.join(repr(escape_pattern(p.to_regexp())) for p in ps) + ']'
            f.write(f'const {pt}s = {patterns}\n\n')

        libs = [lib.split('.pf')[0] for lib in os.listdir('./lib') if lib.endswith('.pf')]
        f.write(f'const libs = {libs}\n\n')

        exports = ', '.join(map(lambda k: k + 's', pattern_types.keys()))
        f.write(f'export {{ {exports}, libs }}')
