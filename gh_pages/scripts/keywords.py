from lark import Lark

## Token types:
##      keyword (recursive, definition, ...)
##      operator (+, -, /, ...)
##      type (fn, bool, type)
##      prim (false, INT, true, ∅, .0., 0)
## Other types:
##      comment
##      whitespace
##      ident
known_tokens = {
    'ALL' : 'keyword', 
    'AMPERSAND': 'operator', 
    'AND': 'keyword',
    'APPLY': 'keyword',
    'ARBITRARY': 'keyword',
    'ARRAY': 'operator',
    'ASSERT': 'keyword',
    'ASSOCIATIVE': 'keyword',
    'ASSUME': 'keyword',
    'AT': 'operator',
    'AUTO': 'keyword',
    'BOOL': 'type',
    'BY': 'keyword',
    'CASE': 'keyword',
    'CASES': 'keyword',
    'CHOOSE': 'keyword',
    'CIRCUMFLEX': 'operator',
    'COLON': 'operator',
    'COMMA': 'operator',
    'COMMENT': 'comment',
    'CONCLUDE': 'keyword',
    'CONJUNCT': 'keyword',
    'CONTRADICT': 'keyword',
    'DEFINE': 'keyword',
    'DOLLAR': 'operator',
    'DOT': 'operator',
    'ELSE': 'keyword',
    'END': 'keyword',
    'EQUAL': 'operator',
    'EQUATIONS': 'keyword',
    'EVALUATE': 'keyword',
    'EXPAND': 'keyword',
    'EXPORT': 'keyword',
    'EXTENSIONALITY': 'keyword',
    'FALSE': 'prim',
    'FN': 'type',
    'FOR': 'keyword',
    'FROM': 'keyword',
    'FUN': 'keyword',
    'GENERIC': 'keyword',
    'HASH': 'operator',
    'HAVE': 'keyword',
    'HELP': 'keyword',
    'IDENT': 'ident',
    'IF': 'keyword',
    'IFF': 'operator',
    'IMPORT': 'keyword',
    'IN': 'keyword',
    'INDUCTION': 'keyword',
    'INJECTIVE': 'keyword',
    'INT': 'prim',
    'LBRACE': 'operator',
    'LEMMA': 'keyword',
    'LESSTHAN': 'operator',
    'LINECOMMENT': 'comment',
    'LPAR': 'operator',
    'LSQB': 'operator',
    'MEASURE': 'keyword',
    'MINUS': 'operator',
    'MODULE': 'keyword',
    'MORETHAN': 'operator',
    'NOT': 'keyword',
    'NAT': 'keyword',
    'PUBLIC': 'keyword',
    'OBTAIN': 'keyword',
    'OF': 'keyword',
    'OPAQUE': 'keyword',
    'OPERATOR': 'keyword',
    'OR': 'keyword',
    'PERCENT': 'operator',
    'PLUS': 'operator',
    'PRINT': 'keyword',
    'PRIVATE': 'keyword',
    'PROOF': 'keyword',
    'PUBLIC': 'keyword',
    'QMARK': 'operator',
    'RBRACE': 'operator',
    'RECALL': 'keyword',
    'RECURSIVE': 'keyword',
    'RECFUN': 'keyword',
    'REFLEXIVE': 'keyword',
    'REPLACE': 'keyword',
    'RPAR': 'operator',
    'RSQB': 'operator',
    'SEMICOLON': 'operator',
    'SHOW': 'keyword',
    'SLASH': 'operator',
    'SOME': 'keyword',
    'SORRY': 'keyword',
    'STAR': 'operator',
    'STOP': 'keyword',
    'SUFFICES': 'keyword',
    'SUPPOSE': 'keyword',
    'SWITCH': 'keyword',
    'SYMMETRIC': 'keyword',
    'TERMINATES': 'keyword',
    'THEN': 'keyword',
    'THEOREM': 'keyword',
    'POSTULATE': 'keyword',
    'TO': 'keyword',
    'TRANSITIVE': 'keyword',
    'TRUE': 'prim',
    'TYPE': 'type',
    'UNION': 'keyword',
    'VBAR': 'operator',
    'WHERE': 'keyword',
    'WS': 'whitespace',
    '__': 'operator',
    '__ANON_0': 'operator',  # <=>
    '__ANON_1': 'operator',  # ⇔
    '__ANON_10': 'operator', # ∈
    '__ANON_11': 'operator', # ∪
    '__ANON_12': 'operator', # ∩
    '__ANON_13': 'operator', # ⨄
    '__ANON_14': 'operator', # \\.\\+\\.
    '__ANON_15': 'operator', # \\+\\+
    '__ANON_16': 'operator', # ⊝
    '__ANON_17': 'operator', # ∘
    '__ANON_18': 'operator', # \\.o\\.
    '__ANON_19': 'keyword',  # operator
    '__ANON_2': 'operator',  # ≠
    '__ANON_20': 'prim',     # ∅
    '__ANON_21': 'prim',     # \\.0\\.
    '__ANON_22': 'operator', # ─
    '__ANON_23': 'operator', # \\.\\.\\.
    '__ANON_24': 'operator', # \\->
    '__ANON_25': 'prim',     # 0
    '__ANON_26': 'prim',     # \.-
    '__ANON_27': 'operator', # ≲
    '__ANON_28': 'operator', # ≈
    '__ANON_3': 'operator',  # /=
    '__ANON_4': 'operator',  # ≤
    '__ANON_5': 'operator',  # <=
    '__ANON_6': 'operator',  # ≥
    '__ANON_7': 'operator',  # >=
    '__ANON_8': 'operator',  # ⊆
    '__ANON_9': 'operator',  # \\(=
    'Λ': 'operator'
}

def get_terminals():
    lark_parser = Lark(open("./Deduce.lark", encoding="utf-8").read(),
                       start='program',
                       debug=True, propagate_positions=True)
    lexer_conf = lark_parser.lexer_conf
    terminals = lexer_conf.terminals
    return terminals


def check_known_tokens():
    terminals = get_terminals()
    token_types = set()
    for terminal in terminals:
        token_types.add(terminal.name)
    for tok in token_types:
        if tok not in known_tokens.keys():
            print("ERROR: " + tok + " from the Lark file is missing from the known_tokens in the the lib_generator.py script.")
            exit(255)
    for tok in known_tokens.keys():
        if tok not in token_types:
            print("ERROR: " + tok + " from the known_tokens in the the lib_generator.py script is not a keyword in the Lark file .")
            exit(255)

def get_known_tokens():
    global known_tokens
    return known_tokens

def get_pattern_types():
    terminals = get_terminals()
    token_values = set(known_tokens.values())
    return { token_value : [terminal.pattern for terminal in terminals if known_tokens[terminal.name] == token_value]
             for token_value in token_values }

if __name__ == '__main__':
    check_known_tokens()
