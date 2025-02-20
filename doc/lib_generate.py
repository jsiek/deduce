from lark import Lark
import os

prelude = '''
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Document</title>

    <link rel="stylesheet" href="stdlib.css">
</head>
<body>
    <pre><code>'''

conclusion = '''
    </code></pre>
</body>
</html>'''

colors = {
    'keyword' : '#d85311',
    'operator' : '#2e2d31',
    'type' : '#0f95af',
    'prim' : '#9329ab',
    'ident' : 'black',
}

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
    'BOOL': 'type',
    'BY': 'keyword',
    'CASE': 'keyword',
    'CASES': 'keyword',
    'CHOOSE': 'keyword',
    'COLON': 'operator',
    'COMMA': 'operator',
    'COMMENT': 'comment',
    'CONCLUDE': 'keyword',
    'CONJUNCT': 'keyword',
    'DEFINE': 'keyword',
    'DEFINITION': 'keyword',
    'DOLLAR': 'operator',
    'DOT': 'operator',
    'ELSE': 'keyword',
    'ENABLE': 'keyword',
    'END': 'keyword',
    'EQUAL': 'operator',
    'EQUATIONS': 'keyword',
    'EVALUATE': 'keyword',
    'EXTENSIONALITY': 'keyword',
    'FALSE': 'prim',
    'FN': 'type',
    'FOR': 'keyword',
    'FROM': 'keyword',
    'FUN': 'keyword',
    'FUNCTION': 'keyword',
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
    'MINUS': 'operator',
    'MORETHAN': 'operator',
    'NOT': 'keyword',
    'OBTAIN': 'keyword',
    'OF': 'keyword',
    'OPERATOR': 'keyword',
    'OR': 'keyword',
    'PERCENT': 'operator',
    'PLUS': 'operator',
    'PRINT': 'keyword',
    'PRIVATE': 'keyword',
    'PROOF': 'keyword',
    'QMARK': 'operator',
    'RBRACE': 'operator',
    'RECALL': 'keyword',
    'RECURSIVE': 'keyword',
    'REFLEXIVE': 'keyword',
    'REPLACE': 'keyword',
    'REWRITE': 'keyword',
    'RPAR': 'operator',
    'RSQB': 'operator',
    'SEMICOLON': 'operator',
    'SLASH': 'operator',
    'SOME': 'keyword',
    'SORRY': 'keyword',
    'STAR': 'operator',
    'STOP': 'keyword',
    'SUFFICES': 'keyword',
    'SUPPOSE': 'keyword',
    'SWITCH': 'keyword',
    'SYMMETRIC': 'keyword',
    'THEN': 'keyword',
    'THEOREM': 'keyword',
    'TO': 'keyword',
    'TRANSITIVE': 'keyword',
    'TRUE': 'prim',
    'TYPE': 'type',
    'UNION': 'keyword',
    'VBAR': 'operator',
    'WHERE': 'keyword',
    'WS': 'whitespace',
    '_DEFINITION': 'keyword',
    '_REWRITE': 'keyword', 
    '__': 'operator',
    '__ANON_0': 'operator', # <=>
    '__ANON_1': 'operator', # ⇔
    '__ANON_10': 'operator', # ∈
    '__ANON_11': 'operator', # ∪
    '__ANON_12': 'operator', # ∩
    '__ANON_13': 'operator', # ⨄
    '__ANON_14': 'operator', # \\.\\+\\.
    '__ANON_15': 'operator', # \\+\\+
    '__ANON_16': 'operator', # ⊝
    '__ANON_17': 'operator', # ∘
    '__ANON_18': 'operator', # \\.o\\.
    '__ANON_19': 'keyword', # operator
    '__ANON_2': 'operator', # ≠
    '__ANON_20': 'prim', # ∅
    '__ANON_21': 'prim', # \\.0\\.
    '__ANON_22': 'operator', # ─
    '__ANON_23': 'operator', # \\.\\.\\.
    '__ANON_24': 'operator', # \\->
    '__ANON_25': 'prim', # 0
    '__ANON_3': 'operator', # /=
    '__ANON_4': 'operator', # ≤
    '__ANON_5': 'operator', # <=
    '__ANON_6': 'operator', # ≥
    '__ANON_7': 'operator', # >=
    '__ANON_8': 'operator', # ⊆
    '__ANON_9': 'operator', # \\(=
    'Λ': 'operator'
}

name_id = 0
def generate_name(name):
    global name_id
    name_id += 1
    return str(name + str(name_id))

def get_basename(f):
    return f[len(lib_dir)+1:-3]

def safeHTMLify(s):
    return s.replace("<", "&lt;")\
            .replace(">", "&gt;")\
            .replace("λ", "&#x03BB;")\
            .replace("≠", "&#x2260;")\
            .replace("≤", "&#x2264;")\
            .replace("≥", "&#x2265;")\
            .replace("⊆", "&#x2286;")\
            .replace("∈", "&#x2208;")\
            .replace("∪", "&#x222A;")\
            .replace("∩", "&#x2229;")\
            .replace("⨄", "&#x2A04;")\
            .replace("∘", "&#x2218;")\
            .replace("∅", "&#x2205;")

def get_operator_name(i, cur_tok, program_text, tokens ):
    rest = []
    j = i + len(str(tokens[cur_tok]))
    while program_text[j].isspace():
        rest.append(program_text[j])
        j+=1
    rest.append(tokens[cur_tok+1])
    return 'operator' + ''.join(rest)

def lex_file(filename, lark_parser):
    with open(filename, 'r') as pf:
        
        program_text = pf.read()
        lexed = lark_parser.lex(program_text)
        tokens = [tok for tok in lexed]

        return program_text, tokens
    
def is_toks_function(tokens, i):
    return tokens[i] == 'recursive' or\
           tokens[i] == 'function' or\
           (tokens[i] == 'fun' and tokens[i+2] != ':')

def get_names_and_imports(tokens, filename):
    unions, functions, theorems = {}, {}, {}
    imports = []
    i = 0
    while i < len(tokens):
        if tokens[i] == 'union': 
            unions[tokens[i+1]] = {'id': generate_name(tokens[i+1]), 'file': filename}
        elif is_toks_function(tokens, i) and not tokens[i+1] == 'operator': 
            functions[tokens[i+1]] = {'id': generate_name(tokens[i+1]), 'file': filename}
        elif is_toks_function(tokens, i): # operators
            functions[tokens[i+1] + tokens[i+2]] = {'id': generate_name(tokens[i+1] + tokens[i+2]), 'file': filename}
        elif tokens[i] == 'theorem' or tokens[i] == 'lemma': 
            theorems[tokens[i+1]] = {'id': generate_name(tokens[i+1]), 'file': filename}
        elif tokens[i] == 'import':
            imports.append(tokens[i+1])    
        i+=1
    return unions, functions, theorems, imports

def generate_html(html_file, program_text, tokens, unions, functions, theorems):
    # add syntax highlighting and anchors
    with open(html_file, 'w') as htmlf:
        cur_tok = 0
        i = 0
        highlighted = []
        while i != len(program_text):
            c = program_text[i]
            # whitespace
            if c.isspace(): 
                highlighted.append(c)
                i += 1
            # block comment
            elif c == '/' and program_text[i+1] == '*':
                highlighted.append('<span style="color: gray">')
                j = i
                while not (program_text[j] == '*' and program_text[j+1] == '/'):
                    highlighted.append(program_text[j])
                    j+=1
                highlighted.append('*/</span>')
                i = j + 2
            # line comment
            elif c == '/' and program_text[i+1] == '/':
                highlighted.append('<span style="color: gray">')
                j = i
                while not (program_text[j] == '\n'):
                    highlighted.append(program_text[j])
                    j+=1
                highlighted.append('</span>')
                i = j
            # normal token
            else:
                tok = tokens[cur_tok]

                if tokens[cur_tok - 1] == 'import':
                    pre = f'<a href="{str(tok)}.pf.html"><span style="color: {colors['type']}">'
                    post = '</span></a>'
                # unions
                elif tokens[cur_tok - 1] == 'union':
                    pre = f'<a href="{unions[tok]['file']}.pf.html#{unions[tok]['id']}"><span id="{unions[tok]['id']}" style="color: {colors['type']}">'
                    post = '</span></a>'
                elif tok in unions: 
                    pre = f'<a href="{unions[tok]['file']}.pf.html#{unions[tok]['id']}"><span style="color: {colors['type']}">'
                    post = '</span></a>'
                # functions
                elif is_toks_function(tokens, cur_tok-1) and not tok == 'operator':
                    pre = f'<a href="{functions[tok]['file']}.pf.html#{functions[tok]['id']}"><span id="{functions[tok]['id']}" style="color: #086c3c">'
                    post = '</span></a>'
                elif is_toks_function(tokens, cur_tok-1): # operator
                    op_name = get_operator_name(i, cur_tok, program_text, tokens)
                    op_id = functions[tok+tokens[cur_tok+1]]
                    pre = f'<a href="{op_id['file']}.pf.html#{op_id['id']}"><span id="{op_id['id']}" style="color: #086c3c">'
                    post = f'{op_name[len("operator"):]}</span></a>'
                    cur_tok += 1
                    i += len(op_name) - len(str(tok))
                elif tok in functions: 
                    pre = f'<a href="{functions[tok]['file']}.pf.html#{functions[tok]['id']}"><span style="color: #086c3c">'
                    post = '</span></a>'
                elif cur_tok+1 != len(tokens) and tok+tokens[cur_tok+1] in functions:
                    op_name = get_operator_name(i, cur_tok, program_text, tokens)
                    op_id = functions[tok+tokens[cur_tok+1]]
                    pre = f'<a href="{op_id['file']}.pf.html#{op_id['id']}"><span style="color: #086c3c">'
                    post = f'{op_name[len("operator"):]}</span></a>'
                    cur_tok += 1
                    i += len(op_name) - len(str(tok))
                # theorems
                elif tokens[cur_tok-1] == 'theorem' or tokens[cur_tok-1] == 'lemma' :
                    pre = f'<a href="{theorems[tok]['file']}.pf.html#{theorems[tok]['id']}"><span id="{theorems[tok]['id']}" style="color: #086c3c">'
                    post = '</span></a>'
                elif tok in theorems: 
                    pre = f'<a href="{theorems[tok]['file']}.pf.html#{theorems[tok]['id']}"><span style="color: #086c3c">'
                    post = '</span></a>'
                # other tokens
                else:
                    pre = f'<span style="color: {colors[known_tokens[tok.type]]}">'
                    post = '</span>'

                highlighted.append(pre)
                highlighted.append(safeHTMLify(tok))
                highlighted.append(post)

                i += len(str(tok))
                cur_tok += 1

        htmlf.write(prelude)
        htmlf.write(''.join(highlighted))
        htmlf.write(conclusion)

def select_definees(definees, imports, name):
    final = {}
    for d in definees:
        if d in imports: final.update(definees[d])
    final.update(definees[name])
    return final

if __name__ == '__main__':
    # Initialize lexer
    lark_parser = Lark(open("../Deduce.lark", encoding="utf-8").read(),
                    start='program',
                    debug=True, propagate_positions=True)

    # Check for updates to Deduce.lark
    lexer_conf = lark_parser.lexer_conf
    terminals = lexer_conf.terminals
    token_types = set()
    for terminal in terminals:
        token_types.add(terminal.name)
    if sorted(token_types) != list(known_tokens.keys()):
        print("ERROR: Lark file has changes that are not reflected in this script. Please update the list of known tokens accordingly.")
        exit(255)

    # get lib files
    lib_dir = '../lib'
    lib_files = []
    for f in [f for f in os.listdir(lib_dir) if os.path.isfile(os.path.join(lib_dir, f))]:
        if f.endswith('.pf'): 
            lib_files.append(lib_dir + '/' + f)

    # get text and token list
    texts_tokens = {}
    for f in lib_files: 
        program_text, tokens = lex_file(f, lark_parser)
        texts_tokens[f] = {'program_text' : program_text, 'tokens' : tokens}


    # first pass to collect imports and union, function and theorem names
    unions, functions, theorems, imports = {}, {}, {}, {}
    for f in lib_files:
        us, fs, ts, imps = get_names_and_imports(texts_tokens[f]['tokens'], get_basename(f))
        name = get_basename(f)
        unions[name] = us
        functions[name] = fs
        theorems[name] = ts
        imports[name] = imps

    # add syntax highlighting and anchors
    for f in lib_files:
        name = get_basename(f)

        generate_html('stdlib/' + name + '.pf.html', 
                      program_text=texts_tokens[f]['program_text'], 
                      tokens=texts_tokens[f]['tokens'], 
                      unions=select_definees(unions, imports, name), 
                      functions=select_definees(functions, imports, name), 
                      theorems=select_definees(theorems, imports, name))