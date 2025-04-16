from lark import Lark
import subprocess
import os

lib_deduce_dir = './lib'
lib_html_dir = './gh_pages/pages/stdlib'

prelude = lambda pf_files, thm_files, cur_file : f'''
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="description" content="Documentation for the deduce standard library: {cur_file}.">
    <meta name="keywords" content="Deduce, Proof, Programming">
    <meta name="author" content="Jeremy Siek">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Standard Library | {cur_file}</title>

    <!-- Social cards -->
    <meta property="og:url" content="https://jsiek.github.io/deduce/pages/stdlib.html" />
    <meta property="og:type" content="website"/>
    <meta property="og:title" content="Standard Library | {cur_file}" />
    <meta property="og:description" content="Documentation for the deduce standard library." />
    <meta property="og:site_name" content="Deduce">
    <meta property="og:image" content="https://jsiek.github.io/deduce/images/logo.svg" />
    <meta name="twitter:card" content="summary_large_image">
    <meta name="twitter:title" content="Standard Library | {cur_file}">
    <meta name="twitter:description" content="Documentation for the deduce standard library: {cur_file}.">
    <meta name="twitter:image" content="https://jsiek.github.io/deduce/images/logo.svg">

    <!-- Favicon -->
    <link rel="icon" type="image/x-icon" href="../../images/logo.svg">

    <!-- Google Fonts -->
    <link rel="preconnect" href="https://fonts.googleapis.com">
    <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
    <link
        href="https://fonts.googleapis.com/css2?family=Inter:ital,opsz,wght@0,14..32,100..900;1,14..32,100..900&family=JetBrains+Mono:ital,wght@0,100..800;1,100..800&family=Josefin+Slab:ital,wght@0,100..700;1,100..700&display=swap"
        rel="stylesheet">

    <!-- Font awesome -->
    <script src="https://kit.fontawesome.com/7005573326.js" crossorigin="anonymous"></script>

    <link rel="stylesheet" href="../../css/normalize.css">
    <link rel="stylesheet" href="../../css/stdlib.css">
</head>
<body>
    <div class="sidebar-bg" aria-hidden="true"></div>
    <div class="sidebar">
        <button class="mobile" id="nav-toggle"><i class="fa-solid fa-bars"></i></button>

        <div class="sidebar-content hidden">

            <section class="titles">
                <a class="nav-logo" href="../../index.html">
                    <svg xmlns="http://www.w3.org/2000/svg" width="1668" height="402" fill="none" viewBox="0 0 1668 402">
                        <ellipse class="blue" cx="52.954" cy="86.34" fill="#5DAAF1" rx="42.5" ry="46"
                            transform="rotate(14.995 52.954 86.34)" />
                        <path class="blue" fill="#5DAAF1" d="m64.373 41.777 35.74 9.573-23.804 88.867-35.74-9.573z" />
                        <rect class="blue" width="89" height="109" x="79.397" y="28.202" fill="#5DAAF1" rx="26"
                            transform="rotate(14.995 79.397 28.202)" />
                        <rect class="blue" width="88" height="109" x="104.511" y="34.929" fill="#5DAAF1" rx="41"
                            transform="rotate(14.995 104.511 34.929)" />
                        <circle cx="102.759" cy="57.343" r="7.5" fill="#fff" transform="rotate(14.995 102.759 57.343)" />
                        <path class="blue" fill="#5DAAF1"
                            d="M138.713 51.92c-.708-2.633-.535-9.472 5.812-15.768 7.934-7.87 13.773-2.974 9.545 5.889-3.382 7.09-7.816 15.009-9.61 18.082l-5.747-8.203Z" />
                        <rect class="blue" width="277" height="144.529" x="159.042" y="50.663" fill="#5DAAF1" rx="58"
                            transform="rotate(13 159.042 50.663)" />
                        <path class="blue" fill="#5DAAF1" d="m164.305 126 248.242 57.311-16.646 72.104-248.242-57.312z" />
                        <path class="blue" fill="#5DAAF1"
                            d="M377 159h40v92h-40zM70 102.825 141.012 45l77.642 95.347-71.012 57.826z" />
                        <path class="blue" fill="#5DAAF1" d="m151.638 49.079 112.866 26.057-15.971 69.18-112.866-26.057z" />
                        <path class="blue" fill="#5DAAF1"
                            d="m147.622 46.516 28.984 9.675-22.482 67.347-28.984-9.675zm236.164 192.862h33.319v67.92h-33.319zm0 67.92v-75.609L362 224l21.786 83.298Zm-245.189-29.614 35.092-92.309-23.029-19.498-12.063 111.807ZM174 283.5l12.562-106.137 29.393-6.821L174 283.5Z" />
                        <path class="blue" fill="#5DAAF1" d="M200.701 113.82 174 283.5l-35.229-6.32 61.93-163.36Z" />
                        <path class="purple" fill="#A770EA"
                            d="m103.459 155.41-48.84 70.804 15.787 23.485 63.822-54.251-30.769-40.038Zm199.156 108.147h28.844v36.191h-28.844z" />
                        <path class="purple" fill="#A770EA" d="m302.615 299.748 28.407-52.007L293 239l9.615 60.748Z" />
                        <path class="purple" fill="#A770EA" d="m331.459 299.748 20.541-47.2-40.207-9.178 19.666 56.378Z" />
                        <path class="blue" fill="#5DAAF1"
                            d="M590.18 307H523.3v-30.4h17.86V71.02H523.3V41h79.8c18.24 0 35.467 3.167 51.68 9.5 16.213 6.08 30.4 14.947 42.56 26.6 12.16 11.653 21.787 25.713 28.88 42.18 7.093 16.213 10.64 34.58 10.64 
                            55.1 0 14.947-2.66 30.273-7.98 45.98-5.067 15.707-13.427 29.893-25.08 42.56-11.653 12.92-26.853 23.56-45.6 31.92-18.493 8.107-41.167 12.16-68.02 12.16ZM572.7 71.02V276.6h26.6c14.947 0 28.88-2.407 
                            41.8-7.22 12.92-4.813 24.193-11.78 33.82-20.9 9.373-8.867 16.72-19.507 22.04-31.92 5.573-12.667 8.36-26.853 8.36-42.56s-2.787-29.893-8.36-42.56c-5.32-12.667-12.667-23.56-22.04-32.68-9.627-8.867-20.9-15.707-33.82-20.52-12.92-4.813-26.853-7.22-41.8-7.22h-26.6Zm266.698 
                            120.84c-7.094 0-13.554 1.267-19.38 3.8-5.574 2.28-10.387 5.573-14.44 9.88-3.04 3.547-5.574 7.6-7.6 12.16-1.774 4.56-2.787 9.5-3.04 14.82a5454.18 5454.18 0 0 0 35.34-12.92 2039.524 2039.524 0 0 1 35.72-13.3c-3.547-4.307-7.6-7.727-12.16-10.26-4.307-2.787-9.12-4.18-14.44-4.18Zm48.26 
                            98.42c-6.334 6.333-13.554 11.273-21.66 14.82-8.107 3.547-16.974 5.32-26.6 5.32-10.64 0-20.647-1.9-30.02-5.7-9.12-4.053-17.1-9.5-23.94-16.34s-12.287-14.693-16.34-23.56c-3.8-9.12-5.7-18.873-5.7-29.26 
                            0-10.133 1.9-19.76 5.7-28.88 4.053-9.12 9.5-17.1 16.34-23.94 6.84-6.587 14.82-11.78 23.94-15.58 9.373-4.053 19.38-6.08 30.02-6.08 7.853 0 15.326 1.647 22.42 4.94 7.346 3.04 13.933 7.347 19.76 12.92 5.573 5.573 10.513 12.287 14.82 20.14 4.306 7.6 7.6 15.96 9.88 
                            25.08l-51.68 19a11397.596 11397.596 0 0 1-51.3 19c3.8 5.32 8.74 9.627 14.82 12.92 6.333 3.04 13.426 4.56 21.28 4.56 5.826 0 11.146-1.013 15.96-3.04 4.813-2.027 9.12-5.067 12.92-9.12l19.38 22.8ZM1115.73 307h-56.62v-15.2c-.25.76-1.52 2.153-3.8 4.18-2.28 2.027-5.44 4.053-9.5 
                            6.08-4.3 2.28-9.37 4.18-15.2 5.7-5.82 1.773-12.41 2.66-19.76 2.66-10.64 0-20.645-1.9-30.018-5.7-9.373-4.053-17.48-9.5-24.32-16.34s-12.287-14.82-16.34-23.94c-3.8-9.12-5.7-18.747-5.7-28.88s1.9-19.633 
                            5.7-28.5c4.053-9.12 9.5-17.1 16.34-23.94s14.947-12.16 24.32-15.96c9.373-4.053 19.378-6.08 30.018-6.08 6.34 0 12.29.887 17.86 2.66 5.83 1.773 10.9 3.8 15.2 6.08 4.31 2.28 7.35 4.18 9.12 5.7 1.78 1.267 2.92 2.28 3.42 3.04-.5-2.027-.88-4.56-1.14-7.6V52.02h-25.08V22h56.62v254.98h28.88V307Zm-104.88-115.14c-6.58 0-12.665 1.14-18.238 
                            3.42-5.573 2.28-10.387 5.32-14.44 9.12-3.547 4.053-6.46 8.74-8.74 14.06-2.027 5.067-3.04 10.767-3.04 17.1 0 6.587 1.267 12.793 3.8 18.62 2.533 5.827 5.953 10.64 10.26 
                            14.44 3.8 3.547 8.233 6.333 13.3 8.36 5.32 1.773 11.018 2.66 17.098 2.66 6.08 0 11.66-.887 16.72-2.66 5.07-2.027 9.63-4.813 13.68-8.36 4.31-3.8 7.73-8.613 10.26-14.44 2.54-5.827
                            3.8-12.033 3.8-18.62 0-7.093-1.39-13.553-4.18-19.38-2.53-5.827-6.08-10.64-10.64-14.44-3.8-3.04-8.23-5.447-13.3-7.22-5.06-1.773-10.51-2.66-16.34-2.66Zm267.47 78.66c-5.06 12.16-13.3 21.913-24.7 29.26-11.14 7.093-23.56 10.64-37.24 
                            10.64-14.94 0-26.72-3.927-35.34-11.78-8.61-7.853-13.17-18.113-13.68-30.78v-73.34h-25.08V164.5h56.62v88.92c.51 6.84 2.92 12.793 7.22 17.86 4.56 4.813 11.66 7.473 21.28 7.98 6.59 0 12.8-1.14 18.62-3.42 6.08-2.28 11.4-5.447 15.96-9.5 4.56-4.053 8.24-8.867 
                            11.02-14.44 2.79-5.573 4.18-11.653 4.18-18.24v-39.14h-25.08V164.5h56.62v115.9h23.56V307h-55.1v-19.38l1.14-17.1Zm204.18 23.56c-6.58 5.067-13.93 9.12-22.04 12.16-7.85 2.787-16.34 4.18-25.46 4.18-10.64 0-20.64-1.9-30.02-5.7-9.12-4.053-17.1-9.5-23.94-16.34s-12.28-14.693-16.34-23.56c-3.8-8.867-5.7-18.62-5.7-29.26 0-10.133
                            1.9-19.76 5.7-28.88 4.06-9.12 9.5-16.973 16.34-23.56 6.84-6.84 14.82-12.16 23.94-15.96 9.38-4.053 19.38-6.08 30.02-6.08 9.38 0 18.12 1.52 26.22 4.56 8.11 2.787 15.46 6.713 22.04 11.78v44.08h-28.12v-25.46c-3.04-1.52-6.33-2.533-9.88-3.04-3.29-.76-6.71-1.14-10.26-1.14-6.08 0-11.78 1.013-17.1 3.04-5.06 1.773-9.5
                            4.307-13.3 7.6-4.56 4.053-8.1 8.867-10.64 14.44-2.28 5.573-3.42 11.78-3.42 18.62 0 6.333 1.14 12.287 3.42 17.86 2.28 5.573 5.45 10.387 9.5 14.44 4.06 3.547 8.74 6.46 14.06 8.74 
                            5.32 2.027 11.15 3.04 17.48 3.04 5.58 0 10.64-.76 15.2-2.28 4.82-1.52 9.25-3.927 13.3-7.22l19 23.94Zm103.54-102.22c-7.1 0-13.56 1.267-19.38 3.8-5.58 2.28-10.39 5.573-14.44 9.88-3.04 3.547-5.58 7.6-7.6 
                            12.16-1.78 4.56-2.79 9.5-3.04 14.82a5726.9 5726.9 0 0 0 35.34-12.92c11.9-4.56 23.81-8.993 35.72-13.3-3.55-4.307-7.6-7.727-12.16-10.26-4.31-2.787-9.12-4.18-14.44-4.18Zm48.26 98.42c-6.34 6.333-13.56 11.273-21.66 14.82-8.11 3.547-16.98 5.32-26.6
                            5.32-10.64 0-20.65-1.9-30.02-5.7-9.12-4.053-17.1-9.5-23.94-16.34s-12.29-14.693-16.34-23.56c-3.8-9.12-5.7-18.873-5.7-29.26 0-10.133 1.9-19.76 5.7-28.88 4.05-9.12 9.5-17.1 16.34-23.94 6.84-6.587 14.82-11.78 23.94-15.58 9.37-4.053 19.38-6.08 30.02-6.08 7.85
                            0 15.32 1.647 22.42 4.94 7.34 3.04 13.93 7.347 19.76 12.92 5.57 5.573 10.51 12.287 14.82 20.14 4.3 7.6 7.6 15.96 9.88 25.08-17.23 6.333-34.46 12.667-51.68 19-16.98 6.333-34.08 12.667-51.3 19 3.8 5.32 8.74 9.627 14.82 12.92 6.33 3.04 13.42 4.56 21.28 4.56 5.82 0 11.14-1.013 15.96-3.04 4.81-2.027 9.12-5.067 12.92-9.12l19.38 22.8Z" />
                    </svg>
                </a>
            </section>

            <section class="links">
                <a href="../stdlib.html"><h2>Standard library</h2></a>
                <details id="thm-details" open>
                    <summary class="{'open' if cur_file.endswith('.thm') else ''}">Theorem files</summary>
                    <ul>
    {'\n'.join([f'<li><a class="{'current' if file + '.thm' == cur_file else ''}" href="./{file}.thm.html">{file}</a></li>' for file in thm_files])}
                    </ul>
                </details>

                <details id="pf-details" open>
                    <summary class="{'open' if cur_file.endswith('.pf') else ''}">Proof files</summary>
                    <ul>
    {'\n'.join([f'<li><a class="{'current' if file + '.pf' == cur_file else ''}" href="./{file}.pf.html">{file}</a></li>' for file in pf_files])}
                    </ul>
                </details>
            </section>
            
            <section class="controls">
                <!--<div class="font-div">
                    <label for="font-size">Font size:</label>
                    <input type="number" id="font-size" name="font-size" theme="Font Size" min="6" max="30" value="14">
                </div>-->
                
                <div class="theme-div">
                    <label for="theme">Theme:</label>
                    <select name="theme" title="Theme" id="theme" value="deduce-light">
                        <option value="deduce-dark">Deduce Dark</option>
                        <option value="deduce" selected>Deduce Light</option>
                        <option value="vs-dark">VS Code Dark</option>
                        <option value="vs">VS Code Light</option>
                        <option value="hc-black">High Contrast</option>
                    </select>
                </div>
            </section>
        </div>
    </div>
    <pre><code>'''

conclusion = '''
    </code></pre>

    <script src="../../js/stdlib.js"></script>
</body>
</html>'''


## Token types:
##      keyword (recursive, definition, ...)
##      operator (+, -, /, ...)
##      type (fn, bool, type)
##      prim (false, INT, true, ∅, .0., 0)
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
    'CIRCUMFLEX': 'operator',
    'COLON': 'operator',
    'COMMA': 'operator',
    'COMMENT': 'comment',
    'CONCLUDE': 'keyword',
    'CONJUNCT': 'keyword',
    'DEFINE': 'keyword',
    'DOLLAR': 'operator',
    'DOT': 'operator',
    'ELSE': 'keyword',
    'END': 'keyword',
    'EQUAL': 'operator',
    'EQUATIONS': 'keyword',
    'EVALUATE': 'keyword',
    'EXPAND': 'keyword',
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
    'MORETHAN': 'operator',
    'NOT': 'keyword',
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
    'TO': 'keyword',
    'TRANSITIVE': 'keyword',
    'TRUE': 'prim',
    'TYPE': 'type',
    'UNION': 'keyword',
    'VBAR': 'operator',
    'WHERE': 'keyword',
    'WS': 'whitespace',
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

def get_basename(f, dir_path=lib_deduce_dir, extension='.pf'):
    return f[len(dir_path)+1:-len(extension)]

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
    with open(filename, 'r') as f:
        if filename.endswith('.thm'):
            program_text = ''.join(f.readlines()[4:])
        else: 
            program_text = f.read()
        lexed = lark_parser.lex(program_text)
        tokens = [tok for tok in lexed]

        return program_text, tokens
    
def is_toks_function(tokens, i):
    return tokens[i] == 'recursive' or \
           tokens[i] == 'function' or \
           (i-2 < len(tokens) and tokens[i] == 'fun' and tokens[i+2] != ':') or \
           (i-3 < len(tokens) and tokens[i] == 'define' and tokens[i+2] == ':' and tokens[i+3] == 'fn') or \
           (i-4 < len(tokens) and tokens[i] == 'define' and tokens[i+1] == 'operator' and tokens[i+3] == ':' and tokens[i+4] == 'fn') or \
           (i-3 < len(tokens) and tokens[i] == 'define' and tokens[i+3] == 'generic') or \
           (i-4 < len(tokens) and tokens[i] == 'define' and tokens[i+1] == 'operator' and tokens[i+4] == 'generic')

def get_names_and_imports(tokens, filename):
    unions, functions, theorems, constructors = {}, {}, {}, {}
    imports = []
    i = 0
    while i < len(tokens):
        if tokens[i] == 'union': 
            union_id = generate_name(tokens[i+1])
            unions[tokens[i+1]] = {'id': union_id, 'file': filename}
            if tokens[i+1] == 'Set':
                constructors['∅'] = {'id' : union_id, 'file': filename}
            if tokens[i+1] == 'Nat':
                constructors['INT'] = {'id': union_id, 'file': filename}
                constructors['0'] = {'id' : union_id, 'file': filename}
            for constr_tok in get_constructors(i, tokens):
                constructors[constr_tok] = {'id': union_id, 'file': filename}
        elif is_toks_function(tokens, i) and not tokens[i+1] == 'operator': 
            functions[tokens[i+1]] = {'id': generate_name(tokens[i+1]), 'file': filename}
        elif is_toks_function(tokens, i): # operators
            functions[tokens[i+1] + tokens[i+2]] = {'id': generate_name(tokens[i+1] + tokens[i+2]), 'file': filename}
        elif tokens[i] == 'theorem' or tokens[i] == 'lemma': 
            theorems[tokens[i+1]] = {'id': generate_name(tokens[i+1]), 'file': filename}
        elif tokens[i] == 'import':
            imports.append(tokens[i+1])    
        i+=1
    return unions, functions, theorems, constructors, imports

def get_constructors(cur_tok, tokens):
    # cur_tok points to 'union', so go until lbrace
    while tokens[cur_tok].type != 'LBRACE': 
        cur_tok+=1
    cur_tok+=1
    constr_list = []
    while tokens[cur_tok].type != 'RBRACE':
        constr_list.append(tokens[cur_tok])
        cur_tok+=1
        if tokens[cur_tok].type == 'LPAR':
            par_depth = 1
            cur_tok += 1
            while par_depth != 0: 
                if tokens[cur_tok].type == 'LPAR': par_depth += 1
                if tokens[cur_tok].type == 'RPAR': par_depth -= 1
                cur_tok += 1
    return constr_list

def generate_html(html_file, lib_pf_files, lib_thm_files, program_text, tokens, unions, functions, theorems, constructors):
    operators = {fun[len('operator'):] : functions[fun] for fun in functions if fun.startswith('operator')}

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
                highlighted.append('<span class="stdlib-comment">')
                j = i
                while not (program_text[j] == '*' and program_text[j+1] == '/'):
                    highlighted.append(program_text[j])
                    j+=1
                highlighted.append('*/</span>')
                i = j + 2
            # line comment
            elif c == '/' and program_text[i+1] == '/':
                highlighted.append('<span class="stdlib-comment">')
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
                    pre = f'<a href="{str(tok)}.pf.html"><span class="stdlib-import"">'
                    post = '</span></a>'
                # unions
                elif tokens[cur_tok - 1] == 'union':
                    pre = f'<a href="{unions[tok]['file']}.pf.html#{unions[tok]['id']}"><span id="{unions[tok]['id']}" class="stdlib-union">'
                    post = '</span></a>'
                elif tok in unions: 
                    pre = f'<a href="{unions[tok]['file']}.pf.html#{unions[tok]['id']}"><span class="stdlib-union">'
                    post = '</span></a>'
                # functions
                elif is_toks_function(tokens, cur_tok-1) and not tok == 'operator' and tok in functions:
                    pre = f'<a href="{functions[tok]['file']}.pf.html#{functions[tok]['id']}"><span id="{functions[tok]['id']}" class="stdlib-function">'
                    post = '</span></a>'
                elif is_toks_function(tokens, cur_tok-1) and tok == 'operator': # operator
                    op_name = get_operator_name(i, cur_tok, program_text, tokens)
                    op_id = functions[tok+tokens[cur_tok+1]]
                    pre = f'<a href="{op_id['file']}.pf.html#{op_id['id']}"><span id="{op_id['id']}" class="stdlib-function">'
                    post = f'{op_name[len("operator"):]}</span></a>'
                    cur_tok += 1
                    i += len(op_name) - len(str(tok))
                elif tok in functions: 
                    pre = f'<a href="{functions[tok]['file']}.pf.html#{functions[tok]['id']}"><span class="stdlib-function">'
                    post = '</span></a>'
                elif cur_tok+1 != len(tokens) and tok+tokens[cur_tok+1] in functions:
                    op_name = get_operator_name(i, cur_tok, program_text, tokens)
                    op_id = functions[tok+tokens[cur_tok+1]]
                    pre = f'<a href="{op_id['file']}.pf.html#{op_id['id']}"><span class="stdlib-function">'
                    post = f'{op_name[len("operator"):]}</span></a>'
                    cur_tok += 1
                    i += len(op_name) - len(str(tok))
                elif tok in operators and tokens[cur_tok-1] != 'operator' and tok != '<' and tok != '>':
                    pre = f'<a href="{operators[tok]['file']}.pf.html#{operators[tok]['id']}"><span class="stdlib-operator">'
                    post = '</span></a>'
                # theorems
                elif tokens[cur_tok-1] == 'theorem' or tokens[cur_tok-1] == 'lemma' :
                    pre = f'<a href="{theorems[tok]['file']}.pf.html#{theorems[tok]['id']}"><span id="{theorems[tok]['id']}" class="stdlib-theorem">'
                    post = '</span></a>'
                elif tok in theorems: 
                    pre = f'<a href="{theorems[tok]['file']}.pf.html#{theorems[tok]['id']}"><span class="stdlib-theorem">'
                    post = '</span></a>'
                # constructors
                elif tok.type in constructors and tok.type == 'INT':
                    pre = f'<a href="{constructors[tok.type]['file']}.pf.html#{constructors[tok.type]['id']}"><span class="stdlib-prim">'
                    post = '</span></a>'
                elif tok in constructors and tok == '0':
                    pre = f'<a href="{constructors[tok]['file']}.pf.html#{constructors[tok]['id']}"><span class="stdlib-prim">'
                    post = '</span></a>'
                elif tok in constructors:
                    pre = f'<a href="{constructors[tok]['file']}.pf.html#{constructors[tok]['id']}"><span class="stdlib-constructor">'
                    post = '</span></a>'
                # other tokens
                else:
                    pre = f'<span class="stdlib-{known_tokens[tok.type]}">'
                    post = '</span>'

                highlighted.append(pre)
                highlighted.append(safeHTMLify(tok))
                highlighted.append(post)

                i += len(str(tok))
                cur_tok += 1


        base_lib_pf_files = [get_basename(f, extension='.pf') for f in lib_pf_files]
        base_lib_thm_files = [get_basename(f, extension='.thm') for f in lib_thm_files]
        base_file_name = get_basename(html_file, dir_path=lib_html_dir, extension='.html')
        htmlf.write(prelude(base_lib_pf_files, base_lib_thm_files, base_file_name))
        htmlf.write(''.join(highlighted))
        htmlf.write(conclusion)

def select_definees(definees, imports, name):
    final = {}
    for d in definees:
        if d in imports: final.update(definees[d])
    final.update(definees[name])
    return final

def call_deduce_lib():
    python_path = ""
    for i in range(14, 10, -1):
        python_path = os.popen("command -v python3." + str(i)).read()[0: -1] # strip the newline character with the splicing
        if python_path != "" and os.system(python_path + " -m pip list | grep lark > /dev/null") == 0:
            break
    
    if python_path == "":
        print("Could not find a python version at or above 3.11 with lark installed")
        exit(1)
    
    subprocess.run([python_path, './deduce.py', './lib'], capture_output=True)

if __name__ == '__main__':
    # Initialize lexer
    print('Initializing lexer')
    lark_parser = Lark(open("./Deduce.lark", encoding="utf-8").read(),
                    start='program',
                    debug=True, propagate_positions=True)

    # Check for updates to Deduce.lark
    lexer_conf = lark_parser.lexer_conf
    terminals = lexer_conf.terminals
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

    # call deduce on lib to generate thm files
    print("Generating lib thm files")
    call_deduce_lib()

    # get lib files
    lib_pf_files = []
    lib_thm_files = []
    for f in [f for f in sorted(os.listdir(lib_deduce_dir)) if os.path.isfile(os.path.join(lib_deduce_dir, f))]:
        if f.endswith('.pf'): 
            lib_pf_files.append(os.path.join(lib_deduce_dir, f))
        if f.endswith('.thm'):
            lib_thm_files.append(os.path.join(lib_deduce_dir, f))

    # get text and token list
    print("Lexing files")
    texts_tokens = {}
    for f in lib_pf_files + lib_thm_files: 
        program_text, tokens = lex_file(f, lark_parser)
        texts_tokens[f] = {'program_text' : program_text, 'tokens' : tokens}

    # first pass to collect imports and union, function and theorem names
    print("Collecting defined names")
    unions, functions, theorems, constructors, imports = {}, {}, {}, {}, {}
    for f in lib_pf_files:
        us, fs, ts, cs, imps = get_names_and_imports(texts_tokens[f]['tokens'], get_basename(f))
        name = get_basename(f)
        unions[name] = us
        functions[name] = fs
        theorems[name] = ts
        constructors[name] = cs
        imports[name] = imps

    print("Creating stdlib folder")
    if not os.path.exists(lib_html_dir):
        os.makedirs(lib_html_dir)

    # clear old html files
    print("Clearing old html files")
    for f in os.listdir(lib_html_dir):
        file_path = os.path.join(lib_html_dir, f)
        if os.path.isfile(file_path) and file_path.endswith('.html'): os.remove(file_path)

    # add syntax highlighting and anchors
    print("Generating pf and thm html")
    for f in lib_pf_files + lib_thm_files:
        extension = '.pf' if f.endswith('.pf') else '.thm' 
        name = get_basename(f, extension=extension)
        generate_html(os.path.join(lib_html_dir, name + extension + '.html'), 
                      lib_pf_files, lib_thm_files,
                      program_text=texts_tokens[f]['program_text'], 
                      tokens=texts_tokens[f]['tokens'], 
                      unions=select_definees(unions, imports, name), 
                      functions=select_definees(functions, imports, name), 
                      theorems=select_definees(theorems, imports, name),
                      constructors=select_definees(constructors, imports, name),)
