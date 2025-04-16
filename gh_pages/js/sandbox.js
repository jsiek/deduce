const isMobile = window.innerWidth < 990;

let editor;
let fontSize = window.innerWidth > 990 ? 14 : 12;
let theme = 'deduce-dark';

const deduceServerURL = "https://deduce.vercel.app/deduce"

const themeIn = document.getElementById("theme")
const sizeIn = document.getElementById("font-size")
const butt = document.getElementById("submit")
const output = document.getElementById("code-output")
const copyButt = document.getElementById("copy-code")
const downloadButt = document.getElementById("download-code")

const themeBgs = {
    "deduce-dark": "#202022",
    "deduce": "#fefef8",
    "vs-dark": "#1e1e1e",
    "vs": "#fffffe",
    "hc-black": "#000",
}
const darkThemes = ["deduce-dark", "vs-dark", "hc-black"]

themeIn.value = theme;
sizeIn.value = fontSize;

/**
 * Monaco
 */

require.config({ paths: { vs: 'https://cdnjs.cloudflare.com/ajax/libs/monaco-editor/0.29.1/min/vs/' } });

window.MonacoEnvironment = {
    getWorkerUrl: function (workerId, label) {
        return `data:text/javascript;charset=utf-8,${encodeURIComponent(`
            self.MonacoEnvironment = { baseUrl: "https://cdnjs.cloudflare.com/ajax/libs/monaco-editor/0.29.1/min/" };
            importScripts("https://cdnjs.cloudflare.com/ajax/libs/monaco-editor/0.29.1/min/vs/base/worker/workerMain.min.js");`
        )}`;
    }
};

function create_editor(fs, tm) {
    fontSize = fs
    theme = tm

    let value = "// Enter deduce code here\n\n\n";

    if (editor) {
        value = editor.getValue()
        editor.dispose()
    }
    editor = monaco.editor.create(document.getElementById('container'), {
        fontSize: fontSize,
        fontFamily: 'JetBrains Mono',
        fontLigatures: true,
        theme: theme,
        value: value,
        language: 'deduce',
        automaticLayout: true,
        tabSize: 2,
        minimap: {enabled: false},
    });
}

require(['vs/editor/editor.main'], function () {
    monaco.languages.register({
        id: 'deduce'
    });
    monaco.languages.setMonarchTokensProvider('deduce', {
        // Set defaultToken to invalid to see what you do not tokenize yet
        // defaultToken: 'invalid',

        keywords: [
            "define", "function", "fun", "switch", "case", "union", "if", "then", "else", "import",
            "generic", "assert", "have", "transitive", "symmetric", "extensionality", "reflexive",
            "injective", "sorry", "help", "conclude", "suffices", "enough", "by", "rewrite",
            "conjunct", "induction", "where", "suppose", "with", "definition", "apply", "to", "cases",
            "obtain", "stop", "equations", "of", "arbitrary", "choose", "term", "from",
            "assume", "for", "recall", "in", "and", "or", "print", "not", "some", "all", "theorem",
            "lemma", "proof", "end"
        ],

        typeKeywords: [
            "MultiSet", "Option", "Pair", "Set", "List", "Int", "Nat", "int", "bool", "fn", "type"
        ],

        operators: [
            "->", "++", "/", "|", "&", "[+]", "[o]", "(=",
            "<=", ">=", "/=", "≠", "⊆", "≤", "≥", "∈", "∪", "+", "%", "(?<!/)*(?!/)", "⨄",
            "-", "∩", "∘", "λ", "@", ":", "<", ">", ",", "=", ".", ";", "#"
        ],

        defines: [
            "node", "suc", "take", "set_of", "empty_no_members",
            "single", "member_union", "single_equal", "length"
        ],

        prims: ["true", "false", "empty"],

        primSymbols: ["∅", "[0]", "?"],


        // we include these common regular expressions
        symbols: /(=|>|<|!|~|\?|:|&|\||\+|-|\^|%|\)|\(|\]|\[|o|0|≠|⊆|≤|≥|∈|∪|∅|\.)/,

        specialSymbols: /((?<!\/|\*)\/(?!\/|\*)|(?<!\/)\*(?!\/))/,

        // The main tokenizer for our languages
        tokenizer: {
            root: [
                // identifiers and keywords
                [/[a-zA-Z'$][\w$]*/, {
                    cases: {
                        '@typeKeywords': 'typeKeyword',
                        '@keywords': 'keyword',
                        '@prims': 'primitive',
                        '@defines': 'defined',
                        '@default': 'identifier',
                    }
                }],

                // delimiters and operators
                [/[{}()\[\],]/, 'brackets'],
                // [/[<>](?!@symbols)/, '@brackets'],
                [/[.@*=><!~?:&|+^%≤≥⇔∘∪∩⊆∈⨄∅-]+/, {
                    cases: {
                        '@primSymbols': 'primitive',
                        '@operators': 'operator',
                        '@default': 'operator'
                    }
                }],

                [/(?<!\/|\*)\/(?!\/|\*)/, "operator"],

                // whitespace
                { include: '@whitespace' },

                // numbers
                [/\d*\.\d+([eE][\-+]?\d+)?/, 'number.float'],
                [/0[xX][0-9a-fA-F]+/, 'number.hex'],
                [/\d+/, 'number'],
            ],

            comment: [
                [/[^\/*]+/, 'comment'],
                [/\/\*/, 'comment', '@push'],    // nested comment
                ["\\*/", 'comment', '@pop'],
                [/[\/*]/, 'comment']
            ],

            whitespace: [
                [/[ \t\r\n]+/, 'white'],
                [/\/\*/, 'comment', '@comment'],
                [/\/\/.*$/, 'comment'],
            ],
        },
    });
    monaco.editor.defineTheme('deduce-dark', {
        base: 'vs-dark',
        inherit: false,
        rules: [
            { token: "", background: "1e1e1e" },
            { token: 'keyword', foreground: 'e9cc60' },
            { token: 'typeKeyword', foreground: 'b689fe' },
            { token: 'operator', foreground: 'cfd6e3' },
            { token: 'brackets', foreground: 'cfd6e3' },
            { token: 'number', foreground: 'f18bea' },
            { token: 'primitive', foreground: 'f18bea' },
            { token: 'comment', foreground: '999999' },
            { token: 'defined', foreground: '67bef9' },
            { token: 'identifier', foreground: 'fa7188' },
        ],
        colors: {
            "editor.background": "#202022",
            "editor.lineHighlightBackground": "#D7D7D708",
        }
    });
    monaco.editor.defineTheme('deduce', {
        base: 'vs',
        inherit: false,
        rules: [
            { token: "", background: "fefef8" },
            { token: 'keyword', foreground: 'd85311' },
            { token: 'typeKeyword', foreground: '0f95af' },
            { token: 'operator', foreground: '2e2d31' },
            { token: 'brackets', foreground: '2e2d31' },
            { token: 'number', foreground: '9329ab' },
            { token: 'primitive', foreground: '9329ab' },
            { token: 'comment', foreground: '666666' },
            { token: 'defined', foreground: 'c553e9' },
            { token: 'identifier', foreground: '2e2d31' },
        ],
        colors: {
            "editor.background": "#fefef8",
            "editor.lineHighlightBackground": "#D7D7D708",
        }
    });

    create_editor(fontSize, theme)
});

function prepare_output(out, is_err = false, re_sp = true) {
    out = out.replaceAll("<", "&lt;")
    out = out.replaceAll(">", "&gt;")

    out = out.replaceAll("\n", "<br>")
    out = out.replaceAll("\t", "    ")
    out = re_sp ? out.replaceAll(" ", "&nbsp;") : out
    return is_err ? `<span class="error">${out}</span>` : out
}

function send_deduce(code) {
    output.innerHTML = '<div class="loader">Deducing<span></span></div>'
    fetch(deduceServerURL, {
        method: "POST",
        body: code
    })
        .then(res => {
            if (res.ok) {
                return res.text()
            }
            throw new Error('')
        })
        .then(data => output.innerHTML = prepare_output(data))
        .catch(err => output.innerHTML = '<span class="error">Something went wrong internally.<br>If this error persists please reach us at <a href="mailto:jsiek@iu.edu">jsiek@iu.edu</a>.</span>')
}

function themeUpdate(create = true) {
    if (create) create_editor(fontSize, themeIn.value)
    output.style.backgroundColor = themeBgs[themeIn.value]
    if (darkThemes.includes(themeIn.value)) output.classList.add("dark")
    else output.classList.remove("dark")
}
function sizeUpdate(create = true) {
    let size = Math.min(Math.max(sizeIn.value, sizeIn.min), sizeIn.max)
    if (create) create_editor(size, theme)
    output.style.fontSize = size + "px";
}

butt.onclick = () => send_deduce(editor.getValue())
themeIn.oninput = themeIn.onload = themeUpdate
sizeIn.oninput = sizeIn.onload = sizeUpdate
sizeIn.onblur = () => sizeIn.value = Math.min(Math.max(sizeIn.value, sizeIn.min), sizeIn.max)


/**
 * Resizer nonsense
 */

const resizerNS = document.querySelector('#resizer-ns');
const resizerEW = document.querySelector('#resizer-ew');
const wrapper = document.querySelector('.sandbox');
const container = wrapper.querySelector('.in');
let isHandlerDraggingNS = false;
let isHandlerDraggingEW = false;

document.addEventListener('mousedown', e => {
    // If mousedown event is fired from .handler, toggle flag to true
    if (e.target === resizerNS) {
        isHandlerDraggingNS = true;
        e.preventDefault()
    }
    if (e.target === resizerEW) {
        isHandlerDraggingEW = true;
        e.preventDefault()
    }
});

const god = document.getElementById("god");

document.addEventListener('mousemove', e => {
    // Don't do anything if dragging flag is false
    if (!isHandlerDraggingNS && !isHandlerDraggingEW) {
        return false;
    }

    e.preventDefault()

    // Get offset
    let containerOffsetLeft = container.offsetLeft;
    let containerOffsetTop = container.offsetTop;

    // Get x-coordinate of pointer relative to container
    let pointerRelativeXpos = e.clientX - containerOffsetLeft;
    let pointerRelativeYpos = e.clientY - containerOffsetTop;

    // Arbitrary minimum width set on box A, otherwise its inner content will collapse to width of 0
    let containerMin = 60;

    god.innerHTML = `X: ${pointerRelativeXpos}<br>W: ${(Math.max(containerMin, pointerRelativeXpos - 8)) - (resizerEW.clientWidth / 2 )}`

    // Resize box A
    if (isHandlerDraggingEW) {
        container.style.width = (Math.max(containerMin, pointerRelativeXpos - 8)) - 
                                (resizerEW.clientWidth / 2 )  + 'px';
        container.style.flexGrow = 0;
    } else if (isHandlerDraggingNS) {
        container.style.height = (Math.max(containerMin, pointerRelativeYpos - 8)) -
                                 (resizerNS.clientHeight / 2) + 'px';
        container.style.flexGrow = 0;
    }
});

document.addEventListener('mouseup', e => {
    // Turn off dragging flag when user mouse is up
    isHandlerDraggingNS = false;
    isHandlerDraggingEW = false;
});

document.addEventListener('mouseleave', e => {
    // Turn off dragging flag when user mouse is gone
    isHandlerDraggingNS = false;
    isHandlerDraggingEW = false;
})

/**
 * Download and copy buttons
 */

copyButt.onclick = () => {
    if (navigator) {
        navigator.clipboard.writeText(editor.getValue())
        alert("Code copied to clipboard!")
    } else {
        alert("Error copying code to clipboard.")
    }
}

downloadButt.onclick = () => download("input.pf", editor.getValue())
if(isMobile) downloadButt.style.display = "none"

function download(filename, text) {
    var element = document.createElement('a');
    element.setAttribute('href', 'data:plain;charset=utf-8,' + encodeURIComponent(text));
    element.setAttribute('download', filename);

    element.style.display = 'none';
    document.body.appendChild(element);

    element.click();

    document.body.removeChild(element);
}

// Not really necessary but hey
themeUpdate(false)
sizeUpdate(false)