const operators = [
    "->", "\\+\\+", "(?<!\\/|\\*)\\/(?!\\/|\\*)", "\\|", "&", "\\[\\+\\]", "\\[o\\]", "\\(=", 
    "<=", ">=", "\\/=", "≠", "⊆", "≤", "≥", "∈", "∪", "\\+", "%", "(?<!\\/)\\*(?!\\/)", "⨄", 
    "-", "∩", "∘", "λ", "@", ":", "&gt;", "&lt;", "\\(", "\\)", "{", "}", ",", "=", "\\.", "\\[", 
    "\\]", ";", "#"
]

const prims = ["true", "false", "0", "[0-9]+", "empty"]

const defines = ["node", "suc", "take", "set_of", "empty_no_members",
    "single", "member_union", "single_equal", "length"]

const primsSym = ["∅", "\\[0\\]", "\\?"]

const types = ["MultiSet", "Option", "Pair", "Set", "List", "Int", "Nat", "int", "bool", "fn", "type"]

const keywords = [
    "define", "function", "fun", "switch", "case", "union", "if", "then", "else", "import",
    "generic", "assert", "have", "transitive", "symmetric", "extensionality", "reflexive",
    "injective", "sorry", "help", "conclude", "suffices", "enough", "by", "rewrite",
    "conjunct", "induction", "where", "suppose", "with", "definition", "apply", "to", "cases",
    "obtain", "stop", "equations", "of", "arbitrary", "choose", "term", "from",
    "assume", "for", "recall", "in", "and", "or", "print", "not", "some", "all", "theorem",
    "lemma", "proof", "end", "replace", "recursive"
]


function getRegex(ls) {
    let fullRegex = ls.reduce((a, s) => `\\b${s}\\b|` + a, "")
    return fullRegex.substring(0, fullRegex.length - 1)
}

function getRegexSymbols(ls) {
    let fullRegex = ls.reduce((a, s) => `${s}|` + a, "")
    return fullRegex.substring(0, fullRegex.length - 1)
}

function replaceLeadingTabs(str) {
    if (str[0] != "\t") return str
    return "<span class=\"tab\"></span>" + replaceLeadingTabs(str.substring(1))
}


function codeToHTML(code) {
    // scan to get user defined functions and variables
    const fncRe = new RegExp("(?<=\\bfunction\\s)\\w+(?=\\s*[\\(|<])", "g")
    const recRe = new RegExp("(?<=\\brecursive\\s)\\w+(?=\\s*[\\(|<])", "g")
    const thmRe = new RegExp("(?<=\\btheorem\\s)\\w+(?=\\s*:)", "g")
    const uniRe = new RegExp("(?<=\\bunion\\s)\\w+(?=\\s*<)?", "g")
    const defRe = new RegExp("(?<=\\bdefine\\s)\\w+(?=\\s*:)?", "g")
    let userDefs = []
        .concat(Array.from(code.matchAll(fncRe)).flat())
        .concat(Array.from(code.matchAll(recRe)).flat())
        .concat(Array.from(code.matchAll(thmRe)).flat())
        .concat(Array.from(code.matchAll(uniRe)).flat())
        .concat(Array.from(code.matchAll(defRe)).flat())
    userDefs = userDefs.filter(e => e !== undefined && e !== "operator")

    // prep regex
    const ore = new RegExp(getRegexSymbols(operators), "g")
    const pre = new RegExp(getRegex(prims) + "|" + getRegexSymbols(primsSym), "g")
    const tre = new RegExp(getRegex(types), "g")
    const kre = new RegExp(getRegex(keywords), "g")
    const dre = new RegExp(getRegex(defines.concat(userDefs)), "g")
    const cre = new RegExp("(\\/\\*(.|\r|\n)+\\*\\/|\\/\\/.+)", "g")
    // remove first new line
    code = (code[0] == '\n' ? code.substring(1) : code)
    // fixing things for html
    code = code.replaceAll("<", "&lt;");
    code = code.replaceAll(">", "&gt;");
    // (heavy quote) lexing (heavy quote)
    code = code.replaceAll("\t", "    ");
    code = code.replaceAll(" ", "\x00"); // temporary
    code = code.replaceAll(ore, "<span class=\"operator\">$&</span>");
    code = code.replaceAll(cre, "<span class=\"comment\">$&</span>");
    code = code.replaceAll(pre, "<span class=\"prim\">$&</span>");
    code = code.replaceAll(tre, "<span class=\"type\">$&</span>");
    code = code.replaceAll(kre, "<span class=\"keyword\">$&</span>");
    code = code.replaceAll(dre, "<span class=\"defines\">$&</span>");
    code = code.replaceAll("\n", "<br>\n");
    code = code.replaceAll("\x00", "&nbsp;"); // told you it was temporary
    // unicode replacement
    code = code.replaceAll("λ", "&#x03BB;");
    code = code.replaceAll("≠", "&#x2260;");
    code = code.replaceAll("≤", "&#x2264;");
    code = code.replaceAll("≥", "&#x2265;");
    code = code.replaceAll("⊆", "&#x2286;");
    code = code.replaceAll("∈", "&#x2208;");
    code = code.replaceAll("∪", "&#x222A;");
    code = code.replaceAll("∩", "&#x2229;");
    code = code.replaceAll("⨄", "&#x2A04;");
    code = code.replaceAll("∘", "&#x2218;");
    code = code.replaceAll("∅", "&#x2205;");

    return code;
}

function removeImports(code){
    split = code.split("\n");
    // remove import statements
    while(split[0].trim().substring(0, 6) == "import") split.shift()
    // remove empty newlines
    while(split[0].trim()== "") split.shift()
    return split.join("\n")
}

function make_button(htmlCode, codeText){
    const copyButton = document.createElement("button")
    const copyTooltip = document.createElement("p")

    copyTooltip.classList.add("button-tooltip")
    copyButton.innerHTML = "<i class=\"fa-solid fa-clone\"></i>"
    copyButton.setAttribute("title", "Copy code")

    copyButton.onclick = () => {
        if (navigator) {
            navigator.clipboard.writeText(codeText[0] == '\n' ? codeText.substring(1) : codeText)
            copyTooltip.innerHTML = "Copied!"
        } else {
            copyTooltip.innerHTML = "Error copying code."
        }
        copyTooltip.style.opacity = "100";
    }
    copyButton.onmouseleave = copyButton.ontouchend = () => copyTooltip.style.opacity = "0";

    htmlCode.appendChild(copyButton)
    htmlCode.appendChild(copyTooltip)
}

// set codeblocks
for (let cb of codeBlocks) {
    try {
        const htmlCode = document.getElementById(cb)
        if (htmlCode == undefined) continue;

        // If code is cached just return that
        let code = cacheJS.get({'codeID': cb, 'type': 'html'})

        if(code){
            let codeText = cacheJS.get({'codeID': cb, 'type': 'text'})
            htmlCode.innerHTML = code
            make_button(htmlCode, codeText)
        } 
        // else make fetch and cache result
        else {
            const url = `${loc.includes("/pages") ? "../" : "./" }deduce-code/${cb}.pf`
            fetch(url)
            .then(res => {if (res.ok) return res.text(); else throw new Error()})
            .then(codeText => {
                codeText = removeImports(codeText)
                code = codeToHTML(codeText)
                cacheJS.set({'codeID': cb, 'type': 'html'}, code, 3600)
                cacheJS.set({'codeID': cb, 'type': 'text'}, codeText, 3600)
                htmlCode.innerHTML = code
                make_button(htmlCode, codeText)
            })
            .catch(err => htmlCode.innerHTML = "Error loading code block...")
        }
    } catch (error) {
        console.error(error);
    }
}
