import SwiftUI

/// A formula whose subterms can be tapped. Tapping selects the smallest
/// subterm under the finger (a call, for its callee or operator); tapping
/// the selected subterm again selects its parent. `selection` is a path into
/// the formula's tree (see `TermTree` in `lsp/query.py`); `nil` means
/// nothing is selected.
struct FormulaView: View {
    let tree: Outline.Tree
    @Binding var selection: [Int]?

    var body: some View {
        Text(attributed)
            .font(TextbookView.formulaFont)
            .tint(.primary)
            .environment(\.openURL, OpenURLAction { url in
                guard let tapped = Self.path(url) else { return .discarded }
                selection = tapped == selection ? (tapped.isEmpty ? nil : Array(tapped.dropLast())) : tapped
                return .handled
            })
    }

    private var attributed: AttributedString {
        var result = AttributedString()
        for (text, path) in Self.runs(tree, path: []) {
            var run = AttributedString(text.replacingOccurrences(of: "'", with: "′"))
            run.link = URL(string: "subterm:" + path.map(String.init).joined(separator: "."))
            if let selection, path.starts(with: selection) {
                run.backgroundColor = Color.accentColor.opacity(0.22)
            }
            result += run
        }
        return result
    }

    private static func path(_ url: URL) -> [Int]? {
        guard url.scheme == "subterm" else { return nil }
        let body = url.absoluteString.dropFirst("subterm:".count)
        return body.isEmpty ? [] : body.split(separator: ".").compactMap { Int($0) }
    }

    /// The formula's text in pieces, each with the path of the subterm a
    /// tap on it selects. `#…#` marks and `@f<T>` instantiations show only
    /// their subject, as in the textbook view.
    static func runs(_ tree: Outline.Tree, path: [Int]) -> [(String, [Int])] {
        let children = subtrees(tree)
        if tree.kind == "Mark" || tree.kind == "TermInst", let subject = children.first {
            return runs(subject, path: path + [0])
        }
        let function = functionIndex(tree)
        var result: [(String, [Int])] = []
        var index = 0
        for part in tree.parts {
            switch part {
            case .text(let text):
                result.append((text, path))
            case .tree(let child):
                result += index == function
                    ? [(child.text, path)]  // a call's callee or operator selects the call
                    : runs(child, path: path + [index])
                index += 1
            }
        }
        return result
    }

    static func subtrees(_ tree: Outline.Tree) -> [Outline.Tree] {
        tree.parts.compactMap { if case .tree(let child) = $0 { child } else { nil } }
    }

    /// Which subtree of a call is its callee (`f(x)`, `not P`) or infix
    /// operator (`x + y`), if any.
    static func functionIndex(_ tree: Outline.Tree) -> Int? {
        guard tree.kind == "Call" else { return nil }
        let children = subtrees(tree)
        if tree.parts.count >= 2, case .tree = tree.parts[0], case .text(let next) = tree.parts[1],
           next.hasPrefix("(") {
            return 0
        }
        if children.count == 3, children[1].kind == "Var" { return 1 }
        if children.count == 2, case .tree(let first) = tree.parts[0], first.kind == "Var" { return 0 }
        return nil
    }

    /// The subterm at `path`.
    static func subtree(_ tree: Outline.Tree, at path: [Int]) -> Outline.Tree? {
        var node = tree
        for i in path {
            let children = subtrees(node)
            guard i < children.count else { return nil }
            node = children[i]
        }
        return node
    }

    /// The definitions called in `tree`, in source spelling (`operator++`),
    /// first occurrence first: what `expand` could unfold there.
    static func calledNames(_ tree: Outline.Tree) -> [String] {
        var names: [String] = []
        func visit(_ node: Outline.Tree) {
            let children = subtrees(node)
            if let f = functionIndex(node), f < children.count {
                var callee = children[f]
                if callee.kind == "TermInst", let subject = subtrees(callee).first { callee = subject }
                let name = callee.text
                if !logical.contains(name) && !names.contains(spelled(name)) { names.append(spelled(name)) }
            }
            children.forEach(visit)
        }
        visit(tree)
        return names
    }

    private static let logical: Set<String> = ["=", "≠", "and", "or", "not", "⇔", "if", "then"]

    /// `name` as written after `expand`: operators take an `operator` prefix.
    private static func spelled(_ name: String) -> String {
        name.unicodeScalars.allSatisfy { CharacterSet.alphanumerics.contains($0) || $0 == "_" }
            ? name : "operator" + name
    }
}
