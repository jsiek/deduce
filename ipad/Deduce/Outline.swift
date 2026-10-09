import Foundation

/// The `deduce/proofOutline` payload (see `ProofStep` / `ProofOutline` in
/// `lsp/query.py`). Lines and characters are 0-indexed, as everywhere in LSP.
struct Outline: Decodable {
    let uri: String
    let steps: [Step]
    let theorems: [Theorem]

    struct Position: Decodable, Comparable, Hashable {
        let line: Int
        let character: Int

        static func < (a: Position, b: Position) -> Bool {
            (a.line, a.character) < (b.line, b.character)
        }
    }

    struct Range: Decodable, Hashable {
        let start: Position
        let end: Position

        func contains(_ other: Range) -> Bool {
            start <= other.start && other.end <= end
        }
    }

    /// A term, formula, type or pattern as Deduce prints it, with its
    /// structure: its text is the concatenation of `parts` (see `TermTree`
    /// in `lsp/query.py`).
    struct Tree: Decodable, Equatable {
        let kind: String
        let parts: [Part]

        enum Part: Decodable, Equatable {
            case text(String)
            indirect case tree(Tree)

            init(from decoder: Decoder) throws {
                let container = try decoder.singleValueContainer()
                if let text = try? container.decode(String.self) {
                    self = .text(text)
                } else {
                    self = .tree(try container.decode(Tree.self))
                }
            }
        }

        /// Exactly what Deduce prints.
        var text: String {
            parts.map { part in
                switch part {
                case .text(let text): text
                case .tree(let tree): tree.text
                }
            }.joined()
        }
    }

    struct Theorem: Decodable {
        let name: String
        let formula: Tree
        let lemma: Bool
        let range: Range
    }

    struct Use: Decodable {
        let name: String
        let kind: String  // "given", "lemma" or "definition"
    }

    struct Given: Decodable {
        let label: String
        let formula: Tree
    }

    struct Step: Decodable {
        let kind: String
        let range: Range
        let goal: Tree?
        let formula: Tree?
        let givens: [Given]
        let uses: [Use]
        let status: String  // "ok", "error" or "incomplete"
        let detail: Detail
    }

    /// Per-kind data; each kind fills in only its own fields.
    struct Detail: Decodable {
        let vars: [Variable]?
        let label: String?
        let premise: Tree?
        let variable: String?
        let subject: Tree?
        let cases: [Case]?
        let lhs: Tree?
        let rhs: Tree?
        let claim: Tree?
        let name: String?
        let term: Tree?
        let witnesses: [Tree]?
    }

    struct Variable: Decodable {
        let name: String
        let type: Tree
    }

    struct Case: Decodable {
        let pattern: Tree?
        let label: String?
        let formula: Tree?
        let hypotheses: [String]?
        let range: Range
    }
}
