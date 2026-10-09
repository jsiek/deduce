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

    struct Theorem: Decodable {
        let name: String
        let formula: String
        let lemma: Bool
        let range: Range
    }

    struct Use: Decodable {
        let name: String
        let kind: String  // "given", "lemma" or "definition"
    }

    struct Given: Decodable {
        let label: String
        let formula: String
    }

    struct Step: Decodable {
        let kind: String
        let range: Range
        let goal: String?
        let formula: String?
        let givens: [Given]
        let uses: [Use]
        let status: String  // "ok", "error" or "incomplete"
        let detail: Detail
    }

    /// Per-kind data; each kind fills in only its own fields.
    struct Detail: Decodable {
        let vars: [Variable]?
        let label: String?
        let premise: String?
        let variable: String?
        let subject: String?
        let cases: [Case]?
        let lhs: String?
        let rhs: String?
        let claim: String?
        let name: String?
        let term: String?
        let witnesses: [String]?
    }

    struct Variable: Decodable {
        let name: String
        let type: String
    }

    struct Case: Decodable {
        let pattern: String?
        let label: String?
        let formula: String?
        let hypotheses: [String]?
        let range: Range
    }
}
