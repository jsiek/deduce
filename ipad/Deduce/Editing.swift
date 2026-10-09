import Foundation

/// A text edit as the server sends it: 0-indexed, with characters counting
/// Unicode scalars (as the server's Python strings index them).
struct TextEdit {
    let range: Outline.Range
    let newText: String

    /// The edits for `uri` in an LSP `WorkspaceEdit` payload.
    static func edits(in workspaceEdit: Any?, for uri: String) -> [TextEdit] {
        guard let edit = workspaceEdit as? [String: Any],
              let changes = edit["changes"] as? [String: Any],
              let items = changes[uri] as? [[String: Any]]
        else { return [] }
        return items.compactMap { item in
            guard let text = item["newText"] as? String, let range = decode(Outline.Range.self, item["range"])
            else { return nil }
            return TextEdit(range: range, newText: text)
        }
    }
}

extension String {
    /// This text with `edit` applied.
    func applying(_ edit: TextEdit) -> String {
        var scalars = Array(unicodeScalars)
        let from = scalarOffset(of: edit.range.start, in: scalars)
        let to = max(from, scalarOffset(of: edit.range.end, in: scalars))
        scalars.replaceSubrange(from..<to, with: edit.newText.unicodeScalars)
        var result = String.UnicodeScalarView()
        result.append(contentsOf: scalars)
        return String(result)
    }

    private func scalarOffset(of position: Outline.Position, in scalars: [Unicode.Scalar]) -> Int {
        var line = 0
        var index = 0
        while line < position.line, index < scalars.count {
            if scalars[index] == "\n" { line += 1 }
            index += 1
        }
        var column = 0
        while column < position.character, index < scalars.count, scalars[index] != "\n" {
            column += 1
            index += 1
        }
        return index
    }
}

/// Decode a JSON value that arrived as part of a `[String: Any]` message.
func decode<T: Decodable>(_ type: T.Type, _ value: Any?) -> T? {
    guard let value, JSONSerialization.isValidJSONObject(value),
          let data = try? JSONSerialization.data(withJSONObject: value)
    else { return nil }
    return try? JSONDecoder().decode(type, from: data)
}

/// The proof steps the server can take at a hole, as typed calls.
extension DeduceServer {
    /// A step the server checked before it's applied: the goal it leaves
    /// (`nil` when it proves the goal) and the edit that makes it.
    struct Preview {
        let goal: Outline.Tree?
        let edits: [TextEdit]
        /// Why the step can't be taken, when it can't.
        let problem: String?
    }

    struct Lemma: Identifiable, Decodable {
        let name: String
        let signature: String?
        let unify_tier: String?

        var id: String { name }
    }

    private func position(_ p: Outline.Position) -> [String: Any] {
        ["line": p.line, "character": p.character]
    }

    /// The server's code actions at `hole` (Refine, Induction), by title.
    func codeActions(at hole: Outline.Position) async -> [(title: String, edits: [TextEdit])] {
        let range = ["start": position(hole), "end": position(hole)]
        let result = await request("textDocument/codeAction",
                                   ["range": range, "context": ["diagnostics": [Any]()]])
        guard let uri = openURI, let actions = result as? [[String: Any]] else { return [] }
        return actions.compactMap { action in
            guard let title = action["title"] as? String else { return nil }
            let edits = TextEdit.edits(in: action["edit"], for: uri)
            return edits.isEmpty ? nil : (title, edits)
        }
    }

    /// The names a `deduce/…VarsAt` / `deduce/matchingGivensAt` request offers.
    func names(_ method: String, at hole: Outline.Position) async -> [String] {
        await request(method, ["position": position(hole)]) as? [String] ?? []
    }

    /// The edit a `WorkspaceEdit`-returning request makes at `hole`.
    func edits(_ method: String, at hole: Outline.Position, _ params: [String: Any]) async -> [TextEdit] {
        var all = params
        all["position"] = position(hole)
        let result = await request(method, all)
        guard let uri = openURI else { return [] }
        return TextEdit.edits(in: result, for: uri)
    }

    /// Preview `expand names` or `replace equation` on the subterm of the
    /// goal at `path` (`[]` for the whole goal).
    func preview(_ method: String, at hole: Outline.Position, subterm path: [Int],
                 _ params: [String: Any]) async -> Preview {
        var all = params
        all["position"] = position(hole)
        all["subterm"] = path
        guard let uri = openURI, let result = await request(method, all) as? [String: Any] else {
            return Preview(goal: nil, edits: [], problem: "The server didn't answer.")
        }
        let edits = TextEdit.edits(in: result["edit"], for: uri)
        let problem = result["outcome"] as? String == "ok" ? nil
            : (result["message"] as? String ?? "This step doesn't apply here.")
        return Preview(goal: decode(Outline.Tree.self, result["goal"]), edits: edits, problem: problem)
    }

    /// Lemmas ranked against the subterm at `path`, best first.
    func lemmas(at hole: Outline.Position, subterm path: [Int]) async -> [Lemma] {
        decode([Lemma].self, await request("deduce/lemmasForSubterm",
                                           ["position": position(hole), "subterm": path, "limit": 12])) ?? []
    }
}
