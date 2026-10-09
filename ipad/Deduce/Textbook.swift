import Foundation

/// A textbook rendering of a checked file, built from its proof outline:
/// each theorem as "Theorem. … Proof. … ∎", each proof step as prose and
/// the formula it establishes, with the reason kept to one side.
struct Textbook {
    enum Status: Int, Comparable {
        case ok, incomplete, error

        init(_ name: String) {
            self = name == "error" ? .error : name == "incomplete" ? .incomplete : .ok
        }

        static func < (a: Status, b: Status) -> Bool { a.rawValue < b.rawValue }
    }

    struct Reason {
        /// Short form built from the step's uses, e.g. "IH; def. of ++, length".
        let summary: String
        /// The reason as written in the source.
        let source: String
    }

    struct Line {
        let range: Outline.Range
        let prose: String
        let formula: String?
        let reason: Reason?
        let status: Status
        /// The steps proving this line, when its reason is a proof of
        /// several steps rather than a single justification.
        var subproof: [Block] = []
    }

    struct Link {
        let range: Outline.Range
        let rhs: String
        let reason: Reason?
        let status: Status
    }

    struct Arm {
        let range: Outline.Range
        let title: String
        let blocks: [Block]
    }

    enum Block: Identifiable {
        case line(Line)
        /// An `equations` chain: the first left-hand side, then `= rhs` links.
        case chain(range: Outline.Range, first: String, links: [Link])
        case cases(range: Outline.Range, intro: String, arms: [Arm])

        var id: Outline.Range {
            switch self {
            case .line(let line): line.range
            case .chain(let range, _, _), .cases(let range, _, _): range
            }
        }
    }

    struct Theorem: Identifiable {
        let range: Outline.Range
        let name: String
        let lemma: Bool
        let statement: String
        let blocks: [Block]
        let status: Status

        var id: Outline.Range { range }
    }

    let theorems: [Theorem]

    init(outline: Outline, source: String) {
        let builder = Builder(source: source)
        theorems = outline.theorems.map { theorem in
            let steps = outline.steps.filter { theorem.range.contains($0.range) }
            let roots = Node.forest(steps)
            return Theorem(
                range: theorem.range,
                name: theorem.name,
                lemma: theorem.lemma,
                statement: withoutTypeParameters(clean(theorem.formula)),
                blocks: builder.blocks(roots),
                status: roots.map(\.status).max() ?? .ok)
        }
    }

    /// A step and the steps nested inside its range.
    final class Node {
        let step: Outline.Step
        var children: [Node] = []

        init(_ step: Outline.Step) { self.step = step }

        /// The worst status of this step and everything nested in it.
        var status: Status {
            children.map(\.status).reduce(Status(step.status), max)
        }

        /// Nest `steps` by range containment; returns the outermost ones in
        /// source order.
        static func forest(_ steps: [Outline.Step]) -> [Node] {
            let sorted = steps.sorted {
                ($0.range.start, $1.range.end) < ($1.range.start, $0.range.end)
            }
            var roots: [Node] = []
            var open: [Node] = []
            for step in sorted {
                let node = Node(step)
                while let top = open.last, !top.step.range.contains(step.range) {
                    open.removeLast()
                }
                if let parent = open.last {
                    parent.children.append(node)
                } else {
                    roots.append(node)
                }
                open.append(node)
            }
            return absorbContinuations(roots)
        }

        /// Kinds that start a new line of the proof. Anything else is part
        /// of some step's reason.
        static let structural: Set<String> = [
            "AllIntro", "ImpIntro", "Induction", "SwitchProof", "Cases", "PTransitive",
            "PLet", "PAnnot", "Suffices", "RewriteGoal", "ApplyDefsGoal", "SimplifyGoal",
            "PHole", "PSorry", "PTLetNew", "SomeIntro",
        ]

        /// Kinds that, found in a step's reason, make the reason a proof of
        /// its own, shown nested under the step.
        static let subproof = structural.subtracting(["RewriteGoal", "ApplyDefsGoal", "SimplifyGoal"])

        /// A reason's last part can fall just outside its step's range: in
        /// `= rhs by expand length.` the `.` is its own step after the
        /// `expand`. A non-structural step that starts on the line where
        /// the previous sibling ends joins that sibling's reason.
        private static func absorbContinuations(_ nodes: [Node]) -> [Node] {
            var kept: [Node] = []
            for node in nodes {
                node.children = absorbContinuations(node.children)
                if let previous = kept.last, !structural.contains(node.step.kind),
                   node.step.range.start.line == previous.step.range.end.line {
                    previous.children.append(node)
                } else {
                    kept.append(node)
                }
            }
            return kept
        }
    }

    private struct Builder {
        let lines: [[Unicode.Scalar]]

        init(source: String) {
            lines = source.split(separator: "\n", omittingEmptySubsequences: false)
                .map { Array($0.unicodeScalars) }
        }

        func blocks(_ nodes: [Node]) -> [Block] {
            var blocks: [Block] = []
            var rest = nodes[...]
            while let node = rest.popFirst() {
                let step = node.step
                let detail = step.detail
                switch step.kind {
                case "AllIntro":
                    // Type parameters are input-only: the statement already
                    // shows them, and textbooks don't introduce them.
                    let vars = (detail.vars ?? []).filter { $0.type != "type" }
                    if !vars.isEmpty {
                        let list = vars.map { "\($0.name) : \(clean($0.type))" }
                        blocks.append(line(node, "Let \(list.joined(separator: ", ")) be arbitrary.", nil))
                    }
                case "ImpIntro":
                    let label = detail.label ?? ""
                    blocks.append(line(node, "Assume \(label)" + (detail.premise == nil ? "." : ":"),
                                       detail.premise.map(clean)))
                case "Induction", "SwitchProof", "Cases":
                    blocks.append(cases(node, rest: &rest))
                case "PTransitive":
                    blocks.append(chain(node, rest: &rest))
                case "PLet":
                    blocks.append(line(node, "\(detail.label ?? "") :", step.formula.map(clean), reason: true))
                case "PAnnot":
                    blocks.append(line(node, "Hence", step.formula.map(clean), reason: true))
                case "Suffices":
                    blocks.append(line(node, "It suffices to show", detail.claim.map(clean), reason: true))
                case "RewriteGoal", "ApplyDefsGoal", "SimplifyGoal":
                    if step.formula == "true" {
                        blocks.append(line(node, "This is immediate.", nil, reason: true))
                    } else {
                        blocks.append(line(node, "It remains to show", step.formula.map(clean), reason: true))
                    }
                case "PHole", "PSorry":
                    blocks.append(line(node, "Still to prove:", step.goal.map(clean)))
                case "PTLetNew":
                    blocks.append(line(node, "Define \(detail.name ?? "") =", detail.term.map(clean)))
                case "SomeIntro":
                    let witnesses = (detail.witnesses ?? []).map(clean).joined(separator: ", ")
                    blocks.append(line(node, "Choose \(witnesses).", nil))
                default:
                    // A proof term that finishes the goal, e.g. `p2` or `.`.
                    blocks.append(line(node, step.uses.isEmpty ? "This is immediate." : "This follows.",
                                       nil, reason: true))
                }
            }
            return blocks
        }

        /// A line for `node`. With `reason`, its reason is either nested as a
        /// sub-proof (when it has steps of its own) or summarized.
        private func line(_ node: Node, _ prose: String, _ formula: String?, reason: Bool = false) -> Block {
            let nested = reason && node.children.contains { Node.subproof.contains($0.step.kind) }
            return .line(Line(range: node.step.range, prose: prose, formula: formula,
                              reason: reason && !nested ? self.reason(node.step) : nil,
                              status: node.status,
                              subproof: nested ? blocks(node.children) : []))
        }

        /// `induction` / `switch` / `cases`: the steps of each arm are those
        /// inside its range, whether nested under the step or following it.
        private func cases(_ node: Node, rest: inout ArraySlice<Node>) -> Block {
            let step = node.step
            let arms = step.detail.cases ?? []
            var members = node.children
            while let next = rest.first, arms.contains(where: { $0.range.contains(next.step.range) }) {
                members.append(rest.removeFirst())
            }
            let intro = switch step.kind {
            case "Induction": "By induction on \(step.detail.variable ?? "it")."
            case "SwitchProof": "By cases on \(clean(step.detail.subject ?? ""))."
            default: "By cases."
            }
            return .cases(range: step.range, intro: intro, arms: arms.map { arm in
                let header = arm.pattern.map(clean) ?? [arm.label, arm.formula.map(clean)]
                    .compactMap { $0 }.joined(separator: ": ")
                let assume = (arm.hypotheses ?? []).isEmpty
                    ? "" : " Assume \(arm.hypotheses!.joined(separator: ", "))."
                return Arm(range: arm.range, title: "Case \(header).\(assume)",
                           blocks: blocks(members.filter { arm.range.contains($0.step.range) }))
            })
        }

        /// `equations`: its links follow it as siblings, each starting where
        /// the previous one ended.
        private func chain(_ node: Node, rest: inout ArraySlice<Node>) -> Block {
            var links: [Node] = []
            while let next = rest.first, next.step.kind == "PAnnot", let lhs = next.step.detail.lhs,
                  links.last.map({ $0.step.detail.rhs == lhs }) ?? true {
                links.append(rest.removeFirst())
            }
            return .chain(
                range: node.step.range,
                first: clean(links.first?.step.detail.lhs ?? ""),
                links: links.map {
                    Link(range: $0.step.range, rhs: clean($0.step.detail.rhs ?? ""),
                         reason: reason($0.step), status: $0.status)
                })
        }

        private func reason(_ step: Outline.Step) -> Reason {
            let names = { (kind: String) in
                step.uses.filter { $0.kind == kind }.map {
                    $0.name.hasPrefix("operator ") ? String($0.name.dropFirst(9)) : $0.name
                }
            }
            let definitions = names("definition")
            let parts = names("given") + names("lemma")
                + (definitions.isEmpty ? [] : ["def. of " + definitions.joined(separator: ", ")])
            var text = slice(step.range)
            if let by = text.range(of: " by ") {
                text = String(text[by.upperBound...])
            }
            text = text.trimmingCharacters(in: .whitespacesAndNewlines)
            if text.hasPrefix("{") && text.hasSuffix("}") {
                text = String(text.dropFirst().dropLast())
            }
            return Reason(summary: parts.joined(separator: "; "),
                          source: text.split(whereSeparator: \.isWhitespace).joined(separator: " "))
        }

        /// The source text of `range`; columns count Unicode scalars, as
        /// Python indexes strings.
        private func slice(_ range: Outline.Range) -> String {
            guard range.start.line < lines.count, range.end.line < lines.count else { return "" }
            var scalars: [Unicode.Scalar] = []
            for n in range.start.line...range.end.line {
                let line = lines[n]
                let from = n == range.start.line ? min(range.start.character, line.count) : 0
                let to = n == range.end.line ? min(range.end.character, line.count) : line.count
                if from < to { scalars += line[from..<to] }
                if n != range.end.line { scalars.append("\n") }
            }
            var text = String.UnicodeScalarView()
            text.append(contentsOf: scalars)
            return String(text)
        }
    }
}

/// Remove input-only syntax from a formula for display: `#…#` expansion
/// marks, explicit type arguments such as `@[]<U>`, and a pair of
/// parentheses around the whole formula. Primes are typeset as ′.
func clean(_ formula: String) -> String {
    var text = formula.replacingOccurrences(of: "#", with: "")
    text = text.replacingOccurrences(
        of: #"@(\[\]|[A-Za-z_][A-Za-z0-9_']*)<[^<>]*>"#, with: "$1", options: .regularExpression)
    if text.hasPrefix("(") && text.hasSuffix(")") && closingParen(of: text) == text.index(before: text.endIndex) {
        text = String(text.dropFirst().dropLast())
    }
    return text.replacingOccurrences(of: "'", with: "′")
}

/// Drop `T:type` binders from a statement's leading `all`, as the proof
/// drops `arbitrary T:type`: "all U:type, xs:List<U>. P" reads
/// "all xs:List<U>. P", and "all T:type. P" reads "P".
func withoutTypeParameters(_ statement: String) -> String {
    statement
        .replacingOccurrences(of: #"^all ([A-Za-z_][A-Za-z0-9_]*:type, )+"#, with: "all ",
                              options: .regularExpression)
        .replacingOccurrences(of: #"^all [A-Za-z_][A-Za-z0-9_]*:type\. "#, with: "",
                              options: .regularExpression)
}

/// The index of the parenthesis that closes the one at `text`'s start.
private func closingParen(of text: String) -> String.Index? {
    var depth = 0
    for index in text.indices {
        if text[index] == "(" { depth += 1 }
        if text[index] == ")" {
            depth -= 1
            if depth == 0 { return index }
        }
    }
    return nil
}
