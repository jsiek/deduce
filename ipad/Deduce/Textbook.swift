import Foundation

/// An error or warning from a check of the open file.
struct Diagnostic: Identifiable {
    let id = UUID()
    let range: Outline.Range
    let warning: Bool
    let message: String

    /// The 1-based line it's on.
    var line: Int { range.start.line + 1 }

    /// An incomplete proof: a `?`, which the textbook already shows.
    var isHole: Bool { message.hasPrefix("incomplete proof") }
}

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
        /// The labels of the givens it introduces (`assume H1`, `have H2`).
        var introduces: [String] = []
    }

    struct Link {
        let range: Outline.Range
        let rhs: String
        let reason: Reason?
        let status: Status
    }

    struct Arm {
        let range: Outline.Range
        /// "Case node(t1, l2)." or, for `cases`, "Case h1: P."
        let title: String
        /// The hypotheses shown after the title ("Assume IH1."): those of
        /// an `induction` or `switch` arm.
        let assumes: [String]
        /// The labels of the givens it introduces: its hypotheses, or the
        /// label in a `cases` arm's title.
        let introduces: [String]
        let blocks: [Block]
    }

    /// How a given can be used at the selected hole, and the line or arm
    /// that introduces it.
    struct GivenUse {
        let range: Outline.Range
        /// It proves the goal (`fillFromGivenAt`), rather than giving a
        /// step to take (`eliminateAt`).
        let proves: Bool
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

    /// A `?` still to prove: what the hole inspector works on.
    struct Hole {
        let range: Outline.Range
        let goal: Outline.Tree
        let givens: [Outline.Given]
    }

    let theorems: [Theorem]
    /// The file's holes in source order.
    let holes: [Hole]
    /// Errors and warnings by where they're shown: the range of the
    /// innermost line or chain link they're in, or else of their theorem.
    let notes: [Outline.Range: [Diagnostic]]
    /// Those that are in no theorem (a definition, an import, a parse error).
    let unplaced: [Diagnostic]

    init(outline: Outline, source: String, diagnostics: [Diagnostic]) {
        holes = outline.steps
            .filter { $0.kind == "PHole" }
            .compactMap { step in step.goal.map { Hole(range: step.range, goal: $0, givens: step.givens) } }
            .sorted { $0.range.start < $1.range.start }
        let builder = Builder(source: source)
        theorems = outline.theorems.map { theorem in
            let steps = outline.steps.filter { theorem.range.contains($0.range) }
            let roots = Node.forest(steps) { builder.slice($0.range) == "equations" }
            return Theorem(
                range: theorem.range,
                name: theorem.name,
                lemma: theorem.lemma,
                statement: withoutTypeParameters(display(theorem.formula)),
                blocks: builder.blocks(roots),
                status: roots.map(\.status).max() ?? .ok)
        }
        var notes: [Outline.Range: [Diagnostic]] = [:]
        var unplaced: [Diagnostic] = []
        let lines = theorems.flatMap { Self.lineRanges($0.blocks) }
        for diagnostic in diagnostics where !diagnostic.isHole {
            let at = diagnostic.range.start
            // Ranges are end-exclusive, so adjacent links don't both claim it.
            let around = { (range: Outline.Range) in
                range.start <= at && (at < range.end || at == range.start)
            }
            // The innermost: the one inside all the others that contain it.
            if let range = lines.filter(around).reduce(nil, { (best: Outline.Range?, range) in
                best.map { $0.contains(range) ? range : $0 } ?? range
            }) ?? theorems.first(where: { around($0.range) })?.range {
                notes[range, default: []].append(diagnostic)
            } else {
                unplaced.append(diagnostic)
            }
        }
        self.notes = notes
        self.unplaced = unplaced
    }

    /// Where each given in scope at `hole` is introduced: the line or case
    /// arm that assumes it, by label (an inner one hides an outer one).
    func givens(at hole: Outline.Range) -> [String: Outline.Range] {
        theorems.first { $0.range.contains(hole) }.flatMap { Self.scope($0.blocks, hole, [:]) } ?? [:]
    }

    /// The givens in scope at `hole`, if it's in `blocks`: those of
    /// `outer`, then those introduced before it. Each line's givens are in
    /// scope in the lines after it, an arm's in the arm.
    private static func scope(_ blocks: [Block], _ hole: Outline.Range,
                              _ outer: [String: Outline.Range]) -> [String: Outline.Range]? {
        var scope = outer
        for block in blocks {
            switch block {
            case .line(let line):
                if line.range == hole { return scope }
                if line.range.contains(hole) { return Self.scope(line.subproof, hole, scope) ?? scope }
                for label in line.introduces { scope[label] = line.range }
            case .chain(let range, _, _):
                if range.contains(hole) { return scope }
            case .cases(let range, _, let arms):
                guard range.contains(hole) else { continue }
                guard let arm = arms.first(where: { $0.range.contains(hole) }) else { return scope }
                for label in arm.introduces { scope[label] = arm.range }
                return Self.scope(arm.blocks, hole, scope) ?? scope
            }
        }
        return nil
    }

    /// The ranges of the lines and chain links in `blocks`, nested ones too.
    private static func lineRanges(_ blocks: [Block]) -> [Outline.Range] {
        blocks.flatMap { block -> [Outline.Range] in
            switch block {
            case .line(let line): [line.range] + lineRanges(line.subproof)
            case .chain(_, _, let links): links.map(\.range)
            case .cases(_, _, let arms): arms.flatMap { lineRanges($0.blocks) }
            }
        }
    }

    /// A step and the steps nested inside its range.
    final class Node {
        let step: Outline.Step
        var children: [Node] = []

        /// The worst status of this step and everything nested in it.
        var status: Status {
            children.map(\.status).reduce(Status(step.status), max)
        }

        /// Nest `steps` by range containment; returns the outermost ones in
        /// source order.
        static func forest(_ steps: [Outline.Step], isChain: (Outline.Step) -> Bool) -> [Node] {
            let sorted = steps.sorted {
                ($0.range.start, $1.range.end) < ($1.range.start, $0.range.end)
            }
            var roots: [Node] = []
            var open: [Node] = []
            for step in sorted {
                let node = Node(step, isChain: step.kind == "PTransitive" && isChain(step))
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

        /// Kinds whose children are parts proved separately: a
        /// conjunction's (`p1, p2`), and an `apply`'s rule and arguments.
        static let hasParts: Set<String> = ["PTuple", "ModusPonens"]

        /// Kinds that lead into the step after them, which proves what's
        /// left: in `have h: P by …` / `?`, the `?` finishes the part.
        static let leading: Set<String> = [
            "AllIntro", "ImpIntro", "PLet", "PTLetNew", "SomeElim", "Suffices",
            "RewriteGoal", "ApplyDefsGoal", "SimplifyGoal",
        ]

        /// An `equations` block, whose links follow it as siblings. A
        /// written-out `transitive (…) (…)` term is the same kind but is a
        /// reason; only the source tells them apart.
        let isChain: Bool

        init(_ step: Outline.Step, isChain: Bool) {
            self.step = step
            self.isChain = isChain
        }

        /// Whether this step starts a new line of the proof.
        var startsLine: Bool {
            Node.structural.contains(step.kind) && (step.kind != "PTransitive" || isChain)
        }

        /// A reason's last part can fall just outside its step's range: in
        /// `= rhs by expand length.` the `.` is its own step after the
        /// `expand`. A non-structural step that starts on the line where
        /// the previous sibling ends joins that sibling's reason, except
        /// among the parts of a `p1, p2` or an `apply … to`.
        private static func absorbContinuations(_ nodes: [Node], separate: Bool = false) -> [Node] {
            var kept: [Node] = []
            for node in nodes {
                node.children = absorbContinuations(node.children, separate: Node.hasParts.contains(node.step.kind))
                if !separate, let previous = kept.last, !node.startsLine,
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
            lines = source.scalarLines
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
                    let vars = (detail.vars ?? []).filter { $0.type.kind != "TypeType" }
                    if !vars.isEmpty {
                        blocks.append(line(node, letArbitrary(vars.map { ($0.name, display($0.type)) }) + ".", nil))
                    }
                case "ImpIntro":
                    let label = detail.label ?? ""
                    blocks.append(line(node, "Assume \(label)" + (detail.premise == nil ? "." : ":"),
                                       detail.premise.map(display), introduces: [label]))
                case "Induction", "SwitchProof", "Cases":
                    blocks.append(cases(node, rest: &rest))
                case "PTransitive" where node.isChain:
                    blocks.append(chain(node, rest: &rest))
                case "PLet":
                    blocks.append(line(node, "\(detail.label ?? "") :", step.formula.map(display), reason: true,
                                       introduces: detail.label.map { [$0] } ?? []))
                case "PAnnot":
                    blocks.append(line(node, "Hence", step.formula.map(display), reason: true))
                case "Suffices":
                    blocks.append(line(node, "It suffices to show", detail.claim.map(display), reason: true))
                case "RewriteGoal", "ApplyDefsGoal", "SimplifyGoal":
                    if step.formula?.text == "true" {
                        blocks.append(line(node, "This is immediate.", nil, reason: true))
                    } else {
                        blocks.append(line(node, "It remains to show", step.formula.map(display), reason: true))
                    }
                case "PHole", "PSorry":
                    blocks.append(line(node, "Still to prove:", step.goal.map(display)))
                case "PTLetNew":
                    blocks.append(line(node, "Define \(detail.name ?? "") =", detail.term.map(display)))
                case "SomeIntro":
                    let witnesses = (detail.witnesses ?? []).map(display).joined(separator: ", ")
                    blocks.append(line(node, "Choose \(witnesses).", nil))
                case "PTuple":
                    blocks.append(withParts(node, "We prove each part:", parts(node.children)))
                case "ModusPonens":
                    blocks.append(modusPonens(node))
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
        private func line(_ node: Node, _ prose: String, _ formula: String?, reason: Bool = false,
                          introduces: [String] = []) -> Block {
            let nested = reason && node.children.contains { $0.startsLine && Node.subproof.contains($0.step.kind) }
            return .line(Line(range: node.step.range, prose: prose, formula: formula,
                              reason: reason && !nested ? self.reason(node.step) : nil,
                              status: node.status,
                              subproof: nested ? blocks(node.children) : [],
                              introduces: introduces))
        }

        /// `apply rule to args`: "By rule, using H2 and H3." Arguments that
        /// are just a given's name are named there; the others (holes,
        /// proofs of their own) are parts listed under it.
        private func modusPonens(_ node: Node) -> Block {
            // The rule's name, without its instantiation (`less_trans[a, b, d]`).
            let rule = node.children.first.map { slice($0.step.range) } ?? ""
            let name = rule.prefix { $0 != "[" && $0 != "<" }.trimmingCharacters(in: .whitespaces)
            let args = node.children.dropFirst().flatMap { $0.step.kind == "PTuple" ? $0.children : [$0] }
            let groups = parts(args)
            let isName = { (part: [Node]) in part.count == 1 && part[0].step.kind == "PVar" }
            let named = groups.filter(isName).map { slice($0[0].step.range) }
            let others = groups.filter { !isName($0) }
            let using = named.isEmpty ? "" : ", using " + listed(named)
            let end = others.isEmpty ? "." : named.isEmpty ? ", using:" : " and:"
            return withParts(node, "By \(name)\(using)\(end)", others)
        }

        /// A line of `prose` with `parts` under it, each a line of its own.
        private func withParts(_ node: Node, _ prose: String, _ parts: [[Node]]) -> Block {
            .line(Line(range: node.step.range, prose: prose, formula: nil, reason: nil,
                       status: node.status, subproof: parts.map(part)))
        }

        /// `nodes` split into parts: each a run of steps that lead into the
        /// next (`have`, `assume`, …), ended by the one that proves the part.
        private func parts(_ nodes: [Node]) -> [[Node]] {
            var parts: [[Node]] = []
            var current: [Node] = []
            for node in nodes {
                current.append(node)
                if !Node.leading.contains(node.step.kind) {
                    parts.append(current)
                    current = []
                }
            }
            return current.isEmpty ? parts : parts + [current]
        }

        /// One part: the formula it proves, with its reason, or with its
        /// steps under it. A hole is its own "Still to prove" line.
        private func part(_ steps: [Node]) -> Block {
            let first = steps[0]
            let goal = first.step.goal.map(display)
            if steps.count == 1, !Node.hasParts.contains(first.step.kind) {
                return ["PHole", "PSorry"].contains(first.step.kind)
                    ? blocks(steps)[0] : line(first, "", goal, reason: true)
            }
            let range = Outline.Range(start: first.step.range.start, end: steps.last!.step.range.end)
            return .line(Line(range: range, prose: "", formula: goal, reason: nil,
                              status: steps.map(\.status).max() ?? .ok, subproof: blocks(steps)))
        }

        /// "H2", "H2 and H3", "H2, H3 and H4".
        private func listed(_ names: [String]) -> String {
            names.count < 2 ? names.joined() : names.dropLast().joined(separator: ", ") + " and " + names.last!
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
            case "SwitchProof": "By cases on \(step.detail.subject.map(display) ?? "it")."
            default: "By cases."
            }
            return .cases(range: step.range, intro: intro, arms: arms.map { arm in
                let header = arm.pattern.map(display) ?? [arm.label, arm.formula.map(display)]
                    .compactMap { $0 }.joined(separator: ": ")
                let assumes = arm.hypotheses ?? []
                return Arm(range: arm.range, title: "Case \(header).", assumes: assumes,
                           introduces: arm.pattern == nil ? [arm.label].compactMap { $0 } : assumes,
                           blocks: blocks(members.filter { arm.range.contains($0.step.range) }))
            })
        }

        /// `equations`: its links follow it as siblings, each starting where
        /// the previous one ended. (`equations` marks each link's left side
        /// with `#…#`, so compare them as displayed.)
        private func chain(_ node: Node, rest: inout ArraySlice<Node>) -> Block {
            var links: [Node] = []
            while let next = rest.first, next.step.kind == "PAnnot", let lhs = next.step.detail.lhs,
                  links.last.map({ $0.step.detail.rhs.map(display) == display(lhs) }) ?? true {
                links.append(rest.removeFirst())
            }
            return .chain(
                range: node.step.range,
                first: links.first?.step.detail.lhs.map(display) ?? "",
                links: links.map {
                    Link(range: $0.step.range, rhs: $0.step.detail.rhs.map(display) ?? "",
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

        func slice(_ range: Outline.Range) -> String {
            sourceText(lines, range)
        }
    }
}

/// The text of `range` in `source`, split into lines of Unicode scalars;
/// columns count Unicode scalars, as Python indexes strings.
func sourceText(_ lines: [[Unicode.Scalar]], _ range: Outline.Range) -> String {
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

extension String {
    /// This text's lines as Unicode scalars, for `sourceText`.
    var scalarLines: [[Unicode.Scalar]] {
        split(separator: "\n", omittingEmptySubsequences: false).map { Array($0.unicodeScalars) }
    }
}

/// A formula for display: without input-only syntax (`#…#` expansion
/// marks, explicit type arguments such as `@[]<U>`) or a pair of
/// parentheses around the whole formula. Primes are typeset as ′. The
/// quantifiers it starts with each end a line (see `leadingBreak`).
func display(_ formula: Outline.Tree) -> String {
    var text = shown(formula, leading: true)
    if text.hasPrefix("(") && text.hasSuffix(")") && closingParen(of: text) == text.index(before: text.endIndex) {
        text = String(text.dropFirst().dropLast())
    }
    return text.replacingOccurrences(of: "'", with: "′")
}

/// `tree`'s text, keeping only the subject of a `Mark` (`#…#`) or of a
/// `TermInst` (`@f<T>`): the first subtree of either. `leading`: `tree`
/// starts the formula, so a quantifier there ends its line.
private func shown(_ tree: Outline.Tree, leading: Bool = false) -> String {
    if tree.kind == "Mark" || tree.kind == "TermInst" {
        for case .tree(let subject) in tree.parts {
            return shown(subject, leading: leading)
        }
    }
    let leading = leading && isQuantifier(tree)
    return tree.parts.map { part in
        switch part {
        case .text(let text): leading ? leadingBreak(text) : text
        case .tree(let child): shown(child, leading: leading)
        }
    }.joined()
}

/// Whether `tree` is an `all` or `some` formula.
func isQuantifier(_ tree: Outline.Tree) -> Bool {
    tree.kind == "All" || tree.kind == "Some"
}

/// A text part of a quantifier that starts a formula: the `. ` after its
/// binders ends the line, so "all x:Nat. P" shows P on a line of its own.
func leadingBreak(_ text: String) -> String {
    text.hasSuffix(". ") ? String(text.dropLast()) + "\n" : text
}

/// `arbitrary a:Nat, xs:List<Nat>` in words: "Let a be an arbitrary Nat
/// and xs an arbitrary List<Nat>".
func letArbitrary(_ vars: [(name: String, type: String)]) -> String {
    let clauses = vars.enumerated().map { i, v in "\(v.name)\(i == 0 ? " be" : "") an arbitrary \(v.type)" }
    let last = clauses.count > 1 ? " and " + clauses.last! : ""
    return "Let " + clauses.dropLast(last.isEmpty ? 0 : 1).joined(separator: ", ") + last
}

/// A checker message without the `/path/to/File.pf:13.86-13.119: `
/// locations it puts in front of nested errors.
func withoutLocations(_ message: String) -> String {
    message.replacingOccurrences(of: #"\S+\.pf:\d+\.\d+-\d+\.\d+: "#, with: "",
                                 options: .regularExpression)
}

/// Drop `T:type` binders from a statement's leading `all`, as the proof
/// drops `arbitrary T:type`: "all U:type, xs:List<U>. P" reads
/// "all xs:List<U>. P", and "all T:type. P" reads "P".
func withoutTypeParameters(_ statement: String) -> String {
    statement
        .replacingOccurrences(of: #"^all ([A-Za-z_][A-Za-z0-9_]*:type, )+"#, with: "all ",
                              options: .regularExpression)
        .replacingOccurrences(of: #"^all [A-Za-z_][A-Za-z0-9_]*:type\.\s"#, with: "",
                              options: .regularExpression)
}

/// The index of the parenthesis that closes the one at `text`'s start.
func closingParen(of text: String) -> String.Index? {
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
