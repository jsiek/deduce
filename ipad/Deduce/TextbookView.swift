import SwiftUI

/// How much of each step's reason to show.
enum ReasonLevel: String, CaseIterable, Identifiable {
    case full = "Full", summary = "Summary", hidden = "Hidden"

    var id: Self { self }

    /// Tapping a reason cycles through the levels.
    var next: ReasonLevel {
        switch self {
        case .full: .summary
        case .summary: .hidden
        case .hidden: .full
        }
    }
}

/// The textbook view of a checked file. Tapping a step selects it (the
/// source pane highlights it); tapping a reason cycles how much of it shows.
/// At a selected hole, the givens it can use are marked where they're
/// introduced (green when one proves the goal), and tapping one uses it.
/// So are the variables it can split on (tap for "Cases on x"), and in its
/// goal, the variables the goal binds up front (tap to make one arbitrary,
/// or to choose between that and induction on it).
struct TextbookView: View {
    let book: Textbook
    let defaultLevel: ReasonLevel
    /// Whether steps can be edited (as text, or at holes).
    let editable: Bool
    @Binding var selection: Outline.Range?
    /// Per-step overrides of `defaultLevel`, by step range.
    @Binding var levels: [Outline.Range: ReasonLevel]
    /// A step to scroll to; cleared once scrolled.
    @Binding var scrollTarget: Outline.Range?
    /// The givens the selected hole can use, by label.
    let uses: [String: Textbook.GivenUse]
    /// Called with a given's label to use it at the selected hole.
    let useGiven: (String) -> Void
    /// The `all` given asking for values, shown in a popover beside it.
    @Binding var instantiating: String?
    /// The popover's content for a given's label.
    let instantiator: (String) -> AnyView
    /// The variables the selected hole can split on, by name, with the
    /// line or arm that introduces each.
    let splittable: [String: Outline.Range]
    /// Called with a variable's name to split on it at the selected hole.
    let split: (String) -> Void
    /// The variables the selected hole's goal binds up front.
    let binders: [DeduceServer.GoalBinder]
    /// Called with the name of one of `binders` when it's tapped.
    let tapBinder: (String) -> Void
    /// The binder whose choice (arbitrary or induction) is showing.
    @Binding var choosingFor: String?
    /// Called to make a binder arbitrary (`false`) or induct on it (`true`).
    let introduce: (String, Bool) -> Void
    /// Assumes the selected hole's goal's premise, when it's an `if`: a
    /// tap on the goal's `if`.
    let assume: (() -> Void)?
    /// Called with a step's range to edit it as text.
    let editAsText: (Outline.Range) -> Void

    var body: some View {
        ScrollViewReader { proxy in
            ScrollView {
                LazyVStack(alignment: .leading, spacing: 32) {
                    ForEach(book.theorems) { theorem in
                        theoremView(theorem).id(theorem.range)
                    }
                }
                .padding(24)
                .frame(maxWidth: 820, alignment: .leading)
            }
            .environment(\.openURL, openVariable)
            .onChange(of: scrollTarget) { _, target in
                guard let target else { return }
                if let theorem = book.theorems.first(where: { $0.range.contains(target) }) {
                    withAnimation { proxy.scrollTo(theorem.range, anchor: .top) }
                }
                scrollTarget = nil
            }
        }
    }

    private func theoremView(_ theorem: Textbook.Theorem) -> some View {
        VStack(alignment: .leading, spacing: 10) {
            HStack(alignment: .firstTextBaseline) {
                (Text(theorem.lemma ? "Lemma" : "Theorem").bold()
                    + Text(" (\(theorem.name)).").italic())
                    .font(.system(.title3, design: .serif))
                statusMark(theorem.status)
            }
            Text(theorem.statement).font(Self.formulaFont).textSelection(.enabled)
            notes(theorem.range)
            Text("Proof.").italic().font(Self.proseFont).padding(.top, 4)
            blocksView(theorem.blocks)
            HStack {
                Spacer()
                Text("∎").font(Self.proseFont)
            }
        }
    }

    private func blocksView(_ blocks: [Textbook.Block]) -> AnyView {
        AnyView(VStack(alignment: .leading, spacing: 8) {
            ForEach(blocks) { block in
                switch block {
                case .line(let line): lineView(line)
                case .chain(_, let first, let links): chainView(first: first, links: links)
                case .cases(_, let intro, let arms): casesView(intro: intro, arms: arms)
                }
            }
        })
    }

    private func lineView(_ line: Textbook.Line) -> some View {
        let level = levels[line.range] ?? defaultLevel
        let isHole = editable && book.holes.contains { $0.range == line.range }
        let given = line.introduces.first { uses[$0]?.range == line.range }
        return VStack(alignment: .leading, spacing: 8) {
            HStack(alignment: .firstTextBaseline, spacing: 8) {
                if isHole {
                    // A hole is marked `?`: tap it to see the steps you can take.
                    Text("?").font(Self.formulaFont).bold()
                        .padding(.horizontal, 8)
                        .background(Capsule().fill(Color.orange.opacity(0.2)))
                }
                variablesText(line.prose, line.variables.filter { splittable[$0] == line.range })
                    .font(Self.proseFont)
                if let formula = line.formula {
                    // The selected hole's goal marks the variables it binds
                    // up front, or the `if` that starts it.
                    let goal = isHole && selection == line.range
                    variablesText(formula, goal ? binders.map(\.name) : [], binder: true,
                                  assume: goal && assume != nil)
                        .font(Self.formulaFont)
                }
                statusMark(line.status)
                Spacer(minLength: 16)
                if let reason = line.reason {
                    reasonView(reason, for: line.range)
                } else if !line.subproof.isEmpty {
                    // A sub-proof folds away like a reason does.
                    Image(systemName: level == .hidden ? "chevron.right" : "chevron.down")
                        .foregroundStyle(.secondary)
                        .contentShape(Rectangle())
                        .onTapGesture { levels[line.range] = level == .hidden ? .full : .hidden }
                }
                line.introduces.first.map(sideLabel)
            }
            .padding(.vertical, 2)
            .background { given.map { usable($0) } ?? AnyView(selected(line.range)) }
            .contentShape(Rectangle())
            .onTapGesture { if let given { useGiven(given) } else { selection = line.range } }
            .popover(isPresented: asking(given)) { given.map(instantiator) }
            .popover(isPresented: choosing(isHole && selection == line.range)) { binderChoice }
            .contextMenu { editMenu(line.range) }
            notes(line.range)
            // A sub-proof with a `?` in it stays open, so the `?` can be seen.
            if !line.subproof.isEmpty && (level != .hidden || holdsHole(line.range)) {
                blocksView(line.subproof)
                    .padding(.leading, 12)
                    .overlay(alignment: .leading) {
                        Rectangle().fill(Color.secondary.opacity(0.25)).frame(width: 2).offset(x: -8)
                    }
                    .padding(.leading, 12)
            }
        }
    }

    private func chainView(first: String, links: [Textbook.Link]) -> some View {
        Grid(alignment: .leadingFirstTextBaseline, horizontalSpacing: 10, verticalSpacing: 6) {
            GridRow {
                Color.clear.gridCellUnsizedAxes([.horizontal, .vertical])
                Text(first).font(Self.formulaFont).fixedSize().gridCellColumns(2)
            }
            ForEach(links, id: \.range) { link in
                GridRow {
                    Text("=").font(Self.formulaFont)
                    HStack(alignment: .firstTextBaseline, spacing: 8) {
                        Text(link.rhs).font(Self.formulaFont).fixedSize()
                        statusMark(link.status)
                    }
                    Group {
                        if let reason = link.reason {
                            reasonView(reason, for: link.range)
                        }
                    }
                    .gridColumnAlignment(.trailing)
                }
                .background(selected(link.range))
                .contentShape(Rectangle())
                .onTapGesture { selection = link.range }
                .contextMenu { editMenu(link.range) }
                if book.notes[link.range] != nil {
                    GridRow {
                        Color.clear.gridCellUnsizedAxes([.horizontal, .vertical])
                        notes(link.range).gridCellColumns(2)
                    }
                }
            }
        }
        .padding(.leading, 16)
    }

    private func casesView(intro: String, arms: [Textbook.Arm]) -> some View {
        VStack(alignment: .leading, spacing: 10) {
            Text(intro).font(Self.proseFont)
            ForEach(arms, id: \.range) { arm in
                VStack(alignment: .leading, spacing: 8) {
                    armTitle(arm)
                    blocksView(arm.blocks).padding(.leading, 20)
                }
            }
        }
    }

    /// "Case xs = node(t1, l2)." then, a line each, its hypotheses ("Assume
    /// …"), each given it introduces marked and tappable when the selected
    /// hole can use it: the hypotheses one by one, or a `cases` arm's whole
    /// title. Their labels, when shown, go beside them.
    private func armTitle(_ arm: Textbook.Arm) -> some View {
        let usable = { (label: String) in self.uses[label].flatMap { $0.range == arm.range ? label : nil } }
        return VStack(alignment: .leading, spacing: 4) {
            HStack(alignment: .firstTextBaseline) {
                givenText(variablesText(arm.title, arm.variables.filter { splittable[$0] == arm.range }),
                          arm.assumes.isEmpty ? arm.introduces.first.flatMap(usable) : nil)
                    .font(Self.proseFont).bold()
                Spacer(minLength: 16)
                if arm.assumes.isEmpty { arm.introduces.first.map(sideLabel) }
            }
            ForEach(arm.assumes, id: \.self) { label in
                HStack(alignment: .firstTextBaseline) {
                    givenText(hypothesis(label, arm.formulas[label]), usable(label))
                    Spacer(minLength: 16)
                    if arm.formulas[label] != nil { sideLabel(label) }
                }
                .padding(.leading, 20)
            }
        }
    }

    /// "Assume formula", the formula's lines lined up, or "Assume IH1."
    /// when what it says isn't known.
    private func hypothesis(_ label: String, _ formula: String?) -> some View {
        HStack(alignment: .firstTextBaseline, spacing: 8) {
            Text(formula == nil ? "Assume \(label)." : "Assume").font(Self.proseFont)
            if let formula { Text(formula).font(Self.formulaFont) }
        }
    }

    /// A given's label, the way a textbook numbers a formula: in
    /// parentheses at the side ("(IH1)"). Shown in Full, and otherwise when
    /// the given is cited by its label (`Textbook.Labels.shown`).
    @ViewBuilder
    private func sideLabel(_ label: String) -> some View {
        if defaultLevel == .full || book.labels.shown(label) {
            Text("(\(label))").font(Self.proseFont)
        }
    }

    /// `text`, marked and tappable when it introduces the usable given `label`.
    @ViewBuilder
    private func givenText(_ text: some View, _ label: String?) -> some View {
        if let label {
            text.background { usable(label) }
                .onTapGesture { useGiven(label) }
                .popover(isPresented: asking(label)) { instantiator(label) }
        } else {
            text
        }
    }

    /// Whether the choice for a goal binder shows, beside the selected
    /// hole's line (`here`).
    private func choosing(_ here: Bool) -> Binding<Bool> {
        Binding(get: { here && choosingFor != nil }, set: { if !$0 { choosingFor = nil } })
    }

    /// For a goal variable that can be inducted on: make it arbitrary, or
    /// induct on it.
    @ViewBuilder
    private var binderChoice: some View {
        if let name = choosingFor, let binder = binders.first(where: { $0.name == name }) {
            VStack(alignment: .leading, spacing: 4) {
                Button(letArbitrary([(name, binder.type)])) { introduce(name, false) }
                Divider()
                Button("Induction on \(name)") { introduce(name, true) }
            }
            .font(Self.proseFont)
            .padding()
        }
    }

    /// `text` with the first occurrence of each of `names`, in order, boxed;
    /// tapping one splits on it (or, with `binder`, is a tap on a goal
    /// binder). With `assume`, the `if` that starts `text` is boxed too,
    /// for `assume`.
    private func variablesText(_ text: String, _ names: [String], binder: Bool = false,
                               assume: Bool = false) -> some View {
        let marks = (assume ? [("if", Self.assumeScheme)] : [])
            + names.map { ($0, binder ? Self.binderScheme : Self.splitScheme) }
        var result = Text(verbatim: "")
        var rest = Substring(text)
        for (name, scheme) in marks {
            let word = "(?<![\\w'′])" + NSRegularExpression.escapedPattern(for: name) + "(?![\\w'′])"
            guard let range = rest.range(of: word, options: .regularExpression),
                  let encoded = name.addingPercentEncoding(withAllowedCharacters: .alphanumerics) else { continue }
            // A hair space each side keeps the box off its neighbors.
            var marked = AttributedString("\u{200A}" + rest[range] + "\u{200A}")
            marked.link = URL(string: "\(scheme):\(encoded)")
            marked.foregroundColor = .accentColor
            result = result + Text(verbatim: String(rest[..<range.lowerBound])) + Text(marked).customAttribute(Boxed())
            rest = rest[range.upperBound...]
        }
        return (result + Text(verbatim: String(rest))).textRenderer(BoxedRenderer())
    }

    /// Handles a tap on a variable `variablesText` marked.
    private var openVariable: OpenURLAction {
        OpenURLAction { url in
            guard let scheme = url.scheme, [Self.splitScheme, Self.binderScheme, Self.assumeScheme].contains(scheme),
                  let name = url.absoluteString.dropFirst(scheme.count + 1).removingPercentEncoding
            else { return .systemAction }
            switch scheme {
            case Self.binderScheme: tapBinder(name)
            case Self.assumeScheme: assume?()
            default: split(name)
            }
            return .handled
        }
    }

    private static let splitScheme = "deduce-split"
    private static let binderScheme = "deduce-binder"
    private static let assumeScheme = "deduce-assume"

    /// Whether a hole other than the line at `range` is inside it.
    private func holdsHole(_ range: Outline.Range) -> Bool {
        editable && book.holes.contains { $0.range != range && range.contains($0.range) }
    }

    /// Whether the given `label` is asking for values.
    private func asking(_ label: String?) -> Binding<Bool> {
        Binding(get: { label != nil && instantiating == label },
                set: { if !$0 { instantiating = nil } })
    }

    /// The mark on a given the selected hole can use: green when it proves
    /// the goal, outlined when it gives a step to take.
    private func usable(_ label: String) -> AnyView {
        let tint = uses[label]?.proves == true ? Color.green : Color.accentColor
        let shape = RoundedRectangle(cornerRadius: 6)
        return AnyView(shape.fill(tint.opacity(uses[label]?.proves == true ? 0.18 : 0.07))
            .overlay(shape.strokeBorder(tint.opacity(0.7),
                                        style: StrokeStyle(lineWidth: 1, dash: uses[label]?.proves == true ? [] : [4, 3])))
            .padding(-4))
    }

    /// The errors and warnings shown at the line, link or theorem `range`.
    @ViewBuilder
    private func notes(_ range: Outline.Range) -> some View {
        if let notes = book.notes[range] {
            VStack(alignment: .leading, spacing: 6) {
                ForEach(notes) { NoteCard(diagnostic: $0) }
            }
        }
    }

    @ViewBuilder
    private func editMenu(_ range: Outline.Range) -> some View {
        if editable {
            Button { editAsText(range) } label: { Label("Edit as text…", systemImage: "character.cursor.ibeam") }
        }
    }

    @ViewBuilder
    private func reasonView(_ reason: Textbook.Reason, for range: Outline.Range) -> some View {
        let level = levels[range] ?? defaultLevel
        Group {
            switch level {
            case .full:
                Text(reason.source)
                    .font(.system(.footnote, design: .monospaced))
                    .foregroundStyle(.secondary)
                    .multilineTextAlignment(.trailing)
            case .summary:
                let summary = book.summary(reason, all: defaultLevel == .full)
                Text(summary.isEmpty ? "by definition" : summary)
                    .font(.footnote)
                    .padding(.horizontal, 8)
                    .padding(.vertical, 2)
                    .background(Capsule().fill(Color.accentColor.opacity(0.12)))
            case .hidden:
                Image(systemName: "ellipsis.circle").foregroundStyle(.tertiary)
            }
        }
        .contentShape(Rectangle())
        .onTapGesture { levels[range] = level.next }
    }

    @ViewBuilder
    private func statusMark(_ status: Textbook.Status) -> some View {
        switch status {
        case .ok: EmptyView()
        case .incomplete: Image(systemName: "questionmark.circle.fill").foregroundStyle(.orange)
        case .error: Image(systemName: "exclamationmark.triangle.fill").foregroundStyle(.red)
        }
    }

    private func selected(_ range: Outline.Range) -> some View {
        RoundedRectangle(cornerRadius: 4)
            .fill(selection == range ? Color.accentColor.opacity(0.12) : .clear)
            .padding(-4)
    }

    static let proseFont = Font.system(.title3, design: .serif)
    static let formulaFont = Font.system(.title3, design: .serif).weight(.medium)
}

/// Marks a word in a `Text` to tap, which `BoxedRenderer` draws boxed.
struct Boxed: TextAttribute {}

/// Draws text with a rounded box around each run marked `Boxed`, the way
/// a given to tap is outlined.
struct BoxedRenderer: TextRenderer {
    func draw(layout: Text.Layout, in context: inout GraphicsContext) {
        for line in layout {
            // A word can be laid out as several runs: one box around them all.
            var boxes: [CGRect] = []
            var open = false
            for run in line {
                let marked = run[Boxed.self] != nil
                if marked, open, let last = boxes.popLast() {
                    boxes.append(last.union(run.typographicBounds.rect))
                } else if marked {
                    boxes.append(run.typographicBounds.rect)
                }
                open = marked
            }
            for rect in boxes {
                let box = RoundedRectangle(cornerRadius: 5).path(in: rect.insetBy(dx: 0, dy: -1))
                context.fill(box, with: .color(.accentColor.opacity(0.08)))
                context.stroke(box, with: .color(.accentColor.opacity(0.7)), lineWidth: 1)
            }
            for run in line { context.draw(run) }
        }
    }
}

/// An error (red) or warning (orange) on the step it's about. Long
/// messages show their first lines until tapped.
struct NoteCard: View {
    let diagnostic: Diagnostic
    @State private var expanded = false

    private static let shortLines = 4

    var body: some View {
        // The card's label already says "Error" / "Warning".
        let message = withoutLocations(diagnostic.message)
            .trimmingCharacters(in: .whitespacesAndNewlines)
            .replacingOccurrences(of: #"^(error,|warning:)\s*"#, with: "", options: .regularExpression)
        let long = message.count > 240
            || message.split(separator: "\n", omittingEmptySubsequences: false).count > Self.shortLines
        let tint = diagnostic.warning ? Color.orange : Color.red
        VStack(alignment: .leading, spacing: 4) {
            Label(diagnostic.warning ? "Warning" : "Error",
                  systemImage: diagnostic.warning ? "exclamationmark.circle" : "exclamationmark.triangle")
                .font(.caption.bold())
                .foregroundStyle(tint)
            Text(message)
                .font(.system(.footnote, design: .monospaced))
                .lineLimit(expanded ? nil : Self.shortLines)
                .textSelection(.enabled)
            if long {
                Text(expanded ? "Show less" : "Show all")
                    .font(.caption)
                    .foregroundStyle(Color.accentColor)
            }
        }
        .padding(10)
        .frame(maxWidth: .infinity, alignment: .leading)
        .background(RoundedRectangle(cornerRadius: 8).fill(tint.opacity(0.08)))
        .overlay(alignment: .leading) {
            RoundedRectangle(cornerRadius: 2).fill(tint).frame(width: 3)
        }
        .contentShape(Rectangle())
        .onTapGesture { if long { expanded.toggle() } }
    }
}

/// The `.pf` source, with the selected step's lines highlighted.
struct SourceView: View {
    let source: String
    let highlight: Outline.Range?

    var body: some View {
        let lines = source.components(separatedBy: "\n")
        ScrollViewReader { proxy in
            ScrollView {
                LazyVStack(alignment: .leading, spacing: 0) {
                    ForEach(lines.indices, id: \.self) { n in
                        HStack(alignment: .firstTextBaseline, spacing: 12) {
                            Text("\(n + 1)").foregroundStyle(.tertiary).frame(width: 36, alignment: .trailing)
                            Text(lines[n].isEmpty ? " " : lines[n])
                        }
                        .font(.system(.footnote, design: .monospaced))
                        .frame(maxWidth: .infinity, alignment: .leading)
                        .background(isHighlighted(n) ? Color.accentColor.opacity(0.15) : .clear)
                        .id(n)
                    }
                }
                .padding(12)
            }
            .onChange(of: highlight) { _, range in
                if let range { withAnimation { proxy.scrollTo(range.start.line, anchor: .center) } }
            }
        }
    }

    private func isHighlighted(_ line: Int) -> Bool {
        guard let highlight else { return false }
        return highlight.start.line <= line && line <= highlight.end.line
    }
}
