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
struct TextbookView: View {
    let book: Textbook
    let defaultLevel: ReasonLevel
    @Binding var selection: Outline.Range?
    /// Per-step overrides of `defaultLevel`, by step range.
    @Binding var levels: [Outline.Range: ReasonLevel]

    var body: some View {
        ScrollView {
            LazyVStack(alignment: .leading, spacing: 32) {
                ForEach(book.theorems) { theorem in
                    theoremView(theorem)
                }
            }
            .padding(24)
            .frame(maxWidth: 820, alignment: .leading)
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
        return VStack(alignment: .leading, spacing: 8) {
            HStack(alignment: .firstTextBaseline, spacing: 8) {
                Text(line.prose).font(Self.proseFont)
                if let formula = line.formula {
                    Text(formula).font(Self.formulaFont)
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
            }
            .padding(.vertical, 2)
            .background(selected(line.range))
            .contentShape(Rectangle())
            .onTapGesture { selection = line.range }
            if !line.subproof.isEmpty && level != .hidden {
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
            }
        }
        .padding(.leading, 16)
    }

    private func casesView(intro: String, arms: [Textbook.Arm]) -> some View {
        VStack(alignment: .leading, spacing: 10) {
            Text(intro).font(Self.proseFont)
            ForEach(arms, id: \.range) { arm in
                VStack(alignment: .leading, spacing: 8) {
                    Text(arm.title).font(Self.proseFont).bold()
                    blocksView(arm.blocks).padding(.leading, 20)
                }
            }
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
                Text(reason.summary.isEmpty ? "by definition" : reason.summary)
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

    static let proseFont = Font.system(.body, design: .serif)
    static let formulaFont = Font.system(.body, design: .serif).weight(.medium)
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
