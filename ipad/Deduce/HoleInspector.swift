import SwiftUI

/// The steps you can take at a `?`. Steps on the whole hole come from the
/// server's existing actions (Refine); using a lemma, and `expand` and
/// `replace` on the part of the goal you tap, are previewed before they're
/// applied (`deduce/previewLemmaAt`, `deduce/preview…AtSubterm`). Givens
/// and variables are used by tapping them in the textbook: a variable for
/// "Cases on" it, one the goal binds to make it arbitrary or induct on it.
struct HoleInspector: View {
    @EnvironmentObject var server: DeduceServer
    let hole: Textbook.Hole
    /// The steps at the hole; `nil` until they arrive.
    let steps: DeduceServer.HoleSteps?
    /// Whether the textbook marks givens or variables to tap at this hole.
    let marked: Bool
    /// Variables to split on that the textbook doesn't show where they're
    /// introduced, offered here instead.
    let otherSplittable: [String]

    @State private var subterm: [Int]?
    /// Lemmas that rewrite the selected part of the goal.
    @State private var lemmas: [DeduceServer.Lemma] = []
    /// Lemmas for the whole hole: those that fit it, or those found by `search`.
    @State private var found: [DeduceServer.Lemma] = []
    /// Whether `found` is being fetched (it may be another hole's until then).
    @State private var findingLemmas = true
    @State private var search = ""
    @State private var preview: (title: String, result: DeduceServer.Preview)?
    /// The step being previewed, while the server checks it.
    @State private var previewing: String?
    @State private var typing = false
    @State private var typed = ""

    private var loading: Bool { steps == nil }
    private var position: Outline.Position { hole.range.start }
    private var selected: Outline.Tree { subterm.flatMap { FormulaView.subtree(hole.goal, at: $0) } ?? hole.goal }

    var body: some View {
        List {
            Section {
                FormulaView(tree: hole.goal, selection: $subterm)
            } header: {
                Text("Goal")
            } footer: {
                Text(subterm == nil ? "Tap part of the goal to work on just that part." : "Tap it again to select more.")
            }
            Section {
                if let steps {
                    // Induction, and making a goal variable arbitrary, are a tap
                    // on the variable in the textbook.
                    ForEach(steps.actions.filter { action in
                        steps.binders.isEmpty || !(action.title == "Induction"
                            || action.edits.first?.newText.hasPrefix("arbitrary ") == true)
                    }, id: \.title) { action in
                        Button(Self.label(action)) { server.apply(action.edits) }
                    }
                    pick("Cases on…", otherSplittable, "deduce/caseSplitAt", "variable")
                    Button("Type a proof…") {
                        typed = ""
                        typing = true
                    }
                } else {
                    ProgressView()
                }
            } header: {
                Text("Steps")
            } footer: {
                if marked {
                    Text("Tap a marked given or variable in the proof to use it. Green givens prove the goal. "
                         + "An underlined variable in the goal can be made arbitrary or inducted on; "
                         + "elsewhere, tap one for cases on it.")
                }
            }
            Section {
                TextField("Search by name or statement", text: $search)
                    .autocorrectionDisabled()
                    .textInputAutocapitalization(.never)
                if findingLemmas {
                    ProgressView()
                } else {
                    ForEach(shownLemmas) { lemma in
                        lemmaRow(lemma)
                    }
                }
            } header: {
                Text("Lemmas")
            } footer: {
                Text(search.isEmpty
                     ? "Lemmas whose conclusion fits the goal. Search for others by name or by a pattern, like _ + 0 = _."
                     : shownLemmas.isEmpty && !findingLemmas ? "No lemma matches." : "")
            }
            Section(subterm == nil ? "The whole goal" : "The selected part: \(display(selected))") {
                // One definition at a time: `expand A | B` fails unless
                // every name unfolds, which can't be known in advance.
                ForEach(FormulaView.calledNames(selected), id: \.self) { name in
                    stepButton("Expand " + name, "deduce/previewExpandAtSubterm",
                               ["names": [name], "subterm": subterm ?? []])
                }
                ForEach(equations, id: \.self) { equation in
                    stepButton("Replace using " + equation, "deduce/previewReplaceAtSubterm",
                               ["equation": equation, "subterm": subterm ?? []])
                }
            }
        }
        // Rows would move under a finger as the steps arrive, and a preview
        // is for the selection it was asked about.
        .disabled(server.checking || loading || previewing != nil)
        // The preview stays in sight below the list, whatever its scroll.
        .safeAreaInset(edge: .bottom) {
            if previewing != nil || preview != nil {
                Group {
                    if let previewing {
                        HStack {
                            Text("Checking “\(previewing)”…").font(.caption).foregroundStyle(.secondary)
                            Spacer()
                            ProgressView()
                        }
                    } else if let preview {
                        previewView(preview.title, preview.result)
                    }
                }
                .frame(maxWidth: .infinity, alignment: .leading)
                .padding()
                .background(.regularMaterial)
                .disabled(server.checking)
            }
        }
        // Start afresh at each hole, and after each edit.
        .task(id: "\(hole.range) v\(server.version)") {
            subterm = nil
            preview = nil
            search = ""
            findingLemmas = true
        }
        // Lemma ranking is the slowest query, so it waits for the steps.
        .task(id: "\(hole.range) v\(server.version) \(loading) \(subterm ?? [])") {
            preview = nil
            guard !loading else { return }
            let ranked = await server.lemmas(at: position, subterm: subterm ?? [])
            if !Task.isCancelled { lemmas = ranked }
        }
        .task(id: "\(hole.range) v\(server.version) \(loading) \(search)") {
            // Search once typing pauses.
            if !search.isEmpty { try? await Task.sleep(for: .milliseconds(300)) }
            guard !Task.isCancelled, !loading else { return }
            findingLemmas = true
            let matches = await server.lemmas(at: position, matching: search)
            guard !Task.isCancelled else { return }
            found = matches
            findingLemmas = false
        }
        .alert("Type a proof", isPresented: $typing) {
            TextField("e.g. conclude … by …", text: $typed)
                .autocorrectionDisabled()
                .textInputAutocapitalization(.never)
            Button("Insert") { server.apply([TextEdit(range: hole.range, newText: typed)]) }
            Button("Cancel", role: .cancel) {}
        } message: {
            Text("It replaces the ?. Write ? where you want to leave more to prove.")
        }
    }

    /// Givens that are equations (either way round), then lemmas that
    /// rewrite the selection.
    private var equations: [String] {
        // A given labeled `_` (a case's unnamed equation) can't be named.
        let givens = hole.givens.filter { $0.label != "_" && isEquation($0.formula) }.map(\.label)
        return givens + givens.map { "symmetric " + $0 }
            + lemmas.filter { $0.unify_tier == "rewrite_subterm" }.map(\.name)
    }

    /// Without a search, the lemmas whose conclusion fits the goal (those
    /// that rewrite it are under Replace); with one, every match.
    private var shownLemmas: [DeduceServer.Lemma] {
        search.isEmpty
            ? found.filter { ["full", "premises_remain", "disjunctive_split"].contains($0.unify_tier ?? "") }
            : found
    }

    private func lemmaRow(_ lemma: DeduceServer.Lemma) -> some View {
        Button {
            run("Use " + lemma.name, "deduce/previewLemmaAt", ["name": lemma.name])
        } label: {
            VStack(alignment: .leading, spacing: 2) {
                HStack(alignment: .firstTextBaseline) {
                    Text(lemma.name)
                    if let fit = Self.fits[lemma.unify_tier ?? ""] {
                        Text(fit).font(.caption).foregroundStyle(.secondary)
                    }
                }
                if let statement = lemma.statement {
                    Text(statement).font(TextbookView.proseFont).foregroundStyle(Color.secondary).lineLimit(2)
                }
            }
        }
    }

    /// How a lemma fits the goal, by the server's `unify_tier`.
    private static let fits = [
        "full": "proves it",
        "premises_remain": "leaves its premises",
        "disjunctive_split": "splits into cases",
        "rewrite_subterm": "rewrites it",
    ]

    private func isEquation(_ formula: Outline.Tree) -> Bool {
        if formula.kind == "All", let body = FormulaView.subtrees(formula).last { return isEquation(body) }
        let children = FormulaView.subtrees(formula)
        return formula.kind == "Call" && children.count == 3 && children[1].text == "="
    }

    @ViewBuilder
    private func pick(_ title: String, _ names: [String], _ method: String, _ key: String) -> some View {
        if !names.isEmpty {
            Menu(title) {
                ForEach(names, id: \.self) { name in
                    Button(name) {
                        Task { server.apply(await server.edits(method, at: position, [key: name])) }
                    }
                }
            }
        }
    }

    /// An `expand` or `replace`: it applies as soon as it checks (Undo
    /// takes it back); the bar below the list shows why when it doesn't,
    /// or what the checker warns about it.
    private func stepButton(_ title: String, _ method: String, _ params: [String: Any]) -> some View {
        Button(title) { run(title, method, params, apply: true) }
    }

    /// Check a step: apply it (`apply`, when it checks), or show it in the
    /// bar below the list, with what it leaves, to apply from there.
    private func run(_ title: String, _ method: String, _ params: [String: Any], apply: Bool = false) {
        Task {
            previewing = title
            let version = server.version
            let result = await server.preview(method, at: position, params)
            previewing = nil
            // Undo or an edit as text may have changed the file meanwhile.
            guard server.version == version else { return }
            if apply && result.problem == nil && result.warnings.isEmpty {
                server.apply(result.edits)
            } else {
                preview = (title, result)
            }
        }
    }

    @ViewBuilder
    private func previewView(_ title: String, _ result: DeduceServer.Preview) -> some View {
        VStack(alignment: .leading, spacing: 8) {
            Text(title).font(.caption).foregroundStyle(.secondary)
            if let problem = result.problem {
                // The checker's messages can be long; keep the list in sight.
                ScrollView {
                    Text(withoutLocations(problem))
                        .font(.system(.footnote, design: .monospaced)).foregroundStyle(.red)
                        .frame(maxWidth: .infinity, alignment: .leading)
                }
                .frame(maxHeight: 160)
            } else if result.goals.count == 1, display(result.goals[0]) == display(hole.goal) {
                Text("Leaves the goal as it is.")
            } else {
                ForEach(result.warnings, id: \.self) { warning in
                    Text(withoutLocations(warning).trimmingCharacters(in: .whitespacesAndNewlines))
                        .font(.system(.footnote, design: .monospaced)).foregroundStyle(.orange)
                }
                if result.goals.isEmpty {
                    Text("Proves the goal.")
                } else {
                    Text(result.goals.count == 1 ? "Leaves:" : "Leaves \(result.goals.count) goals:")
                    ForEach(result.goals.indices, id: \.self) { i in
                        Text(display(result.goals[i])).font(TextbookView.formulaFont)
                    }
                }
                Button("Apply") { server.apply(result.edits) }.buttonStyle(.borderedProminent)
            }
        }
        .padding(.vertical, 4)
    }

    /// What a code action does, in words. The server titles its refine
    /// action "Refine hole" whatever step it inserts, so name the step
    /// from the start of its edit (`refine_at` in `lsp/query.py`).
    private static func label(_ action: (title: String, edits: [TextEdit])) -> String {
        guard action.title == "Refine hole", let text = action.edits.first?.newText else { return action.title }
        var step = String(text.prefix { $0 != "\n" })
        if step.hasPrefix("{ ") { step.removeFirst(2) }  // braced as part of a larger step
        // (`arbitrary` isn't offered here: it's a tap on the goal's variable.)
        if step.hasPrefix("assume "), let colon = step.firstIndex(of: ":") {
            var premise = step[step.index(after: colon)...].trimmingCharacters(in: .whitespaces)
            if premise.hasPrefix("("), closingParen(of: premise) == premise.index(before: premise.endIndex) {
                premise = String(premise.dropFirst().dropLast())
            }
            return "Assume \(step.dropFirst("assume ".count)[..<colon]): \(premise)"
        }
        if step.hasPrefix("choose ") { return "Choose a witness" }
        if step.hasPrefix("?,") { return "Prove each part" }
        if step == "reflexive" { return "Finish: both sides are equal" }
        if step == "." { return "Finish: this is immediate" }
        return action.title
    }
}

/// Values for an `all` given's variables, to use it at a hole: a field per
/// variable, with the server's suggestions to tap. Using it states what
/// the given says for those values (`have H: … by IH1[ys]`).
struct InstantiateView: View {
    @EnvironmentObject var server: DeduceServer
    let label: String
    let hole: Outline.Position
    let done: () -> Void

    @State private var vars: [DeduceServer.InstantiationVar]?
    @State private var values: [String] = []
    @State private var problem: String?
    @State private var working = false

    var body: some View {
        VStack(alignment: .leading, spacing: 14) {
            Text("Use \(label) with").font(.headline)
            if let vars {
                ForEach(vars.indices, id: \.self) { i in
                    VStack(alignment: .leading, spacing: 6) {
                        HStack(alignment: .firstTextBaseline) {
                            Text("\(vars[i].name) =").font(TextbookView.formulaFont)
                            TextField(vars[i].type, text: $values[i])
                                .textFieldStyle(.roundedBorder)
                                .autocorrectionDisabled()
                                .textInputAutocapitalization(.never)
                        }
                        if !vars[i].suggestions.isEmpty {
                            ScrollView(.horizontal, showsIndicators: false) {
                                HStack {
                                    ForEach(vars[i].suggestions, id: \.self) { value in
                                        Button(value) { values[i] = value }
                                            .buttonStyle(.bordered)
                                            .font(TextbookView.formulaFont)
                                    }
                                }
                            }
                        }
                    }
                }
                if let problem {
                    Text(withoutLocations(problem))
                        .font(.system(.footnote, design: .monospaced))
                        .foregroundStyle(.red)
                }
                HStack {
                    Spacer()
                    if working { ProgressView() }
                    Button("Use") { use() }
                        .buttonStyle(.borderedProminent)
                        .disabled(working || values.contains { $0.trimmingCharacters(in: .whitespaces).isEmpty })
                }
            } else {
                ProgressView()
            }
        }
        .padding()
        .frame(width: 380)
        .task {
            let loaded = await server.instantiationVars(at: hole, label: label)
            values = loaded.map { _ in "" }
            vars = loaded
        }
    }

    private func use() {
        Task {
            working = true
            let result = await server.instantiate(at: hole, label: label, values: values)
            working = false
            if let message = result.problem {
                problem = message
            } else {
                server.apply(result.edits)
                done()
            }
        }
    }
}
