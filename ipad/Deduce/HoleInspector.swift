import SwiftUI

/// The steps you can take at a `?`. Steps on the whole hole come from the
/// server's existing actions (Refine, Induction, case split, using a given);
/// using a lemma, and `expand` and `replace` on the part of the goal you
/// tap, are previewed before they're applied (`deduce/previewLemmaAt`,
/// `deduce/preview…AtSubterm`).
struct HoleInspector: View {
    @EnvironmentObject var server: DeduceServer
    let hole: Textbook.Hole

    @State private var subterm: [Int]?
    @State private var actions: [(title: String, edits: [TextEdit])] = []
    @State private var splittable: [String] = []
    @State private var eliminable: [String] = []
    @State private var matching: [String] = []
    /// Lemmas that rewrite the selected part of the goal.
    @State private var lemmas: [DeduceServer.Lemma] = []
    /// Lemmas for the whole hole: those that fit it, or those found by `search`.
    @State private var found: [DeduceServer.Lemma] = []
    @State private var search = ""
    @State private var preview: (title: String, result: DeduceServer.Preview)?
    /// The step being previewed, while the server checks it.
    @State private var previewing: String?
    @State private var loading = true
    @State private var typing = false
    @State private var typed = ""

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
            if !hole.givens.isEmpty {
                Section("Givens") {
                    ForEach(hole.givens, id: \.label) { given in
                        (Text(given.label + ": ").bold() + Text(display(given.formula)))
                            .font(TextbookView.proseFont)
                    }
                }
            }
            Section("Steps") {
                if loading {
                    ProgressView()
                } else {
                    ForEach(actions, id: \.title) { action in
                        Button(action.title) { server.apply(action.edits) }
                    }
                    pick("Cases on…", splittable, "deduce/caseSplitAt", "variable")
                    pick("Use a given…", eliminable, "deduce/eliminateAt", "label")
                    pick("Prove it with a given…", matching, "deduce/fillFromGivenAt", "label")
                    Button("Type a proof…") {
                        typed = ""
                        typing = true
                    }
                }
            }
            Section {
                TextField("Search by name or statement", text: $search)
                    .autocorrectionDisabled()
                    .textInputAutocapitalization(.never)
                ForEach(shownLemmas) { lemma in
                    lemmaRow(lemma)
                }
            } header: {
                Text("Lemmas")
            } footer: {
                Text(search.isEmpty
                     ? "Lemmas whose conclusion fits the goal. Search for others by name or by a pattern, like _ + 0 = _."
                     : shownLemmas.isEmpty ? "No lemma matches." : "")
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
        // Reload when each edit's check is done: an edit can leave a hole
        // at the same range, and until the check the hole may be stale.
        .task(id: "\(hole.range) v\(server.version) \(server.checking)") { await load() }
        .task(id: "\(hole.range) v\(server.version) \(server.checking) \(subterm ?? [])") {
            preview = nil
            guard !server.checking else { return }
            lemmas = await server.lemmas(at: position, subterm: subterm ?? [])
        }
        .task(id: "\(hole.range) v\(server.version) \(server.checking) \(search)") {
            // Search once typing pauses.
            if !search.isEmpty { try? await Task.sleep(for: .milliseconds(300)) }
            guard !Task.isCancelled, !server.checking else { return }
            found = await server.lemmas(at: position, matching: search)
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
        let givens = hole.givens.filter { isEquation($0.formula) }.map(\.label)
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
                    Text(statement).font(TextbookView.proseFont).foregroundStyle(.primary).lineLimit(2)
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

    private func stepButton(_ title: String, _ method: String, _ params: [String: Any]) -> some View {
        Button(title) { run(title, method, params) }
    }

    /// Preview a step, to show in the bar below the list.
    private func run(_ title: String, _ method: String, _ params: [String: Any]) {
        Task {
            previewing = title
            let version = server.version
            let result = await server.preview(method, at: position, params)
            previewing = nil
            // Undo or an edit as text may have changed the file meanwhile.
            if server.version == version { preview = (title, result) }
        }
    }

    @ViewBuilder
    private func previewView(_ title: String, _ result: DeduceServer.Preview) -> some View {
        VStack(alignment: .leading, spacing: 8) {
            Text(title).font(.caption).foregroundStyle(.secondary)
            if let problem = result.problem {
                Text(problem).font(.system(.footnote, design: .monospaced)).foregroundStyle(.red)
            } else if result.goals.count == 1, display(result.goals[0]) == display(hole.goal) {
                Text("Leaves the goal as it is.")
            } else {
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

    /// Ask for every list of steps, then show them together, so the rows
    /// don't move under a finger while they arrive.
    private func load() async {
        subterm = nil
        preview = nil
        search = ""
        loading = true
        // The steps come once the check is done (this runs again then).
        guard !server.checking else { return }
        let newActions = await server.codeActions(at: position)
        let newSplittable = await server.names("deduce/splittableVarsAt", at: position)
        let newEliminable = await server.names("deduce/eliminableVarsAt", at: position)
        let newMatching = await server.names("deduce/matchingGivensAt", at: position)
        (actions, splittable, eliminable, matching) = (newActions, newSplittable, newEliminable, newMatching)
        loading = false
    }
}
