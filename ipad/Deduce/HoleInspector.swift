import SwiftUI

/// The steps you can take at a `?`. Steps on the whole hole come from the
/// server's existing actions (Refine, Induction, case split, using a given,
/// lemmas); `expand` and `replace` act on the part of the goal you tap, and
/// are previewed before they're applied (`deduce/preview…AtSubterm`).
struct HoleInspector: View {
    @EnvironmentObject var server: DeduceServer
    let hole: Textbook.Hole

    @State private var subterm: [Int]?
    @State private var actions: [(title: String, edits: [TextEdit])] = []
    @State private var splittable: [String] = []
    @State private var eliminable: [String] = []
    @State private var matching: [String] = []
    @State private var lemmas: [DeduceServer.Lemma] = []
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
            Section(subterm == nil ? "The whole goal" : "The selected part: \(display(selected))") {
                // One definition at a time: `expand A | B` fails unless
                // every name unfolds, which can't be known in advance.
                ForEach(FormulaView.calledNames(selected), id: \.self) { name in
                    stepButton("Expand " + name, "deduce/previewExpandAtSubterm", ["names": [name]])
                }
                ForEach(equations, id: \.self) { equation in
                    stepButton("Replace using " + equation, "deduce/previewReplaceAtSubterm", ["equation": equation])
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
        Button(title) {
            Task {
                previewing = title
                let version = server.version
                let result = await server.preview(method, at: position, subterm: subterm ?? [], params)
                previewing = nil
                // Undo or an edit as text may have changed the file meanwhile.
                if server.version == version { preview = (title, result) }
            }
        }
    }

    @ViewBuilder
    private func previewView(_ title: String, _ result: DeduceServer.Preview) -> some View {
        VStack(alignment: .leading, spacing: 8) {
            Text(title).font(.caption).foregroundStyle(.secondary)
            if let problem = result.problem {
                Text(problem).font(.system(.footnote, design: .monospaced)).foregroundStyle(.red)
            } else {
                if let goal = result.goal, goal.text != "true" {
                    (Text("Leaves: ") + Text(display(goal)).font(TextbookView.formulaFont))
                } else {
                    Text("Proves the goal.")
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
