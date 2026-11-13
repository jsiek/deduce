import SwiftUI

struct ContentView: View {
    @EnvironmentObject var server: DeduceServer
    @State private var reasonLevel = ReasonLevel.summary
    @State private var levels: [Outline.Range: ReasonLevel] = [:]
    @State private var selection: Outline.Range?
    @State private var scrollTarget: Outline.Range?
    @State private var showSource = false
    @State private var editing: EditingStep?
    /// The steps at a hole, for the file's version they were asked about.
    @State private var loaded: (hole: Outline.Range, version: Int, steps: DeduceServer.HoleSteps)?
    /// The `all` given being given values, in a popover beside it.
    @State private var instantiating: String?

    /// A step being edited as text.
    struct EditingStep: Identifiable {
        let range: Outline.Range
        var text: String
        var id: Outline.Range { range }
    }

    private var exercises: [URL] { files(in: server.exercisesDirectory) }
    private var samples: [URL] { files(in: server.appDirectory.appendingPathComponent("samples")) }
    private var stdlib: [URL] { files(in: server.appDirectory.appendingPathComponent("lib")) }

    /// The selected hole, when editing is possible.
    private var hole: Textbook.Hole? {
        guard server.editable, let selection else { return nil }
        return server.textbook?.holes.first { $0.range == selection }
    }

    /// The selected hole's steps, once they've arrived for this version.
    private var steps: DeduceServer.HoleSteps? {
        guard let hole, let loaded, loaded.hole == hole.range, loaded.version == server.version,
              !server.checking else { return nil }
        return loaded.steps
    }

    /// The givens at the selected hole that the proof shows where they're
    /// introduced, and can be tapped there to use. An `all` over a type
    /// (`all T:type`) counts only when it proves the goal.
    private var uses: [String: Textbook.GivenUse] {
        guard let hole, let steps, let book = server.textbook else { return [:] }
        let quantified = hole.givens.filter { $0.formula.kind == "All" }
        let overTypes = Set(quantified.filter { FormulaView.subtrees($0.formula).first?.kind == "TypeType" }.map(\.label))
        let overTerms = Set(quantified.map(\.label)).subtracting(overTypes)
        return book.givens(at: hole.range).reduce(into: [:]) { uses, given in
            let (label, range) = given
            let proves = steps.matching.contains(label)
            if proves || (steps.eliminable.contains(label) && !overTypes.contains(label)) {
                uses[label] = Textbook.GivenUse(range: range, proves: proves, quantified: overTerms.contains(label))
            }
        }
    }

    /// Use the given `label` at the selected hole: prove the goal with it
    /// if it can, ask for values for an `all` given's variables, or else
    /// take the step its shape calls for.
    private func useGiven(_ label: String) {
        guard let hole, let use = uses[label] else { return }
        if use.quantified && !use.proves {
            instantiating = label
            return
        }
        let method = use.proves ? "deduce/fillFromGivenAt" : "deduce/eliminateAt"
        Task { server.apply(await server.edits(method, at: hole.range.start, ["label": label])) }
    }

    var body: some View {
        NavigationSplitView {
            List {
                Section("Exercises") {
                    ForEach(exercises, id: \.self) { url in
                        Button(url.lastPathComponent) { server.open(url) }
                            .contextMenu {
                                Button("Start over", role: .destructive) {
                                    server.reset(url)
                                    // The same file reopens, so the selection isn't reset otherwise.
                                    selection = nil
                                }
                                    .disabled(server.checking && url.lastPathComponent == server.openFile)
                            }
                    }
                }
                Section("Samples") { fileRows(samples) }
                Section("Standard library") { fileRows(stdlib) }
            }
            .navigationTitle("Deduce")
        } detail: {
            VStack(spacing: 0) {
                HStack(spacing: 0) {
                    textbook
                    if let hole {
                        Divider()
                        HoleInspector(hole: hole, steps: steps, givensToTap: !uses.isEmpty).frame(maxWidth: 440)
                    } else if showSource {
                        Divider()
                        SourceView(source: server.source, highlight: selection)
                            .frame(maxWidth: 460)
                    }
                }
                if !otherDiagnostics.isEmpty {
                    Divider()
                    diagnostics
                }
                Divider()
                statusBar
            }
            .navigationTitle(server.openFile ?? "")
            .navigationBarTitleDisplayMode(.inline)
            .toolbar {
                ToolbarItem(placement: .principal) {
                    Picker("Reasons", selection: $reasonLevel) {
                        ForEach(ReasonLevel.allCases) { Text($0.rawValue).tag($0) }
                    }
                    .pickerStyle(.segmented)
                    .frame(width: 260)
                }
                ToolbarItemGroup(placement: .primaryAction) {
                    if server.editable {
                        Button { server.undo() } label: { Label("Undo", systemImage: "arrow.uturn.backward") }
                            .disabled(!server.canUndo || server.checking)
                        Button { selectNextHole() } label: { Label("Next hole", systemImage: "questionmark.circle") }
                            .disabled(server.textbook?.holes.isEmpty ?? true)
                    }
                    Toggle(isOn: $showSource) { Label("Source", systemImage: "chevron.left.forwardslash.chevron.right") }
                    Button(role: .destructive) { server.interrupt() } label: {
                        Label("Interrupt", systemImage: "stop.circle")
                    }
                }
            }
            .sheet(item: $editing) { step in
                editSheet(step)
            }
            // Ask again when each edit's check is done: an edit can leave a
            // hole at the same range, and until the check it may be stale.
            .task(id: "\(String(describing: hole?.range)) v\(server.version) \(server.checking)") {
                guard let hole, !server.checking else { return }
                let (range, version) = (hole.range, server.version)
                let steps = await server.steps(at: range.start)
                // A load superseded meanwhile must not write over the current one's.
                if !Task.isCancelled { loaded = (range, version, steps) }
            }
            .onChange(of: selection) { instantiating = nil }
            .onChange(of: reasonLevel) { levels = [:] }
            .onChange(of: server.openFile) {
                levels = [:]
                selection = nil
            }
            .onReceive(server.$textbook) { book in
                guard let book, server.editable else { return }
                if let edit = server.lastEdit {
                    // After an edit, go to the hole it left (or the next one).
                    server.lastEdit = nil
                    selection = (book.holes.first { $0.range.start >= edit } ?? book.holes.first)?.range
                    scrollTarget = selection
                } else if selection == nil, let first = book.holes.first {
                    selection = first.range
                    scrollTarget = first.range
                }
            }
        }
    }

    private func selectNextHole() {
        guard let holes = server.textbook?.holes, !holes.isEmpty else { return }
        let after = selection.flatMap { current in holes.first { $0.range.start > current.start } }
        selection = (after ?? holes[0]).range
        scrollTarget = selection
    }

    @ViewBuilder
    private var textbook: some View {
        if let book = server.textbook {
            TextbookView(book: book, defaultLevel: reasonLevel, editable: server.editable,
                         selection: $selection, levels: $levels, scrollTarget: $scrollTarget,
                         uses: uses, useGiven: useGiven, instantiating: $instantiating,
                         instantiator: { label in
                             AnyView(hole.map { hole in
                                 InstantiateView(label: label, hole: hole.range.start) { instantiating = nil }
                                     .environmentObject(server)
                             })
                         }) { range in
                editing = EditingStep(range: range, text: sourceText(server.source.scalarLines, range))
            }
        } else if server.openFile == nil {
            ContentUnavailableView("Open a file", systemImage: "doc.text",
                                   description: Text("Choose an exercise, a sample or a standard library file."))
        } else if case .cancelled = server.check {
            ContentUnavailableView("Check cancelled", systemImage: "stop.circle")
        } else {
            ProgressView("Checking…").frame(maxWidth: .infinity, maxHeight: .infinity)
        }
    }

    private func editSheet(_ step: EditingStep) -> some View {
        NavigationStack {
            TextEditor(text: Binding(get: { editing?.text ?? step.text }, set: { editing?.text = $0 }))
                .font(.system(.body, design: .monospaced))
                .autocorrectionDisabled()
                .textInputAutocapitalization(.never)
                .padding()
                .navigationTitle("Edit as text")
                .navigationBarTitleDisplayMode(.inline)
                .toolbar {
                    ToolbarItem(placement: .cancellationAction) { Button("Cancel") { editing = nil } }
                    ToolbarItem(placement: .confirmationAction) {
                        Button("Done") {
                            if let edited = editing, edited.text != sourceText(server.source.scalarLines, step.range) {
                                server.apply([TextEdit(range: step.range, newText: edited.text)])
                            }
                            editing = nil
                        }
                        .disabled(server.checking)
                    }
                }
        }
    }

    /// Diagnostics the textbook doesn't show on a step: those outside any
    /// theorem, or all of them until there is a textbook.
    private var otherDiagnostics: [Diagnostic] {
        server.textbook?.unplaced ?? server.diagnostics
    }

    private var diagnostics: some View {
        ScrollView {
            VStack(alignment: .leading, spacing: 8) {
                ForEach(otherDiagnostics) { diagnostic in
                    VStack(alignment: .leading) {
                        Text("Line \(diagnostic.line)").font(.caption).foregroundStyle(.secondary)
                        Text(withoutLocations(diagnostic.message)).font(.system(.footnote, design: .monospaced))
                    }
                }
            }
            .padding()
            .frame(maxWidth: .infinity, alignment: .leading)
        }
        .frame(maxHeight: 180)
    }

    private var statusBar: some View {
        HStack(spacing: 16) {
            Text(server.status)
            if server.openFile != nil { Text("Check: \(checkDescription)") }
            if let holes = server.textbook?.holes, server.editable {
                Text(holes.isEmpty ? "No holes left" : "\(holes.count) hole\(holes.count == 1 ? "" : "s") left")
            }
            if let last = server.log.last { Text(last).lineLimit(1) }
            Spacer()
        }
        .font(.caption)
        .foregroundStyle(.secondary)
        .padding(.horizontal)
        .padding(.vertical, 6)
    }

    private var checkDescription: String {
        switch server.check {
        case .running, nil: "running…"
        case .finished(let seconds): String(format: "%.2f s", seconds)
        case .cancelled: "cancelled"
        }
    }

    private func fileRows(_ urls: [URL]) -> some View {
        ForEach(urls, id: \.self) { url in
            Button(url.lastPathComponent) { server.open(url) }
        }
    }

    private func files(in directory: URL) -> [URL] {
        let names = (try? FileManager.default.contentsOfDirectory(atPath: directory.path)) ?? []
        return names.filter { $0.hasSuffix(".pf") }.sorted().map { directory.appendingPathComponent($0) }
    }
}
