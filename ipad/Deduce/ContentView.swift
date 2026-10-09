import SwiftUI

struct ContentView: View {
    @EnvironmentObject var server: DeduceServer
    @State private var reasonLevel = ReasonLevel.summary
    @State private var levels: [Outline.Range: ReasonLevel] = [:]
    @State private var selection: Outline.Range?
    @State private var scrollTarget: Outline.Range?
    @State private var showSource = false
    @State private var editing: EditingStep?

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

    var body: some View {
        NavigationSplitView {
            List {
                Section("Exercises") {
                    ForEach(exercises, id: \.self) { url in
                        Button(url.lastPathComponent) { server.open(url) }
                            .contextMenu {
                                Button("Start over", role: .destructive) { server.reset(url) }
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
                        HoleInspector(hole: hole).frame(maxWidth: 440)
                    } else if showSource {
                        Divider()
                        SourceView(source: server.source, highlight: selection)
                            .frame(maxWidth: 460)
                    }
                }
                if !server.diagnostics.isEmpty {
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
                         selection: $selection, levels: $levels, scrollTarget: $scrollTarget) { range in
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

    private var diagnostics: some View {
        ScrollView {
            VStack(alignment: .leading, spacing: 8) {
                ForEach(server.diagnostics) { diagnostic in
                    VStack(alignment: .leading) {
                        Text("Line \(diagnostic.line)").font(.caption).foregroundStyle(.secondary)
                        Text(diagnostic.message).font(.system(.footnote, design: .monospaced))
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
