import SwiftUI

struct ContentView: View {
    @EnvironmentObject var server: DeduceServer
    @State private var reasonLevel = ReasonLevel.summary
    @State private var levels: [Outline.Range: ReasonLevel] = [:]
    @State private var selection: Outline.Range?
    @State private var showSource = false

    private var samples: [URL] { files(in: "samples") }
    private var stdlib: [URL] { files(in: "lib") }

    var body: some View {
        NavigationSplitView {
            List {
                Section("Samples") { fileRows(samples) }
                Section("Standard library") { fileRows(stdlib) }
            }
            .navigationTitle("Deduce")
        } detail: {
            VStack(spacing: 0) {
                HStack(spacing: 0) {
                    textbook
                    if showSource {
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
                    Toggle(isOn: $showSource) { Label("Source", systemImage: "chevron.left.forwardslash.chevron.right") }
                    Button(role: .destructive) { server.interrupt() } label: {
                        Label("Interrupt", systemImage: "stop.circle")
                    }
                }
            }
            .onChange(of: reasonLevel) { levels = [:] }
            .onChange(of: server.openFile) {
                levels = [:]
                selection = nil
            }
        }
    }

    @ViewBuilder
    private var textbook: some View {
        if let book = server.textbook {
            TextbookView(book: book, defaultLevel: reasonLevel, selection: $selection, levels: $levels)
        } else if server.openFile == nil {
            ContentUnavailableView("Open a file", systemImage: "doc.text",
                                   description: Text("Choose a sample or a standard library file."))
        } else if case .cancelled = server.check {
            ContentUnavailableView("Check cancelled", systemImage: "stop.circle")
        } else {
            ProgressView("Checking…").frame(maxWidth: .infinity, maxHeight: .infinity)
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

    private func files(in folder: String) -> [URL] {
        let directory = server.appDirectory.appendingPathComponent(folder)
        let names = (try? FileManager.default.contentsOfDirectory(atPath: directory.path)) ?? []
        return names.filter { $0.hasSuffix(".pf") }.sorted().map { directory.appendingPathComponent($0) }
    }
}
