import SwiftUI

struct ContentView: View {
    @EnvironmentObject var server: DeduceServer

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
            List {
                Section {
                    LabeledContent("Server", value: server.status)
                    if let file = server.openFile {
                        LabeledContent("File", value: file)
                        LabeledContent("Check", value: checkDescription)
                    }
                    Button("Interrupt check", role: .destructive) { server.interrupt() }
                }
                Section("Diagnostics") {
                    if server.diagnostics.isEmpty {
                        if case .finished = server.check {
                            Text("No problems").foregroundStyle(.secondary)
                        } else {
                            Text("—").foregroundStyle(.secondary)
                        }
                    }
                    ForEach(server.diagnostics) { diagnostic in
                        VStack(alignment: .leading) {
                            Text("Line \(diagnostic.line)").font(.caption).foregroundStyle(.secondary)
                            Text(diagnostic.message).font(.system(.body, design: .monospaced))
                        }
                    }
                }
                if !server.log.isEmpty {
                    Section("Log") { ForEach(server.log, id: \.self) { Text($0).font(.caption) } }
                }
            }
            .navigationTitle(server.openFile ?? "")
        }
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
