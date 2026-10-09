import Foundation

/// The in-process Deduce LSP server (embedded CPython running
/// `lsp/lsp_server.py`) and a minimal JSON-RPC client for it.
@MainActor
final class DeduceServer: ObservableObject {
    struct Diagnostic: Identifiable {
        let id = UUID()
        let line: Int
        let message: String
    }

    enum CheckState {
        case running
        case finished(seconds: Double)
        case cancelled
    }

    @Published var status = "Starting Python…"
    @Published var openFile: String?
    @Published var check: CheckState?
    @Published var diagnostics: [Diagnostic] = []
    @Published var source = ""
    @Published var textbook: Textbook?
    @Published var log: [String] = []
    /// Whether the open file can be edited (exercises are; the bundled
    /// samples and standard library are read-only).
    @Published var editable = false
    @Published var canUndo = false
    /// Where the latest edit started, so the view can select the hole it
    /// left once the new outline arrives.
    @Published var lastEdit: Outline.Position?

    let appDirectory = URL(fileURLWithPath: Bundle.main.resourcePath!).appendingPathComponent("app")
    /// Editable copies of the bundled exercises, in the app's Documents.
    let exercisesDirectory = URL.documentsDirectory.appendingPathComponent("Exercises")

    private let toServer = Pipe()
    private let fromServer = Pipe()
    private let launched = Date()
    private var ready = false
    private var pendingOpen: URL?
    private var openURL: URL?
    private(set) var openURI: String?
    private var version = 1
    private var history: [String] = []
    /// Checks the server hasn't answered yet, by document URI. The server
    /// checks one document at a time, so opening a file mid-check queues it.
    private var checkStarted: [String: Date] = [:]
    private var nextRequest = 2
    private var waiting: [Int: CheckedContinuation<Any?, Never>] = [:]

    init() {
        seedExercises()
        // Python takes ownership of (and closes) the descriptors it is
        // given, so hand it duplicates rather than the Pipes' own.
        let readFD = dup(toServer.fileHandleForReading.fileDescriptor)
        let writeFD = dup(fromServer.fileHandleForWriting.fileDescriptor)
        let resources = Bundle.main.resourcePath!
        let thread = Thread {
            let failed = deduce_python_serve(resources, readFD, writeFD)
            Task { @MainActor in self.status = "Python exited (\(failed))" }
        }
        // The checker recurses deeply (RECURSION_LIMIT is 40000); the
        // default 512 KB secondary-thread stack would crash.
        thread.stackSize = 256 << 20
        thread.name = "deduce-python"
        thread.start()

        let input = fromServer.fileHandleForReading
        Thread.detachNewThread { [weak self] in
            var buffer = Data()
            while true {
                let chunk = input.availableData
                if chunk.isEmpty { return }
                buffer.append(chunk)
                while let message = Self.takeMessage(from: &buffer) {
                    Task { @MainActor in self?.handle(message) }
                }
            }
        }
        send(["jsonrpc": "2.0", "id": 1, "method": "initialize",
              "params": ["processId": NSNull(), "rootUri": NSNull(), "capabilities": [String: Any](),
                         "initializationOptions": ["proofOutline": true]]])
    }

    func open(_ url: URL) {
        guard ready else {
            pendingOpen = url
            return
        }
        guard let text = try? String(contentsOf: url, encoding: .utf8) else { return }
        if let previous = openURI {
            send(["jsonrpc": "2.0", "method": "textDocument/didClose",
                  "params": ["textDocument": ["uri": previous]]])
        }
        let uri = url.absoluteString
        openURL = url
        openFile = url.lastPathComponent
        openURI = uri
        editable = url.standardizedFileURL.path.hasPrefix(exercisesDirectory.standardizedFileURL.path)
        source = text
        history = []
        canUndo = false
        lastEdit = nil
        textbook = nil
        diagnostics = []
        version = 1
        check = .running
        checkStarted[uri] = Date()
        send(["jsonrpc": "2.0", "method": "textDocument/didOpen",
              "params": ["textDocument": ["uri": uri, "languageId": "deduce",
                                          "version": version, "text": text]]])
    }

    /// Apply `edits` (from the server) to the open file: save it, and send
    /// the server the new text, which re-checks it.
    func apply(_ edits: [TextEdit]) {
        guard editable, !edits.isEmpty else { return }
        var text = source
        // Later edits first, so earlier ranges stay valid.
        for edit in edits.sorted(by: { $0.range.start > $1.range.start }) {
            text = text.applying(edit)
        }
        history.append(source)
        replaceSource(with: text, at: edits.map(\.range.start).min()!)
    }

    func undo() {
        guard let previous = history.popLast() else { return }
        replaceSource(with: previous, at: nil)
    }

    private func replaceSource(with text: String, at start: Outline.Position?) {
        guard let url = openURL, let uri = openURI else { return }
        source = text
        canUndo = !history.isEmpty
        lastEdit = start
        do {
            try text.write(to: url, atomically: true, encoding: .utf8)
        } catch {
            record("could not save \(url.lastPathComponent): \(error.localizedDescription)")
        }
        version += 1
        check = .running
        checkStarted[uri] = Date()
        send(["jsonrpc": "2.0", "method": "textDocument/didChange",
              "params": ["textDocument": ["uri": uri, "version": version],
                         "contentChanges": [["text": text]]]])
    }

    /// Send a request about the open document and wait for its result
    /// (`nil` for a null result or an error).
    func request(_ method: String, _ params: [String: Any]) async -> Any? {
        guard let uri = openURI else { return nil }
        let id = nextRequest
        nextRequest += 1
        var all = params
        all["textDocument"] = ["uri": uri]
        return await withCheckedContinuation { continuation in
            waiting[id] = continuation
            send(["jsonrpc": "2.0", "id": id, "method": method, "params": all])
        }
    }

    /// Copy the bundled exercises that aren't in Documents yet, so a
    /// student's work is never overwritten.
    private func seedExercises() {
        let bundled = appDirectory.appendingPathComponent("exercises")
        let names = (try? FileManager.default.contentsOfDirectory(atPath: bundled.path)) ?? []
        try? FileManager.default.createDirectory(at: exercisesDirectory, withIntermediateDirectories: true)
        for name in names where name.hasSuffix(".pf") {
            let target = exercisesDirectory.appendingPathComponent(name)
            if !FileManager.default.fileExists(atPath: target.path) {
                try? FileManager.default.copyItem(at: bundled.appendingPathComponent(name), to: target)
            }
        }
    }

    /// Replace an exercise with its original, bundled version.
    func reset(_ url: URL) {
        let original = appDirectory.appendingPathComponent("exercises").appendingPathComponent(url.lastPathComponent)
        guard let text = try? String(contentsOf: original, encoding: .utf8) else { return }
        try? text.write(to: url, atomically: true, encoding: .utf8)
        open(url)
    }

    func interrupt() {
        DispatchQueue.global().async {
            let interrupted = deduce_python_interrupt() != 0
            Task { @MainActor in self.record("interrupt requested: \(interrupted ? "check cancelled" : "no check running")") }
        }
    }

    private func handle(_ message: [String: Any]) {
        if let id = message["id"] as? Int, let continuation = waiting.removeValue(forKey: id) {
            if let error = message["error"] as? [String: Any] {
                record("request failed: \(error["message"] as? String ?? "unknown error")")
            }
            let result = message["result"]
            continuation.resume(returning: result is NSNull ? nil : result)
            return
        }
        if message["id"] as? Int == 1 {
            ready = true
            let seconds = Date().timeIntervalSince(launched)
            status = String(format: "Ready in %.2f s", seconds)
            print(String(format: "deduce-timing: startup %.3f s", seconds))
            send(["jsonrpc": "2.0", "method": "initialized", "params": [String: Any]()])
            if let url = pendingOpen {
                pendingOpen = nil
                open(url)
            }
            return
        }
        let params = message["params"] as? [String: Any] ?? [:]
        switch message["method"] as? String {
        case "textDocument/publishDiagnostics":
            let uri = params["uri"] as? String ?? ""
            guard let started = checkStarted.removeValue(forKey: uri) else { return }
            let seconds = Date().timeIntervalSince(started)
            let items = params["diagnostics"] as? [[String: Any]] ?? []
            let results = items.map { item in
                let range = item["range"] as? [String: Any]
                let start = range?["start"] as? [String: Any]
                return Diagnostic(line: (start?["line"] as? Int ?? 0) + 1,
                                  message: item["message"] as? String ?? "")
            }
            print(String(format: "deduce-timing: check %@ %.3f s, %d diagnostics",
                         URL(string: uri)?.lastPathComponent ?? uri, seconds, results.count))
            results.forEach { print("deduce-diagnostic: line \($0.line): \($0.message)") }
            if uri == openURI {
                diagnostics = results
                check = .finished(seconds: seconds)
            }
        case "deduce/proofOutline":
            guard params["uri"] as? String == openURI,
                  let data = try? JSONSerialization.data(withJSONObject: params)
            else { return }
            do {
                textbook = Textbook(outline: try JSONDecoder().decode(Outline.self, from: data), source: source)
                print("deduce-outline: \(textbook!.theorems.count) theorems")
            } catch {
                record("could not read the proof outline: \(error)")
            }
        case "window/logMessage":
            let text = params["message"] as? String ?? ""
            let cancelledPrefix = "check cancelled: "
            if text.hasPrefix(cancelledPrefix) {
                let uri = String(text.dropFirst(cancelledPrefix.count))
                checkStarted.removeValue(forKey: uri)
                if uri == openURI { check = .cancelled }
            }
            record(text)
        default:
            break
        }
    }

    private func record(_ line: String) {
        log.append(line)
        print("deduce-log: \(line)")
    }

    private func send(_ message: [String: Any]) {
        guard let body = try? JSONSerialization.data(withJSONObject: message) else { return }
        toServer.fileHandleForWriting.write(Data("Content-Length: \(body.count)\r\n\r\n".utf8) + body)
    }

    /// Remove one complete `Content-Length`-framed JSON-RPC message from the
    /// front of `buffer`, or return nil if it doesn't hold one yet.
    nonisolated private static func takeMessage(from buffer: inout Data) -> [String: Any]? {
        guard let headerEnd = buffer.range(of: Data("\r\n\r\n".utf8)) else { return nil }
        let header = String(decoding: buffer[buffer.startIndex..<headerEnd.lowerBound], as: UTF8.self)
        guard let lengthLine = header.split(separator: "\r\n").first(where: { $0.hasPrefix("Content-Length:") }),
              let length = Int(lengthLine.dropFirst("Content-Length:".count).trimmingCharacters(in: .whitespaces)),
              buffer.distance(from: headerEnd.upperBound, to: buffer.endIndex) >= length
        else { return nil }
        let bodyEnd = buffer.index(headerEnd.upperBound, offsetBy: length)
        let body = buffer[headerEnd.upperBound..<bodyEnd]
        buffer.removeSubrange(buffer.startIndex..<bodyEnd)
        return (try? JSONSerialization.jsonObject(with: body)) as? [String: Any]
    }
}
