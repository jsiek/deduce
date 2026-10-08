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
    @Published var log: [String] = []

    let appDirectory = URL(fileURLWithPath: Bundle.main.resourcePath!).appendingPathComponent("app")

    private let toServer = Pipe()
    private let fromServer = Pipe()
    private let launched = Date()
    private var ready = false
    private var pendingOpen: URL?
    private var checkStarted: Date?

    init() {
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
              "params": ["processId": NSNull(), "rootUri": NSNull(), "capabilities": [String: Any]()]])
    }

    func open(_ url: URL) {
        guard ready else {
            pendingOpen = url
            return
        }
        guard let text = try? String(contentsOf: url, encoding: .utf8) else { return }
        openFile = url.lastPathComponent
        diagnostics = []
        check = .running
        checkStarted = Date()
        send(["jsonrpc": "2.0", "method": "textDocument/didOpen",
              "params": ["textDocument": ["uri": url.absoluteString, "languageId": "deduce",
                                          "version": 1, "text": text]]])
    }

    func interrupt() {
        DispatchQueue.global().async {
            let interrupted = deduce_python_interrupt() != 0
            Task { @MainActor in self.record("interrupt requested: \(interrupted ? "check cancelled" : "no check running")") }
        }
    }

    private func handle(_ message: [String: Any]) {
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
            let items = params["diagnostics"] as? [[String: Any]] ?? []
            diagnostics = items.map { item in
                let range = item["range"] as? [String: Any]
                let start = range?["start"] as? [String: Any]
                return Diagnostic(line: (start?["line"] as? Int ?? 0) + 1,
                                  message: item["message"] as? String ?? "")
            }
            if let started = checkStarted {
                let seconds = Date().timeIntervalSince(started)
                check = .finished(seconds: seconds)
                checkStarted = nil
                print(String(format: "deduce-timing: check %@ %.3f s, %d diagnostics",
                             openFile ?? "?", seconds, diagnostics.count))
                diagnostics.forEach { print("deduce-diagnostic: line \($0.line): \($0.message)") }
            }
        case "window/logMessage":
            let text = params["message"] as? String ?? ""
            if text.hasPrefix("check cancelled") {
                check = .cancelled
                checkStarted = nil
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
