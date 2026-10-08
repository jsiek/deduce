import SwiftUI

@main
struct DeduceApp: App {
    @StateObject private var server = DeduceServer()

    var body: some Scene {
        WindowGroup {
            ContentView()
                .environmentObject(server)
                .task { runLaunchArguments() }
        }
    }

    /// `--open <path under app/>` checks a file at launch, and
    /// `--interrupt-after <seconds>` then interrupts it: for driving the
    /// spike headlessly (`xcrun simctl launch --console ...`).
    private func runLaunchArguments() {
        let arguments = ProcessInfo.processInfo.arguments
        func value(_ flag: String) -> String? {
            arguments.firstIndex(of: flag).flatMap { $0 + 1 < arguments.count ? arguments[$0 + 1] : nil }
        }
        if let path = value("--open") {
            server.open(server.appDirectory.appendingPathComponent(path))
        }
        if let delay = value("--interrupt-after").flatMap(Double.init) {
            DispatchQueue.main.asyncAfter(deadline: .now() + delay) { server.interrupt() }
        }
    }
}
