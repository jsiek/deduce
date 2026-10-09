# Deduce for iPad

A SwiftUI app that runs the Deduce checker on the device, using an embedded CPython and the
existing LSP server (`lsp/lsp_server.py`) in-process. Design: [`docs/ipad-app-design.md`](../docs/ipad-app-design.md).
Tracking issue: #1213.

This is currently the **spike** (#1220). It opens a bundled sample or stdlib file, checks it,
shows the diagnostics and timings, and can interrupt a running check.

## Build

Needs Xcode 16 with the iOS platform installed, and `python3.13` on the Mac.

```sh
bash ipad/scripts/prepare.sh   # once, or after changing lib/
open ipad/Deduce.xcodeproj
```

`prepare.sh` downloads BeeWare's prebuilt Python for iOS (pinned release and SHA-256) into
`ipad/Support/`, vendors the pinned pure-Python packages into `ipad/build/app_packages/`,
and checks `lib/` so every stdlib module has an up-to-date `.thm`.

From the command line, for an iPad simulator:

```sh
xcodebuild -project ipad/Deduce.xcodeproj -target Deduce -sdk iphonesimulator ARCHS=arm64 SYMROOT=$PWD/ipad/build/xcode build
```

## How it fits together

- `Deduce/PythonHost.c` initializes CPython (home: the bundle's `python/`) and calls
  `deduce_ipad.serve`, which runs the LSP server on a pipe pair.
- `Deduce/DeduceServer.swift` starts that on a thread with a 256 MB stack (the checker recurses
  deeply; iOS gives secondary threads 512 KB by default), and speaks JSON-RPC to it.
- `scripts/bundle-app.sh` (an Xcode build phase) copies the checker, `lib/` with its `.thm`
  files, the samples and the packages into the app, then runs BeeWare's `install_python`.
  The `.thm` files make imports skip re-proving the stdlib, and the app never writes into its
  read-only bundle.
- **Interrupt** calls `deduce_ipad.interrupt`, which raises `CheckCancelled` in the checking
  thread with `PyThreadState_SetAsyncExc`.

## Driving it headlessly

```sh
xcrun simctl launch --console-pty <device> org.deduce.Deduce --open samples/Broken.pf
xcrun simctl launch --console-pty <device> org.deduce.Deduce --open samples/Slow.pf --interrupt-after 15
```

The app prints `deduce-timing:`, `deduce-diagnostic:` and `deduce-log:` lines to the console.
