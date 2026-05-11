// VS Code extension wiring for Deduce.
//
// Two pieces live here:
//
//   1. A DebugAdapterDescriptorFactory for ``type: "deduce"`` that
//      spawns ``<python> <deduceRoot>/lsp/dap_server.py``.  Declared
//      imperatively because ``${workspaceFolder}`` substitution
//      doesn't happen for adapter ``program``/``args`` declared
//      statically in package.json -- so we can't point at
//      ``<workspace>/lsp/dap_server.py'' from JSON alone.
//
//   2. A LanguageClient (vscode-languageclient/node) that spawns
//      ``<python> -m lsp.lsp_server`` and gives VS Code diagnostics,
//      go-to-definition, document outline, and code actions for the
//      ``deduce`` language.  Mirror of editor/emacs/deduce-lsp.el.
//
// Both share the ``deduce.pythonPath`` / ``deduce.deduceRoot``
// settings.  The LSP client additionally honors ``deduce.noStdlib``
// (sets DEDUCE_NO_STDLIB=1 in the spawned env).

const path = require('path');
const vscode = require('vscode');
const { LanguageClient, TransportKind } = require('vscode-languageclient/node');

let client;

function resolveDeduceRoot(workspaceFolder) {
    const cfg = vscode.workspace.getConfiguration('deduce');
    return cfg.get('deduceRoot') || (workspaceFolder ? workspaceFolder.uri.fsPath : undefined);
}

function activate(context) {
    // --- Debug adapter --------------------------------------------
    const factory = {
        createDebugAdapterDescriptor(session, _executable) {
            const folder = session.workspaceFolder
                || (vscode.workspace.workspaceFolders
                    ? vscode.workspace.workspaceFolders[0]
                    : undefined);
            if (!folder) {
                vscode.window.showErrorMessage(
                    'Deduce: no workspace folder. Open the deduce repo (or '
                    + 'set deduce.deduceRoot in settings) so the adapter '
                    + 'can find lsp/dap_server.py.');
                return undefined;
            }
            const root = resolveDeduceRoot(folder);
            const script = path.join(root, 'lsp', 'dap_server.py');
            const python = vscode.workspace.getConfiguration('deduce').get('pythonPath') || 'python3';
            return new vscode.DebugAdapterExecutable(python, [script], {
                cwd: root,
            });
        },
    };
    context.subscriptions.push(
        vscode.debug.registerDebugAdapterDescriptorFactory('deduce', factory)
    );

    // --- Language client ------------------------------------------
    //
    // ``deduce.pythonPath -m lsp.lsp_server'' with cwd set to the
    // Deduce installation so the ``lsp.lsp_server'' module resolves.
    // Adding the root to PYTHONPATH in addition to setting cwd is
    // belt-and-suspenders for the case where the user has launched
    // VS Code from a different cwd than the workspace folder.
    const folder = vscode.workspace.workspaceFolders
        ? vscode.workspace.workspaceFolders[0]
        : undefined;
    const root = resolveDeduceRoot(folder);
    if (!root) {
        // No workspace folder and no deduce.deduceRoot -- we can't
        // start the LSP server without knowing where it lives.  The
        // debugger factory above shows a similar error on launch;
        // the LSP client silently no-ops so a user opening a stray
        // .pf file outside any workspace doesn't get a popup on
        // every activation.
        return;
    }

    const cfg = vscode.workspace.getConfiguration('deduce');
    const python = cfg.get('pythonPath') || 'python3';
    const noStdlib = cfg.get('noStdlib') === true;

    const env = { ...process.env, PYTHONPATH: root };
    if (noStdlib) {
        env.DEDUCE_NO_STDLIB = '1';
    }

    const serverOptions = {
        command: python,
        args: ['-m', 'lsp.lsp_server'],
        transport: TransportKind.stdio,
        options: { cwd: root, env },
    };

    const clientOptions = {
        documentSelector: [{ scheme: 'file', language: 'deduce' }],
        // Notify the server about file changes to .pf files outside
        // the open editors -- imports, sibling modules, etc.
        synchronize: {
            fileEvents: vscode.workspace.createFileSystemWatcher('**/*.pf'),
        },
    };

    client = new LanguageClient(
        'deduce',
        'Deduce Language Server',
        serverOptions,
        clientOptions
    );

    // Start asynchronously; failures show up as the server status
    // bar entry going red rather than as a popup on every activation.
    client.start();
}

function deactivate() {
    if (!client) {
        return undefined;
    }
    return client.stop();
}

module.exports = { activate, deactivate };
