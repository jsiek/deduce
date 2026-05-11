// Minimal VS Code extension wiring for the Deduce debugger.
//
// Why this file exists: declarative ``program''/``args'' in the
// ``contributes.debuggers`` package.json block don't get
// ``${workspaceFolder}`` substituted at adapter-spawn time, so we
// can't point at ``<workspace>/lsp/dap_server.py'' declaratively.
// Registering an adapter factory in code gives us full control
// over the spawn -- including reading a user-overridable python
// path from settings, falling back to ``python3'' on $PATH.

const path = require('path');
const vscode = require('vscode');

function activate(context) {
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
            const cfg = vscode.workspace.getConfiguration('deduce');
            const root = cfg.get('deduceRoot') || folder.uri.fsPath;
            const script = path.join(root, 'lsp', 'dap_server.py');
            const python = cfg.get('pythonPath') || 'python3';
            return new vscode.DebugAdapterExecutable(python, [script], {
                cwd: root,
            });
        },
    };
    context.subscriptions.push(
        vscode.debug.registerDebugAdapterDescriptorFactory('deduce', factory)
    );
}

function deactivate() {}

module.exports = { activate, deactivate };
