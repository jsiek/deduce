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

    // --- Goal-at-cursor command ----------------------------------
    //
    // Mirror of editor/emacs/deduce-lsp.el's `deduce-show-goal-at-point'
    // (C-c C-g).  Issues `deduce/goalAt' on the current cursor and
    // renders the result into a dedicated Output channel.  An Output
    // channel is the closest analogue to Emacs's `*Deduce Goal*'
    // buffer: dedicated panel, doesn't disturb the editor layout,
    // append-friendly across repeated calls.
    const goalChannel = vscode.window.createOutputChannel('Deduce Goal');
    context.subscriptions.push(goalChannel);

    context.subscriptions.push(
        vscode.commands.registerCommand('deduce.showGoal', async () => {
            const editor = ensureDeduceEditor();
            if (!editor) return;
            if (!client) {
                vscode.window.showErrorMessage(
                    'Deduce: language server is not running.  See the '
                    + '"Deduce Language Server" status bar entry for details.');
                return;
            }
            const params = textDocumentPosition(editor);
            let response;
            try {
                response = await client.sendRequest('deduce/goalAt', params);
            } catch (err) {
                vscode.window.showErrorMessage(
                    `Deduce: goal-at-cursor request failed: ${err.message || err}`);
                return;
            }
            goalChannel.clear();
            renderGoal(goalChannel, response);
            goalChannel.show(true);
        })
    );

    // --- Phase-4 structured edits --------------------------------
    //
    // Mirror of editor/emacs/deduce-lsp.el's C-c C-{r,c,i,e,f}
    // bindings.  Two patterns:
    //
    //   Refine / Induction      issue `textDocument/codeAction',
    //                           pick the action whose title matches
    //                           ("Refine hole" / "Induction"), apply
    //                           its WorkspaceEdit.  No prompts.
    //   Case split / Eliminate  query `deduce/{splittableVars,
    //                           eliminableVars}At' for candidates,
    //                           show QuickPick, send the matching
    //                           edit request (`deduce/caseSplitAt',
    //                           `deduce/eliminateAt'), apply.
    //   Fill from given         query `deduce/matchingGivensAt', use
    //                           the first candidate without prompting
    //                           (matches Emacs after issue #385),
    //                           send `deduce/fillFromGivenAt', apply.
    //
    // After each successful edit, the cursor moves onto the first
    // `?' inside the inserted text, so the next refine/case-split
    // can fire immediately without repositioning.

    context.subscriptions.push(
        vscode.commands.registerCommand('deduce.refineHole', () =>
            applyCodeActionByTitle(client, 'Refine hole', 'No refinement available at point.')),
        vscode.commands.registerCommand('deduce.induction', () =>
            applyCodeActionByTitle(client, 'Induction', 'No induction available at point.')),
        vscode.commands.registerCommand('deduce.caseSplit', () =>
            applyCandidateEdit(
                client,
                'deduce/splittableVarsAt',
                'deduce/caseSplitAt',
                'variable',
                'Case split on:',
                'No case split available at point.',
            )),
        vscode.commands.registerCommand('deduce.eliminate', () =>
            applyCandidateEdit(
                client,
                'deduce/eliminableVarsAt',
                'deduce/eliminateAt',
                'label',
                'Eliminate on:',
                'No elimination available at point.',
            )),
        vscode.commands.registerCommand('deduce.fillFromGiven', () =>
            applyFirstCandidateEdit(
                client,
                'deduce/matchingGivensAt',
                'deduce/fillFromGivenAt',
                'label',
                'No matching given at point.',
            )),
    );
}

// --- Shared helpers for the command implementations ---------------

// Return the active editor only if it's a .pf buffer with focus, else
// surface a one-time information message and return null.  Centralised
// so every command gives the user the same error text in the same way.
function ensureDeduceEditor() {
    const editor = vscode.window.activeTextEditor;
    if (!editor || editor.document.languageId !== 'deduce') {
        vscode.window.showInformationMessage(
            'Deduce: open a .pf file and place the cursor inside it first.');
        return null;
    }
    return editor;
}

// Build the {textDocument, position} param object common to most LSP
// requests we issue.
function textDocumentPosition(editor) {
    return {
        textDocument: { uri: editor.document.uri.toString() },
        position: {
            line: editor.selection.active.line,
            character: editor.selection.active.character,
        },
    };
}

// Translate an LSP WorkspaceEdit's {changes: {uri: TextEdit[]}} shape
// into a vscode.WorkspaceEdit, then apply it via the workspace API.
// We don't use client.protocol2CodeConverter because it expects fully
// typed (LSPAny) inputs and our custom requests return plain JSON.
async function applyLspWorkspaceEdit(editor, lspEdit) {
    if (!lspEdit) return false;
    const wsEdit = new vscode.WorkspaceEdit();
    const changes = lspEdit.changes || {};
    let foundEdits = false;
    for (const uriStr of Object.keys(changes)) {
        const uri = vscode.Uri.parse(uriStr);
        for (const e of changes[uriStr]) {
            const range = new vscode.Range(
                new vscode.Position(e.range.start.line, e.range.start.character),
                new vscode.Position(e.range.end.line, e.range.end.character),
            );
            wsEdit.replace(uri, range, e.newText || '');
            foundEdits = true;
        }
    }
    if (!foundEdits) return false;
    const ok = await vscode.workspace.applyEdit(wsEdit);
    if (!ok) return false;
    jumpToFirstHole(editor, lspEdit);
    return true;
}

// After a structured edit applies, move the cursor onto the first `?'
// inside what was just inserted.  Searches the document forward from
// the first edit's start position.  Matches Emacs's
// deduce-lsp--apply-text-edit cursor placement and is what makes
// chained edits (refine -> case split -> induction) feel snappy.
function jumpToFirstHole(editor, lspEdit) {
    const uri = editor.document.uri.toString();
    const lspEdits = (lspEdit.changes && lspEdit.changes[uri]) || [];
    if (lspEdits.length === 0) return;
    const start = lspEdits[0].range.start;
    const doc = editor.document;
    for (let line = start.line; line < doc.lineCount; line++) {
        const text = doc.lineAt(line).text;
        const startCol = line === start.line ? start.character : 0;
        const idx = text.indexOf('?', startCol);
        if (idx >= 0) {
            const pos = new vscode.Position(line, idx);
            editor.selection = new vscode.Selection(pos, pos);
            editor.revealRange(new vscode.Range(pos, pos));
            return;
        }
    }
}

// Refine / Induction shape: query `textDocument/codeAction', find the
// action with the matching title, apply its `edit'.
async function applyCodeActionByTitle(client, title, notFoundMessage) {
    const editor = ensureDeduceEditor();
    if (!editor || !client) return;
    const pos = {
        line: editor.selection.active.line,
        character: editor.selection.active.character,
    };
    let actions;
    try {
        actions = await client.sendRequest('textDocument/codeAction', {
            textDocument: { uri: editor.document.uri.toString() },
            range: { start: pos, end: pos },
            context: { diagnostics: [] },
        });
    } catch (err) {
        vscode.window.showErrorMessage(`Deduce: ${title} request failed: ${err.message || err}`);
        return;
    }
    const action = (actions || []).find((a) => a && a.title === title);
    if (!action || !action.edit) {
        vscode.window.showInformationMessage(`Deduce: ${notFoundMessage}`);
        return;
    }
    await applyLspWorkspaceEdit(editor, action.edit);
}

// Case split / Eliminate shape: query a candidate list, prompt the
// user via QuickPick, send the edit request, apply.
async function applyCandidateEdit(
    client, candidatesMethod, editMethod, paramKey, placeHolder, notFoundMessage,
) {
    const editor = ensureDeduceEditor();
    if (!editor || !client) return;
    const params = textDocumentPosition(editor);
    let candidates;
    try {
        candidates = await client.sendRequest(candidatesMethod, params);
    } catch (err) {
        vscode.window.showErrorMessage(
            `Deduce: ${candidatesMethod} failed: ${err.message || err}`);
        return;
    }
    const choices = Array.isArray(candidates) ? candidates : [];
    if (choices.length === 0) {
        vscode.window.showInformationMessage(`Deduce: ${notFoundMessage}`);
        return;
    }
    const pick = await vscode.window.showQuickPick(choices, { placeHolder });
    if (!pick) return;
    let edit;
    try {
        edit = await client.sendRequest(editMethod, { ...params, [paramKey]: pick });
    } catch (err) {
        vscode.window.showErrorMessage(
            `Deduce: ${editMethod} failed: ${err.message || err}`);
        return;
    }
    if (!edit) {
        vscode.window.showErrorMessage(`Deduce: server returned no edit for ${pick}.`);
        return;
    }
    await applyLspWorkspaceEdit(editor, edit);
}

// Fill-from-given shape: query candidates, pick the first match
// without prompting (matches Emacs after issue #385 -- the server
// already filters to formula-equal givens, so any candidate is a
// valid fill), send the edit request, apply.
async function applyFirstCandidateEdit(
    client, candidatesMethod, editMethod, paramKey, notFoundMessage,
) {
    const editor = ensureDeduceEditor();
    if (!editor || !client) return;
    const params = textDocumentPosition(editor);
    let candidates;
    try {
        candidates = await client.sendRequest(candidatesMethod, params);
    } catch (err) {
        vscode.window.showErrorMessage(
            `Deduce: ${candidatesMethod} failed: ${err.message || err}`);
        return;
    }
    const choices = Array.isArray(candidates) ? candidates : [];
    if (choices.length === 0) {
        vscode.window.showInformationMessage(`Deduce: ${notFoundMessage}`);
        return;
    }
    const label = choices[0];
    let edit;
    try {
        edit = await client.sendRequest(editMethod, { ...params, [paramKey]: label });
    } catch (err) {
        vscode.window.showErrorMessage(
            `Deduce: ${editMethod} failed: ${err.message || err}`);
        return;
    }
    if (!edit) {
        vscode.window.showErrorMessage(`Deduce: server returned no edit for ${label}.`);
        return;
    }
    await applyLspWorkspaceEdit(editor, edit);
}

// Pretty-print a deduce/goalAt response into the goal Output channel.
// Mirror of editor/emacs/deduce-lsp.el's `deduce-lsp--render-goal'.
// Shape: { formula: str, givens: [{ label: str|null, formula: str }], range: ... }
function renderGoal(channel, response) {
    if (!response) {
        channel.appendLine('No goal at this position.');
        return;
    }
    channel.appendLine('Goal:');
    channel.appendLine('  ' + (response.formula || '?'));
    const givens = response.givens || [];
    if (givens.length > 0) {
        channel.appendLine('');
        channel.appendLine('Givens:');
        for (const g of givens) {
            const label = g.label || '_';
            const formula = g.formula || '';
            channel.appendLine(`  ${label}: ${formula}`);
        }
    }
}

function deactivate() {
    if (!client) {
        return undefined;
    }
    return client.stop();
}

module.exports = { activate, deactivate };
