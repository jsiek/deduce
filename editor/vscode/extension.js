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
        vscode.commands.registerCommand('deduce.nextHole', () =>
            nextHoleCommand()),
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

    // --- LLM-driven hole filling --------------------------------
    //
    // Mirror of editor/emacs/deduce-fill-hole.el (C-c C-a).  Flow:
    //
    //   1. Issue `deduce/holeContextAt' to get goal + givens +
    //      lemmas + a fingerprint.
    //   2. Snapshot the document version + the hole's text so we can
    //      verify post-sidecar that nothing has shifted.
    //   3. Spawn `<python> -m tools.claude_fill_hole' with cwd =
    //      deduceRoot, write a JSON request to its stdin, await its
    //      JSON response on stdout.
    //   4. If validation succeeded AND the hole hasn't moved AND the
    //      re-fetched fingerprint matches, splice the validated proof
    //      in via `vscode.workspace.applyEdit'.
    //
    // Multiple sidecars may run concurrently, including in the same
    // document.  Each request keeps its own hole range +
    // fingerprint, so later completions still go through the normal
    // stale-marker check before editing.
    const fillHoleInFlight = new Map();
    context.subscriptions.push(
        vscode.commands.registerCommand('deduce.fillHole', () =>
            fillHoleCommand(client, fillHoleInFlight, root)),
    );
}

// --- LLM fill-hole helpers ----------------------------------------

const DEFAULT_FILL_HOLE_MODEL = {
    'anthropic': 'claude-opus-4-7',
    'openai-compat': 'gemma-4-31B-it',
};

const DEFAULT_FILL_HOLE_KEY_ENV = {
    'anthropic': 'ANTHROPIC_API_KEY',
    'openai-compat': 'OPENAI_API_KEY',
};

async function fillHoleCommand(client, inFlight, deduceRoot) {
    const editor = ensureDeduceEditor();
    if (!editor || !client) return;
    const uriStr = editor.document.uri.toString();
    const requestId = `${Date.now()}-${Math.random().toString(16).slice(2)}`;

    // 1. Pull the hole context (goal + givens + lemmas + fingerprint).
    const ctxParams = {
        textDocument: { uri: uriStr },
        position: {
            line: editor.selection.active.line,
            character: editor.selection.active.character,
        },
    };
    let ctx;
    try {
        ctx = await client.sendRequest('deduce/holeContextAt', ctxParams);
    } catch (err) {
        vscode.window.showErrorMessage(
            `Deduce: holeContextAt failed: ${err.message || err}`);
        return;
    }
    if (!ctx) {
        vscode.window.showInformationMessage(
            'Deduce: place the cursor on a `?` hole first.');
        return;
    }

    const filePath = editor.document.uri.fsPath;
    if (!filePath) {
        vscode.window.showErrorMessage(
            'Deduce fill-hole: the active buffer is not a saved file.');
        return;
    }
    const documentContent = editor.document.getText();
    const origFingerprint = ctx.fingerprint || '';
    const holeRange = toVscodeRange(ctx.holeRange);

    // 2. Resolve sidecar configuration.
    const baseCfg = vscode.workspace.getConfiguration('deduce');
    const fillCfg = vscode.workspace.getConfiguration('deduce.fillHole');
    const python = baseCfg.get('pythonPath') || 'python3';
    const backend = fillCfg.get('backend') || 'anthropic';
    const model = fillCfg.get('model') || DEFAULT_FILL_HOLE_MODEL[backend] || DEFAULT_FILL_HOLE_MODEL.anthropic;
    const apiKeyEnv = fillCfg.get('apiKeyEnv') || DEFAULT_FILL_HOLE_KEY_ENV[backend] || DEFAULT_FILL_HOLE_KEY_ENV.anthropic;
    const baseUrl = fillCfg.get('baseUrl') || '';
    const maxAttempts = Number(fillCfg.get('maxAttempts')) || 5;
    const timeoutSec = Number(fillCfg.get('timeout')) || 60;
    const noStdlib = baseCfg.get('noStdlib') === true;

    const args = [
        '-m', 'tools.claude_fill_hole',
        '--backend', backend,
        '--model', model,
        '--api-key-env', apiKeyEnv,
        '--deduce-root', deduceRoot,
        '--max-attempts', String(maxAttempts),
        '--timeout', String(timeoutSec),
    ];
    if (baseUrl) {
        args.push('--base-url', baseUrl);
    }
    if (noStdlib) {
        args.push('--no-stdlib');
    }

    const payload = {
        file: filePath,
        holeRange: ctx.holeRange,
        goal: ctx.goal,
        givens: ctx.givens || [],
        lemmasInScope: ctx.lemmasInScope || [],
        fingerprint: origFingerprint,
        content: documentContent,
    };

    // 3. Spawn the sidecar inside a progress notification so the user
    // can cancel and gets feedback that something's happening.
    inFlight.set(requestId, { uri: uriStr, holeRange: ctx.holeRange });
    let result;
    try {
        result = await vscode.window.withProgress(
            {
                location: vscode.ProgressLocation.Notification,
                title: `Deduce: asking ${model}…`,
                cancellable: true,
            },
            (progress, token) => runFillHoleSidecar(python, args, JSON.stringify(payload), deduceRoot, token),
        );
    } finally {
        inFlight.delete(requestId);
    }

    if (!result) {
        // Cancelled.
        return;
    }
    if (!result.ok) {
        const attempts = result.attempts || 0;
        vscode.window.showErrorMessage(
            `Deduce fill-hole: ${result.error || 'no proof produced'}`
            + (attempts ? ` (after ${attempts} attempt${attempts === 1 ? '' : 's'})` : ''));
        return;
    }

    // 4. Marker check: hole's text must still be `?` after the
    // sidecar's round-trip.  If anyone typed inside the hole or moved
    // it, refuse to splice.
    const currentText = editor.document.getText(holeRange);
    if (currentText !== '?') {
        vscode.window.showErrorMessage(
            `Deduce fill-hole: hole edited while the model was thinking (now ${JSON.stringify(currentText)}).`);
        return;
    }

    // Re-fetch holeContextAt and compare fingerprints.  The lemma
    // list is excluded from the fingerprint by design (adding a new
    // lemma between request and response shouldn't invalidate an
    // otherwise valid proof), so this catches edits to the theorem
    // statement itself.
    try {
        const recheck = await client.sendRequest('deduce/holeContextAt', {
            textDocument: { uri: uriStr },
            position: { line: holeRange.start.line, character: holeRange.start.character },
            includeLemmas: false,
        });
        if (recheck && recheck.fingerprint && recheck.fingerprint !== origFingerprint) {
            vscode.window.showErrorMessage(
                'Deduce fill-hole: hole context changed while the model was thinking.');
            return;
        }
    } catch {
        // If the recheck itself fails (server gone away, etc.), fall
        // through and trust the marker check above.
    }

    // 5. Splice.
    const proof = reindentProof(result.proof || '', holeRange.start.character);
    const wsEdit = new vscode.WorkspaceEdit();
    wsEdit.replace(editor.document.uri, holeRange, proof);
    const applied = await vscode.workspace.applyEdit(wsEdit);
    if (!applied) {
        vscode.window.showErrorMessage('Deduce fill-hole: workspace edit was rejected.');
        return;
    }
    const attempts = result.attempts || 1;
    vscode.window.showInformationMessage(
        `Deduce fill-hole: filled in ${attempts} attempt${attempts === 1 ? '' : 's'}.`);
}

function toVscodeRange(lspRange) {
    return new vscode.Range(
        new vscode.Position(lspRange.start.line, lspRange.start.character),
        new vscode.Position(lspRange.end.line, lspRange.end.character),
    );
}

// Run the hole-fill sidecar as a subprocess.  Writes ``payload'' to
// stdin, captures stdout (the JSON response) and stderr (NDJSON
// progress).  Resolves with the parsed response object on success,
// with ``{ok: false, error, attempts}'' on protocol failure, or with
// ``null'' if the user cancels via the progress notification.
function runFillHoleSidecar(python, args, payload, cwd, cancellationToken) {
    return new Promise((resolve) => {
        const { spawn } = require('child_process');
        const env = { ...process.env, PYTHONPATH: cwd };
        let proc;
        try {
            proc = spawn(python, args, { cwd, env });
        } catch (err) {
            resolve({
                ok: false,
                attempts: 0,
                error: `failed to spawn sidecar: ${err.message || err}`,
            });
            return;
        }
        let stdout = '';
        let stderr = '';
        let cancelled = false;
        proc.stdout.on('data', (chunk) => { stdout += chunk.toString('utf8'); });
        proc.stderr.on('data', (chunk) => { stderr += chunk.toString('utf8'); });
        proc.on('error', (err) => {
            resolve({
                ok: false,
                attempts: 0,
                error: `sidecar error: ${err.message || err}`,
            });
        });
        proc.on('close', (exitCode) => {
            if (cancelled) {
                resolve(null);
                return;
            }
            const trimmed = stdout.trim();
            if (!trimmed) {
                const tail = stderr.length > 2048 ? stderr.slice(-2048) : stderr;
                resolve({
                    ok: false,
                    attempts: 0,
                    error: `sidecar exited ${exitCode} without a response. stderr tail:\n${tail.trim() || '(empty)'}`,
                });
                return;
            }
            try {
                const parsed = JSON.parse(trimmed);
                resolve(parsed);
            } catch (err) {
                resolve({
                    ok: false,
                    attempts: 0,
                    error: `could not parse sidecar response as JSON: ${err.message || err}\nstdout: ${trimmed.slice(0, 500)}`,
                });
            }
        });
        if (cancellationToken) {
            cancellationToken.onCancellationRequested(() => {
                cancelled = true;
                try { proc.kill(); } catch { /* already dead */ }
            });
        }
        proc.stdin.write(payload);
        proc.stdin.end();
    });
}

// Re-indent a multi-line proof so that lines after the first start at
// ``column'' spaces of indentation.  Mirror of
// editor/emacs/deduce-fill-hole.el's ``deduce-fill-hole--reindent-proof''.
// The sidecar emits proof text without knowing the column the `?`
// sits at, so a multi-line response lands with the first line at the
// hole's column (correct) and every following line at column 0 (wrong).
function reindentProof(proof, column) {
    const lines = proof.split('\n');
    if (lines.length <= 1) return proof;
    const first = lines[0];
    const rest = lines.slice(1);
    const nonBlank = rest.filter((l) => l.replace(/[ \t]/g, '').length > 0);
    const common = commonLeadingWhitespace(nonBlank);
    const stripLen = common.length;
    const pad = ' '.repeat(column);
    const restFixed = rest.map((line) => {
        if (line.replace(/[ \t]/g, '').length === 0) return '';
        if (stripLen > 0 && line.length >= stripLen && line.slice(0, stripLen) === common) {
            return pad + line.slice(stripLen);
        }
        return pad + line;
    });
    return [first, ...restFixed].join('\n');
}

function commonLeadingWhitespace(lines) {
    if (lines.length === 0) return '';
    const wsMatch = (l) => (l.match(/^[ \t]*/) || [''])[0];
    let prefix = wsMatch(lines[0]);
    for (const line of lines.slice(1)) {
        const ws = wsMatch(line);
        let i = 0;
        const lim = Math.min(prefix.length, ws.length);
        while (i < lim && prefix[i] === ws[i]) i++;
        prefix = prefix.slice(0, i);
    }
    return prefix;
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

function nextHoleCommand() {
    const editor = ensureDeduceEditor();
    if (!editor) return;
    const doc = editor.document;
    const startOffset = doc.offsetAt(editor.selection.active);
    const foundOffset = findNextHoleOffset(doc.getText(), startOffset);
    if (foundOffset === undefined) {
        vscode.window.showInformationMessage('Deduce: no proof hole found.');
        return;
    }
    const pos = doc.positionAt(foundOffset);
    editor.selection = new vscode.Selection(pos, pos);
    editor.revealRange(new vscode.Range(pos, pos));
}

function findNextHoleOffset(text, startOffset) {
    const after = findHoleOffsetInRange(text, Math.min(startOffset + 1, text.length), text.length);
    if (after !== undefined) return after;
    return findHoleOffsetInRange(text, 0, startOffset);
}

function findHoleOffsetInRange(text, startOffset, endOffset) {
    for (let i = startOffset; i < endOffset; i++) {
        if (text[i] === '?' && isStandaloneHoleAt(text, i)) {
            return i;
        }
    }
    return undefined;
}

function isStandaloneHoleAt(text, index) {
    return !isDeduceIdentifierChar(text[index - 1])
        && !isDeduceIdentifierChar(text[index + 1]);
}

function isDeduceIdentifierChar(ch) {
    return ch !== undefined && /[A-Za-z0-9_?!']/.test(ch);
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

module.exports = {
    activate,
    deactivate,
    findNextHoleOffset,
    isStandaloneHoleAt,
};
