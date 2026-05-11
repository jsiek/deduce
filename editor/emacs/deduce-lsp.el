;;; deduce-lsp.el --- Eglot integration for deduce-mode -*- lexical-binding: t; -*-

;; Copyright (C) 2026 Jeremy G. Siek and Deduce contributors
;; SPDX-License-Identifier: MIT

;; Author: Deduce contributors
;; Maintainer: Jeremy G. Siek
;; Version: 0.1.0
;; Package-Requires: ((emacs "29.1") (deduce-mode "0.1.0"))
;; Keywords: languages
;; URL: https://github.com/jsiek/deduce

;;; Commentary:

;; deduce-lsp.el wires `deduce-mode' buffers to the Deduce LSP server
;; in lsp/lsp_server.py via eglot.  Phase B / Step 4 of the Emacs mode
;; plan (see docs/emacs-plan.md).
;;
;; Installation
;; ------------
;;
;;     (add-to-list 'load-path "/path/to/deduce/editor/emacs")
;;     (require 'deduce-mode)
;;     (require 'deduce-lsp)
;;
;; By default, opening a `.pf' file auto-starts eglot.  Set
;; `deduce-lsp-auto-start' to nil to opt out and trigger eglot
;; manually with `M-x eglot'.
;;
;; What you get
;; ------------
;;
;;   Diagnostics on save        flycheck/flymake-style underlines
;;   M-.                        go to definition (textDocument/definition)
;;   M-x imenu                  outline of top-level decls (documentSymbol)
;;
;; Step 5 adds `C-c C-g' for the custom `deduce/goalAt' request.
;; Step 6 adds the four Phase-4 keybindings: `C-c C-r' (refine, LSP
;; Step 15), `C-c C-c' (case split, LSP Step 16), `C-c C-i'
;; (induction, LSP Step 17), and `C-c C-e' (eliminate / use-fact,
;; LSP Step 18) -- all live.
;;
;; Server command
;; --------------
;;
;; The default command is `python3 -m lsp.lsp_server', invoked from
;; the project root determined by `project-current'.  When you edit
;; `.pf' files inside the deduce repo this works out of the box --
;; `lsp/lsp_server.py' is on Python's import path.
;;
;; If your proofs live OUTSIDE the deduce repo, customize
;; `deduce-lsp-deduce-root' to point at your deduce checkout; the
;; server command will then be invoked with PYTHONPATH including
;; that directory so the import resolves regardless of cwd.
;;
;; Set `deduce-lsp-prelude-disabled' to a non-nil value to skip the
;; standard library prelude (mirrors `deduce.py --no-stdlib').  The
;; server command then includes `DEDUCE_NO_STDLIB=1' in its env.
;;
;; See `editor/emacs/README.md' for the full list of customization
;; variables, keybindings, and a manual smoke-test script.

;;; Code:

(require 'deduce-mode)
(require 'jsonrpc)
(require 'seq)

;; Declare eglot's variables so the byte-compiler doesn't warn when
;; we reference them inside `with-eval-after-load'.  We don't
;; `require' eglot at top level because it isn't strictly needed
;; until the user opens a `.pf' file -- eglot is built into Emacs
;; 29+ so loading it lazily keeps `(require 'deduce-lsp)' fast.
(defvar eglot-server-programs)
(declare-function eglot-ensure "eglot")
(declare-function eglot-current-server "eglot")
(declare-function eglot--signal-textDocument/didChange "eglot")

;; Flymake is built into Emacs 29+; declare the diagnostic accessors so
;; the byte-compiler doesn't warn before `flymake' is loaded.
(declare-function flymake-diagnostics "flymake")
(declare-function flymake-diagnostic-type "flymake")
(declare-function flymake-diagnostic-beg "flymake")
(declare-function flymake-diagnostic-end "flymake")
(declare-function flymake-diagnostic-text "flymake")
(declare-function flymake-diagnostic-buffer "flymake")


(defgroup deduce-lsp nil
  "Eglot integration for `deduce-mode'."
  :group 'deduce
  :prefix "deduce-lsp-")


(defcustom deduce-lsp-python-program "python3"
  "Python interpreter used to launch the Deduce LSP server."
  :type 'string
  :group 'deduce-lsp)


(defcustom deduce-lsp-deduce-root nil
  "Path to a Deduce repository checkout, or nil to rely on cwd.

When nil, eglot launches the server from the project root
determined by `project-current' -- this works when editing `.pf'
files inside the deduce repo, where `lsp/lsp_server.py' is on
Python's import path.

When set to a directory path, the server command runs through
`env' with PYTHONPATH including that directory, so `python3 -m
lsp.lsp_server' resolves regardless of cwd.  Useful when your
proofs live outside the deduce repo."
  :type '(choice (const :tag "Auto (project root)" nil)
                 (directory :tag "Deduce checkout"))
  :group 'deduce-lsp)


(defcustom deduce-lsp-auto-start t
  "If non-nil, automatically start eglot when entering `deduce-mode'.

Set to nil to opt out and trigger eglot manually with `M-x eglot'.
The first call per process bootstraps the prelude (~1s with `.thm'
cache, ~13s without) and is the slowest one; subsequent connects
are warm."
  :type 'boolean
  :group 'deduce-lsp)


(defcustom deduce-lsp-prelude-disabled nil
  "If non-nil, start the LSP server without the standard library prelude.

Sets `DEDUCE_NO_STDLIB=1' in the spawned process environment, which
mirrors `deduce.py --no-stdlib'.  Useful when working on `lib/'
itself or on minimal test fixtures where the prelude bootstrap is
unwanted overhead."
  :type 'boolean
  :group 'deduce-lsp)


(defun deduce-lsp-server-command (&optional _interactive)
  "Return the command list eglot uses to launch the Deduce LSP server.

Two knobs influence the command shape:

- `deduce-lsp-deduce-root', when set, contributes a `PYTHONPATH'
  entry so `python3 -m lsp.lsp_server' resolves regardless of cwd.
- `deduce-lsp-prelude-disabled', when non-nil, contributes
  `DEDUCE_NO_STDLIB=1' so the server skips the stdlib prelude.

Whenever at least one knob is active, the command is wrapped in
`env KEY=VAL ...' so the bindings reach the spawned process.
Otherwise the bare `python3 -m lsp.lsp_server' form is returned
and eglot's cwd is trusted to be the deduce repo root.

The optional argument is unused; it's accepted because eglot
calls server-program functions with one argument (an
`interactive' flag) since Emacs 29."
  (let ((py deduce-lsp-python-program)
        (mod-args '("-m" "lsp.lsp_server"))
        (env-bindings nil))
    (when deduce-lsp-deduce-root
      (push (format "PYTHONPATH=%s"
                    (expand-file-name deduce-lsp-deduce-root))
            env-bindings))
    (when deduce-lsp-prelude-disabled
      (push "DEDUCE_NO_STDLIB=1" env-bindings))
    (if env-bindings
        (append (cons "env" (nreverse env-bindings))
                (cons py mod-args))
      (cons py mod-args))))


(defun deduce-lsp--maybe-ensure ()
  "Hook function: call `eglot-ensure' when entering `deduce-mode'
unless `deduce-lsp-auto-start' is nil."
  (when deduce-lsp-auto-start
    (eglot-ensure)))


;; Register with eglot.  We use `with-eval-after-load' so this works
;; whether eglot is loaded before or after deduce-lsp.
;;;###autoload
(with-eval-after-load 'eglot
  (add-to-list 'eglot-server-programs
               '(deduce-mode . deduce-lsp-server-command)))


;;;###autoload
(add-hook 'deduce-mode-hook #'deduce-lsp--maybe-ensure)


;; ---------------------------------------------------------------------
;; Goal at point (Step 5)
;; ---------------------------------------------------------------------
;;
;; LSP has no built-in for "what proof obligation is at this cursor",
;; so the server (lsp/lsp_server.py) exposes a custom `deduce/goalAt'
;; request.  The command below issues that request via jsonrpc and
;; renders the formula + givens in a `*Deduce Goal*' buffer.

(defconst deduce-lsp-goal-buffer-name "*Deduce Goal*"
  "Buffer name used to display goal-at-point output.")


(defun deduce-lsp--current-uri ()
  "Return the LSP URI for the current buffer's file.

Errors out if the buffer isn't visiting a file.  Resolves
symlinks via `file-truename' so the URI matches what eglot uses
when it sends `textDocument/didOpen' -- otherwise pygls keys its
workspace under the truename URI and our requests (using a
non-resolved path) hit `KeyError'.  This bites on macOS where
`/tmp' is a symlink to `/private/tmp', and on any system where
the user opens a file via a symlinked path."
  (let ((path (or buffer-file-name
                  (user-error "Buffer is not visiting a file"))))
    (concat "file://" (file-truename path))))


(defun deduce-lsp--current-position ()
  "Return the LSP-shape `Position' for point in the current buffer.
LSP positions are 0-indexed (line and character)."
  (list :line (1- (line-number-at-pos))
        :character (current-column)))


(defun deduce-lsp--request (server method params)
  "Issue an LSP request to SERVER, flushing pending buffer changes first.

`jsonrpc-request' on its own races with eglot's didChange
debouncing.  Eglot batches buffer changes into a
`textDocument/didChange' notification fired on idle (after
`eglot-send-changes-idle-time', default 0.5s).  When the user
chains structured edits -- e.g. `C-c C-r' on a hole, then
`C-c C-r' on the inserted hole right away -- the second request
can reach the server before the didChange from the first edit
has gone out, so the server runs against stale buffer content
and returns the wrong (or no) edit.

This helper sends pending changes synchronously, then issues
the JSON-RPC request.  Mirrors the pattern eglot's internal
`eglot--request' uses by default.

Note on private API: `eglot--signal-textDocument/didChange' has
the `--' private-symbol convention, but the function name and
behaviour have been stable across recent eglot releases and it's
the explicit primitive eglot itself uses for this purpose.  If a
future eglot release renames it, this function is the single
point of update."
  (eglot--signal-textDocument/didChange)
  (jsonrpc-request server method params))


(defun deduce-lsp--render-goal (response)
  "Pretty-print a `deduce/goalAt' RESPONSE into the current buffer.

Expected shape (post-JSON-decode plist):

  (:formula STR :givens VEC :range PLIST)

where each element of `givens' is `(:label STR-OR-NIL :formula STR)'.
A nil RESPONSE means \"no goal at this position\"."
  (if (null response)
      (insert "No goal at this position.\n")
    (let ((formula (plist-get response :formula))
          (givens (plist-get response :givens)))
      (insert "Goal:\n  " (or formula "?") "\n")
      (when (and givens (> (length givens) 0))
        (insert "\nGivens:\n")
        (seq-doseq (g givens)
          (let ((label (plist-get g :label))
                (gformula (plist-get g :formula)))
            (insert "  "
                    (or label "_")
                    ": "
                    (or gformula "")
                    "\n")))))))


(defun deduce-lsp--show-goal (response)
  "Display RESPONSE in the `*Deduce Goal*' buffer and pop it up."
  (let ((buf (get-buffer-create deduce-lsp-goal-buffer-name)))
    (with-current-buffer buf
      (let ((inhibit-read-only t))
        (read-only-mode 0)
        (erase-buffer)
        (deduce-lsp--render-goal response)
        (goto-char (point-min)))
      (view-mode 1))
    (display-buffer buf)))


(defun deduce-show-goal-at-point ()
  "Show the proof goal at point in a `*Deduce Goal*' buffer.

Issues a custom `deduce/goalAt' request to the active eglot
server and renders the response.  Errors if no eglot connection
is running in the current buffer."
  (interactive)
  (let ((server (eglot-current-server)))
    (unless server
      (user-error
       "No eglot server active in this buffer; M-x eglot first"))
    (let* ((params (list :textDocument
                         (list :uri (deduce-lsp--current-uri))
                         :position (deduce-lsp--current-position)))
           (response (deduce-lsp--request server :deduce/goalAt params)))
      (deduce-lsp--show-goal response))))


;; Bind `C-c C-g' in `deduce-mode-map'.  We bind here in deduce-lsp
;; rather than in deduce-mode because the command depends on eglot
;; being available, so the binding only makes sense once the user
;; has opted into LSP via `(require 'deduce-lsp)'.
(define-key deduce-mode-map (kbd "C-c C-g") #'deduce-show-goal-at-point)


;; ---------------------------------------------------------------------
;; Phase-4 structured edits (Step 6)
;; ---------------------------------------------------------------------
;;
;; Live bindings (LSP Steps 15-18):
;;
;;   `C-c C-r'  deduce-lsp-refine-hole  (Step 15)
;;     Cursor on a `?'.  Issues `textDocument/codeAction' filtered to
;;     `refactor.rewrite' and applies the action titled "Refine hole".
;;     One keystroke; no prompt.
;;
;;   `C-c C-c'  deduce-lsp-case-split   (Step 16)
;;     Cursor on a `?'.  Issues `deduce/splittableVarsAt' to fetch
;;     candidate variable names, prompts via `completing-read' (TAB
;;     completion), then issues `deduce/caseSplitAt' with the chosen
;;     variable.  Two keystrokes + identifier; no ambiguity about
;;     which `?' the skeleton replaces -- it's the one under the
;;     cursor.
;;
;;   `C-c C-i'  deduce-lsp-induction    (Step 17)
;;     Cursor on a `?' whose goal is `all x:T. P(x)' (T a Union with
;;     >=2 alternatives).  Issues `textDocument/codeAction' filtered
;;     to `refactor.rewrite' and applies the action titled
;;     "Induction".  Same one-keystroke shape as refine -- the goal
;;     itself is the only input the operation needs.
;;
;;   `C-c C-e'  deduce-lsp-eliminate    (Step 18)
;;     Cursor on a `?'.  Issues `deduce/eliminableVarsAt' to fetch
;;     candidate hypothesis labels, prompts via `completing-read'
;;     (TAB completion), then issues `deduce/eliminateAt' with the
;;     chosen label.  Same wire-shape as case split (custom request,
;;     extra user-supplied label argument) -- their UX is symmetric.
;;
;;   `C-c C-f'  deduce-lsp-fill-from-given  (issue #353)
;;     Cursor on a `?'.  Issues `deduce/matchingGivensAt' to fetch
;;     labels of in-scope givens whose formula equals the goal, then
;;     picks the first match without prompting (issue #385).  Issues
;;     `deduce/fillFromGivenAt' with that label and replaces the `?'
;;     with `conclude <goal> by <label>'.
;;
;; Refine and induction use `textDocument/codeAction' because they
;; take no extra user input.  Case-split and eliminate take a
;; user-supplied identifier, which codeAction can't carry, so they
;; get custom server methods.

(defun deduce-lsp--lsp-pos-to-point (line character)
  "Convert LSP 0-indexed (LINE, CHARACTER) to a point in the current buffer.

Assumes ASCII (or at least each codepoint costs one column); for
proof files in practice this is the case.  When/if Deduce gains
non-ASCII source support, swap this for eglot's
`eglot--lsp-position-to-point' which handles UTF-16 properly."
  (save-excursion
    (goto-char (point-min))
    (forward-line line)
    ;; `forward-char' works in characters, which on UTF-16 ASCII text
    ;; matches LSP's `character'.
    (forward-char character)
    (point)))


(defun deduce-lsp--apply-text-edit (edit)
  "Apply a single LSP `TextEdit' EDIT to the current buffer.

EDIT is a plist of the form `(:range PLIST :newText STR)' where
the range is `(:start POS :end POS)' and POS is `(:line N
:character N)'.

After applying the edit, point is moved onto the first `?` in the
inserted text -- the natural next refinement target so the user
can type `C-c C-r' or `C-c C-c' immediately without repositioning.
When the template has no `?' (e.g. `reflexive', `.'), point is
left at the end of the insertion."
  (let* ((range (plist-get edit :range))
         (start (plist-get range :start))
         (end (plist-get range :end))
         (new-text (or (plist-get edit :newText) ""))
         (p1 (deduce-lsp--lsp-pos-to-point
              (plist-get start :line)
              (plist-get start :character)))
         (p2 (deduce-lsp--lsp-pos-to-point
              (plist-get end :line)
              (plist-get end :character))))
    (delete-region p1 p2)
    (goto-char p1)
    (insert new-text)
    (let ((insert-end (point)))
      (goto-char p1)
      (if (search-forward "?" insert-end t)
          ;; `search-forward' lands point AFTER the match; back up
          ;; one so it sits ON the `?'.
          (backward-char 1)
        (goto-char insert-end)))))


(defun deduce-lsp--text-edits-for-uri (changes uri)
  "Extract the TextEdit list for URI from a WorkspaceEdit `changes' plist.

CHANGES is the value of the WorkspaceEdit's `:changes' field --
a plist whose keys are URIs interned as keywords (e.g.
`:file:///path/foo.pf').  Returns the TextEdit list, or nil if
URI has no edits."
  (when changes
    (let ((target (intern-soft (concat ":" uri))))
      (when target
        (plist-get changes target)))))


(defun deduce-lsp--apply-code-action (action)
  "Apply the WorkspaceEdit of CodeAction plist ACTION to the buffer."
  (deduce-lsp--apply-workspace-edit (plist-get action :edit)))


(defun deduce-lsp--find-action-by-title (title)
  "Send `textDocument/codeAction' at point, return the action plist
whose `:title' equals TITLE, or nil if no such action is offered.

Errors out when no eglot server is active in the current buffer
-- the codeAction request needs a server to run against.

This is the shared building block for the Phase-4 keybindings;
each command wraps it with its own \"not available\" message."
  (let ((server (eglot-current-server)))
    (unless server
      (user-error
       "No eglot server active in this buffer; M-x eglot first"))
    (let* ((pos (deduce-lsp--current-position))
           (params (list :textDocument (list :uri (deduce-lsp--current-uri))
                         :range (list :start pos :end pos)
                         :context (list :diagnostics [])))
           (actions (deduce-lsp--request server :textDocument/codeAction params))
           ;; The server returns either a vector or nil; normalise.
           (action-list (if (vectorp actions) (append actions nil) actions)))
      (seq-find
       (lambda (a) (equal (plist-get a :title) title))
       action-list))))


(defun deduce-lsp-refine-hole ()
  "Apply the LSP-suggested refinement for the hole at point.

Issues a `textDocument/codeAction' request and picks the action
titled \"Refine hole\" -- the LSP server's Step-15 output.  The
matching action's WorkspaceEdit is applied directly, skipping the
action picker.  This is the fast path for the keybinding.

When the cursor isn't on a hole (or the goal shape isn't
recognised by the server), errors with `No refinement available
at point.'  When no eglot connection is active, prompts the user
to run `M-x eglot' first."
  (interactive)
  (let ((action (deduce-lsp--find-action-by-title "Refine hole")))
    (unless action
      (user-error "No refinement available at point"))
    (deduce-lsp--apply-code-action action)))


(defun deduce-lsp--text-document-position ()
  "Return the LSP `{textDocument, position}' plist for point."
  (list :textDocument (list :uri (deduce-lsp--current-uri))
        :position (deduce-lsp--current-position)))


(defun deduce-lsp-case-split (variable)
  "Case-split the hole at point on VARIABLE.

The cursor must sit on (or immediately adjacent to) a `?' token;
that `?' is the replacement target.  VARIABLE names the in-scope
binding to split on -- a Union-typed term variable yields a
`switch' skeleton, an `Or'-shaped proof variable yields a
`cases' skeleton.

Interactively, queries the server for the splittable variables in
scope at the hole (custom request `deduce/splittableVarsAt') and
prompts via `completing-read' with TAB completion against that
list.  When the candidate list is empty -- e.g. the cursor isn't
on a `?' or no Union/Or binding is in scope -- errors with `No
case split available at point.'

The chosen variable is then sent in a `deduce/caseSplitAt'
request; the returned WorkspaceEdit is applied directly.  Errors
out without applying when the server returns null."
  (interactive
   (let ((server (eglot-current-server)))
     (unless server
       (user-error
        "No eglot server active in this buffer; M-x eglot first"))
     (let* ((params (deduce-lsp--text-document-position))
            (candidates (deduce-lsp--request server :deduce/splittableVarsAt
                                              params))
            (candidate-list (if (vectorp candidates)
                                (append candidates nil)
                              candidates)))
       (unless candidate-list
         (user-error "No case split available at point"))
       (list (completing-read "Case split on: " candidate-list
                              nil t)))))
  (let ((server (eglot-current-server)))
    (unless server
      (user-error
       "No eglot server active in this buffer; M-x eglot first"))
    (let* ((params (append (deduce-lsp--text-document-position)
                           (list :variable variable)))
           (edit (deduce-lsp--request server :deduce/caseSplitAt params)))
      (unless edit
        (user-error
         "Server returned no edit for case split on %s" variable))
      (deduce-lsp--apply-workspace-edit edit))))


(defun deduce-lsp--apply-workspace-edit (edit)
  "Apply a WorkspaceEdit plist EDIT (`:changes' shape) to the buffer."
  (let* ((changes (plist-get edit :changes))
         (uri (deduce-lsp--current-uri))
         (edits (deduce-lsp--text-edits-for-uri changes uri)))
    (unless edits
      (user-error
       "WorkspaceEdit has no edits for the current buffer"))
    (mapc #'deduce-lsp--apply-text-edit (reverse (append edits nil)))))


(defun deduce-lsp-induction ()
  "Apply the LSP-suggested induction skeleton for the goal at point.

Issues a `textDocument/codeAction' request and picks the action
titled \"Induction\" -- the LSP server's Step-17 output.  The
matching action's WorkspaceEdit replaces the `?' under point
with an `induction T\\n  case Cons1(...) [assume IH<N>: ...] { ? }
  ...' skeleton, one case per constructor.

When the cursor isn't on a hole, when the goal isn't `all x:T.
P(x)' over a Union, or when the union has fewer than two
constructors, errors with `No induction available at point.'
When no eglot connection is active, prompts the user to run
`M-x eglot' first."
  (interactive)
  (let ((action (deduce-lsp--find-action-by-title "Induction")))
    (unless action
      (user-error "No induction available at point"))
    (deduce-lsp--apply-code-action action)))


(defun deduce-lsp-eliminate (label)
  "Use the in-scope hypothesis LABEL at the hole at point.

The cursor must sit on (or immediately adjacent to) a `?' token;
that `?' is the replacement target.  LABEL names an in-scope
proof binding -- typically a hypothesis introduced by `assume'.
The template is chosen from the binding's formula shape:

  H: P and Q     -> destructure with `have ... by conjunct N of H'
  H: P or Q      -> `cases H ...'
  H: if P then Q -> `have h: Q by apply H to ?'
  H: all x:T. P  -> `H[?]'
  H: some x:T. P -> `obtain ... where ... from H'
  H: e1 = e2     -> `replace H'
  H: false       -> `H' (discharges any goal)

Interactively, queries the server for the eliminable hypothesis
labels in scope at the hole (custom request
`deduce/eliminableVarsAt') and prompts via `completing-read' with
TAB completion against that list.  When the candidate list is
empty -- e.g. the cursor isn't on a `?' or no eliminable binding
is in scope -- errors with `No elimination available at point.'

The chosen label is then sent in a `deduce/eliminateAt' request;
the returned WorkspaceEdit is applied directly.  Errors out
without applying when the server returns null."
  (interactive
   (let ((server (eglot-current-server)))
     (unless server
       (user-error
        "No eglot server active in this buffer; M-x eglot first"))
     (let* ((params (deduce-lsp--text-document-position))
            (candidates (deduce-lsp--request server :deduce/eliminableVarsAt
                                              params))
            (candidate-list (if (vectorp candidates)
                                (append candidates nil)
                              candidates)))
       (unless candidate-list
         (user-error "No elimination available at point"))
       (list (completing-read "Eliminate on: " candidate-list
                              nil t)))))
  (let ((server (eglot-current-server)))
    (unless server
      (user-error
       "No eglot server active in this buffer; M-x eglot first"))
    (let* ((params (append (deduce-lsp--text-document-position)
                           (list :label label)))
           (edit (deduce-lsp--request server :deduce/eliminateAt params)))
      (unless edit
        (user-error
         "Server returned no edit for elimination on %s" label))
      (deduce-lsp--apply-workspace-edit edit))))


(defun deduce-lsp-fill-from-given (label)
  "Fill the hole at point with `conclude <goal> by LABEL'.

The cursor must sit on (or immediately adjacent to) a `?' token;
that `?' is the replacement target.  LABEL names an in-scope local
proof binding whose formula equals the goal at the hole.

Interactively, queries the server for the matching given labels in
scope at the hole (custom request `deduce/matchingGivensAt'),
errors with `No matching given at point.' when the candidate list
is empty, and otherwise picks the first candidate without prompting
\(issue #385\).

The chosen label is then sent in a `deduce/fillFromGivenAt'
request; the returned WorkspaceEdit is applied directly.  Errors
out without applying when the server returns null."
  (interactive
   (let ((server (eglot-current-server)))
     (unless server
       (user-error
        "No eglot server active in this buffer; M-x eglot first"))
     (let* ((params (deduce-lsp--text-document-position))
            (candidates (deduce-lsp--request server :deduce/matchingGivensAt
                                              params))
            (candidate-list (if (vectorp candidates)
                                (append candidates nil)
                              candidates)))
       (unless candidate-list
         (user-error "No matching given at point"))
       (list (car candidate-list)))))
  (let ((server (eglot-current-server)))
    (unless server
      (user-error
       "No eglot server active in this buffer; M-x eglot first"))
    (let* ((params (append (deduce-lsp--text-document-position)
                           (list :label label)))
           (edit (deduce-lsp--request server :deduce/fillFromGivenAt params)))
      (unless edit
        (user-error
         "Server returned no edit for fill-from-given on %s" label))
      (deduce-lsp--apply-workspace-edit edit))))


;; Bind `C-c C-r' (refine), `C-c C-c' (case split), `C-c C-i'
;; (induction), `C-c C-e' (eliminate), and `C-c C-f' (fill from
;; given) in `deduce-mode-map'.  Same rationale as `C-c C-g': only
;; meaningful when LSP is loaded.
(define-key deduce-mode-map (kbd "C-c C-r") #'deduce-lsp-refine-hole)
(define-key deduce-mode-map (kbd "C-c C-c") #'deduce-lsp-case-split)
(define-key deduce-mode-map (kbd "C-c C-i") #'deduce-lsp-induction)
(define-key deduce-mode-map (kbd "C-c C-e") #'deduce-lsp-eliminate)
(define-key deduce-mode-map (kbd "C-c C-f") #'deduce-lsp-fill-from-given)


;; ---------------------------------------------------------------------
;; Show diagnostic at point (issue #430)
;; ---------------------------------------------------------------------
;;
;; Deduce error messages are multi-line by design: a one-line headline
;; followed by a location line and one or more tab-indented grammar
;; rules (parse errors) or a goal/givens block (proof errors).  The
;; echo area, where flymake/eglot surface the diagnostic at point,
;; shows only the first line on most Emacs configurations -- the body
;; gets clipped and the user can't see why their proof failed.
;;
;; `deduce-show-diagnostic-at-point' pulls every flymake diagnostic
;; overlapping point and renders the full text into a `*Deduce
;; Diagnostic*' popup buffer.  Same display strategy as the goal-at
;; popup (read-only `view-mode', `display-buffer'), so the keybinding
;; is symmetric: `C-c C-g' for the proof goal, `C-c C-x' for the
;; error explanation.

(defconst deduce-lsp-diagnostic-buffer-name "*Deduce Diagnostic*"
  "Buffer name used to display the full diagnostic message at point.")


(defun deduce-lsp--diagnostics-at-point ()
  "Return the list of flymake diagnostics overlapping point.

When point sits between diagnostics, this returns nil; the caller
widens the search to the current line."
  (require 'flymake)
  (when (fboundp 'flymake-diagnostics)
    (flymake-diagnostics (point) (point))))


(defun deduce-lsp--diagnostics-on-line ()
  "Return the list of flymake diagnostics overlapping the current line."
  (require 'flymake)
  (when (fboundp 'flymake-diagnostics)
    (flymake-diagnostics (line-beginning-position) (line-end-position))))


(defun deduce-lsp--render-diagnostic (diag)
  "Insert a flymake DIAG into the current buffer.

Renders a one-line header (severity + 1-indexed line:col range) so
the user can correlate the popup with the underline in the source
buffer, then the full diagnostic text on subsequent lines -- newlines
and tab-indented continuations preserved."
  (let* ((type   (flymake-diagnostic-type diag))
         (beg    (flymake-diagnostic-beg diag))
         (end    (flymake-diagnostic-end diag))
         (text   (or (flymake-diagnostic-text diag) ""))
         (buffer (flymake-diagnostic-buffer diag))
         (sev    (cond ((eq type :error)   "error")
                       ((eq type :warning) "warning")
                       ((eq type :note)    "note")
                       (t                  (format "%s" type)))))
    (insert (format "[%s]" sev))
    (when (and buffer (buffer-live-p buffer) beg end)
      (let (line col-start col-end)
        (with-current-buffer buffer
          (save-excursion
            (goto-char beg)
            (setq line (line-number-at-pos)
                  col-start (1+ (current-column)))
            (goto-char end)
            (setq col-end (1+ (current-column)))))
        (insert (format " %d:%d-%d" line col-start col-end))))
    (insert "\n")
    (insert text)
    (unless (string-suffix-p "\n" text)
      (insert "\n"))))


(defun deduce-lsp--show-diagnostics (diags)
  "Display the list of DIAGS in the `*Deduce Diagnostic*' buffer."
  (let ((buf (get-buffer-create deduce-lsp-diagnostic-buffer-name)))
    (with-current-buffer buf
      (let ((inhibit-read-only t))
        (read-only-mode 0)
        (erase-buffer)
        (if (null diags)
            (insert "No diagnostic at point.\n")
          (let ((first t))
            (dolist (d diags)
              (unless first (insert "\n"))
              (setq first nil)
              (deduce-lsp--render-diagnostic d))))
        (goto-char (point-min)))
      (view-mode 1))
    (display-buffer buf)))


(defun deduce-show-diagnostic-at-point ()
  "Show the full text of the diagnostic(s) at point in a popup buffer.

Deduce error messages span several lines (a headline, a location,
and a grammar / proof context).  Flymake clips that to the first
line in the echo area, so this command opens a `*Deduce
Diagnostic*' buffer with every diagnostic that overlaps point --
or, if point is between diagnostics, every diagnostic on the
current line."
  (interactive)
  (let ((diags (or (deduce-lsp--diagnostics-at-point)
                   (deduce-lsp--diagnostics-on-line))))
    (deduce-lsp--show-diagnostics diags)))


(define-key deduce-mode-map (kbd "C-c C-x") #'deduce-show-diagnostic-at-point)


(provide 'deduce-lsp)

;;; deduce-lsp.el ends here
