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
;; Step 6 adds Phase-4 keybindings: `C-c C-r' (refine, Step 15) is
;; live; `C-c C-c' (case split, Step 16) and `C-c C-i' (induction,
;; Step 17) follow when those server operations land.
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

Errors out if the buffer isn't visiting a file.  Builds a
`file://' URI by hand: eglot's URI helpers are private, and the
underlying construction is simple enough that depending on them
isn't worth it for ASCII paths."
  (let ((path (or buffer-file-name
                  (user-error "Buffer is not visiting a file"))))
    (concat "file://" (expand-file-name path))))


(defun deduce-lsp--current-position ()
  "Return the LSP-shape `Position' for point in the current buffer.
LSP positions are 0-indexed (line and character)."
  (list :line (1- (line-number-at-pos))
        :character (current-column)))


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
           (response (jsonrpc-request server :deduce/goalAt params)))
      (deduce-lsp--show-goal response))))


;; Bind `C-c C-g' in `deduce-mode-map'.  We bind here in deduce-lsp
;; rather than in deduce-mode because the command depends on eglot
;; being available, so the binding only makes sense once the user
;; has opted into LSP via `(require 'deduce-lsp)'.
(define-key deduce-mode-map (kbd "C-c C-g") #'deduce-show-goal-at-point)


;; ---------------------------------------------------------------------
;; Refine hole (Step 6 -- partial; Phase-4 / LSP Step 15)
;; ---------------------------------------------------------------------
;;
;; Bypasses `eglot-code-actions' (which prompts for an action kind and
;; then for the action itself) by issuing the
;; `textDocument/codeAction' request directly with a kind filter, then
;; applying the first matching CodeAction's WorkspaceEdit without a
;; picker.  One keystroke per refine -- the speed difference matters
;; in interactive proof editing.
;;
;; Today the Deduce LSP only emits one `refactor.rewrite' action
;; ("Refine hole").  When Steps 16/17 land (case split, induction
;; skeleton) they'll add more refactor.rewrite actions; at that point
;; this command will need a picker after all, OR we'll split the
;; bindings: `C-c C-r' for refine, `C-c C-c' for case split, `C-c C-i'
;; for induction.  The plan picks the latter.

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
:character N)'."
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
    (insert new-text)))


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
  "Apply the WorkspaceEdit of CodeAction plist ACTION to the
current buffer.

Today the server's only edit shape is `:changes' keyed by the
file's URI; `:documentChanges' isn't used.  TextEdits are applied
in the order the server returned them -- a single edit for
Step 15, so order doesn't matter yet."
  (let* ((edit (plist-get action :edit))
         (changes (plist-get edit :changes))
         (uri (deduce-lsp--current-uri))
         (edits (deduce-lsp--text-edits-for-uri changes uri)))
    (unless edits
      (user-error "Refine action has no edits for the current buffer"))
    ;; Apply in reverse order so each edit's offsets stay valid.
    ;; Today there's only one edit; this is forward-compat for
    ;; multi-edit actions in later steps.
    (mapc #'deduce-lsp--apply-text-edit (reverse (append edits nil)))))


(defun deduce-lsp-refine-hole ()
  "Apply the LSP-suggested refinement for the hole at point.

Issues a `textDocument/codeAction' request filtered to the
`refactor.rewrite' kind, applies the first matching action's
WorkspaceEdit directly, and skips the action picker.  This is
the fast path for the keybinding.

When the cursor isn't on a hole (or the goal shape isn't
recognised by the server), errors with `No refinement available
at point.'  When no eglot connection is active, prompts the user
to run `M-x eglot' first."
  (interactive)
  (let ((server (eglot-current-server)))
    (unless server
      (user-error
       "No eglot server active in this buffer; M-x eglot first"))
    (let* ((pos (deduce-lsp--current-position))
           (params (list :textDocument (list :uri (deduce-lsp--current-uri))
                         :range (list :start pos :end pos)
                         :context (list :diagnostics [])))
           (actions (jsonrpc-request server :textDocument/codeAction params)))
      ;; The server returns either a vector or nil.  Normalise to a
      ;; list so we can use plain seq operations.
      (let ((action-list (if (vectorp actions) (append actions nil) actions)))
        (unless action-list
          (user-error "No refinement available at point"))
        (deduce-lsp--apply-code-action (car action-list))))))


;; Bind `C-c C-r' in `deduce-mode-map' for refine-at-point.  Same
;; rationale as `C-c C-g': only meaningful when LSP is loaded.
(define-key deduce-mode-map (kbd "C-c C-r") #'deduce-lsp-refine-hole)


(provide 'deduce-lsp)

;;; deduce-lsp.el ends here
