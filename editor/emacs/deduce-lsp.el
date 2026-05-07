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
;; Step 6 adds Phase-4 keybindings (`C-c C-r', `C-c C-c', `C-c C-i')
;; for the LSP-side structured-editing operations once they land.
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


(defun deduce-lsp-server-command (&optional _interactive)
  "Return the command list eglot uses to launch the Deduce LSP server.

When `deduce-lsp-deduce-root' is set, prepend it to PYTHONPATH
via `env'.  Otherwise return the bare `python3 -m lsp.lsp_server'
form and trust eglot's cwd to be the deduce repo root.

The optional argument is unused; it's accepted because eglot
calls server-program functions with one argument (an
`interactive' flag) since Emacs 29."
  (let ((py deduce-lsp-python-program)
        (mod-args '("-m" "lsp.lsp_server")))
    (if deduce-lsp-deduce-root
        (let ((root (expand-file-name deduce-lsp-deduce-root)))
          (append (list "env" (format "PYTHONPATH=%s" root) py) mod-args))
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


(provide 'deduce-lsp)

;;; deduce-lsp.el ends here
