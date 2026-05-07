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

;; Declare eglot's variables so the byte-compiler doesn't warn when
;; we reference them inside `with-eval-after-load'.  We don't
;; `require' eglot at top level because it isn't strictly needed
;; until the user opens a `.pf' file -- eglot is built into Emacs
;; 29+ so loading it lazily keeps `(require 'deduce-lsp)' fast.
(defvar eglot-server-programs)
(declare-function eglot-ensure "eglot")


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


(provide 'deduce-lsp)

;;; deduce-lsp.el ends here
