;;; deduce-dap.el --- dap-mode integration for deduce-mode -*- lexical-binding: t; -*-

;; Copyright (C) 2026 Jeremy G. Siek and Deduce contributors
;; SPDX-License-Identifier: MIT

;; Author: Deduce contributors
;; Maintainer: Jeremy G. Siek
;; Version: 0.1.0
;; Package-Requires: ((emacs "29.1") (deduce-mode "0.1.0") (dap-mode "0.7"))
;; Keywords: languages
;; URL: https://github.com/jsiek/deduce

;;; Commentary:

;; deduce-dap.el wires `deduce-mode' buffers to the Deduce DAP
;; adapter in lsp/dap_server.py via dap-mode.  Phase 5 / Step 26
;; of the LSP plan (see docs/lsp-plan.md).
;;
;; Installation
;; ------------
;;
;;     (add-to-list 'load-path "/path/to/deduce/editor/emacs")
;;     (require 'deduce-mode)
;;     (require 'deduce-dap)
;;
;; And install the `dap-mode' package from MELPA if you don't already
;; have it.  The integration registers a debug template; launch
;; sessions either via `M-x dap-debug' (pick "Deduce :: launch
;; current file") or with the convenience binding `C-c C-d' from
;; any `.pf' buffer.
;;
;; The session uses the same command-line debugger surfaced by
;; `python deduce.py --debug' -- see `gh_pages/doc/Debugger.md' for
;; the command reference.  The DAP adapter merely translates between
;; dap-mode's UI (gutter breakpoints, the call-stack pane, the
;; locals view, etc.) and the underlying debugger.
;;
;; Adapter command
;; ---------------
;;
;; The default command is `python3 -m lsp.dap_server', invoked from
;; the project root determined by `project-current'.  When you edit
;; `.pf' files inside the deduce repo this works out of the box --
;; `lsp/dap_server.py' is on Python's import path.
;;
;; If your proofs live OUTSIDE the deduce repo, customize
;; `deduce-dap-deduce-root' to point at your deduce checkout; the
;; adapter is then invoked through `env PYTHONPATH=...' so the
;; module resolves regardless of cwd.  Mirrors `deduce-lsp's same
;; knob.
;;
;; Set `deduce-dap-prelude-disabled' to a non-nil value to launch
;; sessions without the standard library prelude (the DAP-protocol
;; equivalent of `deduce.py --no-stdlib').

;;; Code:

(require 'deduce-mode)

;; dap-mode is an external package (MELPA).  Declare what we use so
;; the byte-compiler doesn't warn when it's not installed.
(defvar dap-debug-template-configurations)
(declare-function dap-debug "dap-mode")
(declare-function dap-register-debug-provider "dap-mode")
(declare-function dap-register-debug-template "dap-mode")
(declare-function dap-hydra "dap-hydra")


(defgroup deduce-dap nil
  "dap-mode integration for `deduce-mode'."
  :group 'deduce
  :prefix "deduce-dap-")


(defcustom deduce-dap-python-program "python3"
  "Python interpreter used to launch the Deduce DAP adapter.

Set this to an absolute path (e.g. ``\"/usr/local/bin/python3.13\"``)
if your default ``python3'' doesn't have ``lark'' installed.  The
adapter dies with ``ModuleNotFoundError: No module named 'lark'''
if pointed at the wrong interpreter -- a common pitfall on systems
with multiple Python installs."
  :type 'string
  :group 'deduce-dap)


(defcustom deduce-dap-deduce-root nil
  "Path to a Deduce repository checkout, or nil to rely on cwd.

When nil, dap-mode launches the adapter from the project root
determined by `project-current' -- this works when editing `.pf'
files inside the deduce repo, where `lsp/dap_server.py' is on
Python's import path.

When set to a directory path, the adapter command runs through
`env' with PYTHONPATH including that directory.  Useful when your
proofs live outside the deduce repo."
  :type '(choice (const :tag "Auto (project root)" nil)
                 (directory :tag "Deduce checkout"))
  :group 'deduce-dap)


(defcustom deduce-dap-prelude-disabled nil
  "If non-nil, launch DAP sessions without the standard library prelude.

Sets `DEDUCE_NO_STDLIB=1' in the spawned process environment,
mirroring `deduce.py --no-stdlib' and `deduce-lsp's option of the
same name.  Useful when working on `lib/' itself or on minimal
test fixtures."
  :type 'boolean
  :group 'deduce-dap)


(defun deduce-dap-server-command ()
  "Return the command list dap-mode uses to launch the Deduce DAP adapter.

Same shape as `deduce-lsp-server-command': bare `python3 -m
lsp.dap_server' when no knobs are active, wrapped in
`env KEY=VAL ...' when `deduce-dap-deduce-root' and/or
`deduce-dap-prelude-disabled' have non-default values."
  (let ((py deduce-dap-python-program)
        (mod-args '("-m" "lsp.dap_server"))
        (env-bindings nil))
    (when deduce-dap-deduce-root
      (push (format "PYTHONPATH=%s"
                    (expand-file-name deduce-dap-deduce-root))
            env-bindings))
    (when deduce-dap-prelude-disabled
      (push "DEDUCE_NO_STDLIB=1" env-bindings))
    (if env-bindings
        (append (cons "env" (nreverse env-bindings))
                (cons py mod-args))
      (cons py mod-args))))


(defun deduce-dap--project-root ()
  "Best guess at the Deduce checkout root for the current buffer.

`python3 -m lsp.dap_server' needs to be launched from a directory
that has `lsp/' on its import path -- the Deduce repo root.
`default-directory' is usually wrong (it's the buffer's own
directory, often a `tmp/' or proofs subdirectory).  Prefer the
`project-current' root when emacs can find one; fall back to
`default-directory'.  Users can override via `deduce-dap-deduce-root',
which is consulted by `deduce-dap-server-command' for `PYTHONPATH'."
  (or (when-let* ((proj (project-current nil)))
        (expand-file-name (project-root proj)))
      default-directory))


(defun deduce-dap--populate-launch (conf)
  "Provider hook: fill in defaults on the dap-mode launch CONF
plist before the session is spawned.

dap-mode looks up the registered provider for `:type \"deduce\"',
calls this function with the user's partial config, and uses the
returned plist verbatim.  We set `:dap-server-path' to the adapter
command, default `:program' to the current buffer's file, and
default `:cwd' to the project root so `python3 -m lsp.dap_server'
resolves (the buffer's `default-directory' is usually a `tmp/'
subdirectory and won't have `lsp/' on the path)."
  (let ((cmd (deduce-dap-server-command)))
    (setq conf (plist-put conf :dap-server-path cmd))
    (setq conf (plist-put conf :type "deduce"))
    (unless (plist-get conf :cwd)
      (setq conf (plist-put conf :cwd (deduce-dap--project-root))))
    (unless (plist-get conf :program)
      (setq conf (plist-put conf :program (buffer-file-name))))
    (unless (plist-get conf :name)
      (setq conf (plist-put conf :name "Deduce :: launch current file")))
    conf))


(defun deduce-dap-debug-current-buffer ()
  "Launch a DAP debug session on the current `.pf' file.

Convenience wrapper around `dap-debug' that doesn't make the user
visit the debug-templates picker.  Requires `dap-mode' to be
installed; errors out informatively otherwise."
  (interactive)
  (unless (buffer-file-name)
    (user-error "Buffer is not visiting a file"))
  (unless (require 'dap-mode nil 'noerror)
    (user-error
     "deduce-dap: dap-mode is not installed; install it from MELPA"))
  (dap-debug (list :type "deduce"
                   :request "launch"
                   :name "Deduce :: launch current file"
                   :program (buffer-file-name))))


;; Register with dap-mode.  `with-eval-after-load' so the
;; registration happens whenever dap-mode is loaded (before or
;; after deduce-dap).
;;;###autoload
(with-eval-after-load 'dap-mode
  (dap-register-debug-provider "deduce" #'deduce-dap--populate-launch)
  (dap-register-debug-template
   "Deduce :: launch current file"
   (list :type "deduce"
         :request "launch"
         :name "Deduce :: launch current file"
         :program nil)))


;; Convenience keybindings.  Two equivalent surfaces:
;;
;; - The F-keys mirror VS Code / gdb conventions so debug-toolbar
;;   muscle memory transfers.  Caveat: F5 / F10 / F11 are
;;   intercepted by macOS (volume / mute / Mission Control's "Show
;;   Desktop") and by some Linux WMs; see README.md for the
;;   workarounds.
;; - The ``C-c d <letter>'' prefix is a non-F-key fallback that no
;;   OS or window manager fights us for: ``C-c d c'' continue,
;;   ``C-c d n'' next, ``C-c d s'' step-in, ``C-c d o'' step-out,
;;   ``C-c d q'' disconnect.  ``C-c d d'' is the same as
;;   ``C-c C-d'' (launch).
;;
;; Bindings reference dap-mode commands so they're no-ops outside
;; an active session and error informatively if dap-mode itself
;; isn't installed.
;;;###autoload
(with-eval-after-load 'deduce-mode
  (define-key deduce-mode-map (kbd "C-c C-d")
              #'deduce-dap-debug-current-buffer)
  ;; F-key surface.
  (define-key deduce-mode-map (kbd "<f5>")    #'dap-continue)
  (define-key deduce-mode-map (kbd "<f10>")   #'dap-next)
  (define-key deduce-mode-map (kbd "<f11>")   #'dap-step-in)
  (define-key deduce-mode-map (kbd "S-<f11>") #'dap-step-out)
  (define-key deduce-mode-map (kbd "S-<f5>")  #'dap-disconnect)
  ;; ``C-c d <letter>'' fallback.
  (define-key deduce-mode-map (kbd "C-c d d") #'deduce-dap-debug-current-buffer)
  (define-key deduce-mode-map (kbd "C-c d c") #'dap-continue)
  (define-key deduce-mode-map (kbd "C-c d n") #'dap-next)
  (define-key deduce-mode-map (kbd "C-c d s") #'dap-step-in)
  (define-key deduce-mode-map (kbd "C-c d o") #'dap-step-out)
  (define-key deduce-mode-map (kbd "C-c d q") #'dap-disconnect)
  ;; ``C-c d h'' opens dap-mode's transient single-key menu --
  ;; an OS-independent way to step (``n''/``s''/``o''), continue
  ;; (``c''), eval (``e''), quit (``q''), etc. without
  ;; multi-keystroke chords.  See the README's *Useful dap-mode
  ;; commands* section.
  (define-key deduce-mode-map (kbd "C-c d h") #'dap-hydra))


(provide 'deduce-dap)
;;; deduce-dap.el ends here
