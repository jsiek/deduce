;;; deduce-lsp-test.el --- ert tests for deduce-lsp -*- lexical-binding: t; -*-

;; SPDX-License-Identifier: MIT

;;; Commentary:

;; Run with:
;;
;;     emacs --batch -L editor/emacs -L editor/emacs/test \
;;           -l deduce-lsp-test -f ert-run-tests-batch-and-exit
;;
;; The end-to-end loop (subprocess server, JSON-RPC, real LSP traffic)
;; is impractical to drive from a batch process.  These tests pin the
;; pieces of `deduce-lsp.el' that live entirely in Emacs Lisp:
;; eglot-server-programs registration, server-command shape under
;; both `deduce-lsp-deduce-root' branches, and the auto-start hook.

;;; Code:

(require 'ert)
(require 'eglot)
(require 'deduce-mode)
(require 'deduce-lsp)


(ert-deftest deduce-lsp/registered-with-eglot ()
  "Loading `deduce-lsp' should add a `(deduce-mode . ...)' entry to
`eglot-server-programs'."
  (should (assq 'deduce-mode eglot-server-programs)))


(ert-deftest deduce-lsp/server-command-default-form ()
  "With `deduce-lsp-deduce-root' nil, the command is just python3 +
the module spec."
  (let ((deduce-lsp-deduce-root nil)
        (deduce-lsp-python-program "python3"))
    (should (equal (deduce-lsp-server-command)
                   '("python3" "-m" "lsp.lsp_server")))))


(ert-deftest deduce-lsp/server-command-default-form-respects-python-program ()
  "Customizing `deduce-lsp-python-program' swaps the interpreter."
  (let ((deduce-lsp-deduce-root nil)
        (deduce-lsp-python-program "python3.13"))
    (should (equal (deduce-lsp-server-command)
                   '("python3.13" "-m" "lsp.lsp_server")))))


(ert-deftest deduce-lsp/server-command-with-deduce-root-uses-env ()
  "Setting `deduce-lsp-deduce-root' wraps the command in `env' so
PYTHONPATH carries the checkout location."
  (let ((deduce-lsp-deduce-root "/tmp/deduce-checkout")
        (deduce-lsp-python-program "python3"))
    (let ((cmd (deduce-lsp-server-command)))
      (should (equal (car cmd) "env"))
      (should (equal (cadr cmd) "PYTHONPATH=/tmp/deduce-checkout"))
      (should (equal (nthcdr 2 cmd)
                     '("python3" "-m" "lsp.lsp_server"))))))


(ert-deftest deduce-lsp/server-command-expands-deduce-root ()
  "`~/...' in `deduce-lsp-deduce-root' expands to absolute path."
  (let ((deduce-lsp-deduce-root "~/deduce")
        (deduce-lsp-python-program "python3"))
    (let ((cmd (deduce-lsp-server-command)))
      (should (string-prefix-p "PYTHONPATH=/" (cadr cmd)))
      (should-not (string-match-p "~" (cadr cmd))))))


(ert-deftest deduce-lsp/auto-start-hook-installed ()
  "`deduce-lsp--maybe-ensure' is on `deduce-mode-hook' after load."
  (should (memq #'deduce-lsp--maybe-ensure deduce-mode-hook)))


(ert-deftest deduce-lsp/maybe-ensure-respects-auto-start-flag ()
  "When `deduce-lsp-auto-start' is nil, the hook is a no-op."
  (let ((deduce-lsp-auto-start nil)
        (eglot-called nil))
    (cl-letf (((symbol-function 'eglot-ensure)
               (lambda () (setq eglot-called t))))
      (deduce-lsp--maybe-ensure)
      (should-not eglot-called))))


(ert-deftest deduce-lsp/maybe-ensure-calls-eglot-when-enabled ()
  "When `deduce-lsp-auto-start' is non-nil, the hook calls
`eglot-ensure'."
  (let ((deduce-lsp-auto-start t)
        (eglot-called nil))
    (cl-letf (((symbol-function 'eglot-ensure)
               (lambda () (setq eglot-called t))))
      (deduce-lsp--maybe-ensure)
      (should eglot-called))))


(provide 'deduce-lsp-test)

;;; deduce-lsp-test.el ends here
