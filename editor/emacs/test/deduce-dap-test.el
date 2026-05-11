;;; deduce-dap-test.el --- ert tests for deduce-dap -*- lexical-binding: t; -*-

;; SPDX-License-Identifier: MIT

;;; Commentary:

;; Run with:
;;
;;     emacs --batch -L editor/emacs -L editor/emacs/test \
;;           -l deduce-dap-test -f ert-run-tests-batch-and-exit
;;
;; The end-to-end loop (subprocess adapter, DAP traffic, dap-mode UI)
;; is impractical to drive from a batch process and depends on
;; dap-mode being installed.  These tests pin the pieces of
;; `deduce-dap.el' that live entirely in Emacs Lisp:
;;
;; - `deduce-dap-server-command' under the four (deduce-root,
;;   prelude-disabled) combinations
;; - the provider hook `deduce-dap--populate-launch' filling in
;;   missing keys without overwriting user-supplied ones
;; - the `C-c C-d' keybinding being installed on `deduce-mode-map'
;;
;; The actual DAP session interaction relies on the manual smoke
;; test documented in `editor/emacs/README.md'.

;;; Code:

(require 'ert)
(require 'deduce-mode)
(require 'deduce-dap)


(ert-deftest deduce-dap/server-command-default-form ()
  "With both knobs at their defaults, the command is just python3 +
the module spec.  No `env' wrapper."
  (let ((deduce-dap-deduce-root nil)
        (deduce-dap-prelude-disabled nil)
        (deduce-dap-python-program "python3"))
    (should (equal (deduce-dap-server-command)
                   '("python3" "-m" "lsp.dap_server")))))


(ert-deftest deduce-dap/server-command-respects-python-program ()
  "Customizing `deduce-dap-python-program' swaps the interpreter."
  (let ((deduce-dap-deduce-root nil)
        (deduce-dap-prelude-disabled nil)
        (deduce-dap-python-program "python3.13"))
    (should (equal (deduce-dap-server-command)
                   '("python3.13" "-m" "lsp.dap_server")))))


(ert-deftest deduce-dap/server-command-with-deduce-root-uses-env ()
  "Setting `deduce-dap-deduce-root' wraps the command in
`env PYTHONPATH=...' so the adapter resolves outside the repo."
  (let ((deduce-dap-deduce-root "/tmp/deduce-checkout")
        (deduce-dap-prelude-disabled nil)
        (deduce-dap-python-program "python3"))
    (should (equal (deduce-dap-server-command)
                   '("env" "PYTHONPATH=/tmp/deduce-checkout"
                     "python3" "-m" "lsp.dap_server")))))


(ert-deftest deduce-dap/server-command-prelude-disabled-alone ()
  "`deduce-dap-prelude-disabled' alone wraps in `env DEDUCE_NO_STDLIB=1'."
  (let ((deduce-dap-deduce-root nil)
        (deduce-dap-prelude-disabled t)
        (deduce-dap-python-program "python3"))
    (should (equal (deduce-dap-server-command)
                   '("env" "DEDUCE_NO_STDLIB=1"
                     "python3" "-m" "lsp.dap_server")))))


(ert-deftest deduce-dap/server-command-both-knobs ()
  "Both knobs combine into a single env wrapper preserving order:
PYTHONPATH first (the deduce-root knob is more fundamental),
DEDUCE_NO_STDLIB second."
  (let ((deduce-dap-deduce-root "/srv/deduce")
        (deduce-dap-prelude-disabled t)
        (deduce-dap-python-program "python3"))
    (should (equal (deduce-dap-server-command)
                   '("env" "PYTHONPATH=/srv/deduce" "DEDUCE_NO_STDLIB=1"
                     "python3" "-m" "lsp.dap_server")))))


(ert-deftest deduce-dap/server-command-expands-deduce-root ()
  "`~/...' in `deduce-dap-deduce-root' expands to an absolute path
in the env binding."
  (let ((deduce-dap-deduce-root "~/deduce")
        (deduce-dap-prelude-disabled nil)
        (deduce-dap-python-program "python3"))
    (let ((cmd (deduce-dap-server-command)))
      (should (equal (car cmd) "env"))
      (should (string-prefix-p "PYTHONPATH=/" (cadr cmd)))
      (should-not (string-match-p "~" (cadr cmd))))))


(ert-deftest deduce-dap/populate-launch-fills-defaults ()
  "The provider hook fills in `:dap-server-path', `:type', `:cwd',
`:program', and `:name' when the user-supplied conf omits them."
  (let* ((deduce-dap-deduce-root nil)
         (deduce-dap-prelude-disabled nil)
         (deduce-dap-python-program "python3")
         (default-directory "/tmp/proj/")
         (conf (deduce-dap--populate-launch
                (list :request "launch")))
         (path (plist-get conf :dap-server-path)))
    (should (equal path '("python3" "-m" "lsp.dap_server")))
    (should (equal (plist-get conf :type) "deduce"))
    (should (equal (plist-get conf :cwd) "/tmp/proj/"))
    (should (equal (plist-get conf :name)
                   "Deduce :: launch current file"))))


(ert-deftest deduce-dap/populate-launch-preserves-user-values ()
  "User-supplied keys (`:program', `:cwd', `:name') should not be
overwritten by the provider hook."
  (let* ((deduce-dap-deduce-root nil)
         (deduce-dap-prelude-disabled nil)
         (deduce-dap-python-program "python3")
         (conf (deduce-dap--populate-launch
                (list :request "launch"
                      :program "/explicit/program.pf"
                      :cwd "/explicit/dir"
                      :name "Custom"))))
    (should (equal (plist-get conf :program) "/explicit/program.pf"))
    (should (equal (plist-get conf :cwd) "/explicit/dir"))
    (should (equal (plist-get conf :name) "Custom"))))


(ert-deftest deduce-dap/keybinding-installed ()
  "Loading `deduce-dap' installs `C-c C-d' on `deduce-mode-map'."
  (should (eq (lookup-key deduce-mode-map (kbd "C-c C-d"))
              #'deduce-dap-debug-current-buffer)))


(ert-deftest deduce-dap/fkey-bindings-installed ()
  "F-key bindings (gdb / VS Code convention) cover the four step
commands plus disconnect, all on `deduce-mode-map'."
  (should (eq (lookup-key deduce-mode-map (kbd "<f5>"))
              #'dap-continue))
  (should (eq (lookup-key deduce-mode-map (kbd "<f10>"))
              #'dap-next))
  (should (eq (lookup-key deduce-mode-map (kbd "<f11>"))
              #'dap-step-in))
  (should (eq (lookup-key deduce-mode-map (kbd "S-<f11>"))
              #'dap-step-out))
  (should (eq (lookup-key deduce-mode-map (kbd "S-<f5>"))
              #'dap-disconnect)))


(ert-deftest deduce-dap/cc-d-prefix-bindings-installed ()
  "Non-F-key fallback bindings on `C-c d <letter>'.  Useful when
macOS / a WM intercepts the function row."
  (should (eq (lookup-key deduce-mode-map (kbd "C-c d d"))
              #'deduce-dap-debug-current-buffer))
  (should (eq (lookup-key deduce-mode-map (kbd "C-c d c"))
              #'dap-continue))
  (should (eq (lookup-key deduce-mode-map (kbd "C-c d n"))
              #'dap-next))
  (should (eq (lookup-key deduce-mode-map (kbd "C-c d s"))
              #'dap-step-in))
  (should (eq (lookup-key deduce-mode-map (kbd "C-c d o"))
              #'dap-step-out))
  (should (eq (lookup-key deduce-mode-map (kbd "C-c d q"))
              #'dap-disconnect))
  (should (eq (lookup-key deduce-mode-map (kbd "C-c d h"))
              #'dap-hydra)))


(provide 'deduce-dap-test)
;;; deduce-dap-test.el ends here
