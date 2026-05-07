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


(ert-deftest deduce-lsp/server-command-prelude-disabled-alone ()
  "`deduce-lsp-prelude-disabled' alone wraps in `env DEDUCE_NO_STDLIB=1'."
  (let ((deduce-lsp-deduce-root nil)
        (deduce-lsp-prelude-disabled t)
        (deduce-lsp-python-program "python3"))
    (should (equal (deduce-lsp-server-command)
                   '("env" "DEDUCE_NO_STDLIB=1"
                     "python3" "-m" "lsp.lsp_server")))))


(ert-deftest deduce-lsp/server-command-prelude-disabled-with-root ()
  "Both knobs combine: `env PYTHONPATH=... DEDUCE_NO_STDLIB=1 python3 ...'."
  (let ((deduce-lsp-deduce-root "/tmp/deduce-checkout")
        (deduce-lsp-prelude-disabled t)
        (deduce-lsp-python-program "python3"))
    (let ((cmd (deduce-lsp-server-command)))
      (should (equal (car cmd) "env"))
      ;; Both bindings present (order is implementation-defined; assert
      ;; membership rather than position).
      (should (member "PYTHONPATH=/tmp/deduce-checkout" cmd))
      (should (member "DEDUCE_NO_STDLIB=1" cmd))
      ;; Interpreter + module spec come last, in order.
      (should (equal (last cmd 3) '("python3" "-m" "lsp.lsp_server"))))))


(ert-deftest deduce-lsp/server-command-prelude-disabled-nil-stays-bare ()
  "With both knobs nil, no `env' wrapper is introduced."
  (let ((deduce-lsp-deduce-root nil)
        (deduce-lsp-prelude-disabled nil)
        (deduce-lsp-python-program "python3"))
    (let ((cmd (deduce-lsp-server-command)))
      (should-not (equal (car cmd) "env"))
      (should (equal cmd '("python3" "-m" "lsp.lsp_server"))))))


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


;; ---------------------------------------------------------------------
;; Step 5: deduce-show-goal-at-point
;; ---------------------------------------------------------------------

(defun deduce-lsp-test--with-mock-server (response thunk)
  "Run THUNK with `jsonrpc-request' and `eglot-current-server'
mocked: any request returns RESPONSE, and `eglot-current-server'
returns the symbol `mock-server'.  Returns the captured request
arguments."
  (let ((captured nil))
    (cl-letf (((symbol-function 'eglot-current-server)
               (lambda () 'mock-server))
              ((symbol-function 'jsonrpc-request)
               (lambda (server method params)
                 (setq captured (list :server server :method method :params params))
                 response)))
      (funcall thunk))
    captured))


(ert-deftest deduce-lsp/show-goal-at-point-issues-goalAt-request ()
  "The command sends a `deduce/goalAt' request with a properly
shaped textDocument+position payload."
  (let* ((tmp (make-temp-file "deduce-lsp-test" nil ".pf"))
         captured)
    (unwind-protect
        (with-temp-buffer
          (insert "theorem t: true\nproof\n  ?\nend\n")
          (setq buffer-file-name tmp)
          (deduce-mode)
          ;; Cursor at line 3, column 2 (0-indexed for LSP: line 2, char 2)
          (goto-char (point-min))
          (forward-line 2)
          (forward-char 2)
          (setq captured
                (deduce-lsp-test--with-mock-server
                 nil
                 (lambda () (deduce-show-goal-at-point))))
          (should (eq (plist-get captured :method) :deduce/goalAt))
          (let* ((params (plist-get captured :params))
                 (uri (plist-get (plist-get params :textDocument) :uri))
                 (pos (plist-get params :position)))
            (should (string-prefix-p "file://" uri))
            (should (= (plist-get pos :line) 2))
            (should (= (plist-get pos :character) 2))))
      (delete-file tmp))))


(ert-deftest deduce-lsp/show-goal-at-point-renders-formula-and-givens ()
  (let* ((tmp (make-temp-file "deduce-lsp-test" nil ".pf"))
         (response '(:formula "P = P"
                     :givens [(:label "h" :formula "P")
                              (:label nil :formula "Q")]
                     :range (:start (:line 3 :character 2)
                             :end (:line 3 :character 2)))))
    (unwind-protect
        (progn
          (with-temp-buffer
            (insert "theorem t: true\n")
            (setq buffer-file-name tmp)
            (deduce-mode)
            (deduce-lsp-test--with-mock-server
             response
             (lambda () (deduce-show-goal-at-point))))
          (let ((text (with-current-buffer deduce-lsp-goal-buffer-name
                        (buffer-substring-no-properties (point-min) (point-max)))))
            (should (string-match-p "Goal:" text))
            (should (string-match-p "P = P" text))
            (should (string-match-p "Givens:" text))
            (should (string-match-p "h: P" text))
            ;; Anonymous given gets rendered as `_'
            (should (string-match-p "_: Q" text))))
      (delete-file tmp)
      (when (get-buffer deduce-lsp-goal-buffer-name)
        (kill-buffer deduce-lsp-goal-buffer-name)))))


(ert-deftest deduce-lsp/show-goal-at-point-renders-no-goal-message ()
  "A nil response (no goal at cursor) shows a helpful message."
  (let ((tmp (make-temp-file "deduce-lsp-test" nil ".pf")))
    (unwind-protect
        (progn
          (with-temp-buffer
            (insert "x")
            (setq buffer-file-name tmp)
            (deduce-mode)
            (deduce-lsp-test--with-mock-server
             nil
             (lambda () (deduce-show-goal-at-point))))
          (let ((text (with-current-buffer deduce-lsp-goal-buffer-name
                        (buffer-substring-no-properties (point-min) (point-max)))))
            (should (string-match-p "No goal at this position" text))))
      (delete-file tmp)
      (when (get-buffer deduce-lsp-goal-buffer-name)
        (kill-buffer deduce-lsp-goal-buffer-name)))))


(ert-deftest deduce-lsp/show-goal-at-point-without-server-errors ()
  "Without an active eglot server, the command signals a user
error rather than silently failing."
  (let ((tmp (make-temp-file "deduce-lsp-test" nil ".pf")))
    (unwind-protect
        (cl-letf (((symbol-function 'eglot-current-server)
                   (lambda () nil)))
          (with-temp-buffer
            (insert "x")
            (setq buffer-file-name tmp)
            (deduce-mode)
            (should-error (deduce-show-goal-at-point) :type 'user-error)))
      (delete-file tmp))))


(ert-deftest deduce-lsp/c-c-c-g-bound-to-show-goal-at-point ()
  "`C-c C-g' in deduce-mode-map runs `deduce-show-goal-at-point'."
  (should (eq (lookup-key deduce-mode-map (kbd "C-c C-g"))
              #'deduce-show-goal-at-point)))


(provide 'deduce-lsp-test)

;;; deduce-lsp-test.el ends here
