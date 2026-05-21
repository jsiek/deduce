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
arguments.

Also no-ops `eglot--signal-textDocument/didChange', which our
`deduce-lsp--request' wrapper calls before each request to flush
pending buffer changes (issue #339).  In the test harness there's
no real eglot server to track against, so we just stub the call."
  (let ((captured nil))
    (cl-letf (((symbol-function 'eglot-current-server)
               (lambda () 'mock-server))
              ((symbol-function 'eglot--signal-textDocument/didChange)
               (lambda () nil))
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


;; ---------------------------------------------------------------------
;; Step 6 (partial): deduce-lsp-refine-hole
;; ---------------------------------------------------------------------
;;
;; The Phase-4 / Step 15 hole-refine code action, fronted by `C-c C-r'.
;; The command sends `textDocument/codeAction' filtered to
;; `refactor.rewrite' and applies the first matching action's
;; WorkspaceEdit directly -- skipping the picker that
;; `eglot-code-actions' shows.

(ert-deftest deduce-lsp/refine-hole-bound-to-c-c-c-r ()
  "`C-c C-r' in deduce-mode-map runs `deduce-lsp-refine-hole'."
  (should (eq (lookup-key deduce-mode-map (kbd "C-c C-r"))
              #'deduce-lsp-refine-hole)))


(ert-deftest deduce-lsp/refine-hole-issues-codeAction-request ()
  "The command sends `textDocument/codeAction' with a single-point
range at the cursor."
  (let ((tmp (make-temp-file "deduce-lsp-refine" nil ".pf"))
        captured)
    (unwind-protect
        (with-temp-buffer
          (insert "theorem t: all P:bool. P = P\nproof\n  arbitrary P:bool\n  ?\nend\n")
          (setq buffer-file-name tmp)
          (deduce-mode)
          ;; Cursor at line 4, col 3 (the `?').  LSP-space: line 3, char 2.
          (goto-char (point-min))
          (forward-line 3)
          (forward-char 2)
          (setq captured
                (deduce-lsp-test--with-mock-server
                 ;; Empty vector -> no actions; the command will
                 ;; user-error.  We only care about the captured
                 ;; request shape here.
                 []
                 (lambda ()
                   (ignore-errors (deduce-lsp-refine-hole)))))
          (should (eq (plist-get captured :method) :textDocument/codeAction))
          (let* ((params (plist-get captured :params))
                 (uri (plist-get (plist-get params :textDocument) :uri))
                 (range (plist-get params :range))
                 (start (plist-get range :start))
                 (end (plist-get range :end)))
            (should (string-prefix-p "file://" uri))
            ;; Range degenerates to a single point at the cursor.
            (should (= (plist-get start :line) 3))
            (should (= (plist-get start :character) 2))
            (should (equal start end))))
      (delete-file tmp))))


(ert-deftest deduce-lsp/refine-hole-applies-text-edit ()
  "Given a CodeAction with a TextEdit replacing the `?', the
buffer ends up with the new text in its place."
  (let ((tmp (make-temp-file "deduce-lsp-refine" nil ".pf")))
    (unwind-protect
        (with-temp-buffer
          (insert "theorem t: all P:bool. P = P\nproof\n  arbitrary P:bool\n  ?\nend\n")
          (setq buffer-file-name tmp)
          (deduce-mode)
          ;; Cursor on the `?'.
          (goto-char (point-min))
          (forward-line 3)
          (forward-char 2)
          (let* ((uri (deduce-lsp--current-uri))
                 ;; CodeAction response: one action, one text-edit
                 ;; replacing the `?' (line 3, char 2..3) with
                 ;; `reflexive'.
                 (action `(:title "Refine hole"
                           :kind "refactor.rewrite"
                           :edit
                           (:changes
                            (,(intern (concat ":" uri))
                             [(:range (:start (:line 3 :character 2)
                                       :end (:line 3 :character 3))
                                      :newText "reflexive")]))))
                 (response (vector action)))
            (deduce-lsp-test--with-mock-server
             response
             (lambda () (deduce-lsp-refine-hole))))
          (let ((text (buffer-substring-no-properties (point-min) (point-max))))
            (should (string-match-p "reflexive" text))
            ;; `?' is gone.
            (should-not (string-match-p "?\nend" text))))
      (delete-file tmp))))


(ert-deftest deduce-lsp/apply-text-edit-leaves-point-on-first-question-mark ()
  "After applying a multi-line template that contains a `?', point
lands on the FIRST `?' in the inserted text -- not at the end of
the insertion -- so successive C-c C-r / C-c C-c can fire without
the user repositioning the cursor."
  (with-temp-buffer
    (insert "  ?\n")
    ;; Cursor on the `?` at line 1, col 3 (LSP line 0, char 2).
    (let* ((uri "file:///tmp/x.pf")
           (target-key (intern (concat ":" uri)))
           (skeleton "switch x {\n    case z { ? }\n    case s(n1) { ? }\n  }")
           (edit `(:range (:start (:line 0 :character 2)
                           :end (:line 0 :character 3))
                          :newText ,skeleton)))
      (cl-letf (((symbol-function 'deduce-lsp--current-uri)
                 (lambda () uri)))
        (deduce-lsp--apply-text-edit edit))
      ;; Buffer is now:
      ;;   "  switch x {\n    case z { ? }\n    case s(n1) { ? }\n  }\n"
      ;; The first `?' lives in `case z { ? }' on line 2.  Point
      ;; should be sitting ON it.
      (should (eq (char-after) ?\?))
      ;; And the char after point is `?', not `?,' or anything else.
      (should (looking-at-p "\\? }")))))


(ert-deftest deduce-lsp/apply-text-edit-no-question-mark-lands-at-end ()
  "If the template contains no `?' (e.g. `reflexive', `.'), point
lands at the end of the insertion -- there's no inner hole to
prefer."
  (with-temp-buffer
    (insert "  ?\n")
    (let* ((uri "file:///tmp/x.pf")
           (edit `(:range (:start (:line 0 :character 2)
                           :end (:line 0 :character 3))
                          :newText "reflexive")))
      (cl-letf (((symbol-function 'deduce-lsp--current-uri)
                 (lambda () uri)))
        (deduce-lsp--apply-text-edit edit))
      ;; Buffer is "  reflexive\n".  Point is at end of "reflexive"
      ;; (12, just before the newline) -- char-after is the newline.
      (should (eq (char-after) ?\n))
      ;; Char before point is the last `e' of "reflexive".
      (should (eq (char-before) ?e)))))


(ert-deftest deduce-lsp/refine-hole-no-actions-signals-user-error ()
  "An empty action list yields a `No refinement available' user-error."
  (let ((tmp (make-temp-file "deduce-lsp-refine" nil ".pf")))
    (unwind-protect
        (with-temp-buffer
          (insert "x")
          (setq buffer-file-name tmp)
          (deduce-mode)
          (deduce-lsp-test--with-mock-server
           nil
           (lambda ()
             (should-error (deduce-lsp-refine-hole) :type 'user-error))))
      (delete-file tmp))))


(ert-deftest deduce-lsp/refine-hole-without-server-errors ()
  "Without an active eglot server, the command signals a user error."
  (let ((tmp (make-temp-file "deduce-lsp-refine" nil ".pf")))
    (unwind-protect
        (cl-letf (((symbol-function 'eglot-current-server)
                   (lambda () nil)))
          (with-temp-buffer
            (insert "x")
            (setq buffer-file-name tmp)
            (deduce-mode)
            (should-error (deduce-lsp-refine-hole) :type 'user-error)))
      (delete-file tmp))))


(ert-deftest deduce-lsp/lsp-pos-to-point-converts-zero-indexed-coords ()
  "LSP (line, character) maps to the right buffer point."
  (with-temp-buffer
    (insert "abc\ndef\nghi\n")
    ;; Line 0, char 0 -> point 1 (start of `a').
    (should (= (deduce-lsp--lsp-pos-to-point 0 0) 1))
    ;; Line 1, char 0 -> point 5 (start of `d').
    (should (= (deduce-lsp--lsp-pos-to-point 1 0) 5))
    ;; Line 2, char 2 -> point 11 (the `i' on line 3, 1-indexed).
    (should (= (deduce-lsp--lsp-pos-to-point 2 2) 11))))


(ert-deftest deduce-lsp/text-edits-for-uri-finds-keyword-keyed-changes ()
  "The `:changes' plist uses URIs as keywords; the helper finds them."
  (let* ((uri "file:///tmp/foo.pf")
         (target-key (intern (concat ":" uri)))
         (changes (list target-key (vector "edit-A")
                        :other-uri (vector "edit-B"))))
    (should (equal (deduce-lsp--text-edits-for-uri changes uri)
                   (vector "edit-A")))
    ;; URI not present -> nil.
    (should-not
     (deduce-lsp--text-edits-for-uri changes "file:///nope.pf"))))


;; ---------------------------------------------------------------------
;; Step 6 (partial): deduce-lsp-case-split
;; ---------------------------------------------------------------------
;;
;; Phase-4 / LSP Step 16, fronted by `C-c C-c'.  UX: cursor on a `?',
;; press `C-c C-c', completing-read prompts for the variable to split
;; on.  The interactive form fetches candidates via
;; `deduce/splittableVarsAt'; the chosen variable then drives a
;; `deduce/caseSplitAt' request.

(ert-deftest deduce-lsp/case-split-bound-to-c-c-c-c ()
  "`C-c C-c' in deduce-mode-map runs `deduce-lsp-case-split'."
  (should (eq (lookup-key deduce-mode-map (kbd "C-c C-c"))
              #'deduce-lsp-case-split)))


(defun deduce-lsp-test--with-method-mock (responses-by-method thunk)
  "Run THUNK with `jsonrpc-request' returning per-method responses.
RESPONSES-BY-METHOD is an alist of (METHOD . RESPONSE) where
METHOD is a keyword like :deduce/caseSplitAt.  Returns the list
of every captured (method . params) pair, in call order.

Also no-ops `eglot--signal-textDocument/didChange' (called by
`deduce-lsp--request' before every request) so the mock harness
doesn't try to flush against a non-existent server."
  (let ((calls nil))
    (cl-letf (((symbol-function 'eglot-current-server)
               (lambda () 'mock-server))
              ((symbol-function 'eglot--signal-textDocument/didChange)
               (lambda () nil))
              ((symbol-function 'jsonrpc-request)
               (lambda (_server method params)
                 (push (cons method params) calls)
                 (cdr (assq method responses-by-method)))))
      (funcall thunk))
    (reverse calls)))


(ert-deftest deduce-lsp/case-split-issues-caseSplitAt-request ()
  "Calling `deduce-lsp-case-split' with a variable arg sends
`deduce/caseSplitAt' with `{textDocument, position, variable}'."
  (let ((tmp (make-temp-file "deduce-lsp-split" nil ".pf"))
        calls)
    (unwind-protect
        (with-temp-buffer
          (insert "union N {\n  z\n  s(N)\n}\n\ntheorem t: all x:N. x = x\nproof\n  arbitrary x:N\n  ?\nend\n")
          (setq buffer-file-name tmp)
          (deduce-mode)
          ;; Cursor on the `?' (line 9, col 3) -> LSP line 8, char 2.
          (goto-char (point-min))
          (forward-line 8)
          (forward-char 2)
          (setq calls
                (deduce-lsp-test--with-method-mock
                 ;; Server returns nil for caseSplitAt -> the
                 ;; command will user-error; we only care about
                 ;; the captured request shape.
                 '((:deduce/caseSplitAt . nil))
                 (lambda ()
                   (ignore-errors (deduce-lsp-case-split "x")))))
          (let* ((call (assq :deduce/caseSplitAt calls))
                 (params (cdr call))
                 (text-doc (plist-get params :textDocument))
                 (pos (plist-get params :position)))
            (should call)
            (should (string-prefix-p "file://"
                                      (plist-get text-doc :uri)))
            (should (= (plist-get pos :line) 8))
            (should (= (plist-get pos :character) 2))
            (should (equal (plist-get params :variable) "x"))))
      (delete-file tmp))))


(ert-deftest deduce-lsp/case-split-applies-workspace-edit ()
  "Given a server response with a `:changes' WorkspaceEdit, the
buffer ends up with the new text replacing the `?'."
  (let ((tmp (make-temp-file "deduce-lsp-split" nil ".pf")))
    (unwind-protect
        (with-temp-buffer
          (insert "union N {\n  z\n  s(N)\n}\n\ntheorem t: all x:N. x = x\nproof\n  arbitrary x:N\n  ?\nend\n")
          (setq buffer-file-name tmp)
          (deduce-mode)
          ;; Cursor on the `?' at line 9 col 3.
          (goto-char (point-min))
          (forward-line 8)
          (forward-char 2)
          (let* ((uri (deduce-lsp--current-uri))
                 (skeleton "switch x {\n  case z { ? }\n  case s(n1) { ? }\n}")
                 (edit `(:changes
                         (,(intern (concat ":" uri))
                          [(:range (:start (:line 8 :character 2)
                                    :end (:line 8 :character 3))
                                   :newText ,skeleton)]))))
            (deduce-lsp-test--with-method-mock
             `((:deduce/caseSplitAt . ,edit))
             (lambda () (deduce-lsp-case-split "x"))))
          (let ((text (buffer-substring-no-properties (point-min) (point-max))))
            (should (string-match-p "switch x" text))
            (should (string-match-p "case z {" text))
            (should (string-match-p "case s(n1) {" text))))
      (delete-file tmp))))


(ert-deftest deduce-lsp/case-split-null-server-response-errors ()
  "If the server returns null for caseSplitAt, the command
user-errors instead of silently no-op-ing."
  (let ((tmp (make-temp-file "deduce-lsp-split" nil ".pf")))
    (unwind-protect
        (with-temp-buffer
          (insert "x")
          (setq buffer-file-name tmp)
          (deduce-mode)
          (deduce-lsp-test--with-method-mock
           '((:deduce/caseSplitAt . nil))
           (lambda ()
             (should-error (deduce-lsp-case-split "x") :type 'user-error))))
      (delete-file tmp))))


(ert-deftest deduce-lsp/case-split-without-server-errors ()
  "Without an active eglot server, the command signals a user error."
  (let ((tmp (make-temp-file "deduce-lsp-split" nil ".pf")))
    (unwind-protect
        (cl-letf (((symbol-function 'eglot-current-server)
                   (lambda () nil)))
          (with-temp-buffer
            (insert "x")
            (setq buffer-file-name tmp)
            (deduce-mode)
            (should-error (deduce-lsp-case-split "x") :type 'user-error)))
      (delete-file tmp))))


(ert-deftest deduce-lsp/case-split-interactive-uses-completing-read ()
  "Interactive entry hits `deduce/splittableVarsAt' for candidates
and feeds them to `completing-read'."
  (let ((tmp (make-temp-file "deduce-lsp-split" nil ".pf"))
        captured-prompt
        captured-collection)
    (unwind-protect
        (with-temp-buffer
          (insert "x")
          (setq buffer-file-name tmp)
          (deduce-mode)
          (cl-letf (((symbol-function 'eglot-current-server)
                     (lambda () 'mock-server))
                    ((symbol-function 'eglot--signal-textDocument/didChange)
                     (lambda () nil))
                    ((symbol-function 'jsonrpc-request)
                     (lambda (_server method _params)
                       (cond
                        ((eq method :deduce/splittableVarsAt) ["H" "x"])
                        ((eq method :deduce/caseSplitAt) nil))))
                    ((symbol-function 'completing-read)
                     (lambda (prompt collection &rest _rest)
                       (setq captured-prompt prompt)
                       (setq captured-collection collection)
                       "H")))
            (ignore-errors
              (call-interactively #'deduce-lsp-case-split)))
          (should (string-match-p "Case split on:" captured-prompt))
          ;; The collection passed to completing-read is the list of
          ;; candidates.
          (should (member "H" captured-collection))
          (should (member "x" captured-collection)))
      (delete-file tmp))))


(ert-deftest deduce-lsp/case-split-interactive-empty-candidates-errors ()
  "If `deduce/splittableVarsAt' returns no candidates, the
interactive entry user-errors with `No case split available'."
  (let ((tmp (make-temp-file "deduce-lsp-split" nil ".pf")))
    (unwind-protect
        (with-temp-buffer
          (insert "x")
          (setq buffer-file-name tmp)
          (deduce-mode)
          (cl-letf (((symbol-function 'eglot-current-server)
                     (lambda () 'mock-server))
                    ((symbol-function 'eglot--signal-textDocument/didChange)
                     (lambda () nil))
                    ((symbol-function 'jsonrpc-request)
                     (lambda (_server _method _params) [])))
            (should-error (call-interactively #'deduce-lsp-case-split)
                          :type 'user-error)))
      (delete-file tmp))))


;; ---------------------------------------------------------------------
;; deduce-lsp--request: flush pending didChange before each request
;; ---------------------------------------------------------------------
;;
;; Issue #339: a sequence like `C-c C-r' -> `C-c C-r' (chained refines)
;; races eglot's `eglot-send-changes-idle-time' debouncing when we
;; call `jsonrpc-request' directly -- the second request can reach
;; the server before eglot has sent didChange for the first edit.
;; `deduce-lsp--request' wraps `jsonrpc-request' with a synchronous
;; `eglot--signal-textDocument/didChange' first, the same primitive
;; eglot's own internal `eglot--request' uses.

(ert-deftest deduce-lsp/request-flushes-pending-didChange-before-request ()
  "`deduce-lsp--request' calls `eglot--signal-textDocument/didChange'
*before* `jsonrpc-request', so the server sees the latest buffer
state when the request is processed."
  (let ((order nil))
    (cl-letf (((symbol-function 'eglot--signal-textDocument/didChange)
               (lambda () (push 'flush order)))
              ((symbol-function 'jsonrpc-request)
               (lambda (_server _method _params)
                 (push 'request order)
                 'mock-response)))
      (let ((response (deduce-lsp--request 'mock-server :foo nil)))
        (should (eq response 'mock-response))))
    ;; `push' adds to the head, so the call sequence is the reverse.
    (should (equal (reverse order) '(flush request)))))


(ert-deftest deduce-lsp/current-uri-resolves-symlinks ()
  "`deduce-lsp--current-uri' uses `file-truename' so the URI
matches what eglot's didOpen registered.  Without this, files
opened via a symlinked path (e.g. `/tmp' -> `/private/tmp' on
macOS) would land under one URI in pygls's workspace and be
queried under another, surfacing as `KeyError' on every
request."
  (let ((tmpdir (make-temp-file "deduce-lsp-symlink" t)))
    (unwind-protect
        (let* ((real-target (expand-file-name "real.pf" tmpdir))
               (symlink-path (expand-file-name "alias.pf" tmpdir)))
          (with-temp-file real-target (insert "x"))
          (make-symbolic-link real-target symlink-path)
          (with-temp-buffer
            ;; Visit via the symlink path.
            (setq buffer-file-name symlink-path)
            (let ((uri (deduce-lsp--current-uri)))
              ;; URI must point at the *target*, not the symlink.
              (should (string-suffix-p "/real.pf" uri))
              (should-not (string-suffix-p "/alias.pf" uri)))))
      (delete-directory tmpdir t))))


;; ---------------------------------------------------------------------
;; deduce-lsp-induction (LSP Step 17, fronted by `C-c C-i')
;; ---------------------------------------------------------------------
;;
;; Same wire-shape as refine -- a `textDocument/codeAction' request,
;; filtered by `:title' "Induction".  No user input beyond the
;; cursor on a `?'.

(ert-deftest deduce-lsp/induction-bound-to-c-c-c-i ()
  "`C-c C-i' in deduce-mode-map runs `deduce-lsp-induction'."
  (should (eq (lookup-key deduce-mode-map (kbd "C-c C-i"))
              #'deduce-lsp-induction)))


(ert-deftest deduce-lsp/induction-applies-text-edit ()
  "Given a CodeAction titled \"Induction\" with a TextEdit replacing
the `?', the buffer ends up with an `induction T' skeleton."
  (let ((tmp (make-temp-file "deduce-lsp-induction" nil ".pf")))
    (unwind-protect
        (with-temp-buffer
          (insert "union N {\n  z\n  s(N)\n}\n\ntheorem t: all x:N. x = x\nproof\n  ?\nend\n")
          (setq buffer-file-name tmp)
          (deduce-mode)
          ;; Cursor on the `?` at line 8 col 3 -> LSP line 7, char 2.
          (goto-char (point-min))
          (forward-line 7)
          (forward-char 2)
          (let* ((uri (deduce-lsp--current-uri))
                 (skeleton "induction N\n    case z { ? }\n    case s(n1) assume IH1: n1 = n1 { ? }")
                 (action `(:title "Induction"
                           :kind "refactor.rewrite"
                           :edit
                           (:changes
                            (,(intern (concat ":" uri))
                             [(:range (:start (:line 7 :character 2)
                                       :end (:line 7 :character 3))
                                      :newText ,skeleton)]))))
                 (response (vector action)))
            (deduce-lsp-test--with-mock-server
             response
             (lambda () (deduce-lsp-induction))))
          (let ((text (buffer-substring-no-properties (point-min) (point-max))))
            (should (string-match-p "induction N" text))
            (should (string-match-p "case z {" text))
            (should (string-match-p "case s(n1) assume IH1" text))))
      (delete-file tmp))))


(ert-deftest deduce-lsp/induction-no-action-signals-user-error ()
  "An empty action list yields a `No induction available' user-error."
  (let ((tmp (make-temp-file "deduce-lsp-induction" nil ".pf")))
    (unwind-protect
        (with-temp-buffer
          (insert "x")
          (setq buffer-file-name tmp)
          (deduce-mode)
          (deduce-lsp-test--with-mock-server
           nil
           (lambda ()
             (should-error (deduce-lsp-induction) :type 'user-error))))
      (delete-file tmp))))


(ert-deftest deduce-lsp/induction-rejects-non-matching-title ()
  "If the server returns an action titled \"Refine hole\" instead
of \"Induction\", the induction command must NOT apply it -- it
should user-error."
  (let ((tmp (make-temp-file "deduce-lsp-induction" nil ".pf")))
    (unwind-protect
        (with-temp-buffer
          (insert "x")
          (setq buffer-file-name tmp)
          (deduce-mode)
          (let* ((uri (deduce-lsp--current-uri))
                 (action `(:title "Refine hole"
                           :kind "refactor.rewrite"
                           :edit (:changes
                                  (,(intern (concat ":" uri)) []))))
                 (response (vector action)))
            (deduce-lsp-test--with-mock-server
             response
             (lambda ()
               (should-error (deduce-lsp-induction) :type 'user-error)))))
      (delete-file tmp))))


;; ---------------------------------------------------------------------
;; deduce-lsp-eliminate (LSP Step 18, fronted by `C-c C-e')
;; ---------------------------------------------------------------------
;;
;; Same wire shape as case split (Step 16): cursor on `?', the
;; interactive form fetches candidate labels via
;; `deduce/eliminableVarsAt' and uses completing-read; the chosen
;; label drives a `deduce/eliminateAt' request.

(ert-deftest deduce-lsp/eliminate-bound-to-c-c-c-e ()
  "`C-c C-e' in deduce-mode-map runs `deduce-lsp-eliminate'."
  (should (eq (lookup-key deduce-mode-map (kbd "C-c C-e"))
              #'deduce-lsp-eliminate)))


(ert-deftest deduce-lsp/eliminate-issues-eliminateAt-request ()
  "Calling `deduce-lsp-eliminate' with a label arg sends
`deduce/eliminateAt' with `{textDocument, position, label}'."
  (let ((tmp (make-temp-file "deduce-lsp-elim" nil ".pf"))
        calls)
    (unwind-protect
        (with-temp-buffer
          (insert "theorem t: all P:bool, Q:bool. if P or Q then Q or P\nproof\n  arbitrary P:bool, Q:bool\n  assume H: P or Q\n  ?\nend\n")
          (setq buffer-file-name tmp)
          (deduce-mode)
          ;; `?` at line 5 col 3 -> LSP line 4, char 2.
          (goto-char (point-min))
          (forward-line 4)
          (forward-char 2)
          (setq calls
                (deduce-lsp-test--with-method-mock
                 '((:deduce/eliminateAt . nil))
                 (lambda ()
                   (ignore-errors (deduce-lsp-eliminate "H")))))
          (let* ((call (assq :deduce/eliminateAt calls))
                 (params (cdr call))
                 (text-doc (plist-get params :textDocument))
                 (pos (plist-get params :position)))
            (should call)
            (should (string-prefix-p "file://"
                                      (plist-get text-doc :uri)))
            (should (= (plist-get pos :line) 4))
            (should (= (plist-get pos :character) 2))
            (should (equal (plist-get params :label) "H"))))
      (delete-file tmp))))


(ert-deftest deduce-lsp/eliminate-applies-workspace-edit ()
  "Given a server response with a `:changes' WorkspaceEdit, the
buffer ends up with the new text replacing the `?'."
  (let ((tmp (make-temp-file "deduce-lsp-elim" nil ".pf")))
    (unwind-protect
        (with-temp-buffer
          (insert "theorem t: all P:bool, Q:bool. if P or Q then Q or P\nproof\n  arbitrary P:bool, Q:bool\n  assume H: P or Q\n  ?\nend\n")
          (setq buffer-file-name tmp)
          (deduce-mode)
          (goto-char (point-min))
          (forward-line 4)
          (forward-char 2)
          (let* ((uri (deduce-lsp--current-uri))
                 (skeleton "cases H\n    case h1: P { ? }\n    case h2: Q { ? }")
                 (edit `(:changes
                         (,(intern (concat ":" uri))
                          [(:range (:start (:line 4 :character 2)
                                    :end (:line 4 :character 3))
                                   :newText ,skeleton)]))))
            (deduce-lsp-test--with-method-mock
             `((:deduce/eliminateAt . ,edit))
             (lambda () (deduce-lsp-eliminate "H"))))
          (let ((text (buffer-substring-no-properties (point-min) (point-max))))
            (should (string-match-p "cases H" text))
            (should (string-match-p "case h1: P" text))
            (should (string-match-p "case h2: Q" text))))
      (delete-file tmp))))


(ert-deftest deduce-lsp/eliminate-null-server-response-errors ()
  "If the server returns null for eliminateAt, the command
user-errors instead of silently no-op-ing."
  (let ((tmp (make-temp-file "deduce-lsp-elim" nil ".pf")))
    (unwind-protect
        (with-temp-buffer
          (insert "x")
          (setq buffer-file-name tmp)
          (deduce-mode)
          (deduce-lsp-test--with-method-mock
           '((:deduce/eliminateAt . nil))
           (lambda ()
             (should-error (deduce-lsp-eliminate "H") :type 'user-error))))
      (delete-file tmp))))


(ert-deftest deduce-lsp/eliminate-interactive-uses-completing-read ()
  "Interactive entry hits `deduce/eliminableVarsAt' for candidates
and feeds them to `completing-read'."
  (let ((tmp (make-temp-file "deduce-lsp-elim" nil ".pf"))
        captured-prompt
        captured-collection)
    (unwind-protect
        (with-temp-buffer
          (insert "x")
          (setq buffer-file-name tmp)
          (deduce-mode)
          (cl-letf (((symbol-function 'eglot-current-server)
                     (lambda () 'mock-server))
                    ((symbol-function 'eglot--signal-textDocument/didChange)
                     (lambda () nil))
                    ((symbol-function 'jsonrpc-request)
                     (lambda (_server method _params)
                       (cond
                        ((eq method :deduce/eliminableVarsAt) ["H1" "H2"])
                        ((eq method :deduce/eliminateAt) nil))))
                    ((symbol-function 'completing-read)
                     (lambda (prompt collection &rest _rest)
                       (setq captured-prompt prompt)
                       (setq captured-collection collection)
                       "H1")))
            (ignore-errors
              (call-interactively #'deduce-lsp-eliminate)))
          (should (string-match-p "Eliminate on:" captured-prompt))
          (should (member "H1" captured-collection))
          (should (member "H2" captured-collection)))
      (delete-file tmp))))


(ert-deftest deduce-lsp/eliminate-interactive-empty-candidates-errors ()
  "If `deduce/eliminableVarsAt' returns no candidates, the
interactive entry user-errors with `No elimination available'."
  (let ((tmp (make-temp-file "deduce-lsp-elim" nil ".pf")))
    (unwind-protect
        (with-temp-buffer
          (insert "x")
          (setq buffer-file-name tmp)
          (deduce-mode)
          (cl-letf (((symbol-function 'eglot-current-server)
                     (lambda () 'mock-server))
                    ((symbol-function 'eglot--signal-textDocument/didChange)
                     (lambda () nil))
                    ((symbol-function 'jsonrpc-request)
                     (lambda (_server _method _params) [])))
            (should-error (call-interactively #'deduce-lsp-eliminate)
                          :type 'user-error)))
      (delete-file tmp))))


;; ---------------------------------------------------------------------
;; deduce-lsp-fill-from-given (issue #353, fronted by `C-c C-f')
;; ---------------------------------------------------------------------
;;
;; Cursor on `?', the interactive form fetches candidate labels via
;; `deduce/matchingGivensAt' and picks the first one without prompting
;; (issue #385).  The chosen label drives a `deduce/fillFromGivenAt'
;; request.

(ert-deftest deduce-lsp/fill-from-given-bound-to-c-c-c-f ()
  "`C-c C-f' in deduce-mode-map runs `deduce-lsp-fill-from-given'."
  (should (eq (lookup-key deduce-mode-map (kbd "C-c C-f"))
              #'deduce-lsp-fill-from-given)))


(ert-deftest deduce-lsp/fill-from-given-issues-fillFromGivenAt-request ()
  "Calling `deduce-lsp-fill-from-given' with a label arg sends
`deduce/fillFromGivenAt' with `{textDocument, position, label}'."
  (let ((tmp (make-temp-file "deduce-lsp-fill" nil ".pf"))
        calls)
    (unwind-protect
        (with-temp-buffer
          (insert "theorem t: all P:bool. if P then P\nproof\n  arbitrary P:bool\n  assume H: P\n  ?\nend\n")
          (setq buffer-file-name tmp)
          (deduce-mode)
          ;; `?` at line 5 col 3 -> LSP line 4, char 2.
          (goto-char (point-min))
          (forward-line 4)
          (forward-char 2)
          (setq calls
                (deduce-lsp-test--with-method-mock
                 '((:deduce/fillFromGivenAt . nil))
                 (lambda ()
                   (ignore-errors (deduce-lsp-fill-from-given "H")))))
          (let* ((call (assq :deduce/fillFromGivenAt calls))
                 (params (cdr call))
                 (text-doc (plist-get params :textDocument))
                 (pos (plist-get params :position)))
            (should call)
            (should (string-prefix-p "file://"
                                      (plist-get text-doc :uri)))
            (should (= (plist-get pos :line) 4))
            (should (= (plist-get pos :character) 2))
            (should (equal (plist-get params :label) "H"))))
      (delete-file tmp))))


(ert-deftest deduce-lsp/fill-from-given-applies-workspace-edit ()
  "Given a server response with a `:changes' WorkspaceEdit, the
buffer ends up with the new text replacing the `?'."
  (let ((tmp (make-temp-file "deduce-lsp-fill" nil ".pf")))
    (unwind-protect
        (with-temp-buffer
          (insert "theorem t: all P:bool. if P then P\nproof\n  arbitrary P:bool\n  assume H: P\n  ?\nend\n")
          (setq buffer-file-name tmp)
          (deduce-mode)
          (goto-char (point-min))
          (forward-line 4)
          (forward-char 2)
          (let* ((uri (deduce-lsp--current-uri))
                 (skeleton "conclude P by H")
                 (edit `(:changes
                         (,(intern (concat ":" uri))
                          [(:range (:start (:line 4 :character 2)
                                    :end (:line 4 :character 3))
                                   :newText ,skeleton)]))))
            (deduce-lsp-test--with-method-mock
             `((:deduce/fillFromGivenAt . ,edit))
             (lambda () (deduce-lsp-fill-from-given "H"))))
          (let ((text (buffer-substring-no-properties (point-min) (point-max))))
            (should (string-match-p "conclude P by H" text))))
      (delete-file tmp))))


(ert-deftest deduce-lsp/fill-from-given-null-server-response-errors ()
  "If the server returns null for fillFromGivenAt, the command
user-errors instead of silently no-op-ing."
  (let ((tmp (make-temp-file "deduce-lsp-fill" nil ".pf")))
    (unwind-protect
        (with-temp-buffer
          (insert "x")
          (setq buffer-file-name tmp)
          (deduce-mode)
          (deduce-lsp-test--with-method-mock
           '((:deduce/fillFromGivenAt . nil))
           (lambda ()
             (should-error (deduce-lsp-fill-from-given "H") :type 'user-error))))
      (delete-file tmp))))


(ert-deftest deduce-lsp/fill-from-given-interactive-single-match-autoselects ()
  "With exactly one matching given, the interactive entry uses the
single candidate without prompting via `completing-read'."
  (let ((tmp (make-temp-file "deduce-lsp-fill" nil ".pf"))
        completing-read-called)
    (unwind-protect
        (with-temp-buffer
          (insert "x")
          (setq buffer-file-name tmp)
          (deduce-mode)
          (cl-letf (((symbol-function 'eglot-current-server)
                     (lambda () 'mock-server))
                    ((symbol-function 'eglot--signal-textDocument/didChange)
                     (lambda () nil))
                    ((symbol-function 'jsonrpc-request)
                     (lambda (_server method _params)
                       (cond
                        ((eq method :deduce/matchingGivensAt) ["H"])
                        ((eq method :deduce/fillFromGivenAt) nil))))
                    ((symbol-function 'completing-read)
                     (lambda (&rest _args)
                       (setq completing-read-called t)
                       "H")))
            (ignore-errors
              (call-interactively #'deduce-lsp-fill-from-given)))
          (should-not completing-read-called))
      (delete-file tmp))))


(ert-deftest deduce-lsp/fill-from-given-interactive-multi-picks-first ()
  "With multiple matches, the interactive entry picks the first
candidate without prompting via `completing-read' (issue #385)."
  (let ((tmp (make-temp-file "deduce-lsp-fill" nil ".pf"))
        completing-read-called
        captured-label)
    (unwind-protect
        (with-temp-buffer
          (insert "x")
          (setq buffer-file-name tmp)
          (deduce-mode)
          (cl-letf (((symbol-function 'eglot-current-server)
                     (lambda () 'mock-server))
                    ((symbol-function 'eglot--signal-textDocument/didChange)
                     (lambda () nil))
                    ((symbol-function 'jsonrpc-request)
                     (lambda (_server method params)
                       (cond
                        ((eq method :deduce/matchingGivensAt) ["H1" "H2"])
                        ((eq method :deduce/fillFromGivenAt)
                         (setq captured-label (plist-get params :label))
                         nil))))
                    ((symbol-function 'completing-read)
                     (lambda (&rest _args)
                       (setq completing-read-called t)
                       "H2")))
            (ignore-errors
              (call-interactively #'deduce-lsp-fill-from-given)))
          (should-not completing-read-called)
          (should (equal captured-label "H1")))
      (delete-file tmp))))


(ert-deftest deduce-lsp/fill-from-given-interactive-empty-candidates-errors ()
  "If `deduce/matchingGivensAt' returns no candidates, the
interactive entry user-errors with `No matching given'."
  (let ((tmp (make-temp-file "deduce-lsp-fill" nil ".pf")))
    (unwind-protect
        (with-temp-buffer
          (insert "x")
          (setq buffer-file-name tmp)
          (deduce-mode)
          (cl-letf (((symbol-function 'eglot-current-server)
                     (lambda () 'mock-server))
                    ((symbol-function 'eglot--signal-textDocument/didChange)
                     (lambda () nil))
                    ((symbol-function 'jsonrpc-request)
                     (lambda (_server _method _params) [])))
            (should-error (call-interactively #'deduce-lsp-fill-from-given)
                          :type 'user-error)))
      (delete-file tmp))))


(ert-deftest deduce-lsp/fill-from-given-implies-candidate-flows-through ()
  "When `deduce/matchingGivensAt' returns an implies-only candidate
\(issue #361 widens the filter to `check_implies'\), the interactive
entry sends `deduce/fillFromGivenAt' with that label just like an
exact-match candidate -- no special-casing at the transport layer."
  (let ((tmp (make-temp-file "deduce-lsp-fill" nil ".pf"))
        captured-label)
    (unwind-protect
        (with-temp-buffer
          (insert "x")
          (setq buffer-file-name tmp)
          (deduce-mode)
          (cl-letf (((symbol-function 'eglot-current-server)
                     (lambda () 'mock-server))
                    ((symbol-function 'eglot--signal-textDocument/didChange)
                     (lambda () nil))
                    ((symbol-function 'jsonrpc-request)
                     (lambda (_server method params)
                       (cond
                        ;; H: P implies goal P or Q -- single candidate,
                        ;; returned by the widened filter.
                        ((eq method :deduce/matchingGivensAt) ["H"])
                        ((eq method :deduce/fillFromGivenAt)
                         (setq captured-label (plist-get params :label))
                         nil)))))
            (ignore-errors
              (call-interactively #'deduce-lsp-fill-from-given)))
          (should (equal captured-label "H")))
      (delete-file tmp))))


;; ---------------------------------------------------------------------
;; deduce-show-diagnostic-at-point (issue #430)
;; ---------------------------------------------------------------------
;;
;; The popup-buffer command for full multi-line diagnostics.  We don't
;; run a live flymake-eglot loop in these tests; instead we stub
;; `flymake-diagnostics' to return a hand-built diagnostic and check
;; that the render routine preserves the newlines / tabs that the echo
;; area would otherwise clip.

(require 'flymake)

(defun deduce-lsp-test--make-diag (buffer beg end type text)
  "Build a flymake diagnostic for the tests.

The flymake constructor (`flymake-make-diagnostic') accepts the
five-positional form `(buffer beg end type text)' across every
Emacs version we support; using it keeps the diagnostic structurally
identical to one flymake itself would emit."
  (flymake-make-diagnostic buffer beg end type text))


(ert-deftest deduce-lsp/show-diagnostic-bound-to-c-c-c-x ()
  "`C-c C-x' in deduce-mode-map runs `deduce-show-diagnostic-at-point'."
  (should (eq (lookup-key deduce-mode-map (kbd "C-c C-x"))
              #'deduce-show-diagnostic-at-point)))


(ert-deftest deduce-lsp/show-diagnostic-renders-multiline-text ()
  "The popup buffer preserves newlines and tab-indented continuations
from the diagnostic text -- the whole point of the command."
  (let ((tmp (make-temp-file "deduce-diag" nil ".pf"))
        (multi (concat "Missing type annotation. Expected ':' followed by a type.\n"
                       "/tmp/x.pf:1.18-1.20: while parsing\n"
                       "\ttype_annot_list ::= identifier \":\" type")))
    (unwind-protect
        (with-temp-buffer
          (insert "theorem foo: all P. P = P\n")
          (setq buffer-file-name tmp)
          (deduce-mode)
          (goto-char (point-min))
          (forward-char 18)
          (let* ((src-buffer (current-buffer))
                 (diag (deduce-lsp-test--make-diag
                        src-buffer (point) (1+ (point)) :error multi)))
            (cl-letf (((symbol-function 'flymake-diagnostics)
                       (lambda (&rest _) (list diag))))
              (deduce-show-diagnostic-at-point)))
          (let ((rendered
                 (with-current-buffer
                     (get-buffer deduce-lsp-diagnostic-buffer-name)
                   (buffer-substring-no-properties (point-min) (point-max)))))
            (should (string-match-p "\\[error\\]" rendered))
            (should (string-match-p "Missing type annotation" rendered))
            (should (string-match-p "while parsing" rendered))
            ;; The tab-indented continuation must survive intact --
            ;; without this the echo-area version (which clips at
            ;; the first newline) is exactly what the user already
            ;; sees, and the command is pointless.
            (should (string-match-p "\ttype_annot_list" rendered))))
      (when (get-buffer deduce-lsp-diagnostic-buffer-name)
        (kill-buffer deduce-lsp-diagnostic-buffer-name))
      (delete-file tmp))))


(ert-deftest deduce-lsp/show-diagnostic-falls-back-to-line ()
  "When point sits between diagnostics, the command widens its
search to the current line and still finds the diagnostic."
  (let ((tmp (make-temp-file "deduce-diag" nil ".pf"))
        (calls nil))
    (unwind-protect
        (with-temp-buffer
          (insert "theorem foo: all P. P = P\n")
          (setq buffer-file-name tmp)
          (deduce-mode)
          (goto-char (point-min))
          (let* ((src-buffer (current-buffer))
                 (diag (deduce-lsp-test--make-diag
                        src-buffer 19 20 :error
                        "Missing type annotation.")))
            (cl-letf (((symbol-function 'flymake-diagnostics)
                       (lambda (beg end)
                         (push (cons beg end) calls)
                         ;; First call (point .. point) returns nil;
                         ;; second call (line bounds) returns the diag.
                         (if (= beg end) nil (list diag)))))
              (deduce-show-diagnostic-at-point)))
          ;; Two queries: point-level, then line-level.
          (should (= (length calls) 2))
          (let ((rendered
                 (with-current-buffer
                     (get-buffer deduce-lsp-diagnostic-buffer-name)
                   (buffer-substring-no-properties (point-min) (point-max)))))
            (should (string-match-p "Missing type annotation" rendered))))
      (when (get-buffer deduce-lsp-diagnostic-buffer-name)
        (kill-buffer deduce-lsp-diagnostic-buffer-name))
      (delete-file tmp))))


(ert-deftest deduce-lsp/show-diagnostic-empty-reports-none ()
  "With no diagnostics at point or on the line, the popup buffer
states `No diagnostic at point.' rather than displaying stale text."
  (let ((tmp (make-temp-file "deduce-diag" nil ".pf")))
    (unwind-protect
        (with-temp-buffer
          (insert "theorem t: bool\n")
          (setq buffer-file-name tmp)
          (deduce-mode)
          (cl-letf (((symbol-function 'flymake-diagnostics)
                     (lambda (&rest _) nil)))
            (deduce-show-diagnostic-at-point))
          (let ((rendered
                 (with-current-buffer
                     (get-buffer deduce-lsp-diagnostic-buffer-name)
                   (buffer-substring-no-properties (point-min) (point-max)))))
            (should (string-match-p "No diagnostic at point" rendered))))
      (when (get-buffer deduce-lsp-diagnostic-buffer-name)
        (kill-buffer deduce-lsp-diagnostic-buffer-name))
      (delete-file tmp))))


(ert-deftest deduce-lsp/show-diagnostic-multiple-diagnostics ()
  "When several diagnostics overlap point, each is rendered with its
own [severity] header so the user can tell them apart."
  (let ((tmp (make-temp-file "deduce-diag" nil ".pf")))
    (unwind-protect
        (with-temp-buffer
          (insert "x\n")
          (setq buffer-file-name tmp)
          (deduce-mode)
          (let* ((src-buffer (current-buffer))
                 (d1 (deduce-lsp-test--make-diag
                      src-buffer 1 2 :error "first error\nwith body"))
                 (d2 (deduce-lsp-test--make-diag
                      src-buffer 1 2 :warning "second warning")))
            (cl-letf (((symbol-function 'flymake-diagnostics)
                       (lambda (&rest _) (list d1 d2))))
              (deduce-show-diagnostic-at-point)))
          (let ((rendered
                 (with-current-buffer
                     (get-buffer deduce-lsp-diagnostic-buffer-name)
                   (buffer-substring-no-properties (point-min) (point-max)))))
            (should (string-match-p "\\[error\\]" rendered))
            (should (string-match-p "\\[warning\\]" rendered))
            (should (string-match-p "first error" rendered))
            (should (string-match-p "with body" rendered))
            (should (string-match-p "second warning" rendered))))
      (when (get-buffer deduce-lsp-diagnostic-buffer-name)
        (kill-buffer deduce-lsp-diagnostic-buffer-name))
      (delete-file tmp))))


;; ---------------------------------------------------------------------
;; deduce-lsp-search-lemma (issue #690, Part 3, fronted by `C-c C-l')
;; ---------------------------------------------------------------------
;;
;; Cursor on `?', the interactive form fetches ranked lemmas via
;; `deduce/availableLemmasAt' and presents them through
;; `completing-read'.  The chosen lemma drives a `deduce/insertLemma'
;; request whose WorkspaceEdit is applied directly.  The picker
;; annotates each candidate with the unify tier and module.

(ert-deftest deduce-lsp/search-lemma-bound-to-c-c-c-l ()
  "`C-c C-l' in deduce-mode-map runs `deduce-lsp-search-lemma'."
  (should (eq (lookup-key deduce-mode-map (kbd "C-c C-l"))
              #'deduce-lsp-search-lemma)))


(ert-deftest deduce-lsp/search-lemma-tier-tag-full-no-discharged ()
  "Tier `full' with no discharged premises renders as `applies'."
  (let ((lemma '(:unify_tier "full" :discharged_premises [])))
    (should (equal (deduce-lsp--lemma-tier-tag lemma) "applies"))))


(ert-deftest deduce-lsp/search-lemma-tier-tag-full-with-discharged ()
  "Tier `full' with discharged premises lists the given labels."
  (let ((lemma '(:unify_tier "full"
                 :discharged_premises [["a <= b" "h"]
                                       ["b <= c" "g"]])))
    (should (equal (deduce-lsp--lemma-tier-tag lemma)
                   "applies (by h, g)"))))


(ert-deftest deduce-lsp/search-lemma-tier-tag-premises-remain ()
  "Tier `premises_remain' renders as `premises remain'."
  (let ((lemma '(:unify_tier "premises_remain"
                 :discharged_premises [])))
    (should (equal (deduce-lsp--lemma-tier-tag lemma)
                   "premises remain"))))


(ert-deftest deduce-lsp/search-lemma-tier-tag-rewrite-subterm ()
  "Tier `rewrite_subterm' renders as `rewrite subterm'."
  (let ((lemma '(:unify_tier "rewrite_subterm"
                 :discharged_premises [])))
    (should (equal (deduce-lsp--lemma-tier-tag lemma)
                   "rewrite subterm"))))


(ert-deftest deduce-lsp/search-lemma-tier-tag-no-tier ()
  "Nil `unify_tier' returns nil -- the annotation column collapses."
  (let ((lemma '(:unify_tier nil :discharged_premises [])))
    (should (null (deduce-lsp--lemma-tier-tag lemma)))))


(ert-deftest deduce-lsp/search-lemma-display-string-includes-signature ()
  "Picker rows show `name : signature' so users can pick by formula
shape, not just by memorized name."
  (let ((lemma '(:name "uint_add_commute"
                 :signature "all a:UInt, b:UInt. a + b = b + a")))
    (should (equal (deduce-lsp--lemma-display-string lemma)
                   "uint_add_commute : all a:UInt, b:UInt. a + b = b + a"))))


(ert-deftest deduce-lsp/search-lemma-display-string-no-signature ()
  "When the signature is missing or empty, fall back to just the name."
  (let ((lemma '(:name "lemma_x" :signature "")))
    (should (equal (deduce-lsp--lemma-display-string lemma)
                   "lemma_x"))))


(ert-deftest deduce-lsp/search-lemma-build-alist-disambiguates-duplicates ()
  "Two lemmas with the same display string get unique alist keys --
otherwise `completing-read' can't tell them apart."
  (let* ((lemmas (list '(:name "foo" :signature "Sig" :module "A")
                       '(:name "foo" :signature "Sig" :module "B")))
         (alist (deduce-lsp--build-lemma-alist lemmas))
         (keys (mapcar #'car alist)))
    (should (= (length keys) 2))
    (should (equal (length (delete-dups (copy-sequence keys))) 2))
    ;; The second occurrence is suffixed; the first keeps the plain
    ;; form so the common case has no visual noise.
    (should (equal (car keys) "foo : Sig"))
    (should (equal (cadr keys) "foo : Sig (2)"))))


(ert-deftest deduce-lsp/search-lemma-annotation-fn-renders-tier-and-module ()
  "The annotation function appends `-- <tier-tag> [<module>]' to each
picker row so the user sees how each candidate applies."
  (let* ((lemma '(:name "uint_add_commute"
                  :signature "all a,b:UInt. a + b = b + a"
                  :module "UInt"
                  :unify_tier "rewrite_subterm"
                  :discharged_premises []))
         (alist `(("uint_add_commute : sig" . ,lemma)))
         (anno (deduce-lsp--lemma-annotation-fn alist))
         (result (funcall anno "uint_add_commute : sig")))
    (should (string-match-p "rewrite subterm" result))
    (should (string-match-p "\\[UInt\\]" result))))


(ert-deftest deduce-lsp/search-lemma-annotation-fn-handles-null-module ()
  "JSON `null' for module (`:null' or `:json-null') is treated as no
module -- the bracket is omitted rather than printed as `[:null]'."
  (let* ((lemma '(:name "x" :signature "" :module :null
                  :unify_tier nil :discharged_premises []))
         (alist `(("x" . ,lemma)))
         (anno (deduce-lsp--lemma-annotation-fn alist)))
    (should (equal (funcall anno "x") ""))))


(ert-deftest deduce-lsp/search-lemma-issues-availableLemmasAt-and-insertLemma ()
  "Calling `deduce-lsp-search-lemma' issues the picker request first,
then the insertion request with the picked lemma name."
  (let ((tmp (make-temp-file "deduce-lsp-lemma" nil ".pf"))
        calls)
    (unwind-protect
        (with-temp-buffer
          (insert "theorem t: all P:bool. P = P\nproof\n  arbitrary P:bool\n  ?\nend\n")
          (setq buffer-file-name tmp)
          (deduce-mode)
          ;; `?` at line 4 col 3 -> LSP line 3, char 2.
          (goto-char (point-min))
          (forward-line 3)
          (forward-char 2)
          (let ((lemma `(:name "eq_refl"
                         :kind "theorem"
                         :signature "all x:bool. x = x"
                         :module "Base"
                         :relevance 1.0
                         :unify_tier "full"
                         :discharged_premises [])))
            (cl-letf (((symbol-function 'eglot-current-server)
                       (lambda () 'mock-server))
                      ((symbol-function 'eglot--signal-textDocument/didChange)
                       (lambda () nil))
                      ((symbol-function 'jsonrpc-request)
                       (lambda (_server method params)
                         (push (cons method params) calls)
                         (cond
                          ((eq method :deduce/availableLemmasAt)
                           (vector lemma))
                          ((eq method :deduce/insertLemma) nil))))
                      ((symbol-function 'completing-read)
                       (lambda (&rest _args)
                         "eq_refl : all x:bool. x = x")))
              (ignore-errors (deduce-lsp-search-lemma))))
          (let* ((calls (reverse calls))
                 (call1 (assq :deduce/availableLemmasAt calls))
                 (call2 (assq :deduce/insertLemma calls))
                 (p1 (cdr call1))
                 (p2 (cdr call2)))
            (should call1)
            (should call2)
            (should (string-prefix-p "file://"
                                      (plist-get
                                       (plist-get p1 :textDocument) :uri)))
            (should (= (plist-get (plist-get p1 :position) :line) 3))
            (should (= (plist-get (plist-get p1 :position) :character) 2))
            (should (equal (plist-get p2 :name) "eq_refl"))))
      (delete-file tmp))))


(ert-deftest deduce-lsp/search-lemma-passes-query-with-prefix-arg ()
  "With a non-nil QUERY argument, `deduce/availableLemmasAt' carries a
`:query' field so the server can filter the candidate list."
  (let ((tmp (make-temp-file "deduce-lsp-lemma" nil ".pf"))
        captured-params)
    (unwind-protect
        (with-temp-buffer
          (insert "x")
          (setq buffer-file-name tmp)
          (deduce-mode)
          (cl-letf (((symbol-function 'eglot-current-server)
                     (lambda () 'mock-server))
                    ((symbol-function 'eglot--signal-textDocument/didChange)
                     (lambda () nil))
                    ((symbol-function 'jsonrpc-request)
                     (lambda (_server method params)
                       (when (eq method :deduce/availableLemmasAt)
                         (setq captured-params params))
                       nil)))
            (ignore-errors (deduce-lsp-search-lemma "commute"))))
      (delete-file tmp))
    (should (equal (plist-get captured-params :query) "commute"))))


(ert-deftest deduce-lsp/search-lemma-empty-candidates-errors ()
  "When the server returns an empty candidate list, the command
user-errors rather than calling `completing-read' with an empty
candidate set."
  (let ((tmp (make-temp-file "deduce-lsp-lemma" nil ".pf")))
    (unwind-protect
        (with-temp-buffer
          (insert "x")
          (setq buffer-file-name tmp)
          (deduce-mode)
          (cl-letf (((symbol-function 'eglot-current-server)
                     (lambda () 'mock-server))
                    ((symbol-function 'eglot--signal-textDocument/didChange)
                     (lambda () nil))
                    ((symbol-function 'jsonrpc-request)
                     (lambda (_server _method _params) [])))
            (should-error (deduce-lsp-search-lemma) :type 'user-error)))
      (delete-file tmp))))


(ert-deftest deduce-lsp/search-lemma-null-insert-response-errors ()
  "If the server returns null for `insertLemma' (lemma not in scope),
the command user-errors rather than silently doing nothing."
  (let ((tmp (make-temp-file "deduce-lsp-lemma" nil ".pf")))
    (unwind-protect
        (with-temp-buffer
          (insert "x")
          (setq buffer-file-name tmp)
          (deduce-mode)
          (cl-letf (((symbol-function 'eglot-current-server)
                     (lambda () 'mock-server))
                    ((symbol-function 'eglot--signal-textDocument/didChange)
                     (lambda () nil))
                    ((symbol-function 'jsonrpc-request)
                     (lambda (_server method _params)
                       (cond
                        ((eq method :deduce/availableLemmasAt)
                         (vector '(:name "eq_refl" :kind "theorem"
                                   :signature "" :module "Base"
                                   :relevance 1.0
                                   :unify_tier nil
                                   :discharged_premises [])))
                        ((eq method :deduce/insertLemma) nil))))
                    ((symbol-function 'completing-read)
                     (lambda (&rest _args) "eq_refl")))
            (should-error (deduce-lsp-search-lemma) :type 'user-error)))
      (delete-file tmp))))


(ert-deftest deduce-lsp/search-lemma-applies-workspace-edit ()
  "A successful `insertLemma' response splices its newText into the
buffer at the picker's chosen lemma."
  (let ((tmp (make-temp-file "deduce-lsp-lemma" nil ".pf")))
    (unwind-protect
        (with-temp-buffer
          (insert "theorem t: all P:bool. P = P\nproof\n  arbitrary P:bool\n  ?\nend\n")
          (setq buffer-file-name tmp)
          (deduce-mode)
          (goto-char (point-min))
          (forward-line 3)
          (forward-char 2)
          (let* ((uri (deduce-lsp--current-uri))
                 (skeleton "conclude P = P by eq_refl")
                 (edit `(:changes
                         (,(intern (concat ":" uri))
                          [(:range (:start (:line 3 :character 2)
                                    :end (:line 3 :character 3))
                                   :newText ,skeleton)]))))
            (cl-letf (((symbol-function 'eglot-current-server)
                       (lambda () 'mock-server))
                      ((symbol-function 'eglot--signal-textDocument/didChange)
                       (lambda () nil))
                      ((symbol-function 'jsonrpc-request)
                       (lambda (_server method _params)
                         (cond
                          ((eq method :deduce/availableLemmasAt)
                           (vector '(:name "eq_refl" :kind "theorem"
                                     :signature "all x:bool. x = x"
                                     :module "Base"
                                     :relevance 1.0
                                     :unify_tier "full"
                                     :discharged_premises [])))
                          ((eq method :deduce/insertLemma) edit))))
                      ((symbol-function 'completing-read)
                       (lambda (&rest _args)
                         "eq_refl : all x:bool. x = x")))
              (deduce-lsp-search-lemma)))
          (let ((text (buffer-substring-no-properties (point-min) (point-max))))
            (should (string-match-p "conclude P = P by eq_refl" text))))
      (delete-file tmp))))


(ert-deftest deduce-lsp/search-lemma-without-server-errors ()
  "Without an active eglot server, the command signals a user error."
  (let ((tmp (make-temp-file "deduce-lsp-lemma" nil ".pf")))
    (unwind-protect
        (with-temp-buffer
          (insert "x")
          (setq buffer-file-name tmp)
          (deduce-mode)
          (cl-letf (((symbol-function 'eglot-current-server)
                     (lambda () nil)))
            (should-error (deduce-lsp-search-lemma) :type 'user-error)))
      (delete-file tmp))))


(provide 'deduce-lsp-test)

;;; deduce-lsp-test.el ends here
