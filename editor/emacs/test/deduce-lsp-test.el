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
of every captured (method . params) pair, in call order."
  (let ((calls nil))
    (cl-letf (((symbol-function 'eglot-current-server)
               (lambda () 'mock-server))
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
                    ((symbol-function 'jsonrpc-request)
                     (lambda (_server _method _params) [])))
            (should-error (call-interactively #'deduce-lsp-case-split)
                          :type 'user-error)))
      (delete-file tmp))))


(provide 'deduce-lsp-test)

;;; deduce-lsp-test.el ends here
