;;; deduce-mode-test.el --- ert tests for deduce-mode -*- lexical-binding: t; -*-

;; SPDX-License-Identifier: MIT

;;; Commentary:

;; Run with:
;;
;;     emacs --batch -L editor/emacs -L editor/emacs/test \
;;           -l deduce-mode-test -f ert-run-tests-batch-and-exit

;;; Code:

(require 'ert)
(require 'deduce-mode)


(ert-deftest deduce-mode/auto-mode-alist-includes-pf ()
  "`.pf' files should open in deduce-mode."
  (should (eq (assoc-default "foo.pf" auto-mode-alist #'string-match)
              'deduce-mode)))


(ert-deftest deduce-mode/mode-name-is-deduce ()
  (with-temp-buffer
    (deduce-mode)
    (should (equal mode-name "Deduce"))))


(ert-deftest deduce-mode/line-comment-toggles-with-double-slash ()
  "`comment-region' / `uncomment-region' use `// '."
  (with-temp-buffer
    (deduce-mode)
    (insert "theorem t: true")
    (comment-region (point-min) (point-max))
    (should (string-prefix-p "// " (buffer-string)))
    (uncomment-region (point-min) (point-max))
    (should (equal (string-trim-right (buffer-string)) "theorem t: true"))))


(ert-deftest deduce-mode/block-comments-recognized-by-syntax ()
  "`/*' ... `*/' should put the inside but not the outside into a
syntactic comment region (so font-lock and movement can rely on it)."
  (with-temp-buffer
    (deduce-mode)
    (insert "/* hello */ rest")
    (goto-char 5)               ; inside the comment
    (should (nth 4 (syntax-ppss)))
    (goto-char (point-max))     ; past `*/'
    (should-not (nth 4 (syntax-ppss)))))


(ert-deftest deduce-mode/block-comments-do-not-nest ()
  "Deduce.lark uses non-nested block comments; the syntax table
should match (so a `/*' inside a comment doesn't keep the outer
open)."
  (with-temp-buffer
    (deduce-mode)
    (insert "/* outer /* inner */ after")
    (goto-char (point-max))
    (should-not (nth 4 (syntax-ppss)))))


(ert-deftest deduce-mode/identifier-trailing-marks-are-symbol-class ()
  "Identifiers like `n''` and `done?` shouldn't have their trailing
character break sexp motion."
  (with-temp-buffer
    (deduce-mode)
    (insert "n' done?")
    (goto-char (point-min))
    (forward-sexp)
    (should (= (point) 3))      ; after `n''
    (forward-sexp)
    (should (= (point) (point-max)))))


;; ---------------------------------------------------------------------
;; Step 2: font-lock
;; ---------------------------------------------------------------------

(defun deduce-mode-test--face-at (target text)
  "Return the `face' text property at the start of TARGET in TEXT,
after `deduce-mode' font-locking.  Returns nil if TARGET isn't
found or if the position has no face property."
  (with-temp-buffer
    (insert text)
    (deduce-mode)
    (font-lock-ensure)
    (goto-char (point-min))
    (when (search-forward target nil t)
      (get-text-property (match-beginning 0) 'face))))


(ert-deftest deduce-mode/keyword-theorem-gets-keyword-face ()
  (should (eq (deduce-mode-test--face-at
               "theorem"
               "theorem t: true\nproof\n  .\nend\n")
              'font-lock-keyword-face)))


(ert-deftest deduce-mode/keyword-proof-gets-keyword-face ()
  (should (eq (deduce-mode-test--face-at
               "proof"
               "theorem t: true\nproof\n  .\nend\n")
              'font-lock-keyword-face)))


(ert-deftest deduce-mode/keyword-arbitrary-gets-keyword-face ()
  (should (eq (deduce-mode-test--face-at
               "arbitrary"
               "theorem t: all P:bool. P\nproof\n  arbitrary P:bool\n  ?\nend\n")
              'font-lock-keyword-face)))


(ert-deftest deduce-mode/constant-true-gets-constant-face ()
  (should (eq (deduce-mode-test--face-at
               "true"
               "theorem t: true\n")
              'font-lock-constant-face)))


(ert-deftest deduce-mode/constant-false-gets-constant-face ()
  (should (eq (deduce-mode-test--face-at
               "false"
               "theorem t: false\n")
              'font-lock-constant-face)))


(ert-deftest deduce-mode/integer-literal-gets-constant-face ()
  (should (eq (deduce-mode-test--face-at
               "42"
               "define x: bool = 42 = 42\n")
              'font-lock-constant-face)))


(ert-deftest deduce-mode/builtin-type-bool-gets-type-face ()
  (should (eq (deduce-mode-test--face-at
               "bool"
               "define x: bool = true\n")
              'font-lock-type-face)))


(ert-deftest deduce-mode/capitalized-identifier-gets-type-face ()
  "User-defined types and constructors (capitalized identifiers)
should be type-faced."
  (should (eq (deduce-mode-test--face-at
               "Nat"
               "import Nat\n")
              'font-lock-type-face))
  (should (eq (deduce-mode-test--face-at
               "Color"
               "union Color {\n  Red\n}\n")
              'font-lock-type-face)))


(ert-deftest deduce-mode/type-arguments-each-get-type-face ()
  "`Option<Pos>' parses as three tokens, not one symbol -- the type
parameters should each be picked up by the capitalized-identifier
rule.  Regression test for an early bug where `<' and `>' were
symbol-class and swallowed the symbol boundary, leaving `Option'
and `Pos' default-faced inside `Foo<Bar>'."
  (with-temp-buffer
    (insert "recursive nat2pos(Nat) -> Option<Pos> {\n  ?\n}\n")
    (deduce-mode)
    (font-lock-ensure)
    ;; case-fold-search defaults to t, which would let `search-forward
    ;; "Nat"' match `nat' inside `nat2pos'. Bind it nil so we land on
    ;; the capitalized occurrence.
    (let ((case-fold-search nil))
      (dolist (name '("Nat" "Option" "Pos"))
        (goto-char (point-min))
        (should (search-forward name nil t))
        (goto-char (match-beginning 0))
        (should (eq (get-text-property (point) 'face)
                    'font-lock-type-face))))))


(ert-deftest deduce-mode/standalone-question-mark-gets-warning-face ()
  "A standalone `?' (proof hole) should be warning-faced."
  (should (eq (deduce-mode-test--face-at
               "?"
               "theorem t: true\nproof\n  ?\nend\n")
              'font-lock-warning-face)))


(ert-deftest deduce-mode/sorry-gets-warning-face ()
  (should (eq (deduce-mode-test--face-at
               "sorry"
               "theorem t: true\nproof\n  sorry\nend\n")
              'font-lock-warning-face)))


(ert-deftest deduce-mode/question-mark-inside-identifier-not-warning ()
  "The `?' in `done?' is part of the identifier, not a hole, and
should not be warning-faced."
  (with-temp-buffer
    (insert "define done?: bool = true\n")
    (deduce-mode)
    (font-lock-ensure)
    (goto-char (point-min))
    (search-forward "done?")
    ;; Move to the `?' character itself.
    (backward-char)
    (should-not (eq (get-text-property (point) 'face)
                    'font-lock-warning-face))))


(ert-deftest deduce-mode/keyword-not-matched-inside-identifier ()
  "`theoremish' should NOT be highlighted as `theorem' followed by
trailing characters: symbol boundaries protect against that."
  (with-temp-buffer
    (insert "define theoremish: bool = true\n")
    (deduce-mode)
    (font-lock-ensure)
    (goto-char (point-min))
    (search-forward "theoremish")
    (goto-char (match-beginning 0))
    (should-not (eq (get-text-property (point) 'face)
                    'font-lock-keyword-face))))


(ert-deftest deduce-mode/keywords-inside-comments-not-highlighted ()
  "Keywords inside line and block comments should not be highlighted."
  (with-temp-buffer
    (insert "// theorem t: true\n/* theorem t: true */\n")
    (deduce-mode)
    (font-lock-ensure)
    (goto-char (point-min))
    (search-forward "theorem")
    (goto-char (match-beginning 0))
    (should (eq (get-text-property (point) 'face)
                'font-lock-comment-face))
    (search-forward "theorem")
    (goto-char (match-beginning 0))
    (should (eq (get-text-property (point) 'face)
                'font-lock-comment-face))))


(provide 'deduce-mode-test)

;;; deduce-mode-test.el ends here
