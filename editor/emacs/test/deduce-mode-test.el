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


(provide 'deduce-mode-test)

;;; deduce-mode-test.el ends here
