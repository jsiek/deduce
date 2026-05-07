;;; deduce-mode.el --- Major mode for Deduce proof files -*- lexical-binding: t; -*-

;; Copyright (C) 2026 Jeremy G. Siek and Deduce contributors
;; SPDX-License-Identifier: MIT

;; Author: Deduce contributors
;; Maintainer: Jeremy G. Siek
;; Version: 0.1.0
;; Package-Requires: ((emacs "29.1"))
;; Keywords: languages
;; URL: https://github.com/jsiek/deduce

;;; Commentary:

;; deduce-mode is a major mode for editing Deduce proof files (.pf).
;;
;; This is Step 1 of the Emacs mode plan (see docs/emacs-plan.md).
;; It establishes the major mode, comment syntax, and file
;; association.  Font-lock, indentation, and LSP integration are
;; layered on by later steps.
;;
;; Installation (Step 1 -- syntax highlighting and LSP land in
;; later commits):
;;
;;     (add-to-list 'load-path "/path/to/deduce/editor/emacs")
;;     (require 'deduce-mode)
;;
;; Files matching `\\.pf\\'' open in deduce-mode automatically.
;; `M-;' toggles a `//' line comment; `/* */' block comments are
;; recognized by the syntax engine.

;;; Code:

(defgroup deduce nil
  "Major mode for editing Deduce proof files."
  :prefix "deduce-"
  :group 'languages)


;; ---------------------------------------------------------------------
;; Syntax table
;; ---------------------------------------------------------------------
;;
;; Deduce comment syntax (verified against `Deduce.lark`):
;;
;;   //  ... \n      -- line comment
;;   /*  ...  */     -- block comment, non-nested
;;
;; Identifier characters include the usual letters/digits/underscore
;; plus subscript digits (₀-₉) and `!', `?', `'' as continuation
;; characters.  We mark only the ASCII identifier characters here;
;; the unicode subscripts default to symbol class which is fine for
;; word-motion purposes.

(defvar deduce-mode-syntax-table
  (let ((st (make-syntax-table)))
    ;; Comment markers.  `/' is the first character of `/*' (start
    ;; of style A), the fourth of `*/' (end of style A), and the
    ;; first of `//' (start of style B).  `*' is the second of
    ;; `/*' and the third of `*/'.  `\n' ends a style-B comment.
    (modify-syntax-entry ?/ ". 124b" st)
    (modify-syntax-entry ?* ". 23"   st)
    (modify-syntax-entry ?\n "> b"   st)

    ;; Underscore is part of identifiers.
    (modify-syntax-entry ?_ "w" st)
    ;; `?' and `'' appear inside identifiers in Deduce (e.g. `n'',
    ;; `done?').  Mark them as symbol so they don't break sexp
    ;; motion across an identifier.
    (modify-syntax-entry ?? "_" st)
    (modify-syntax-entry ?' "_" st)
    (modify-syntax-entry ?! "_" st)

    ;; Brackets pair up.  Deduce uses `(' / `)', `[' / `]', `{' / `}',
    ;; and `<' / `>' (for type-argument lists).  Pairing `<>' is
    ;; convenient for sexp navigation but interferes with `<', `>'
    ;; as comparison operators -- skip it for now and revisit if
    ;; users complain.
    (modify-syntax-entry ?\( "()" st)
    (modify-syntax-entry ?\) ")(" st)
    (modify-syntax-entry ?\[ "(]" st)
    (modify-syntax-entry ?\] ")[" st)
    (modify-syntax-entry ?\{ "(}" st)
    (modify-syntax-entry ?\} "){" st)

    st)
  "Syntax table for `deduce-mode'.")


;; ---------------------------------------------------------------------
;; Mode definition
;; ---------------------------------------------------------------------

;;;###autoload
(define-derived-mode deduce-mode prog-mode "Deduce"
  "Major mode for editing Deduce proof files.

Step 1 of the Emacs mode plan: comment syntax and file
association.  Font-lock and indentation are added in later
steps; LSP integration lives in `deduce-lsp.el'.

\\{deduce-mode-map}"
  :syntax-table deduce-mode-syntax-table
  ;; Comments: prefer `//' for `comment-dwim' since it round-trips
  ;; without picking an end delimiter.  Block comments still parse
  ;; correctly via the syntax table.
  (setq-local comment-start "// ")
  (setq-local comment-end "")
  (setq-local comment-start-skip "\\(?://+\\|/\\*+\\)\\s-*")
  (setq-local comment-end-skip "[ \t]*\\(?:\n\\|\\*+/\\)")
  ;; Use the syntax table's comment markers for `comment-region'
  ;; instead of `comment-padright'-derived ones.  Avoids the dwim
  ;; helper inserting `/*' '*/' around a single-line comment.
  (setq-local comment-use-syntax t))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.pf\\'" . deduce-mode))

(provide 'deduce-mode)

;;; deduce-mode.el ends here
