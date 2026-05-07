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

;; ---------------------------------------------------------------------
;; Font-lock (Step 2)
;; ---------------------------------------------------------------------
;;
;; Keyword categorization is based on the actual `Deduce.lark` grammar,
;; not a guess.  All quoted lowercase tokens in the grammar become
;; keywords; `true' / `false' become constants; `bool' / `type' (the
;; built-in kind) become types; `sorry' and a standalone `?' become
;; warning-faced.  Capitalized identifiers (constructors, type names
;; like `Nat' or `List') are heuristically rendered as type-face.
;;
;; If `Deduce.lark' grows a new keyword, append it to one of the lists
;; below -- nothing else needs to change.

(defconst deduce-mode--keywords
  '(;; declaration / structure
    "theorem" "lemma" "postulate" "define" "recursive" "recfun"
    "union" "inductive" "predicate" "relation" "import" "export"
    "module" "auto" "assert" "print" "operator" "associative"
    "terminates" "measure" "trace" "generic" "fun" "λ"
    ;; visibility
    "public" "private" "opaque"
    ;; proof structure
    "proof" "end" "case" "cases" "with" "where"
    ;; tactics
    "arbitrary" "assume" "suppose" "have" "show" "obtain" "from" "for"
    "induction" "rule" "inversion" "switch" "replace" "expand"
    "evaluate" "simplify" "equations" "recall" "reflexive" "symmetric"
    "transitive" "injective" "extensionality" "apply" "to" "conclude"
    "conjunct" "contradict" "suffices" "choose" "stop" "help" "by" "of"
    ;; logical / control
    "if" "then" "else" "all" "some" "in"
    "not" "and" "or" "iff"
    ;; built-in operators / forms
    "fn" "array")
  "Deduce keywords highlighted with `font-lock-keyword-face'.")

(defconst deduce-mode--constants
  '("true" "false")
  "Deduce literal constants highlighted with `font-lock-constant-face'.")

(defconst deduce-mode--types
  '("bool" "type")
  "Built-in Deduce type-level identifiers highlighted with
`font-lock-type-face'.  User-defined types (capitalized
identifiers) are caught by a separate rule.")

(defconst deduce-mode--warnings
  '("sorry")
  "Words highlighted with `font-lock-warning-face' to draw the eye
to incomplete proofs.  Standalone `?' is matched separately.")

(defun deduce-mode--symbol-regexp (words)
  "Build a `\\_<...\\_>' alternation from WORDS.

Symbol boundaries (rather than word boundaries) ensure that
`theorem' inside an identifier like `theorem1?' is not
mis-highlighted: identifier-trailing characters `'', `?', `!'
are symbol-class in our syntax table, so the boundary fires only
at true symbol edges."
  (concat "\\_<" (regexp-opt words t) "\\_>"))

(defvar deduce-mode-font-lock-keywords
  ;; Order matters: the first rule that matches a span sets the face,
  ;; and later rules don't override unless told to.  We put the most
  ;; specific (warning-face) first.
  `(;; Standalone `?' as a proof hole.  Symbol boundaries skip the `?'
    ;; inside identifiers like `done?'.
    ("\\_<\\?\\_>" 0 font-lock-warning-face)
    ;; Other warning-face words (currently just `sorry').
    (,(deduce-mode--symbol-regexp deduce-mode--warnings)
     0 font-lock-warning-face)
    ;; Built-in constants: `true', `false'.
    (,(deduce-mode--symbol-regexp deduce-mode--constants)
     0 font-lock-constant-face)
    ;; Integer / Nat literals.
    ("\\_<\\(?:ℕ\\)?[0-9]+\\_>" 0 font-lock-constant-face)
    ;; Built-in types: `bool', `type'.
    (,(deduce-mode--symbol-regexp deduce-mode--types)
     0 font-lock-type-face)
    ;; All Deduce keywords.
    (,(deduce-mode--symbol-regexp deduce-mode--keywords)
     0 font-lock-keyword-face)
    ;; Capitalized identifiers (user-defined types and constructors).
    ;; ASCII only for now; subscripted variants like `Nat₁' fall
    ;; through to default face -- revisit if it comes up.
    ("\\_<[A-Z][[:alnum:]_]*\\_>" 0 font-lock-type-face))
  "Font-lock keywords for `deduce-mode'.")


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
  (setq-local comment-use-syntax t)
  ;; Font-lock: keyword highlighting (Step 2).  No multi-line
  ;; constructs need special treatment yet, so the default
  ;; defaults tuple is sufficient.
  (setq-local font-lock-defaults '(deduce-mode-font-lock-keywords)))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.pf\\'" . deduce-mode))

(provide 'deduce-mode)

;;; deduce-mode.el ends here
