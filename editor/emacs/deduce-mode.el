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
;; Indentation (Step 3)
;; ---------------------------------------------------------------------
;;
;; A simple custom `indent-line-function' rather than SMIE.  Deduce's
;; structure has two flavors of opener/closer:
;;
;;   * Bracket pairs: `{' / `}', `(' / `)', `[' / `]'.
;;   * Keyword pair:  `proof' / `end'.
;;
;; Rules at TAB / RET on a line:
;;
;;   1. If the line starts with `end', find the matching `proof' by
;;      depth-counting backward and align with `proof''s column.
;;   2. If the line starts with `}', `)', or `]', use Emacs's syntax
;;      engine (`backward-up-list') to find the opener's line and
;;      align with that line's first non-whitespace column.
;;   3. Otherwise, look at the previous non-blank, non-comment-only
;;      line.  If it ends with an opener (`proof', `{', `(', `['),
;;      indent one `deduce-mode-indent-offset' deeper than that
;;      line; otherwise match its indent.
;;
;; The rules cover the common Deduce shapes:
;;
;;   theorem t: ...   ; col 0
;;   proof            ; col 0
;;     arbitrary ...  ; col 2 (proof opens)
;;     induction Nat  ; col 2 (no opener, same as prev)
;;     case zero {    ; col 2 (no opener, same as prev)
;;       body         ; col 4 (`{' opens)
;;     }              ; col 2 (matches `case zero {' line)
;;     case suc(n) {  ; col 2
;;       ...
;;     }
;;   end              ; col 0 (matches `proof')
;;
;; Refinements (e.g. SMIE-grade alignment for multi-line type
;; signatures, smarter handling of `case' placement) can replace
;; this function later without changing the mode's interface.

(defcustom deduce-mode-indent-offset 2
  "Indentation step for `deduce-mode', in spaces."
  :type 'integer
  :group 'deduce
  :safe #'integerp)


(defun deduce-mode--line-starter ()
  "Return a symbol describing how the current line starts.

Possible values: `end' for the `end' keyword, `rbra' / `rpar' /
`rbrk' for `}', `)', `]', or nil for anything else."
  (save-excursion
    (back-to-indentation)
    (cond
     ((looking-at-p "\\_<end\\_>") 'end)
     ((eq (char-after) ?})        'rbra)
     ((eq (char-after) ?\))       'rpar)
     ((eq (char-after) ?\])       'rbrk))))


(defun deduce-mode--match-proof-for-end ()
  "Find the column of the `proof' keyword that matches the `end'
on the current line.  Returns the column, or nil if no match."
  (save-excursion
    (back-to-indentation)
    (let ((depth 1)
          (col nil))
      (while (and (> depth 0) (not (bobp)))
        (forward-line -1)
        (back-to-indentation)
        (cond
         ((looking-at-p "\\_<end\\_>")
          (setq depth (1+ depth)))
         ((looking-at-p "\\_<proof\\_>")
          (setq depth (1- depth))
          (when (zerop depth)
            (setq col (current-column))))))
      col)))


(defun deduce-mode--match-bracket-line-indent ()
  "Find the column of the line containing the opener for the
closing bracket on the current line.  Returns the column or nil."
  (save-excursion
    (back-to-indentation)
    (when (memq (char-after) '(?} ?\) ?\]))
      (forward-char 1)
      (condition-case nil
          (progn
            (backward-list)
            (back-to-indentation)
            (current-column))
        (scan-error nil)))))


(defun deduce-mode--prev-line-info ()
  "Move to the previous non-blank, non-comment-only line.
Return cons (INDENT . OPENS) where INDENT is its indent column
and OPENS is t if it ends with an opener (`proof', `{', `(', `[').
Returns nil if no such line exists above point."
  (save-excursion
    (let ((found nil))
      ;; `forward-line -1' returns 0 on success, nonzero (-N) when it
      ;; couldn't move that many lines (e.g. already at bobp).  Loop
      ;; until we either find a content line or run out of buffer.
      (while (and (not found) (zerop (forward-line -1)))
        (back-to-indentation)
        (unless (or (eolp)
                    (looking-at-p "\\(?://\\|/\\*\\)"))
          (setq found t)))
      (when found
        (let ((indent (current-column))
              (opens nil))
          (end-of-line)
          (skip-chars-backward " \t")
          (cond
           ((memq (char-before) '(?{ ?\( ?\[))
            (setq opens t))
           ((looking-back "\\_<proof\\_>"
                          (max (point-min) (- (point) 6)))
            (setq opens t)))
          (cons indent opens))))))


(defun deduce-mode-indent-line ()
  "Indent the current line for `deduce-mode'.

See the comment block above for the rules.  Bound to TAB and used
by `electric-indent-mode' on RET."
  (interactive)
  (let* ((closer (deduce-mode--line-starter))
         (target
          (cond
           ((eq closer 'end)
            (or (deduce-mode--match-proof-for-end) 0))
           ((memq closer '(rbra rpar rbrk))
            (or (deduce-mode--match-bracket-line-indent) 0))
           (t
            (let ((info (deduce-mode--prev-line-info)))
              (if info
                  (+ (car info)
                     (if (cdr info) deduce-mode-indent-offset 0))
                0)))))
         (point-was-at-or-before-indent
          (<= (current-column) (current-indentation))))
    (indent-line-to (max 0 target))
    (when point-was-at-or-before-indent
      (back-to-indentation))))


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


(defun deduce-mode--identifier-char-p (pos)
  "Return non-nil if POS is on a Deduce identifier character."
  (and (<= (point-min) pos)
       (< pos (point-max))
       (memq (char-syntax (char-after pos)) '(?w ?_))))

(defun deduce-mode--standalone-hole-at-p (pos)
  "Return non-nil if POS is a standalone proof hole."
  (and (eq (char-after pos) ??)
       (not (deduce-mode--identifier-char-p (1- pos)))
       (not (deduce-mode--identifier-char-p (1+ pos)))))

(defun deduce-mode--search-next-hole (limit)
  "Search forward for the next standalone proof hole before LIMIT."
  (let ((found nil))
    (while (and (not found)
                (search-forward "?" limit t))
      (when (deduce-mode--standalone-hole-at-p (1- (point)))
        (setq found t)))
    found))

(defun deduce-mode-next-hole ()
  "Move point to the next standalone `?' proof hole.

Search starts after point and wraps once at end of buffer."
  (interactive)
  (let ((start (point))
        found)
    (unless (eobp)
      (forward-char 1))
    (setq found (deduce-mode--search-next-hole nil))
    (unless found
      (goto-char (point-min))
      (setq found (deduce-mode--search-next-hole start)))
    (if found
        (goto-char (match-beginning 0))
      (goto-char start)
      (user-error "No proof hole found"))))


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

    ;; Operator chars Emacs's default syntax table marks as
    ;; symbol-class (or, for `%', word-class).  We need them
    ;; punctuation so they break symbol boundaries -- otherwise
    ;; `Option<Pos>' would parse as one symbol and `\_<...\_>'
    ;; couldn't match the inner identifiers.
    (dolist (c '(?+ ?- ?= ?< ?> ?& ?| ?%))
      (modify-syntax-entry c "." st))

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
  (setq-local font-lock-defaults '(deduce-mode-font-lock-keywords))
  ;; Indentation (Step 3).  TAB and (via electric-indent-mode) RET
  ;; both call this.
  (setq-local indent-line-function #'deduce-mode-indent-line))

(define-key deduce-mode-map (kbd "C-c C-n") #'deduce-mode-next-hole)

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.pf\\'" . deduce-mode))

(provide 'deduce-mode)

;;; deduce-mode.el ends here
