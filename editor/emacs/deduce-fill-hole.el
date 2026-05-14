;;; deduce-fill-hole.el --- Claude proof-completion for deduce-mode -*- lexical-binding: t; -*-

;; Copyright (C) 2026 Jeremy G. Siek and Deduce contributors
;; SPDX-License-Identifier: MIT

;; Author: Deduce contributors
;; Maintainer: Jeremy G. Siek
;; Version: 0.1.0
;; Package-Requires: ((emacs "29.1") (deduce-mode "0.1.0") (deduce-lsp "0.1.0"))
;; Keywords: languages
;; URL: https://github.com/jsiek/deduce

;;; Commentary:

;; Fill a `?' hole in a Deduce proof by asking the model.  Phase 3 of
;; the hole-fill plan (see docs/hole-fill-plan.md).
;;
;; The flow:
;;
;;   1. User places point on or just past a `?' and runs
;;      `M-x deduce-fill-hole' (or `C-c C-a').
;;   2. We issue `deduce/holeContextAt' synchronously to get goal +
;;      givens + lemmas + a stable fingerprint over them.
;;   3. We plant a marker pair around the hole's range, spawn the
;;      sidecar (`tools/claude_fill_hole') asynchronously, send the
;;      JSON request on stdin, and return -- emacs stays interactive
;;      while Claude works.
;;   4. On completion, the sentinel parses the sidecar's JSON
;;      response.  If the markers are still live and the fingerprint
;;      hasn't changed (hole hasn't moved or had its statement
;;      edited), the validated proof is spliced into the marker
;;      range.  Otherwise we error out with a clear message and
;;      leave the buffer untouched.
;;
;; Phase 3 / Step 7 only -- this is the MVP.  Step 8 polish
;; (cancellation, fallback buffer for stale-marker cases, mode-line
;; indicator) lands separately.

;;; Code:

(require 'cl-lib)
(require 'deduce-lsp)
(require 'json)
(require 'project)
(require 'subr-x)

;; eglot is built into Emacs 29+ but we declare its functions to keep
;; the byte-compiler quiet -- mirrors the pattern in deduce-lsp.el.
(declare-function eglot-current-server "eglot")


(defgroup deduce-fill-hole nil
  "Claude proof-completion for `deduce-mode'."
  :group 'deduce
  :prefix "deduce-fill-hole-")


(defcustom deduce-fill-hole-python-program "python3"
  "Python interpreter used to launch the hole-fill sidecar.

Defaults to whatever `python3' resolves to on PATH.  The sidecar
needs the `anthropic' Python package; see
`requirements-fill-hole.txt' at the deduce repo root."
  :type 'string
  :group 'deduce-fill-hole)


(defcustom deduce-fill-hole-deduce-root nil
  "Path to a Deduce repository checkout, or nil to inherit from
`deduce-lsp-deduce-root'.

The sidecar is invoked as `python3 -m tools.claude_fill_hole'
which needs `tools/claude_fill_hole/' on Python's import path.
When this variable is set we spawn the process under that
directory and add it to PYTHONPATH; when it's nil we fall back to
`deduce-lsp-deduce-root', and finally to the project root.

Mirrors the corresponding `deduce-lsp' knob so editor users with
proofs outside the deduce repo only have to set the path once."
  :type '(choice (const :tag "Inherit from deduce-lsp-deduce-root" nil)
                 (directory :tag "Deduce checkout"))
  :group 'deduce-fill-hole)


(defcustom deduce-fill-hole-max-attempts 5
  "Maximum number of `validate_proof' calls per fill-hole invocation.

Each attempt costs one model round-trip plus one `deduce.py'
invocation (warm: ~1s; cold: ~14s).  First valid proof wins, so
this is a ceiling -- typical successful runs use 1-3 attempts."
  :type 'integer
  :group 'deduce-fill-hole)


(defcustom deduce-fill-hole-backend 'anthropic
  "Which model backend the sidecar drives.

`anthropic' uses the Anthropic SDK (Claude models, requires an
ANTHROPIC_API_KEY).  `openai-compat' uses an OpenAI-compatible
HTTP endpoint -- works for IU REALLMs (set
`deduce-fill-hole-base-url' to
\"https://reallms.rescloud.iu.edu/direct/v1\"), real OpenAI
(leave the base URL unset), or local Ollama
(\"http://localhost:11434/v1\").

When you switch backends, you typically also want to update
`deduce-fill-hole-model' and `deduce-fill-hole-api-key-env' to
match.  Sensible defaults shift with this variable: setting it
to `openai-compat' makes the sidecar default to model
\"gemma-4-31B-it\" (a fast REALLMs model that scored well on
the hole-fill benchmark) and reads `OPENAI_API_KEY' if you
don't override the env var name."
  :type '(choice (const :tag "Anthropic API" anthropic)
                 (const :tag "OpenAI-compatible (REALLMs / OpenAI / Ollama)"
                        openai-compat))
  :group 'deduce-fill-hole)


(defcustom deduce-fill-hole-base-url nil
  "Base URL for the openai-compat backend, or nil for real OpenAI.

Examples:
  \"https://reallms.rescloud.iu.edu/direct/v1\"  -- IU REALLMs
  \"http://localhost:11434/v1\"                  -- local Ollama
  nil                                            -- api.openai.com (default)

Ignored when `deduce-fill-hole-backend' is `anthropic'."
  :type '(choice (const :tag "Real OpenAI (api.openai.com)" nil)
                 (string :tag "Custom base URL"))
  :group 'deduce-fill-hole)


(defcustom deduce-fill-hole-model nil
  "Model id the sidecar uses, or nil to pick a backend-appropriate default.

When nil, the default is `claude-opus-4-7' for
`deduce-fill-hole-backend' = `anthropic', or `gemma-4-31B-it'
for `openai-compat'.  When set explicitly, this overrides the
default.  Examples: `claude-sonnet-4-6' for cheaper Claude;
`gpt-oss-120b', `Qwen3-Coder-Next', or `llama-4-scout' for
REALLMs alternatives; `gpt-4o' or `gpt-5' for real OpenAI."
  :type '(choice (const :tag "Backend default" nil)
                 (string :tag "Model id"))
  :group 'deduce-fill-hole)


(defcustom deduce-fill-hole-api-key-env nil
  "Environment variable the sidecar reads for the API key, or nil for the default.

When nil, defaults to `ANTHROPIC_API_KEY' for the anthropic
backend or `OPENAI_API_KEY' for the openai-compat backend.  IU
users on REALLMs typically override to `REALLMS_API_KEY'.

The variable must already be exported in the emacs process'
environment (e.g. via `setenv', `exec-path-from-shell', or your
shell init).  When unset at run time, the sidecar exits with a
structured error and `deduce-fill-hole' surfaces it to you."
  :type '(choice (const :tag "Backend default" nil)
                 (string :tag "Custom env var name"))
  :group 'deduce-fill-hole)


(defcustom deduce-fill-hole-prelude-disabled nil
  "If non-nil, the sidecar invokes `deduce.py --no-stdlib'.

Mirrors `deduce-lsp-prelude-disabled'.  Useful when working on
`lib/' itself or on minimal fixtures where the prelude
bootstrap is unwanted overhead."
  :type 'boolean
  :group 'deduce-fill-hole)


(defcustom deduce-fill-hole-timeout 60
  "Per-validate-proof timeout in seconds passed to the sidecar.

The sidecar caps each `deduce.py' invocation at this many
seconds; on timeout the attempt is reported as a failure to the
model and the loop continues until the budget is exhausted."
  :type 'integer
  :group 'deduce-fill-hole)


;; ---------------------------------------------------------------------
;; Internal state -- in-flight sessions for the buffer-local fill-hole
;; ---------------------------------------------------------------------

(defvar-local deduce-fill-hole--sessions nil
  "In-flight hole-fill sessions for this buffer.

Each element is a plist describing one active request:

  :request-id    -- monotonically increasing integer for this buffer
  :process       -- the `make-process' handle
  :source-buffer -- the .pf buffer the user invoked from (where the
                    proof gets spliced).  Tracked separately because
                    `process-buffer' returns the *stdout* buffer
                    (since we set :buffer stdout-buffer on the process)
                    and we need to know which `.pf' buffer to apply to.
  :start-marker  -- marker at the hole's start position
  :end-marker    -- marker at the hole's end position (advance-on-insert)
  :fingerprint   -- the SHA-256 fingerprint captured at request time
  :stdout-buffer -- buffer accumulating sidecar stdout
  :stderr-buffer -- buffer accumulating sidecar stderr (NDJSON progress)

Multiple fills may run concurrently in the same buffer.  Each keeps
its own marker pair + fingerprint, so if one request applies first,
later results will fail the existing stale-marker check instead of
silently patching the wrong location.")


(defvar-local deduce-fill-hole--next-request-id 0
  "Next request id for `deduce-fill-hole--sessions' in this buffer.")


(defun deduce-fill-hole--allocate-request-id ()
  "Return a fresh request id for the current buffer."
  (setq deduce-fill-hole--next-request-id
        (1+ deduce-fill-hole--next-request-id)))


(defun deduce-fill-hole--register-session (session)
  "Add SESSION to the current buffer's in-flight session list."
  (push session deduce-fill-hole--sessions))


(defun deduce-fill-hole--drop-session (session)
  "Remove SESSION from the current buffer's in-flight session list."
  (setq deduce-fill-hole--sessions
        (delq session deduce-fill-hole--sessions)))


(defun deduce-fill-hole--effective-deduce-root ()
  "Return the best guess for the directory containing `tools/claude_fill_hole'.

Resolution order:
  1. `deduce-fill-hole-deduce-root', if set.
  2. `deduce-lsp-deduce-root', if set.
  3. The project root (via `project-current'), if any.
  4. `default-directory'.

The result is always an absolute path."
  (expand-file-name
   (or deduce-fill-hole-deduce-root
       deduce-lsp-deduce-root
       (let ((proj (project-current)))
         (and proj (project-root proj)))
       default-directory)))


(defun deduce-fill-hole-sidecar-command ()
  "Return the command list used to spawn the hole-fill sidecar.

Always wraps in `env PYTHONPATH=<root> ...' so `python -m
tools.claude_fill_hole' resolves regardless of the cwd emacs
hands to `make-process'.  The other CLI flags (`--max-attempts',
`--model', `--timeout', `--no-stdlib') are appended in
`deduce-fill-hole'."
  (let* ((root (deduce-fill-hole--effective-deduce-root))
         (env-bindings (list (format "PYTHONPATH=%s" root))))
    (append (cons "env" env-bindings)
            (list deduce-fill-hole-python-program
                  "-m" "tools.claude_fill_hole"))))


;; ---------------------------------------------------------------------
;; The synchronous holeContextAt round-trip
;; ---------------------------------------------------------------------

(defun deduce-fill-hole--hole-context ()
  "Issue `deduce/holeContextAt' at point and return the response plist.

Errors out when no eglot server is active or the cursor isn't on
a `?'.  Reuses `deduce-lsp--request' so pending didChange
notifications are flushed first -- otherwise the fingerprint we
compute now wouldn't match what the sidecar sees on validate."
  (let ((server (eglot-current-server)))
    (unless server
      (user-error "No eglot server active in this buffer; M-x eglot first"))
    (let* ((params (list :textDocument
                         (list :uri (deduce-lsp--current-uri))
                         :position (deduce-lsp--current-position)
                         :includeLemmas t))
           (response (deduce-lsp--request server :deduce/holeContextAt params)))
      (unless response
        (user-error
         "No hole at point.  Place point on a `?' and try again"))
      response)))


;; ---------------------------------------------------------------------
;; The async sidecar round-trip
;; ---------------------------------------------------------------------

(defun deduce-fill-hole--lsp-pos-to-point (line character)
  "Convert LSP 0-indexed (LINE CHARACTER) to a buffer point.

Mirrors `deduce-lsp--lsp-pos-to-point' (which is private to that
file) -- duplicated here so deduce-fill-hole doesn't depend on
internals of deduce-lsp."
  (save-excursion
    (goto-char (point-min))
    (forward-line line)
    (forward-char character)
    (point)))


(defun deduce-fill-hole--build-request (context)
  "Build the JSON payload to send the sidecar from CONTEXT.

CONTEXT is the response plist from `deduce/holeContextAt'.  We
augment it with the file path and the buffer's current content
(so unsaved edits are honoured) and serialise."
  (let* ((file-path
          (or buffer-file-name
              (user-error "Buffer is not visiting a file")))
         (payload
          (append context
                  (list :file file-path
                        :content (buffer-substring-no-properties
                                  (point-min) (point-max))))))
    ;; `json-encode' yields camelCase keys when we use plist syntax
    ;; with keyword keys (e.g. `:holeRange').  The schema on the
    ;; sidecar side accepts exactly that.
    (let ((json-encoding-pretty-print nil)
          (json-object-type 'plist))
      (json-encode payload))))


(defun deduce-fill-hole--make-stdout-buffer ()
  "Create a fresh hidden buffer for sidecar stdout."
  (generate-new-buffer " *deduce-fill-hole-stdout*"))


(defun deduce-fill-hole--make-stderr-buffer (request-buffer)
  "Create a hidden buffer for sidecar stderr (NDJSON progress).

Linked to REQUEST-BUFFER's name in case the user wants to inspect
progress while the sidecar runs.  The buffer is not displayed by
default; users can switch to it via `M-x switch-to-buffer'."
  (generate-new-buffer
   (format " *deduce-fill-hole-progress<%s>*"
           (buffer-name request-buffer))))


(defun deduce-fill-hole--cleanup (session)
  "Tear down SESSION's I/O buffers.

Does NOT nil the session's markers.  Markers are read by
`deduce-fill-hole--splice-proof', which runs after cleanup; if we
nilled them here, the splice's `(marker-position start-marker)'
check would always return nil and falsely report `hole moved while
the model was thinking'.  The markers become unreferenced once the
session plist is set to nil (in the sentinel) and GC reclaims them
on its own schedule -- explicit nil-ing is an optimization we
don't need."
  (when-let ((b (plist-get session :stdout-buffer)))
    (when (buffer-live-p b)
      (kill-buffer b)))
  (when-let ((b (plist-get session :stderr-buffer)))
    (when (buffer-live-p b)
      (kill-buffer b))))


(defun deduce-fill-hole--apply-result (session)
  "Parse SESSION's stdout buffer and splice the proof or error out.

Called from the process sentinel.  Performs the marker check
(both markers still live and pointing at our `?') and the
fingerprint check (re-issue `deduce/holeContextAt' and compare
fingerprints) before mutating the buffer.  On either check
failing, errors with a message that names the failure mode
without touching the source."
  (let* ((source-buffer (plist-get session :source-buffer))
         (stdout-buffer (plist-get session :stdout-buffer))
         (stderr-buffer (plist-get session :stderr-buffer))
         (process (plist-get session :process))
         (start-marker (plist-get session :start-marker))
         (end-marker (plist-get session :end-marker))
         (orig-fingerprint (plist-get session :fingerprint))
         (raw (when (buffer-live-p stdout-buffer)
                (with-current-buffer stdout-buffer
                  (buffer-substring-no-properties
                   (point-min) (point-max)))))
         (stderr-tail (when (buffer-live-p stderr-buffer)
                        (with-current-buffer stderr-buffer
                          (let ((all (buffer-substring-no-properties
                                      (point-min) (point-max))))
                            (if (> (length all) 2048)
                                (substring all (- (length all) 2048))
                              all)))))
         (exit-code (and (processp process) (process-exit-status process)))
         (source-alive (buffer-live-p source-buffer)))
    ;; Cleanup is destructive (kills the stdout/stderr buffers, clears
    ;; markers) so we read everything we need first.
    (deduce-fill-hole--cleanup session)
    (cond
     ((not source-alive)
      (message
       "deduce-fill-hole: source buffer was killed before result arrived"))
     (t
      (with-current-buffer source-buffer
        (deduce-fill-hole--drop-session session)
        (let* ((response (deduce-fill-hole--parse-response (or raw "")))
               (ok (plist-get response :ok))
               (proof (plist-get response :proof))
               (error-msg (plist-get response :error))
               (attempts (or (plist-get response :attempts) 0))
               (validations (plist-get response :validations))
               ;; If the sidecar wrote nothing on stdout it usually
               ;; crashed at import time or argparse rejected the
               ;; flags -- the actual diagnostic lives on stderr.
               ;; If it wrote a non-ok response with validation
               ;; attempts, surface those instead -- the user wants
               ;; to see what proofs the model tried and why each
               ;; failed.
               (no-stdout (or (null raw)
                              (string-empty-p (string-trim raw))))
               (debug-buf
                (cond
                 ((and no-stdout stderr-tail
                       (not (string-empty-p (string-trim stderr-tail))))
                  (deduce-fill-hole--stash-debug-output
                   stderr-tail exit-code))
                 ((and (not ok) validations
                       (> (length (or validations [])) 0))
                  (deduce-fill-hole--stash-validation-trace
                   error-msg attempts validations)))))
          (cond
           ((not ok)
            (if debug-buf
                (message
                 "deduce-fill-hole: %s (after %d attempt%s); see %s"
                 (or error-msg "no proof produced")
                 attempts
                 (if (= attempts 1) "" "s")
                 debug-buf)
              (message "deduce-fill-hole: %s (after %d attempt%s)"
                       (or error-msg "no proof produced")
                       attempts
                       (if (= attempts 1) "" "s"))))
           (t
            (deduce-fill-hole--splice-proof
             start-marker end-marker proof orig-fingerprint attempts)))))))))


(defconst deduce-fill-hole--debug-buffer-name "*deduce-fill-hole debug*"
  "Name of the buffer that captures sidecar stderr after an empty-stdout
failure.  Persistent across runs (each failure overwrites it) so the
user has somewhere stable to look.")


(defun deduce-fill-hole--stash-debug-output (stderr-tail exit-code)
  "Stash STDERR-TAIL into a debug buffer, return the buffer's name.

EXIT-CODE is the sidecar process's exit status (an integer or symbol
like `signal').  Used as a header so the user can see at a glance
whether the sidecar crashed (non-zero exit), was killed (signal),
or completed but somehow produced no stdout."
  (let ((buf (get-buffer-create deduce-fill-hole--debug-buffer-name)))
    (with-current-buffer buf
      (let ((inhibit-read-only t))
        (read-only-mode 0)
        (erase-buffer)
        (insert (format "deduce-fill-hole sidecar exited with status: %s\n"
                        (or exit-code "?")))
        (insert "Stderr (last 2KB; NDJSON progress + any Python traceback):\n")
        (insert "----------------------------------------------------------\n")
        (insert stderr-tail)
        (unless (eq (char-before) ?\n) (insert "\n"))
        (goto-char (point-min)))
      (special-mode))
    (buffer-name buf)))


(defun deduce-fill-hole--stash-validation-trace
    (error-msg attempts validations)
  "Pretty-print the per-attempt validation trace into the debug buffer.

ERROR-MSG is the sidecar's top-level error string (e.g. \"budget
exhausted without a valid proof\").  ATTEMPTS is the count.
VALIDATIONS is the list of plists from `:validations' in the
response, each carrying `:attempt', `:ok', `:proofPreview', and
`:errorTail'.

The trace is what the user actually needs when the model tried but
nothing validated -- proof previews so they can see what the model
thought to write, error tails so they can see why each was
rejected.  Returns the buffer's name."
  (let ((buf (get-buffer-create deduce-fill-hole--debug-buffer-name)))
    (with-current-buffer buf
      (let ((inhibit-read-only t))
        (read-only-mode 0)
        (erase-buffer)
        (insert (format "deduce-fill-hole: %s (%d attempt%s)\n"
                        (or error-msg "no proof produced")
                        attempts
                        (if (= attempts 1) "" "s")))
        (insert "================================================================\n")
        (let ((vlist (if (vectorp validations)
                         (append validations nil)
                       validations)))
          (dolist (v vlist)
            (let ((n (plist-get v :attempt))
                  (ok (plist-get v :ok))
                  (preview (plist-get v :proofPreview))
                  (err (plist-get v :errorTail)))
              (insert (format "\n--- Attempt %s%s ---\n"
                              (or n "?")
                              (if ok "  [OK]" "")))
              (insert "Proof (first ~80 chars):\n")
              (insert (or preview "(empty)"))
              (unless (eq (char-before) ?\n) (insert "\n"))
              (when (and (not ok) err (not (string-empty-p err)))
                (insert "Checker error (last ~200 chars):\n")
                (insert err)
                (unless (eq (char-before) ?\n) (insert "\n"))))))
        (goto-char (point-min)))
      (special-mode))
    (buffer-name buf)))


(defun deduce-fill-hole--parse-response (raw)
  "Parse RAW as the sidecar's stdout JSON, or return an error plist.

The sidecar always emits a single JSON object.  Bad output
(crash, partial write) gets converted into an error plist with
`:ok' nil and a synthetic `:error' so the rest of the sentinel
doesn't have to special-case parse failures."
  (let ((trimmed (string-trim raw)))
    (cond
     ((string-empty-p trimmed)
      (list :ok nil :error "sidecar wrote no output" :attempts 0))
     (t
      (condition-case err
          (let ((json-object-type 'plist)
                (json-array-type 'list)
                (json-key-type 'keyword)
                (json-false nil)
                (json-null nil))
            (json-read-from-string trimmed))
        (error
         (list :ok nil
               :error (format "could not parse sidecar output: %s"
                              (error-message-string err))
               :attempts 0)))))))


(defun deduce-fill-hole--reindent-proof (proof column)
  "Return PROOF with each line after the first prefixed by COLUMN spaces.

The model emits proof text without knowing the column the `?'
sits at, so a multi-line response lands with the first line at
the hole's column (correct) and every following line at column 0
(wrong).  We re-indent to match the hole's column so the splice
lines up with the surrounding source.  If the model already
prefixed lines with whitespace (mirroring the excerpt's
indentation), strip a common leading-whitespace prefix from the
follow-on lines first so we don't double-indent."
  (let* ((lines (split-string proof "\n"))
         (first (car lines))
         (rest (cdr lines)))
    (if (null rest)
        proof
      (let* ((non-blank (seq-filter
                         (lambda (l) (not (string-match-p "\\`[ \t]*\\'" l)))
                         rest))
             (common (deduce-fill-hole--common-leading-whitespace non-blank))
             (strip (length common))
             (pad (make-string column ?\s))
             (rest-fixed
              (mapcar (lambda (l)
                        (cond
                         ;; Blank lines stay blank -- don't pad trailing
                         ;; whitespace onto an otherwise-empty line.
                         ((string-match-p "\\`[ \t]*\\'" l) "")
                         ((and (> strip 0)
                               (>= (length l) strip)
                               (string= (substring l 0 strip) common))
                          (concat pad (substring l strip)))
                         (t (concat pad l))))
                      rest)))
        (mapconcat #'identity (cons first rest-fixed) "\n")))))


(defun deduce-fill-hole--common-leading-whitespace (lines)
  "Return the longest leading-whitespace prefix shared by LINES.

Used by `deduce-fill-hole--reindent-proof' to detect the model's
own indentation so it can be stripped before re-indenting to the
hole's column.  Returns the empty string when LINES is empty or
no shared prefix exists."
  (if (null lines)
      ""
    (let ((prefix (progn
                    (string-match "\\`\\([ \t]*\\)" (car lines))
                    (match-string 1 (car lines)))))
      (dolist (line (cdr lines))
        (string-match "\\`\\([ \t]*\\)" line)
        (let ((this (match-string 1 line))
              (i 0)
              (lim (min (length prefix)
                        (length (match-string 1 line)))))
          (while (and (< i lim) (eq (aref prefix i) (aref this i)))
            (setq i (1+ i)))
          (setq prefix (substring prefix 0 i))))
      prefix)))


(defun deduce-fill-hole--splice-proof (start-marker end-marker proof
                                                    orig-fingerprint attempts)
  "Replace the marker range with PROOF after the marker + fingerprint check.

If the markers no longer live (file reverted, region deleted) or
the fingerprint at the marker's position differs from
ORIG-FINGERPRINT (theorem statement edited), errors out without
applying.  ATTEMPTS is the number of tries the sidecar took, used
in the success message."
  (unless (and (marker-position start-marker)
               (marker-position end-marker))
    (user-error
     "deduce-fill-hole: hole moved while the model was thinking"))
  ;; The text between the markers should still be exactly `?'; if
  ;; the user typed inside the hole, refuse.
  (let ((current (buffer-substring-no-properties
                  start-marker end-marker)))
    (unless (string= current "?")
      (user-error
       "deduce-fill-hole: hole edited while the model was thinking (now %S)"
       current)))
  ;; Re-query holeContextAt at the marker's position and compare
  ;; fingerprints.  Skips the check if eglot is no longer alive.
  (let ((server (eglot-current-server)))
    (when server
      (let* ((line (1- (line-number-at-pos start-marker)))
             (char (save-excursion
                     (goto-char start-marker)
                     (current-column)))
             (params (list :textDocument
                           (list :uri (deduce-lsp--current-uri))
                           :position (list :line line :character char)
                           :includeLemmas :json-false))
             (recheck (ignore-errors
                        (deduce-lsp--request
                         server :deduce/holeContextAt params))))
        (when (and recheck
                   (not (string= orig-fingerprint
                                 (plist-get recheck :fingerprint))))
          (user-error
           "deduce-fill-hole: hole context changed while the model was thinking")))))
  (save-excursion
    (goto-char start-marker)
    (let ((column (current-column)))
      (delete-region start-marker end-marker)
      (insert (deduce-fill-hole--reindent-proof proof column))))
  (message "deduce-fill-hole: filled in %d attempt%s"
           attempts (if (= attempts 1) "" "s")))


(defun deduce-fill-hole--sentinel (process _event)
  "Process sentinel: when PROCESS exits, apply its result to the buffer."
  (when (memq (process-status process) '(exit signal))
    (let ((session (process-get process 'deduce-fill-hole-session)))
      (when session
        (deduce-fill-hole--apply-result session)))))


(defun deduce-fill-hole--default-model ()
  "Return the model id appropriate for the current backend, when
`deduce-fill-hole-model' is nil."
  (pcase deduce-fill-hole-backend
    ('anthropic "claude-opus-4-7")
    ('openai-compat "gemma-4-31B-it")
    (_ "claude-opus-4-7")))


(defun deduce-fill-hole--effective-model ()
  "Return the model id that will be passed to the sidecar, honoring the
user's `deduce-fill-hole-model' override before falling back to the
backend default."
  (or deduce-fill-hole-model (deduce-fill-hole--default-model)))


(defun deduce-fill-hole--default-api-key-env ()
  "Return the env-var name appropriate for the current backend, when
`deduce-fill-hole-api-key-env' is nil."
  (pcase deduce-fill-hole-backend
    ('anthropic "ANTHROPIC_API_KEY")
    ('openai-compat "OPENAI_API_KEY")
    (_ "ANTHROPIC_API_KEY")))


(defun deduce-fill-hole--backend-flag ()
  "Return the `--backend' CLI value matching the customization variable.

The defcustom uses elisp symbols (`anthropic', `openai-compat')
for nicer customize UI; the sidecar takes hyphenated string flags."
  (pcase deduce-fill-hole-backend
    ('anthropic "anthropic")
    ('openai-compat "openai-compat")
    (sym (symbol-name sym))))


(defun deduce-fill-hole--build-cli-args ()
  "Return the CLI flag list for the current customization values."
  (let ((model (deduce-fill-hole--effective-model))
        (api-key-env (or deduce-fill-hole-api-key-env
                         (deduce-fill-hole--default-api-key-env))))
    (append (list "--backend" (deduce-fill-hole--backend-flag)
                  "--max-attempts" (number-to-string deduce-fill-hole-max-attempts)
                  "--model" model
                  "--timeout" (number-to-string deduce-fill-hole-timeout)
                  "--api-key-env" api-key-env
                  "--deduce-root" (deduce-fill-hole--effective-deduce-root))
            (when deduce-fill-hole-base-url
              (list "--base-url" deduce-fill-hole-base-url))
            (when deduce-fill-hole-prelude-disabled
              (list "--no-stdlib")))))


;; ---------------------------------------------------------------------
;; The interactive command
;; ---------------------------------------------------------------------

;;;###autoload
(defun deduce-fill-hole ()
  "Fill the `?' hole at point by asking the model.

Issues `deduce/holeContextAt' synchronously to capture the goal,
givens, lemmas in scope, and a stable fingerprint over them.
Plants markers around the hole's range, then spawns the sidecar
(`tools/claude_fill_hole') asynchronously to drive Claude through
a `validate_proof' loop -- first valid proof wins, up to
`deduce-fill-hole-max-attempts' tries.

Emacs stays interactive while the sidecar runs.  When it finishes
the sentinel verifies the markers are still live and the
fingerprint hasn't changed, then splices the validated proof in.
On stale marker or fingerprint mismatch, errors with a clear
message and leaves the buffer untouched.

Multiple fill-hole requests may run in parallel, including in the
same buffer.  Different buffers keep separate session lists."
  (interactive)
  (let* ((context (deduce-fill-hole--hole-context))
         (range (plist-get context :holeRange))
         (start (plist-get range :start))
         (end (plist-get range :end))
         (start-pt (deduce-fill-hole--lsp-pos-to-point
                    (plist-get start :line)
                    (plist-get start :character)))
         (end-pt (deduce-fill-hole--lsp-pos-to-point
                  (plist-get end :line)
                  (plist-get end :character)))
         (start-marker (copy-marker start-pt nil))   ; insertion-type nil
         (end-marker (copy-marker end-pt t))         ; advance on insert
         (fingerprint (or (plist-get context :fingerprint) ""))
         (request-id (deduce-fill-hole--allocate-request-id))
         (stdout-buffer (deduce-fill-hole--make-stdout-buffer))
         (stderr-buffer (deduce-fill-hole--make-stderr-buffer
                         (current-buffer)))
         (cmd (append (deduce-fill-hole-sidecar-command)
                      (deduce-fill-hole--build-cli-args)))
         (process
          (make-process
           :name (format "deduce-fill-hole<%d>" request-id)
           :buffer stdout-buffer
           :command cmd
           :connection-type 'pipe
           :stderr stderr-buffer
           :coding 'utf-8
           :noquery t
           :sentinel #'deduce-fill-hole--sentinel)))
    (let ((session (list :request-id request-id
                         :process process
                         :source-buffer (current-buffer)
                         :start-marker start-marker
                         :end-marker end-marker
                         :fingerprint fingerprint
                         :stdout-buffer stdout-buffer
                         :stderr-buffer stderr-buffer)))
      (process-put process 'deduce-fill-hole-session session)
      (deduce-fill-hole--register-session session))
    (process-send-string process
                         (deduce-fill-hole--build-request context))
    (process-send-eof process)
    (message "deduce-fill-hole[%d]: asking %s..."
             request-id
             (deduce-fill-hole--effective-model))))


;; Bind `C-c C-a' (ask AI) in `deduce-mode-map'.  Same rationale as
;; `deduce-lsp's bindings: the command depends on the LSP being
;; loaded, so the binding only makes sense once the user has opted
;; in via `(require 'deduce-fill-hole)'.
;;
;; Why `C-c C-a' rather than `C-c C-f': the simpler in-scope-given
;; matcher (`deduce-lsp-fill-from-given') already owns `C-c C-f'.
;; We pick `C-c C-a' for "ask AI" so the keystroke makes the
;; intent obvious.
(define-key deduce-mode-map (kbd "C-c C-a") #'deduce-fill-hole)


(provide 'deduce-fill-hole)

;;; deduce-fill-hole.el ends here
