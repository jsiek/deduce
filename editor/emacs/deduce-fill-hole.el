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
;; indicator, multiple concurrent sessions) lands separately.

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


(defcustom deduce-fill-hole-model "claude-opus-4-7"
  "Claude model the sidecar drives.

Default is `claude-opus-4-7', the most capable model.  For
cost-sensitive use, `claude-sonnet-4-6' is cheaper and still
strong at this kind of structured-output work.  The exact string
must match a real model id (see the `claude-api' skill's catalog
in the deduce repo for the up-to-date list)."
  :type 'string
  :group 'deduce-fill-hole)


(defcustom deduce-fill-hole-api-key-env "ANTHROPIC_API_KEY"
  "Environment variable the sidecar reads for the Anthropic API key.

The variable must already be exported in the emacs process'
environment (e.g. via `setenv', `exec-path-from-shell', or
your shell init).  When unset, the sidecar exits with a
structured error and `deduce-fill-hole' surfaces that to you."
  :type 'string
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
;; Internal state -- the active session for the buffer-local fill-hole
;; ---------------------------------------------------------------------

(defvar-local deduce-fill-hole--session nil
  "Active hole-fill session in this buffer, or nil.

When non-nil, this is a plist describing the in-flight request:

  :process       -- the `make-process' handle
  :start-marker  -- marker at the hole's start position
  :end-marker    -- marker at the hole's end position (advance-on-insert)
  :fingerprint   -- the SHA-256 fingerprint captured at request time
  :stdout-buffer -- buffer accumulating sidecar stdout
  :stderr-buffer -- buffer accumulating sidecar stderr (NDJSON progress)

Only one fill-hole can run per buffer at a time; a second
invocation while the first is in flight is rejected.  Buffer-local
so two different .pf buffers can each have their own session in
parallel (Step 8 polish).")


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
  "Clean up SESSION's markers, buffers, and process handle."
  (when-let ((m (plist-get session :start-marker)))
    (set-marker m nil))
  (when-let ((m (plist-get session :end-marker)))
    (set-marker m nil))
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
  (let* ((buffer (process-buffer (plist-get session :process)))
         (stdout-buffer (plist-get session :stdout-buffer))
         (start-marker (plist-get session :start-marker))
         (end-marker (plist-get session :end-marker))
         (orig-fingerprint (plist-get session :fingerprint))
         (raw (with-current-buffer stdout-buffer
                (buffer-substring-no-properties (point-min) (point-max)))))
    (deduce-fill-hole--cleanup session)
    (unless (buffer-live-p buffer)
      (user-error "Source buffer was killed before fill-hole completed"))
    (with-current-buffer buffer
      (when (eq deduce-fill-hole--session session)
        (setq deduce-fill-hole--session nil))
      (let* ((response (deduce-fill-hole--parse-response raw))
             (ok (plist-get response :ok))
             (proof (plist-get response :proof))
             (error-msg (plist-get response :error))
             (attempts (or (plist-get response :attempts) 0)))
        (cond
         ((not ok)
          (message "deduce-fill-hole: %s (after %d attempt%s)"
                   (or error-msg "no proof produced")
                   attempts
                   (if (= attempts 1) "" "s")))
         (t
          (deduce-fill-hole--splice-proof
           start-marker end-marker proof orig-fingerprint attempts)))))))


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
    (delete-region start-marker end-marker)
    (insert proof))
  (message "deduce-fill-hole: filled in %d attempt%s"
           attempts (if (= attempts 1) "" "s")))


(defun deduce-fill-hole--sentinel (process _event)
  "Process sentinel: when PROCESS exits, apply its result to the buffer."
  (when (memq (process-status process) '(exit signal))
    (let ((session (process-get process 'deduce-fill-hole-session)))
      (when session
        (deduce-fill-hole--apply-result session)))))


(defun deduce-fill-hole--build-cli-args ()
  "Return the CLI flag list for the current customization values."
  (append (list "--max-attempts" (number-to-string deduce-fill-hole-max-attempts)
                "--model" deduce-fill-hole-model
                "--timeout" (number-to-string deduce-fill-hole-timeout)
                "--api-key-env" deduce-fill-hole-api-key-env
                "--deduce-root" (deduce-fill-hole--effective-deduce-root))
          (when deduce-fill-hole-prelude-disabled
            (list "--no-stdlib"))))


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

Only one fill-hole per buffer at a time; a second invocation while
the first is in flight is rejected.  Different buffers can each
have their own session in parallel."
  (interactive)
  (when (and deduce-fill-hole--session
             (process-live-p (plist-get deduce-fill-hole--session :process)))
    (user-error
     "deduce-fill-hole: a fill-hole is already in progress in this buffer"))

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
         (stdout-buffer (deduce-fill-hole--make-stdout-buffer))
         (stderr-buffer (deduce-fill-hole--make-stderr-buffer
                         (current-buffer)))
         (cmd (append (deduce-fill-hole-sidecar-command)
                      (deduce-fill-hole--build-cli-args)))
         (process
          (make-process
           :name "deduce-fill-hole"
           :buffer stdout-buffer
           :command cmd
           :connection-type 'pipe
           :stderr stderr-buffer
           :coding 'utf-8
           :noquery t
           :sentinel #'deduce-fill-hole--sentinel)))
    (let ((session (list :process process
                         :start-marker start-marker
                         :end-marker end-marker
                         :fingerprint fingerprint
                         :stdout-buffer stdout-buffer
                         :stderr-buffer stderr-buffer)))
      (process-put process 'deduce-fill-hole-session session)
      (process-put process 'deduce-fill-hole-buffer (current-buffer))
      (setq deduce-fill-hole--session session))
    (process-send-string process
                         (deduce-fill-hole--build-request context))
    (process-send-eof process)
    (message "deduce-fill-hole: asking the model...")))


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
