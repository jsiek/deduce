;;; deduce-fill-hole-test.el --- ert tests for deduce-fill-hole -*- lexical-binding: t; -*-

;; SPDX-License-Identifier: MIT

;;; Commentary:

;; Run with:
;;
;;     emacs --batch -L editor/emacs -L editor/emacs/test \
;;           -l deduce-fill-hole-test -f ert-run-tests-batch-and-exit
;;
;; The full end-to-end loop (sidecar subprocess, real LSP server,
;; real Anthropic API) is impractical to drive from a batch process.
;; These tests pin the pieces of `deduce-fill-hole.el' that live
;; entirely in Emacs Lisp: command construction, request payload
;; assembly, response parsing, marker handling, and the
;; deduce-root resolution priority.

;;; Code:

(require 'ert)
(require 'eglot)
(require 'deduce-mode)
(require 'deduce-lsp)
(require 'deduce-fill-hole)
(require 'json)


;; ---------------------------------------------------------------------
;; Sidecar command construction
;; ---------------------------------------------------------------------


(ert-deftest deduce-fill-hole/sidecar-command-default-uses-cwd ()
  "With both deduce-root vars nil, the command's PYTHONPATH points at
the current `default-directory'."
  (let ((deduce-fill-hole-deduce-root nil)
        (deduce-lsp-deduce-root nil)
        (deduce-fill-hole-python-program "python3")
        (default-directory "/tmp/some-dir/"))
    (let ((cmd (deduce-fill-hole-sidecar-command)))
      (should (equal (car cmd) "env"))
      (should (string-prefix-p "PYTHONPATH=" (cadr cmd)))
      (should (string-suffix-p "/some-dir/" (cadr cmd)))
      (should (equal (nthcdr 2 cmd)
                     '("python3" "-m" "tools.claude_fill_hole"))))))


(ert-deftest deduce-fill-hole/sidecar-command-with-explicit-root ()
  "Explicit `deduce-fill-hole-deduce-root' wins over everything."
  (let ((deduce-fill-hole-deduce-root "/opt/deduce")
        (deduce-lsp-deduce-root "/should/not/win")
        (deduce-fill-hole-python-program "python3")
        (default-directory "/tmp/"))
    (let ((cmd (deduce-fill-hole-sidecar-command)))
      (should (equal (cadr cmd) "PYTHONPATH=/opt/deduce")))))


(ert-deftest deduce-fill-hole/sidecar-command-falls-back-to-deduce-lsp-root ()
  "When deduce-fill-hole-deduce-root is nil, falls back to
deduce-lsp-deduce-root before defaulting to the cwd."
  (let ((deduce-fill-hole-deduce-root nil)
        (deduce-lsp-deduce-root "/opt/deduce-checkout")
        (deduce-fill-hole-python-program "python3")
        (default-directory "/tmp/"))
    (let ((cmd (deduce-fill-hole-sidecar-command)))
      (should (equal (cadr cmd) "PYTHONPATH=/opt/deduce-checkout")))))


(ert-deftest deduce-fill-hole/sidecar-command-respects-python-program ()
  "Customizing `deduce-fill-hole-python-program' swaps the interpreter
without disturbing the rest of the command shape."
  (let ((deduce-fill-hole-deduce-root "/opt/deduce")
        (deduce-lsp-deduce-root nil)
        (deduce-fill-hole-python-program "python3.13"))
    (let ((cmd (deduce-fill-hole-sidecar-command)))
      (should (equal (nthcdr 2 cmd)
                     '("python3.13" "-m" "tools.claude_fill_hole"))))))


(ert-deftest deduce-fill-hole/sidecar-command-expands-tilde ()
  "`~/...' in `deduce-fill-hole-deduce-root' expands to absolute path."
  (let ((deduce-fill-hole-deduce-root "~/deduce")
        (deduce-lsp-deduce-root nil)
        (deduce-fill-hole-python-program "python3"))
    (let ((cmd (deduce-fill-hole-sidecar-command)))
      (should (string-prefix-p "PYTHONPATH=/" (cadr cmd)))
      (should-not (string-match-p "~" (cadr cmd))))))


;; ---------------------------------------------------------------------
;; CLI argument construction
;; ---------------------------------------------------------------------


(ert-deftest deduce-fill-hole/build-cli-args-default ()
  "Default custom values produce the expected flag set, no --no-stdlib,
no --base-url (defaults to anthropic backend)."
  (let ((deduce-fill-hole-backend 'anthropic)
        (deduce-fill-hole-base-url nil)
        (deduce-fill-hole-max-attempts 5)
        (deduce-fill-hole-model nil)            ; -> backend default
        (deduce-fill-hole-timeout 60)
        (deduce-fill-hole-api-key-env nil)      ; -> backend default
        (deduce-fill-hole-prelude-disabled nil)
        (deduce-fill-hole-deduce-root "/opt/deduce")
        (deduce-lsp-deduce-root nil))
    (let ((args (deduce-fill-hole--build-cli-args)))
      (should (member "--backend" args))
      (should (member "anthropic" args))
      (should (member "--max-attempts" args))
      (should (member "5" args))
      (should (member "--model" args))
      (should (member "claude-opus-4-7" args)) ; the anthropic default
      (should (member "--timeout" args))
      (should (member "60" args))
      (should (member "--api-key-env" args))
      (should (member "ANTHROPIC_API_KEY" args)) ; the anthropic default
      (should (member "--deduce-root" args))
      (should (member "/opt/deduce" args))
      (should-not (member "--no-stdlib" args))
      (should-not (member "--base-url" args)))))


(ert-deftest deduce-fill-hole/build-cli-args-explicit-overrides-defaults ()
  "Explicit `deduce-fill-hole-model' / `deduce-fill-hole-api-key-env'
override the backend defaults."
  (let ((deduce-fill-hole-backend 'anthropic)
        (deduce-fill-hole-base-url nil)
        (deduce-fill-hole-max-attempts 5)
        (deduce-fill-hole-model "claude-sonnet-4-6")
        (deduce-fill-hole-timeout 60)
        (deduce-fill-hole-api-key-env "MY_KEY")
        (deduce-fill-hole-prelude-disabled nil)
        (deduce-fill-hole-deduce-root "/opt/deduce")
        (deduce-lsp-deduce-root nil))
    (let ((args (deduce-fill-hole--build-cli-args)))
      (should (member "claude-sonnet-4-6" args))
      (should (member "MY_KEY" args)))))


(ert-deftest deduce-fill-hole/build-cli-args-openai-compat-defaults ()
  "Switching backend to openai-compat picks gemma-4-31B-it + OPENAI_API_KEY
defaults; setting base-url adds --base-url."
  (let ((deduce-fill-hole-backend 'openai-compat)
        (deduce-fill-hole-base-url
         "https://reallms.rescloud.iu.edu/direct/v1")
        (deduce-fill-hole-max-attempts 5)
        (deduce-fill-hole-model nil)
        (deduce-fill-hole-timeout 60)
        (deduce-fill-hole-api-key-env nil)
        (deduce-fill-hole-prelude-disabled nil)
        (deduce-fill-hole-deduce-root "/opt/deduce")
        (deduce-lsp-deduce-root nil))
    (let ((args (deduce-fill-hole--build-cli-args)))
      (should (member "openai-compat" args))
      (should (member "gemma-4-31B-it" args))
      (should (member "OPENAI_API_KEY" args))
      (should (member "--base-url" args))
      (should (member "https://reallms.rescloud.iu.edu/direct/v1" args)))))


(ert-deftest deduce-fill-hole/build-cli-args-openai-compat-no-base-url ()
  "openai-compat with base-url nil omits --base-url (real-OpenAI path)."
  (let ((deduce-fill-hole-backend 'openai-compat)
        (deduce-fill-hole-base-url nil)
        (deduce-fill-hole-max-attempts 5)
        (deduce-fill-hole-model nil)
        (deduce-fill-hole-timeout 60)
        (deduce-fill-hole-api-key-env nil)
        (deduce-fill-hole-prelude-disabled nil)
        (deduce-fill-hole-deduce-root "/opt/deduce")
        (deduce-lsp-deduce-root nil))
    (let ((args (deduce-fill-hole--build-cli-args)))
      (should-not (member "--base-url" args)))))


(ert-deftest deduce-fill-hole/effective-model-uses-override ()
  "An explicit `deduce-fill-hole-model' wins over the backend default."
  (let ((deduce-fill-hole-backend 'anthropic)
        (deduce-fill-hole-model "claude-sonnet-4-6"))
    (should (equal (deduce-fill-hole--effective-model)
                   "claude-sonnet-4-6"))))


(ert-deftest deduce-fill-hole/effective-model-falls-back-to-backend-default ()
  "With `deduce-fill-hole-model' nil the helper picks the backend default."
  (let ((deduce-fill-hole-backend 'openai-compat)
        (deduce-fill-hole-model nil))
    (should (equal (deduce-fill-hole--effective-model)
                   "gemma-4-31B-it")))
  (let ((deduce-fill-hole-backend 'anthropic)
        (deduce-fill-hole-model nil))
    (should (equal (deduce-fill-hole--effective-model)
                   "claude-opus-4-7"))))


(ert-deftest deduce-fill-hole/build-cli-args-with-prelude-disabled ()
  "`deduce-fill-hole-prelude-disabled' adds --no-stdlib."
  (let ((deduce-fill-hole-backend 'anthropic)
        (deduce-fill-hole-base-url nil)
        (deduce-fill-hole-prelude-disabled t)
        (deduce-fill-hole-max-attempts 3)
        (deduce-fill-hole-model "claude-sonnet-4-6")
        (deduce-fill-hole-timeout 30)
        (deduce-fill-hole-deduce-root "/opt/deduce")
        (deduce-lsp-deduce-root nil)
        (deduce-fill-hole-api-key-env "ANTHROPIC_API_KEY"))
    (should (member "--no-stdlib" (deduce-fill-hole--build-cli-args)))))


;; ---------------------------------------------------------------------
;; Effective deduce-root resolution
;; ---------------------------------------------------------------------


(ert-deftest deduce-fill-hole/effective-deduce-root-priority ()
  "Resolution order: fill-hole var > lsp var > project root > cwd."
  (let ((deduce-fill-hole-deduce-root "/explicit")
        (deduce-lsp-deduce-root "/lsp")
        (default-directory "/tmp/"))
    (should (equal (deduce-fill-hole--effective-deduce-root) "/explicit")))
  (let ((deduce-fill-hole-deduce-root nil)
        (deduce-lsp-deduce-root "/lsp")
        (default-directory "/tmp/"))
    (should (equal (deduce-fill-hole--effective-deduce-root) "/lsp")))
  (let ((deduce-fill-hole-deduce-root nil)
        (deduce-lsp-deduce-root nil)
        (default-directory "/tmp/some-dir/"))
    (should (string-suffix-p "/some-dir/"
                             (deduce-fill-hole--effective-deduce-root)))))


;; ---------------------------------------------------------------------
;; Request payload assembly
;; ---------------------------------------------------------------------


(ert-deftest deduce-fill-hole/build-request-includes-file-and-content ()
  "`deduce-fill-hole--build-request' adds the buffer's file path and
its current content to the LSP-supplied context."
  (let ((tmp (make-temp-file "deduce-fill-hole-test" nil ".pf")))
    (unwind-protect
        (with-temp-buffer
          (setq buffer-file-name tmp)
          (insert "theorem t: true\nproof\n  ?\nend\n")
          (let* ((context
                  (list :holeRange
                        (list :start (list :line 2 :character 2)
                              :end (list :line 2 :character 3))
                        :goal "true"
                        :givens []
                        :lemmasInScope []
                        :fingerprint "fp"))
                 (raw (deduce-fill-hole--build-request context))
                 (json-object-type 'plist)
                 (json-array-type 'list)
                 (json-key-type 'keyword)
                 (decoded (json-read-from-string raw)))
            (should (equal (plist-get decoded :file) tmp))
            (should (equal (plist-get decoded :goal) "true"))
            (should (equal (plist-get decoded :fingerprint) "fp"))
            (should (string-match "theorem t: true"
                                  (plist-get decoded :content)))
            (should (string-match "?" (plist-get decoded :content)))))
      (delete-file tmp))))


(ert-deftest deduce-fill-hole/build-request-errors-without-file ()
  "Without `buffer-file-name', the request can't be built."
  (with-temp-buffer
    (insert "?")
    (should-error
     (deduce-fill-hole--build-request
      (list :holeRange
            (list :start (list :line 0 :character 0)
                  :end (list :line 0 :character 1))
            :goal "true"))
     :type 'user-error)))


;; ---------------------------------------------------------------------
;; Response parsing
;; ---------------------------------------------------------------------


(ert-deftest deduce-fill-hole/parse-response-success ()
  "An ok JSON response decodes to a plist with the expected fields."
  (let* ((raw "{\"ok\": true, \"proof\": \"reflexive\", \"attempts\": 2,
                \"fingerprint\": \"fp\", \"elapsedMs\": 100,
                \"model\": \"claude-opus-4-7\", \"validations\": []}")
         (response (deduce-fill-hole--parse-response raw)))
    (should (eq (plist-get response :ok) t))
    (should (equal (plist-get response :proof) "reflexive"))
    (should (= (plist-get response :attempts) 2))))


(ert-deftest deduce-fill-hole/parse-response-failure ()
  "A failure response carries `:ok' nil and an `:error' message."
  (let* ((raw "{\"ok\": false, \"error\": \"budget exhausted\",
                \"attempts\": 5, \"fingerprint\": \"fp\",
                \"elapsedMs\": 1000, \"model\": \"claude-opus-4-7\",
                \"validations\": []}")
         (response (deduce-fill-hole--parse-response raw)))
    (should (eq (plist-get response :ok) nil))
    (should (equal (plist-get response :error) "budget exhausted"))
    (should (= (plist-get response :attempts) 5))))


(ert-deftest deduce-fill-hole/parse-response-empty ()
  "Empty stdout is converted into a synthetic error plist."
  (let ((response (deduce-fill-hole--parse-response "")))
    (should (eq (plist-get response :ok) nil))
    (should (string-match-p "no output" (plist-get response :error)))))


(ert-deftest deduce-fill-hole/parse-response-malformed ()
  "Bad JSON is converted into a synthetic error plist."
  (let ((response (deduce-fill-hole--parse-response "not json {")))
    (should (eq (plist-get response :ok) nil))
    (should (string-match-p "could not parse" (plist-get response :error)))))


;; ---------------------------------------------------------------------
;; LSP position translation
;; ---------------------------------------------------------------------


(ert-deftest deduce-fill-hole/lsp-pos-to-point ()
  "LSP (line, character) lookups match buffer positions."
  (with-temp-buffer
    (insert "abc\ndef\nghi\n")
    ;; Line 0 character 0 -> point 1 (start of "abc").
    (should (= (deduce-fill-hole--lsp-pos-to-point 0 0) 1))
    ;; Line 1 character 0 -> point 5 (start of "def").
    (should (= (deduce-fill-hole--lsp-pos-to-point 1 0) 5))
    ;; Line 2 character 2 -> point 11 ("h" within "ghi").
    (should (= (deduce-fill-hole--lsp-pos-to-point 2 2) 11))))


;; ---------------------------------------------------------------------
;; Keybinding registration
;; ---------------------------------------------------------------------


(ert-deftest deduce-fill-hole/binding-installed ()
  "Loading deduce-fill-hole binds `C-c C-a' in `deduce-mode-map'."
  (should (eq (lookup-key deduce-mode-map (kbd "C-c C-a"))
              #'deduce-fill-hole)))


(ert-deftest deduce-fill-hole/does-not-shadow-fill-from-given ()
  "Loading `deduce-fill-hole' must NOT clobber `deduce-lsp's
`C-c C-f' (the simpler in-scope-given matcher) -- the two are
distinct features and live on distinct keystrokes."
  (should (eq (lookup-key deduce-mode-map (kbd "C-c C-f"))
              #'deduce-lsp-fill-from-given)))


;; ---------------------------------------------------------------------
;; Sentinel-path tests
;; ---------------------------------------------------------------------
;;
;; The sentinel runs after the sidecar exits.  Its job is to read
;; stdout/stderr, verify the source buffer hasn't been killed and the
;; markers still cover a live `?', then either splice the proof in or
;; surface a diagnostic to the user.  Three real bugs lived along this
;; path and weren't caught by the construction-only tests above:
;;
;;   - process-buffer returned the stdout buffer, not the source buffer
;;     (sentinel always thought source was killed).
;;   - cleanup nilled markers before splice could read them (sentinel
;;     always thought hole had moved).
;;   - empty-stdout failures and budget-exhausted failures both swallowed
;;     all diagnostic info, leaving "no output" / "budget exhausted"
;;     with no breadcrumb.
;;
;; These tests construct a plausible session, invoke
;; `deduce-fill-hole--apply-result' directly (no real subprocess), and
;; assert on the post-conditions: was the buffer mutated?  was the
;; *deduce-fill-hole debug* buffer populated?  did the right
;; `(current-message)' come out?


(defvar deduce-fill-hole-test--messages nil
  "List of formatted message strings captured by
`deduce-fill-hole-test--with-captured-messages'.  defvar'd so the
override-message lambda can resolve it dynamically -- a lexical
closure over a `let'-bound local doesn't survive `cl-letf''s
trampoline reliably across emacs versions.")


(defun deduce-fill-hole-test--capture-message (fmt &rest args)
  "Push the formatted message into `deduce-fill-hole-test--messages'."
  (push (apply #'format fmt args) deduce-fill-hole-test--messages)
  nil)


(defmacro deduce-fill-hole-test--with-captured-messages (&rest body)
  "Run BODY with `message' captured to a list, then return that list
in source order (oldest first).  Used because `current-message' is
unreliable in `emacs --batch' -- ert sees nil even after `(message
...)' has fired."
  (declare (indent 0) (debug t))
  `(let ((deduce-fill-hole-test--messages '()))
     (cl-letf (((symbol-function 'message)
                #'deduce-fill-hole-test--capture-message))
       ,@body)
     (nreverse deduce-fill-hole-test--messages)))


(defun deduce-fill-hole-test--make-session (source-buffer stdout-text stderr-text)
  "Build a session plist suitable for `deduce-fill-hole--apply-result'.

Hole markers cover the first `?' in SOURCE-BUFFER.  No real process
is started -- `apply-result' only reads :process via
`process-exit-status', which returns nil when :process is nil, and
that's fine for the diagnostic header."
  (let* ((qpos (with-current-buffer source-buffer
                 (goto-char (point-min))
                 (and (search-forward "?" nil t) (1- (point)))))
         ;; Markers cover exactly the `?' character: start AT the
         ;; `?', end one past.  Mirrors what production code plants
         ;; via copy-marker on lsp-pos-to-point output.
         (start (and qpos (copy-marker qpos nil)))
         (end (and qpos (copy-marker (1+ qpos) t)))
         (stdout-buf (generate-new-buffer " *test-stdout*"))
         (stderr-buf (generate-new-buffer " *test-stderr*")))
    (when stdout-text
      (with-current-buffer stdout-buf (insert stdout-text)))
    (when stderr-text
      (with-current-buffer stderr-buf (insert stderr-text)))
    (list :process nil
          :source-buffer source-buffer
          :start-marker start
          :end-marker end
          :fingerprint "test-fp"
          :stdout-buffer stdout-buf
          :stderr-buffer stderr-buf)))


(ert-deftest deduce-fill-hole/cleanup-does-not-nil-markers ()
  "Regression for the third sentinel bug: cleanup must NOT nil
markers, because splice-proof reads them after cleanup runs."
  (with-temp-buffer
    (insert "hello ? world")
    (let* ((session (deduce-fill-hole-test--make-session
                     (current-buffer) nil nil))
           (start (plist-get session :start-marker))
           (end (plist-get session :end-marker)))
      (should (markerp start))
      (should (marker-position start))
      (deduce-fill-hole--cleanup session)
      ;; After cleanup, the markers must still point at the hole --
      ;; otherwise splice-proof's `(unless (marker-position ...))'
      ;; check would always fire.
      (should (marker-position start))
      (should (marker-position end)))))


(ert-deftest deduce-fill-hole/sentinel-success-splices-proof ()
  "When stdout is `{ok: true, proof: ...}' and the buffer state
hasn't changed, the proof replaces the `?' and the user gets a
`filled in N attempts' message."
  (with-temp-buffer
    (insert "theorem t: bool = true\nproof\n  ?\nend\n")
    (let* ((source (current-buffer))
           (session (deduce-fill-hole-test--make-session
                     source
                     (concat "{\"ok\": true, \"proof\": \"reflexive\","
                             " \"attempts\": 1, \"fingerprint\": \"test-fp\","
                             " \"elapsedMs\": 100, \"model\": \"test\","
                             " \"validations\": []}")
                     nil)))
      (let ((msgs (deduce-fill-hole-test--with-captured-messages
                    (deduce-fill-hole--apply-result session))))
        (should (string-match-p "reflexive" (buffer-string)))
        (should-not (string-match-p "\\?" (buffer-string)))
        (should (cl-some (lambda (m) (string-match-p "filled in 1 attempt" m))
                         msgs))))))


(ert-deftest deduce-fill-hole/sentinel-validation-trace-populates-debug-buffer ()
  "When the sidecar reports ok=false with per-attempt validations,
the debug buffer is populated and the user is pointed at it."
  (when (get-buffer deduce-fill-hole--debug-buffer-name)
    (kill-buffer deduce-fill-hole--debug-buffer-name))
  (with-temp-buffer
    (insert "theorem t: bool = true\nproof\n  ?\nend\n")
    (let* ((source (current-buffer))
           (session (deduce-fill-hole-test--make-session
                     source
                     (concat "{\"ok\": false,"
                             " \"error\": \"budget exhausted\","
                             " \"attempts\": 2, \"fingerprint\": \"test-fp\","
                             " \"elapsedMs\": 100, \"model\": \"test\","
                             " \"validations\": ["
                             "  {\"attempt\": 1, \"ok\": false,"
                             "   \"proofPreview\": \"bad-proof-1\","
                             "   \"errorTail\": \"goal mismatch\"},"
                             "  {\"attempt\": 2, \"ok\": false,"
                             "   \"proofPreview\": \"bad-proof-2\","
                             "   \"errorTail\": \"undefined label\"}"
                             "]}")
                     nil)))
      (let ((msgs (deduce-fill-hole-test--with-captured-messages
                    (deduce-fill-hole--apply-result session))))
        ;; Buffer NOT mutated -- the `?' is still there.
        (should (string-match-p "\\?" (buffer-string)))
        (let ((buf (get-buffer deduce-fill-hole--debug-buffer-name)))
          (should buf)
          (with-current-buffer buf
            (let ((text (buffer-string)))
              (should (string-match-p "Attempt 1" text))
              (should (string-match-p "bad-proof-1" text))
              (should (string-match-p "goal mismatch" text))
              (should (string-match-p "Attempt 2" text))
              (should (string-match-p "bad-proof-2" text))
              (should (string-match-p "undefined label" text)))))
        (should (cl-some
                 (lambda (m) (string-match-p
                              (regexp-quote deduce-fill-hole--debug-buffer-name)
                              m))
                 msgs))))))


(ert-deftest deduce-fill-hole/sentinel-empty-stdout-stashes-stderr ()
  "When stdout is empty but stderr has content (sidecar crash case),
the debug buffer is populated with the stderr tail and the user is
pointed at it."
  (when (get-buffer deduce-fill-hole--debug-buffer-name)
    (kill-buffer deduce-fill-hole--debug-buffer-name))
  (with-temp-buffer
    (insert "theorem t: bool = true\nproof\n  ?\nend\n")
    (let* ((source (current-buffer))
           (session (deduce-fill-hole-test--make-session
                     source
                     ""
                     "Traceback (most recent call last):\n  ImportError: lark\n")))
      (let ((msgs (deduce-fill-hole-test--with-captured-messages
                    (deduce-fill-hole--apply-result session))))
        (let ((buf (get-buffer deduce-fill-hole--debug-buffer-name)))
          (should buf)
          (with-current-buffer buf
            (should (string-match-p "Traceback" (buffer-string)))
            (should (string-match-p "ImportError" (buffer-string)))))
        (should (cl-some
                 (lambda (m) (string-match-p
                              (regexp-quote deduce-fill-hole--debug-buffer-name)
                              m))
                 msgs))))))


(ert-deftest deduce-fill-hole/sentinel-handles-killed-source-buffer ()
  "If the user killed the source buffer while the model was
thinking, the sentinel must not raise -- just message the user."
  (let* ((source (generate-new-buffer "*test-source*"))
         session)
    (with-current-buffer source
      (insert "theorem t: bool = true\nproof\n  ?\nend\n")
      (setq session (deduce-fill-hole-test--make-session source
                                                         "{\"ok\": true, \"proof\": \"reflexive\", \"attempts\": 1, \"fingerprint\": \"test-fp\", \"elapsedMs\": 100, \"model\": \"test\", \"validations\": []}"
                                                         nil)))
    (kill-buffer source)
    (let ((msgs (deduce-fill-hole-test--with-captured-messages
                  (deduce-fill-hole--apply-result session))))
      (should (cl-some (lambda (m) (string-match-p "source buffer was killed" m))
                       msgs)))))


;; ---------------------------------------------------------------------
;; Multi-line proof re-indentation (issue #391)
;; ---------------------------------------------------------------------


(ert-deftest deduce-fill-hole/reindent-leaves-single-line-proofs-alone ()
  "A proof with no newline has no follow-on lines to indent."
  (should (equal (deduce-fill-hole--reindent-proof "reflexive" 2)
                 "reflexive")))


(ert-deftest deduce-fill-hole/reindent-pads-followon-lines-to-column ()
  "Lines after the first get prefixed by COLUMN spaces so the splice
lines up under the hole's indent."
  (should (equal (deduce-fill-hole--reindent-proof
                  "arbitrary x:Nat\nassume p: P x\np" 2)
                 "arbitrary x:Nat\n  assume p: P x\n  p")))


(ert-deftest deduce-fill-hole/reindent-strips-common-prefix-then-pads ()
  "When the model already indented its follow-on lines (mirroring the
excerpt), strip a common leading-whitespace prefix before padding."
  (should (equal (deduce-fill-hole--reindent-proof
                  "arbitrary x:Nat\n  assume p: P x\n  p" 4)
                 "arbitrary x:Nat\n    assume p: P x\n    p")))


(ert-deftest deduce-fill-hole/reindent-blank-lines-stay-blank ()
  "Blank follow-on lines must not collect trailing whitespace."
  (should (equal (deduce-fill-hole--reindent-proof
                  "arbitrary x:Nat\n\nassume p: P x" 2)
                 "arbitrary x:Nat\n\n  assume p: P x")))


(ert-deftest deduce-fill-hole/reindent-zero-column-is-noop ()
  "A hole at column 0 (theorems start there) needs no padding."
  (should (equal (deduce-fill-hole--reindent-proof
                  "arbitrary x:Nat\nassume p: P x" 0)
                 "arbitrary x:Nat\nassume p: P x")))


(ert-deftest deduce-fill-hole/sentinel-success-indents-multiline-proof ()
  "End-to-end: a multi-line proof from the sidecar gets each follow-on
line padded to the `?''s column when spliced into the buffer."
  (with-temp-buffer
    (insert "theorem t: bool = true\nproof\n  ?\nend\n")
    (let* ((source (current-buffer))
           (session (deduce-fill-hole-test--make-session
                     source
                     (concat "{\"ok\": true,"
                             " \"proof\": \"arbitrary x:Nat\\nassume p: P x\\np\","
                             " \"attempts\": 1, \"fingerprint\": \"test-fp\","
                             " \"elapsedMs\": 100, \"model\": \"test\","
                             " \"validations\": []}")
                     nil)))
      (deduce-fill-hole-test--with-captured-messages
        (deduce-fill-hole--apply-result session))
      (should (string-match-p
               "  arbitrary x:Nat\n  assume p: P x\n  p"
               (buffer-string))))))


(provide 'deduce-fill-hole-test)
;;; deduce-fill-hole-test.el ends here
