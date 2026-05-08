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
  "Switching backend to openai-compat picks Qwen3-Coder-Next + OPENAI_API_KEY
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
      (should (member "Qwen3-Coder-Next" args))
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


(provide 'deduce-fill-hole-test)
;;; deduce-fill-hole-test.el ends here
