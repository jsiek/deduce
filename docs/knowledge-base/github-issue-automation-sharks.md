# GitHub issue automation on sharks

This workflow runs Codex on `sharks` instead of on a laptop. It is meant for
interactive but long-lived GitHub issue work: Codex can keep running in `tmux`
on `sharks`, continue after laptop disconnects, open draft PRs, and move on to
another issue as soon as a PR is created.

The scripts live on `sharks` under:

```bash
/u/jsiek/.codex/remote-automations/github-issue/
```

The important entry points are:

- `interactive.sh`: starts or attaches the issue supervisor.
- `pr-followup.sh <PR_NUMBER>`: resumes work on an existing PR.
- `pr-cleanup.sh <PR_NUMBER>`: manually cleans local state for a merged PR.

## Start the interactive supervisor

From the laptop:

```bash
ssh -t sharks-codex /u/jsiek/.codex/remote-automations/github-issue/interactive.sh
```

This attaches to a `tmux` session named `codex-github-issue`. Detach without
stopping anything:

```text
Ctrl-b d
```

Reconnect later with the same `ssh -t` command.

The supervisor keeps a manager window named `issue-manager`. It starts each
issue in its own `tmux` window and its own Git worktree under:

```bash
/var/tmp/jsiek/codex-github-issue/worktrees/<run-id>
```

The `issue-manager` window is the supervisor, not a Codex chat session. Codex
chat sessions are in dynamically named `issue-...` windows.

Codex runs with interactive approvals:

```bash
--sandbox workspace-write --ask-for-approval on-request --model gpt-5.5
```

## Issue loop

Each Codex issue window should work on exactly one issue. When Codex creates or
updates the draft PR for that issue, it writes a PR state file for the
supervisor. The supervisor records durable state at:

```bash
/var/tmp/jsiek/codex-github-issue/prs/pr-<number>.env
```

Then the supervisor immediately starts another issue in a fresh worktree. It
does not wait for the PR to merge.

The original PR window remains alive, so it can still be used for follow-up
requests while the supervisor starts new work elsewhere.

## Follow up on a PR

To ask Codex for changes on an existing PR:

```bash
ssh -t sharks-codex '/u/jsiek/.codex/remote-automations/github-issue/pr-followup.sh 959'
```

The follow-up launcher:

1. Starts or attaches a `tmux` session named `codex-pr-<PR_NUMBER>`.
2. Uses the recorded PR worktree when available.
3. Falls back to `/u/jsiek/deduce` for older PR records.
4. Looks for the original Codex thread ID in the PR state file or PR body.
5. Runs `codex resume <thread-id>` when possible.
6. Refreshes PR, branch, review, and diff context before making changes.

This gives the closest practical version of "put the request into the original
chat session" while still allowing the issue supervisor to continue picking new
issues.

## Cleanup after merge

Cleanup is normally automatic. While the supervisor is running, it periodically
calls:

```bash
/u/jsiek/.codex/remote-automations/github-issue/pr-cleanup.sh --all --quiet
```

The default cleanup interval is 300 seconds. Override it for a supervisor run
with:

```bash
GITHUB_ISSUE_CLEANUP_SECONDS=60 ssh -t sharks-codex /u/jsiek/.codex/remote-automations/github-issue/interactive.sh
```

Batch cleanup scans:

```bash
/var/tmp/jsiek/codex-github-issue/prs/pr-*.env
```

Open or closed-unmerged PRs are skipped. Merged PRs are cleaned by:

1. Verifying the PR is merged.
2. Removing the recorded worktree if it is clean.
3. Deleting the local PR branch when it is no longer checked out.
4. Deleting the remote PR branch if it still exists.
5. Archiving the PR state file under:

   ```bash
   /var/tmp/jsiek/codex-github-issue/archived-prs/
   ```

If cleanup finds a dirty worktree, it refuses to remove it automatically. After
inspecting the worktree, force cleanup manually only if the uncommitted state is
safe to discard:

```bash
ssh -t sharks-codex '/u/jsiek/.codex/remote-automations/github-issue/pr-cleanup.sh --force 959'
```

## GitHub and Git authentication

GitHub CLI auth on `sharks` is expected to use:

```bash
/u/jsiek/.config/gh/hosts.yml
```

Do not run `gh auth logout`, and do not replace the existing auth setup unless
the user explicitly asks.

SSH Git transport may fail on `sharks` even when GitHub CLI auth is working. If
Git over `git@github.com:jsiek/deduce.git` fails, use HTTPS Git transport with
the existing GitHub CLI credential helper instead of trying to repair SSH keys:

```bash
git -c 'credential.helper=!gh auth git-credential' \
  fetch https://github.com/jsiek/deduce.git main
```

Codex has narrow execpolicy rules on `sharks` that pre-approve HTTPS
`fetch`, `push`, and `ls-remote` commands for `https://github.com/jsiek/deduce.git`
when they use `credential.helper=!gh auth git-credential`. Direct
`gh auth git-credential get` is not pre-approved because it can print the token.

## Python and validation

The Deduce `Makefile` expects `python3.13`. On `sharks`, that command is a
wrapper under:

```bash
/u/jsiek/.local/bin/python3.13
```

It points at a Python 3.13 environment under:

```bash
/var/tmp/jsiek/codex-python313
```

This keeps Python, `ruff`, `mypy`, and their caches off NFS to avoid
`autofs_wait` hangs. Normal validation is:

```bash
make tests
```

## Useful state locations

- Automation memory:

  ```bash
  /u/jsiek/.codex/remote-automations/github-issue/memory.md
  ```

- Durable PR state:

  ```bash
  /var/tmp/jsiek/codex-github-issue/prs/pr-<number>.env
  ```

- Archived PR state:

  ```bash
  /var/tmp/jsiek/codex-github-issue/archived-prs/
  ```

- Per-issue worktrees:

  ```bash
  /var/tmp/jsiek/codex-github-issue/worktrees/
  ```

## Common recovery steps

List the supervisor windows:

```bash
ssh sharks-codex 'tmux list-windows -t codex-github-issue -F "#{window_index}:#{window_name}:#{window_active}:#{pane_title}"'
```

Attach to the supervisor:

```bash
ssh -t sharks-codex /u/jsiek/.codex/remote-automations/github-issue/interactive.sh
```

Attach directly to the `issue-manager` supervisor window:

```bash
ssh -t sharks-codex 'tmux attach -t codex-github-issue:issue-manager'
```

This window is useful for watching the issue loop, stopping the supervisor, or
diagnosing why a new issue did not start. It is not a Codex chat session.

Attach directly to a Codex chat window by first listing windows, then choosing
one of the dynamically named `issue-...` windows:

```bash
ssh -t sharks-codex 'tmux attach -t codex-github-issue:<ISSUE_WINDOW_NAME>'
```

If you are already attached to the `codex-github-issue` tmux session, switch to
the desired window with the tmux window list:

```text
Ctrl-b w
```

Select `issue-manager` for the supervisor, or an `issue-...` window for a Codex
chat, and press Enter. You can also jump by window name:

```text
Ctrl-b '
```

Type `issue-manager` or the `issue-...` window name and press Enter.

Follow up on a PR:

```bash
ssh -t sharks-codex '/u/jsiek/.codex/remote-automations/github-issue/pr-followup.sh <PR_NUMBER>'
```

Clean up a merged PR manually:

```bash
ssh -t sharks-codex '/u/jsiek/.codex/remote-automations/github-issue/pr-cleanup.sh <PR_NUMBER>'
```

Run batch cleanup manually:

```bash
ssh sharks-codex '/u/jsiek/.codex/remote-automations/github-issue/pr-cleanup.sh --all --quiet'
```

If the supervisor was updated while an old `tmux` session was already running,
restart that session or start a fresh session name so the updated script is
loaded.
