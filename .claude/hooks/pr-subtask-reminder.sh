#!/bin/bash
set -e
input=$(cat)
cmd=$(printf '%s' "$input" | jq -r '.tool_input.command // ""')
msg=""
if echo "$cmd" | grep -qE '(^|[[:space:]&|;])gh[[:space:]]+pr[[:space:]]+create([[:space:]]|$)'; then
  msg='REMINDER (gh pr create): If this PR addresses a multi-part issue (one with a sub-task checklist or GitHub sub-issues), do BOTH of the following: (1) In the PR title/body use "Addresses #N (X portion)" or "Refs #N" — NOT "Closes #N" / "Fixes #N", which auto-close the parent even when the body says "remains". (2) In the PR body, explicitly list which sub-tasks this PR completes and which remain. Skip this reminder if the PR fully resolves a single-task issue.'
elif echo "$cmd" | grep -qE '(^|[[:space:]&|;])gh[[:space:]]+pr[[:space:]]+merge([[:space:]]|$)'; then
  msg='REMINDER (gh pr merge): This PR was just merged. Identify the parent issue (the one whose sub-task this PR completed) and check its remaining sub-tasks via `gh issue view N`. Then: (a) If more sub-tasks remain — post a comment on the parent listing what is now done vs. what remains, AND remove the "in progress" label if present (`gh issue edit N --remove-label "in progress"`). (b) If this PR completed the LAST sub-task — close the parent issue (`gh issue close N`) with a closing comment summarizing the completed work. Skip entirely if the PR resolved a single-task issue (GitHub already auto-closed it).'
fi
if [ -n "$msg" ]; then
  jq -n --arg msg "$msg" '{hookSpecificOutput: {hookEventName: "PostToolUse", additionalContext: $msg}}'
fi
