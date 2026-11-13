#!/bin/sh
# Start the Deduce MCP server (registered in .mcp.json) from the checkout
# root. Uses the checkout's .venv Python if there is one, else python3 on
# PATH. A git worktree has no .venv of its own, so also look in the main
# checkout.
main=$(dirname "$(git rev-parse --path-format=absolute --git-common-dir 2>/dev/null)")
for py in .venv/bin/python "$main/.venv/bin/python"; do
  [ -x "$py" ] && exec "$py" -m lsp.mcp_server
done
exec python3 -m lsp.mcp_server
