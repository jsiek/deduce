#!/bin/sh
# Start the Deduce MCP server (registered in .mcp.json) from the checkout
# root, with the first Python that has the `mcp` package: the checkout's
# .venv, the main checkout's .venv (a git worktree has none of its own),
# or python3 on PATH. If none has it, python3's import error is reported.
main=$(dirname "$(git rev-parse --path-format=absolute --git-common-dir 2>/dev/null)")
for py in .venv/bin/python "$main/.venv/bin/python" python3; do
  "$py" -c 'import mcp' 2>/dev/null && exec "$py" -m lsp.mcp_server
done
exec python3 -m lsp.mcp_server
