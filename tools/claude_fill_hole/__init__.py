"""Claude hole-fill sidecar for the Deduce LSP.

A standalone Python program that reads a hole-fill request on stdin,
calls Claude with a manual tool-use loop, and writes a validated
proof on stdout. See docs/hole-fill-plan.md and README.md.
"""
