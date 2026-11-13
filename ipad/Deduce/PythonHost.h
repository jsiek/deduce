#ifndef PythonHost_h
#define PythonHost_h

/// Start the embedded interpreter and serve the Deduce LSP over the given
/// file descriptors. Blocks for the life of the server, so call it on a
/// dedicated thread with a large stack. Post-prelude snapshots are saved
/// in `cache_path` (#1217). Returns nonzero on failure.
int deduce_python_serve(const char *resource_path, const char *cache_path, int read_fd, int write_fd);

/// Cancel the check or request in progress, if any. Safe to call from any
/// thread once the server is running. Returns 1 if one was interrupted.
int deduce_python_interrupt(void);

#endif
