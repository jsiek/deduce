#ifndef PythonHost_h
#define PythonHost_h

/// Start the embedded interpreter and serve the Deduce LSP over the given
/// file descriptors. Blocks for the life of the server, so call it on a
/// dedicated thread with a large stack. Returns nonzero on failure.
int deduce_python_serve(const char *resource_path, int read_fd, int write_fd);

/// Cancel the check in progress, if any. Safe to call from any thread
/// once the server is running. Returns 1 if a check was interrupted.
int deduce_python_interrupt(void);

#endif
