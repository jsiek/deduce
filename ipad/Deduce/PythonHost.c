// Embeds CPython (BeeWare's Python.xcframework) and runs deduce_ipad.serve.
// Adapted from the iOS testbed that ships with the framework.

#include "PythonHost.h"
#include <Python/Python.h>
#include <stdio.h>
#include <unistd.h>

static int python_ready = 0;

static int fail(const char *what, PyStatus status) {
    fprintf(stderr, "deduce: %s: %s\n", what, status.err_msg ? status.err_msg : "?");
    return 1;
}

int deduce_python_serve(const char *resource_path, int read_fd, int write_fd) {
    char path[4096];
    PyPreConfig preconfig;
    PyConfig config;
    PyStatus status;

    PyPreConfig_InitIsolatedConfig(&preconfig);
    preconfig.utf8_mode = 1;
    status = Py_PreInitialize(&preconfig);
    if (PyStatus_Exception(status)) return fail("pre-initialize", status);

    PyConfig_InitIsolatedConfig(&config);
    config.buffered_stdio = 0;
    config.write_bytecode = 0;   // the signed bundle is read-only
    snprintf(path, sizeof path, "%s/python", resource_path);
    status = PyConfig_SetBytesString(&config, &config.home, path);
    if (PyStatus_Exception(status)) return fail("set home", status);
    status = Py_InitializeFromConfig(&config);
    PyConfig_Clear(&config);
    if (PyStatus_Exception(status)) return fail("initialize", status);

    snprintf(path, sizeof path, "%s/app", resource_path);
    if (chdir(path) != 0) {
        perror("deduce: chdir");
        return 1;
    }
    PyObject *sys_path = PySys_GetObject("path");  // borrowed
    PyObject *app = PyUnicode_FromString(path);
    PyList_Insert(sys_path, 0, app);
    Py_DECREF(app);

    snprintf(path, sizeof path, "%s/app_packages", resource_path);
    PyObject *site = PyImport_ImportModule("site");
    PyObject *added = site ? PyObject_CallMethod(site, "addsitedir", "s", path) : NULL;
    Py_XDECREF(added);
    Py_XDECREF(site);

    PyObject *host = PyImport_ImportModule("deduce_ipad");
    if (host == NULL) {
        PyErr_Print();
        return 1;
    }
    python_ready = 1;
    PyObject *result = PyObject_CallMethod(host, "serve", "ii", read_fd, write_fd);
    if (result == NULL) PyErr_Print();
    Py_XDECREF(result);
    Py_DECREF(host);
    return result == NULL;
}

int deduce_python_interrupt(void) {
    if (!python_ready) return 0;
    PyGILState_STATE gil = PyGILState_Ensure();
    int interrupted = 0;
    PyObject *host = PyImport_ImportModule("deduce_ipad");
    PyObject *result = host ? PyObject_CallMethod(host, "interrupt", NULL) : NULL;
    if (result == NULL) PyErr_Print();
    else interrupted = PyObject_IsTrue(result);
    Py_XDECREF(result);
    Py_XDECREF(host);
    PyGILState_Release(gil);
    return interrupted;
}
