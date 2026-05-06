from flags import *
from abstract_syntax import init_import_directories, add_import_directory, print_theorems, set_recursive_descent, VerboseLevel
from lsp.library import check_file
from signal import signal, SIGINT
import sys
import os
from pathlib import Path

traceback_flag = False
suppress_theorems = False

def handle_sigint(signal, stack_frame):
    print('SIGINT caught, exiting...')
    exit(137)

def deduce_file(filename, error_expected, tracing_functions, prelude: list[str] = []):
    """CLI wrapper around lsp.library.check_file.

    Translates CheckResult into the historical print/exit behavior so
    test-deduce.py and existing tooling keep working.
    """
    result = check_file(filename, tracing_functions=tracing_functions, prelude=prelude)
    if result.ok:
        if error_expected:
            print('an error was expected in', filename, "but it was not caught")
            exit(-1)
        if not suppress_theorems:
            print_theorems(filename, result.ast)
        print(filename + ' is valid')
    else:
        if error_expected:
            print(filename + ' caught an error as expected')
        else:
            print(result.error_message)
            if traceback_flag:
                print(result.error_traceback)
            exit(1)

def compile_file(filename: str, output: str, prelude: list[str],
                 no_prune: bool = False) -> None:
    """Compile a checked .pf file to a single .c source file.

    Pipeline: parse + uniquify + type-check via the existing front-end,
    then lower → closure-convert → (prune) → emit_c. The runtime in
    compiler/runtime/ supplies the matching deduce.h / deduce.c that
    callers must compile alongside the generated source.

    Pruning drops definitions not transitively reached from a `print`
    statement. Pass `no_prune=True` to keep every lowered decl in the
    output — useful when debugging an emitter issue on code the
    pruner would normally have removed.
    """
    from compiler import closure as _closure, emit_c, ir, lower
    from compiler import prune as _prune

    result = check_file(filename, tracing_functions=(), prelude=prelude)
    if not result.ok:
        print(result.error_message)
        if traceback_flag:
            print(result.error_traceback)
        exit(1)
    program = lower.lower_program(result.ast)
    ir.verify(program)
    program = _closure.closure_convert(program)
    ir.verify(program)
    if not no_prune:
        program = _prune.prune(program)
        ir.verify(program)
    src = emit_c.emit_program(program)
    if output == "-":
        sys.stdout.write(src)
    else:
        with open(output, "w", encoding="utf-8") as f:
            f.write(src)

def deduce_directory(directory, recursive_directories, tracing_functions, prelude: list[str] = []):
    for file in sorted(os.listdir(directory)):
        fpath = os.path.join(directory, file)
        if os.path.isfile(fpath):
            if file[-3:] == '.pf':
                deduce_file(fpath, error_expected, tracing_functions, prelude)
        elif recursive_directories and os.path.isdir(fpath):
            deduce_directory(fpath, recursive_directories, tracing_functions, prelude)
    
def check_in_prelude(deducable : str, stdlib_dir : str) -> bool:
    deducable_path = Path(deducable)
    stdlib_path = Path(stdlib_dir)
    if deducable_path.is_file():
        return deducable_path.parent.absolute() == stdlib_path
    elif deducable_path.is_dir():
        return deducable_path.absolute() == stdlib_path.absolute()
    else:
        # If the funciton reaches this point then the path does not exist
        # However, there is handling for that in another place
        # So return false
        return False

if __name__ == "__main__":
    signal(SIGINT, handle_sigint)
    # Check command line arguments

    if (sys.argv[0] == 'deduce.py'):
        sys.argv[0] = os.path.join(os.getcwd(), sys.argv[0])

    stdlib_dir = os.path.join(os.path.dirname(sys.argv[0]), 'lib')
    add_stdlib = True
    deducables = []
    tracing_functions = []
    error_expected = False
    recursive_directories = False
    already_processed_next = False
    compile_target = None
    compile_output = None
    no_prune = False
    init_import_directories()

    # TODO: Cleanup 
    # Adding parameters is easy and all but this looks REALLY ugly
    for i in range(1, len(sys.argv)):
        if already_processed_next:
            already_processed_next = False
            continue
    
        argument = sys.argv[i]
        if argument == '--error':
            error_expected = True
        elif argument == '--unique-names':
            set_unique_names(True)
        elif argument == '--verbose':
            if i + 1 < len(sys.argv) and sys.argv[i+1] == 'full':
              set_verbose(VerboseLevel.FULL)
              set_unique_names(True)
            else:
              set_verbose(VerboseLevel.CURR_ONLY)
        elif argument == '--dir' and i + 1 < len(sys.argv):
            if sys.argv[i + 1] == stdlib_dir:
                add_stdlib = False
            add_import_directory(sys.argv[i+1])
            already_processed_next = True
        elif argument == '--recursive-descent':
            set_recursive_descent(True)
        elif argument == '--lalr':
            set_recursive_descent(False)
        elif argument == '--quiet':
            set_quiet_mode(True)
        elif argument == '--trace':
            if i + 1 < len(sys.argv):
                tracing_functions.append(sys.argv[i+1])
            already_processed_next = True
        elif argument == '--traceback':
            traceback_flag = True
        elif argument == '--recursive-directories' or argument == '-r':
            recursive_directories = True
        elif argument == '--no-stdlib':
            add_stdlib = False
        elif argument == '--suppress-theorems':
            suppress_theorems = True
        elif argument == '--version' or argument == '-v':
            print("Deduce: version 1.3")
            exit(0)
        elif argument == '--no-check-imports':
            set_check_imports(False)
        elif argument == '--compile':
            compile_target = '__pending__'
        elif argument == '-o' and i + 1 < len(sys.argv):
            compile_output = sys.argv[i + 1]
            already_processed_next = True
        elif argument == '--no-prune':
            no_prune = True
        else:
            deducables.append(argument)
    
    prelude = []
    if add_stdlib:
        add_import_directory(stdlib_dir)
        # Find files in the prelude
        # For now we consider the entire stdlib the prelude
        for file in sorted(os.listdir(stdlib_dir)):
            if file.endswith('.pf'):
                prelude.append(file.removesuffix('.pf'))

    if len(deducables) == 0:
        print("Couldn't find a file to deduce!")
        exit(1)

    sys.setrecursionlimit(10000)
    # We can probably use a loop for some tail recursive functions
    # And even the non-tail recursive functions can be turned into a
    # loop by using an explicit stack.  But these alternatives would
    # hurt the readability of the code and increase the maintenance
    # burden. So when you hit the recursion limit, just bump the number
    # higher.

    # Start deducing

    for deducable in deducables:
        # If a file is in the prelude and we include the prelude
        # Then we'll process the file twice, hence using an empty "prelude"
        # For said file

        if check_in_prelude(deducable, stdlib_dir):
            deducable_prelude = []
        else:
            deducable_prelude = prelude

        if compile_target is not None:
            if not os.path.isfile(deducable):
                print(deducable, "was not found!")
                exit(1)
            out = compile_output if compile_output is not None \
                else os.path.splitext(deducable)[0] + ".c"
            compile_file(deducable, out, deducable_prelude, no_prune=no_prune)
        elif os.path.isfile(deducable):
            deduce_file(deducable, error_expected, tracing_functions, deducable_prelude)
        elif os.path.isdir(deducable):
            deduce_directory(deducable, recursive_directories, tracing_functions, deducable_prelude)
        else:
            print(deducable, "was not found!")
            exit(1)
