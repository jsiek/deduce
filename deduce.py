from error import set_verbose, get_verbose, set_unique_names, get_unique_names
from proof_checker import check_deduce, uniquify_deduce
from abstract_syntax import init_import_directories, add_import_directory, print_theorems, get_recursive_descent, set_recursive_descent, get_uniquified_modules, add_uniquified_module, VerboseLevel
from signal import signal, SIGINT
import sys
import os
import parser
import rec_desc_parser
#from parser import parse, set_filename, get_filename, set_deduce_directory, init_parser
#from rec_desc_parser import parse, set_filename, get_filename, set_deduce_directory, init_parser
import traceback
from pathlib import Path

traceback_flag = False
suppress_theorems = False

def handle_sigint(signal, stack_frame):
    print('SIGINT caught, exiting...')
    exit(137)

def deduce_file(filename, error_expected):
    if get_verbose():
        print("Deducing file:", filename)
    module_name = Path(filename).stem

    try:
    
        if module_name in get_uniquified_modules().keys():
            ast = get_uniquified_modules()[module_name]
        else:
            file = open(filename, 'r', encoding="utf-8")
            program_text = file.read()

            if get_verbose():
                print("about to parse")
            if get_recursive_descent():
                rec_desc_parser.set_deduce_directory(os.path.dirname(sys.argv[0]))
                rec_desc_parser.set_filename(filename)
                rec_desc_parser.init_parser()
                ast = rec_desc_parser.parse(program_text, trace=get_verbose(),
                                            error_expected=error_expected)
            else:
                parser.set_deduce_directory(os.path.dirname(sys.argv[0]))
                parser.set_filename(filename)
                parser.init_parser()
                ast = parser.parse(program_text, trace=get_verbose(),
                                   error_expected=error_expected)
            if get_verbose():
                print("abstract syntax tree:\n" \
                      +'\n'.join([str(s) for s in ast])+"\n\n")
                print("starting uniquify:\n" + '\n'.join([str(d) for d in ast]))
            uniquify_deduce(ast)
            if get_verbose():
                print("finished uniquify:\n" + '\n'.join([str(d) for d in ast]))
            add_uniquified_module(module_name, ast)

        check_deduce(ast, module_name)
        if error_expected:
            print('an error was expected in', filename, "but it was not caught")
            exit(-1)
        else:
            if not suppress_theorems:
                print_theorems(filename, ast)
            print(filename + ' is valid')

    except Exception as e:
        if error_expected:
            print(filename + ' caught an error as expected')
            # exit(0)
        else:
            print(str(e))
            # Use the following when debugging internal exceptions -Jeremy
            if traceback_flag:
                print(traceback.format_exc())
            # for production, exit
            exit(1)
            # during development, reraise
            # raise e

def deduce_directory(directory, recursive_directories):
    for file in os.listdir(directory):
        fpath = os.path.join(directory, file)
        if os.path.isfile(fpath):
            if file[-3:] == '.pf':
                deduce_file(fpath, error_expected)
        elif recursive_directories and os.path.isdir(fpath):
            deduce_directory(fpath, recursive_directories)

if __name__ == "__main__":
    signal(SIGINT, handle_sigint)
    # Check command line arguments

    if (sys.argv[0] == 'deduce.py'):
        sys.argv[0] = os.path.join(os.getcwd(), sys.argv[0])

    stdlib_dir = os.path.join(os.path.dirname(sys.argv[0]), 'lib/')
    add_stdlib = True
    deducables = []
    error_expected = False
    recursive_directories = False
    already_processed_next = False
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
        elif argument == '--traceback':
            traceback_flag = True
        elif argument == '--recursive-directories' or argument == '-r':
            recursive_directories = True
        elif argument == '--no-stdlib':
            add_stdlib = False
        elif argument == '--suppress-theorems':
            suppress_theorems = True
        elif argument == '--version' or argument == '-v':
            print("Deduce: version 1.2")
            exit(0)
        else:
            deducables.append(argument)
    
    if add_stdlib:
        add_import_directory(stdlib_dir)
    
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
        if os.path.isfile(deducable):
            deduce_file(deducable, error_expected)
        elif os.path.isdir(deducable):
            deduce_directory(deducable, recursive_directories)
        else:
            print(deducable, "was not found!")
            exit(1)
