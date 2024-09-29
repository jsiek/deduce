from error import set_verbose, get_verbose
from proof_checker import check_deduce, uniquify_deduce
from abstract_syntax import add_import_directory, print_theorems
import sys
import os
from parser import parse, set_filename, get_filename, set_deduce_directory, init_parser
import traceback

def deduce_file(filename, error_expected):
    file = open(filename, 'r', encoding="utf-8")
    program_text = file.read()
    set_filename(filename)
    try:
        if get_verbose():
            print("Deducing file:", filename)
            print("about to parse")
        ast = parse(program_text, trace=False, error_expected=error_expected)
        if get_verbose():
            print("starting uniquify:\n" + '\n'.join([str(d) for d in ast]))
        uniquify_deduce(ast)
        if get_verbose():
            print("finished uniquify:\n" + '\n'.join([str(d) for d in ast]))
        check_deduce(ast)
        if error_expected:
            print('an error was expected in', filename, "but it was not caught")
            exit(-1)
        else:
            print_theorems(filename, ast)
            print(filename + ' is valid')

    except Exception as e:
        if error_expected:
            print(filename + ' has an error as expected')
            exit(0)
        else:
            print(str(e))
            # Use the following when debugging internal exceptions -Jeremy
            # print(traceback.format_exc())
            # for production, exit
            exit(1)
            # during development, reraise
            # raise e


if __name__ == "__main__":
    # Check command line arguments
    filenames = []
    error_expected = False

    already_processed_next = False
    for i in range(1, len(sys.argv)):
        if already_processed_next:
            already_processed_next = False
            continue
    
        argument = sys.argv[i]

        if argument == '--error':
            error_expected = True
        elif argument == '--verbose':
            set_verbose(True)
        elif argument == '--dir':
            add_import_directory(sys.argv[i+1])
            already_processed_next = True
        else:
            filenames.append(argument)
    
    if len(filenames) == 0:
        print("Couldn't find a file to deduce!")
        exit(1)

    if len(filenames) > 1:
        print("TODO: support deducing multiple files")
        exit(1)
    
    # Start deducing
    sys.setrecursionlimit(5000) # We can probably use a loop for some tail recursive functions

    set_deduce_directory(os.path.dirname(sys.argv[0]))
    init_parser()

    for filename in filenames:
        deduce_file(filename, error_expected)
