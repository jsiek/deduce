from dataclasses import dataclass
import os
from signal import signal, SIGINT
import sys
from threading import Thread


parsers = ['--recursive-descent', '--lalr']

lib_dir = './lib'
pass_dir = './test/should-validate'
error_dir = './test/should-error'
test_imports_dir = './test/test-imports'
site_dir = './gh_pages/deduce-code'
parse_dir = './test/parse'
max_threads = 10

def handle_sigint(signal, stack_frame):
    print('SIGINT caught, exiting...')
    exit(137)

def test_deduce(parsers, deduce_call, paths, expected_return = 0, extra_arguments=""):
    if isinstance(paths, list):
        deduce_call += ' ' + ' '.join(paths)
    else:
        deduce_call += paths
    for parser in parsers:
        call = deduce_call + ' ' + parser + ' ' + extra_arguments + ' --suppress-theorems' #+ ' --traceback'
        print('Testing:', call)
        return_code = os.system(call) // 256 # Why does it multiply the return code by 256???
        if return_code != expected_return:
            if return_code == SIGINT:
                exit(137)
            elif expected_return == 0:
                print('\nTest failed!')
            else:
                print('\nDeduce failed to catch an error!')
            exit(1)
    
def list_dir_sorted(dir):
    ret = os.listdir(dir)
    ret.sort()
    return ret
            
def generate_deduce_errors(deduce_call, path):
    # We don't pass in the --error flag so we can generate error messages
    # However, that means we can't levarage deduces already existed directory stuff
    # So we manually do it here

    if os.path.isfile(path):
        test_deduce(['--recursive-descent'], deduce_call, path, 1, '> ' + path + '.err')
    elif os.path.isdir(path):
        running_threads = []

        if path[-1] != '/' or path[-1] != '\\':
            path += '/'
        for file in list_dir_sorted(path): 
            if os.path.isfile(path + file):
                if file[-3:] == '.pf':
                    thread = Thread(target=generate_deduce_errors, args=(deduce_call, path + file))
                    thread.start()
                    running_threads.append(thread)

                    while len(running_threads) > max_threads:
                        t = running_threads[0]
                        t.join()
                        running_threads.remove(t)

            elif os.path.isdir(path + file):
                # TODO: recursive directories
                pass
        for t in running_threads:
            t.join()
            running_threads.remove(t)
    else:
        print(path, 'was not found!')
        exit(1)

@dataclass
class ErrorThread:
    path : str
    text : str
    thread : Thread

    def __init__(self, path):
        self.path = path
        self.text = None

    def start(self, deduce_call):
        self.thread = Thread(target=self.test_deduce_errors_thread, args=(deduce_call,))
        self.thread.start()

    def test_deduce_errors_thread(self, deduce_call):
        text = os.popen(deduce_call + ' ' + self.path).read()
        self.text = text

def join_error_threads(threads : list[ErrorThread], join_count : int):
    temp_file  = './actual_error.tmp'

    # for thread in threads:
    for _ in range(join_count):
        # if join_count <= 0 :
        if len(threads) == 0: break

        thread = threads[0]

        if thread.thread.is_alive:
            thread.thread.join()

        threads.remove(thread)
        if thread.text == None:
            print("Got an exception when checking:", thread.path)
            exit(-1)
        
        with open(temp_file, 'w') as fd:
            fd.write(thread.text)

        diff_call = 'diff --ignore-space-change ' + thread.path + '.err ' + temp_file
        ret_code = os.system(diff_call)
        if ret_code == 0:
            os.remove(temp_file)
            print(thread.path, "produces the expected error.")
        else:
            print("*** The error message for", thread.path, "has changed! See actual_error.tmp")
            exit(1)

def test_deduce_errors(deduce_call, path):
    if os.path.isfile(path):
        thread = ErrorThread(path)
        join_error_threads([thread], 1)
    else:
        if path[-1] != '/' or path[-1] != '\\': # Windows moment
            path += '/'

        threads = []
        for file in list_dir_sorted(path):
            if os.path.isfile(path + file):
                if file[-3:] == '.pf':
                    if not os.path.isfile(path + file + '.err'):
                        print("Couldn't find an expected error for", path + file)
                        print("Did you mean to generate it? If so, use --generate-error <filename>")
                        exit(1)
                    
                    thread = ErrorThread(path + file)
                    threads.append(thread)
                    thread.start(deduce_call)
                    if len(threads) == max_threads:
                        # I think passing 1 is for the best
                        # As this function will remove any already finished threads
                        # And also if we don't pass one, we'll repeatedly get into a situation like
                        # 5 threads running 0 threads running 5 threads running 0 threads running
                        # However, we want to maximize the amount of threads running so we're doing more
                        join_error_threads(threads, 1)
                    
            elif os.path.isdir(path + file):
                # TODO: recursive directories?
                pass

        join_error_threads(threads, len(threads))

if __name__ == "__main__":
    signal(SIGINT, handle_sigint)
    # Check command line arguments
    extra_arguments = []

    regenerables = []
    generate_errors = False

    test_lib = False
    test_passable = False
    test_errors = False
    test_site = False
    test_parse = False
    gen_parse = False

    already_processed_next = False
    generate_some_errors = False
    for i in range(1, len(sys.argv)):
        if already_processed_next:
            already_processed_next = False
            continue
    
        argument = sys.argv[i]
        if argument == '--regenerate-errors':
            generate_errors = True
        elif argument == '--generate-error':
            regenerables.append(sys.argv[i + 1])
            already_processed_next = True
            generate_some_errors = True
        elif argument == '--max-threads':
            max_threads = int(sys.argv[i + 1])
            already_processed_next = True
        elif argument == '--lib':
            test_lib = True
        elif argument == '--passable':
            test_passable = True
        elif argument == '--errors':
            test_errors = True
        elif argument == '--parser':
            test_parse = True
        elif argument == '--gen-parse':
            gen_parse = True
        elif argument == '--site':
            test_site = True
        else:
            extra_arguments.append(argument)

    if generate_errors + generate_some_errors + test_lib + test_passable + test_errors + test_site > 1:
        print("Error: you specified too many flags, some are mutually exclusive")
        exit(-1)
            
    python_path = ""
    for i in range(14, 10, -1):
        python_path = os.popen("command -v python3." + str(i)).read()[0: -1] # strip the newline character with the splicing
        if python_path != "" and os.system(python_path + " -m pip list | grep lark > /dev/null") == 0:
            break
    
    if python_path == "":
        print("Could not find a python version at or above 3.11 with lark installed")
        exit(1)
    
    deduce_call = python_path + " ./deduce.py " + " ".join(extra_arguments)

    if generate_errors:
        print('Regenerating ALL errors')
        generate_deduce_errors(deduce_call +  f' --dir {test_imports_dir} ', error_dir)
    elif generate_some_errors:
        for generable in regenerables:
            print('Generating error for:', generable)
            generate_deduce_errors(deduce_call +  f' --dir {test_imports_dir} ', generable)
            generate_errors = True # So we don't run ALL tests
    elif gen_parse:
        print('Regenerating ALL parser errors')
        generate_deduce_errors(deduce_call, parse_dir)

    elif test_site:
        # generate test files for doc code without generating html
        from gh_pages.doc.convert import convert_dir
        convert_dir("./gh_pages/doc/", False)
        # test generated files
        for f in list_dir_sorted(pass_dir):
            if f.startswith('doc_') and f.endswith('.pf'):
                test_deduce(parsers, deduce_call, pass_dir + '/' + f)
    elif test_lib:
        test_deduce(parsers, deduce_call, lib_dir)
    elif test_passable:
        test_deduce(parsers, deduce_call +  f' --dir {test_imports_dir} ', pass_dir)
    elif test_errors:
        test_deduce_errors(deduce_call +  f' --dir {test_imports_dir} ', error_dir)
    elif test_parse:
        test_deduce_errors(deduce_call, parse_dir)
    else:
        # By default, test everything except for the doc code that gets
        # generated by doc.convert, because that requires markdown and
        # Jeremy doesn't have that installed.
        # Also not the parse errors
        test_deduce(parsers, deduce_call +  f' --dir {test_imports_dir} ', [lib_dir, pass_dir])
        test_deduce_errors(deduce_call +  f' --dir {test_imports_dir} ', error_dir)
    
