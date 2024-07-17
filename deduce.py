from error import set_verbose, get_verbose
from proof_checker import check_deduce, uniquify_deduce
import sys
from parser import parse, set_filename
from lark import exceptions
import traceback

def token_str(token):
    if len(token.value) > 0:
        str = token.value
    else:
        str =  t.token.type
    str = str.lower()
    if str[0] == '$':
        str = str[1:]
    return str

if __name__ == "__main__":
    sys.setrecursionlimit(5000)
    
    filename = sys.argv[1]
    file = open(filename, 'r')
    p = file.read()
    set_verbose(False)
    set_filename(filename)

    error_expected = False
    if len(sys.argv) >= 3:
        if sys.argv[2] == '--error':
            error_expected = True
    
    try:
        if get_verbose():
            print("about to parse")
        ast = parse(p, trace=False)
        if get_verbose():
            print("starting uniquify:\n" + '\n'.join([str(d) for d in ast]))
        uniquify_deduce(ast)
        if get_verbose():
            print("finished uniquify:\n" + '\n'.join([str(d) for d in ast]))
        check_deduce(ast)
        if error_expected:
            print('an error was expected, but it was not caught')
            exit(-1)
        else:
            print(filename + ' is valid')
            exit(0)

    except exceptions.UnexpectedToken as t:
        if error_expected:
            exit(0)
        else:
            print(filename + ":" + str(t.token.line) + "." + str(t.token.column) \
                  + "-" + str(t.token.end_line) + "." + str(t.token.end_column) + ": " \
                  + "error in parsing, unexpected token: " + token_str(t.token))
            #print('expected one of ' + ', '.join([str(e) for e in t.expected]))
            exit(-1)
        
    except Exception as e:
        if error_expected:
            exit(0)
        else:
            print(str(e))
            # Use the following when debugging internal exceptions -Jeremy
            # print(traceback.format_exc())
            # for production, exit
            exit(1)
            # during development, reraise
            #raise e

