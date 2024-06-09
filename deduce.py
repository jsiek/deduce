from error import set_verbose, get_verbose
from proof_checker import check_deduce, uniquify_deduce
import sys
from parser import parse, set_filename
from lark import exceptions

if __name__ == "__main__":
    sys.setrecursionlimit(5000)
    filename = sys.argv[1]
    file = open(filename, 'r')
    p = file.read()
    set_verbose(False)
    set_filename(filename)
    try:
        ast = parse(p, trace=False)
        if get_verbose():
            print("starting uniquify:\n" + '\n'.join([str(d) for d in ast]))
        uniquify_deduce(ast)
        if get_verbose():
            print("finished uniquify:\n" + '\n'.join([str(d) for d in ast]))
        check_deduce(ast)
        print(filename + ' is valid')
        exit(0)

    except exceptions.UnexpectedToken as t:
        print(filename + ":" + str(t.token.line) + "." + str(t.token.column) \
              + "-" + str(t.token.end_line) + "." + str(t.token.end_column) + ": " \
              + "error in parsing, unexpected string: " + t.token.type.lower()[1:])
        #print('expected one of ' + ', '.join([str(e) for e in t.expected]))
        exit(-1)
        
    except Exception as e:
        print(str(e))
        # for production, exit
        exit(1)
        # during development, reraise
        #raise e

