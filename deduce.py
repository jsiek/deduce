from proof_checker import check_deduce, set_verbose, get_verbose
import sys
from parser import parse, set_filename
from lark import exceptions

if __name__ == "__main__":
    filename = sys.argv[1]
    file = open(filename, 'r')
    p = file.read()
    set_verbose(False)
    try:
      set_filename(filename)
      ast = parse(p, trace=False)
      if get_verbose():
          print("finished parsing")
      try:
          check_deduce(ast)
          print(filename + ' is valid')
          exit(0)
      except Exception as e:
          print(str(e))
          exit(1)

    except exceptions.UnexpectedToken as t:
        print(filename + ":" + str(t.token.line) + "." + str(t.token.column) \
              + "-" + str(t.token.end_line) + "." + str(t.token.end_column) + ": " \
              + "error in parsing: unexpected token '" + t.token.value + "'")
        print('expected one of ' + ', '.join([str(e) for e in t.expected]))
        exit(-1)
        #print(str(t))
        
    # print(str(ast))
