from flask import Flask, jsonify, request, Response
from contextlib import redirect_stdout, redirect_stderr
from pathlib import Path
import subprocess
import os
import uuid
import sys
import io

from proof_checker import check_deduce, uniquify_deduce
from abstract_syntax import get_uniquified_modules, add_uniquified_module, add_import_directory
import rec_desc_parser

app = Flask(__name__)
PORT = 12357

def deduce_file(filename, error_expected):
    module_name = Path(filename).stem

    try:
        if module_name in get_uniquified_modules().keys():
            ast = get_uniquified_modules()[module_name]
        else:
            file = open(filename, 'r', encoding="utf-8")
            program_text = file.read()
            rec_desc_parser.set_filename(filename)

            ast = rec_desc_parser.parse(program_text, False, False)
            uniquify_deduce(ast)
            add_uniquified_module(module_name, ast)
                
        check_deduce(ast, module_name, False)
        print(filename + ' is valid')

    except Exception as e:
        print(str(e))



@app.route('/deduce', methods=['POST'])
def deduce_req():
    # Get user code
    deduce_code = request.data.decode("utf-8")
    print("Code received: " + deduce_code)

    # Generate a unique filename for the user code
    unique_id = str(uuid.uuid4())
    code_filename = f"/tmp/{unique_id}.pf"
    with open(code_filename, "w") as code_file:
        code_file.write(deduce_code)

    command = "mv lib /tmp/lib"
    result = subprocess.check_output(command, shell=True, text=True)
    print(result)

    command = "ls /tmp"
    result = subprocess.check_output(command, shell=True, text=True)
    print(result)
        
    # Start deducing
    rec_desc_parser.set_deduce_directory("./")
    rec_desc_parser.init_parser()
    add_import_directory("/tmp/lib")
    
    try:    
        with redirect_stdout(io.StringIO()) as stdout:
            deduce_file(f"/tmp/{unique_id}.pf", False)
        deduce_output = stdout.getvalue()
    except Exception as e:
        deduce_output = str(e)

    deduce_output = deduce_output.replace(f"/tmp/{unique_id}", "input")
    print(f"Output: {deduce_output}")
    
    # Cleanup temporary files
    pf_file  = f"/tmp/{unique_id}.pf"
    thm_file = f"/tmp/{unique_id}.thm"
    if os.path.isfile(pf_file) : os.remove(pf_file)
    if os.path.isfile(thm_file): os.remove(thm_file)
    
    # Return the output
    res = Response(deduce_output)
    res.headers["Access-Control-Allow-Origin"] = "*"
    return res


if __name__ == '__main__':
    app.run(port=12347)
