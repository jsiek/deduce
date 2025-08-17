from flask import Flask, jsonify, request, Response
from contextlib import redirect_stdout, redirect_stderr
from pathlib import Path
import subprocess
import os
import uuid
import sys
import io
import builtins

from proof_checker import check_deduce, uniquify_deduce
from abstract_syntax import get_uniquified_modules, add_uniquified_module, add_import_directory, set_recursive_descent, set_check_imports
from deduce import deduce_file
import rec_desc_parser

app = Flask(__name__)
PORT = 12357        

@app.route('/deduce', methods=['POST'])
def deduce_req():
    # Overwrite exit
    builtins.exit = lambda exit_code: None
    sys.argv[0] = './'
    
    # Get user code
    deduce_code = request.data.decode("utf-8")
    print("Code received: " + deduce_code)

    # Generate a unique filename for the user code
    unique_id = str(uuid.uuid4())
    code_filename = f"/tmp/{unique_id}.pf"
    with open(code_filename, "w") as code_file:
        code_file.write(deduce_code)
    
    # Start deducing
    add_import_directory("./lib")

    set_recursive_descent(True)
    set_check_imports(False)
    
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
    app.run(port=PORT, ssl_context='adhoc')
