from flask import Flask, jsonify, request, Response
import subprocess
import os
import uuid

import rec_desc_parser
from deduce import deduce_file

app = Flask(__name__)

PORT = 12357

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

    try:
        # Build and run the Docker container
        # Start deducing
        rec_desc_parser.set_deduce_directory("./")
        rec_desc_parser.init_parser()
        
        deduce_file(f"/tmp/{unique_id}.pf", False)

        deduce_output = "Outputte!"

        # Cleanup temporary files
        pf_file  = f"/tmp/{unique_id}.pf"
        thm_file = f"/tmp/{unique_id}.thm"
        if os.path.isfile(pf_file) : os.remove(pf_file)
        if os.path.isfile(thm_file): os.remove(thm_file)

        # Return the output
        res = Response(deduce_output)
        res.headers["Access-Control-Allow-Origin"] = "*"
        return res

    except subprocess.CalledProcessError as e:
        return jsonify({"error": str(e)}), 500

if __name__ == '__main__':
    app.run(port=12347)
