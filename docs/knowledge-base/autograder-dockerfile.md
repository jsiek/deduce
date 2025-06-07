# The Dockerfile

### Building the image in the Autograder
The [Dockerfile](../../autograder_docker/Dockerfile) provides an easy way to grade students code for a course that's utilizing `autograder.io`. In order to utilize the Dockerfile, first start by creating a new image by clicking the cogwheel next to your course, pressing "sandbox images", then press new image and drop the Dockerfile inside before pressing build. 

The Dockerfile will automatically download and install the latest version of deduce (which can be found [here](github.com/jsiek/deduce/releases/latest/)), then cache the library files. 

### Test case creation
Creating test cases involves levaraging deduce's return code, and creating an external file contaning the test cases. For testing a proof, simply create a file that imports the students code, then write a proof that would otherwise fail without the theorem in the students code. For testing functions, generous use of the `assert` and calling the students functions can be done. 

After the file with the test case(s) has been generated, you can use the command `python3 deduce/deduce.py $FILE` where `$FILE` is the name of the test case. If everything works out, deduce will exit with a return code of 0, but on errors (for example an assertion failing) will return a nonzero error code.

> [!NOTE]
Files with proofs that use the > `sorry` keyword will still generate a return code of 0