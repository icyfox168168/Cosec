import subprocess
import re
import sys
import os

# Runs a test '.c' file
def run_test(cosec_exec, test_file):
    f = open(test_file, "r")
    contents = f.read()
    expected_output = int(re.search(r'\/\/ expect\: (\d+)', contents).group(1))
    result = subprocess.run([cosec_exec, test_file], capture_output=True)
    if result.returncode != 0:
        print("Test '" + test_file + "' failed to compile")
    subprocess.run(["nasm", "-f", "macho64", "out.s"])
    subprocess.run(["ld", "-L/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/lib", "-lSystem", "out.o"])
    result = subprocess.run(["./a.out"])
    if result.returncode != expected_output:
        print("Test '" + test_file + "' FAILED")
    else:
        print("Test '" + test_file + "' PASSED")

def run_tests_in(cosec_exec, dir):
    print("Running tests in '" + dir + "'...")
    for file in os.listdir(dir):
        path = dir + "/" + file
        if os.path.isdir(path):
            run_tests_in(cosec_exec, path)
        else:
            _, extension = os.path.splitext(path)
            if extension == ".c":
                run_test(cosec_exec, path)

cosec_exec = sys.argv[1]
run_tests_in(cosec_exec, ".")
os.remove("./out.s")
os.remove("./out.o")
os.remove("./a.out")
