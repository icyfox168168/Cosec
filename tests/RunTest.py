# Look into using Csmith: https://github.com/csmith-project/csmith

import subprocess
import re
import sys
import os

cosec_exec = sys.argv[1]
test_file = sys.argv[2]

f = open(test_file, "r")
contents = f.read()

# Find the expected return code
re_search = re.search(r'\/\/ expect\: (\d+)', contents)
if re_search is None:
    print("No '// expect: ' in test file")
    sys.exit(1)
groups = re_search.groups()
if len(groups) == 0:
    print("No matching regex '// expect: (\\d+)' found in test file")
    sys.exit(1)
expected_output = int(groups[0])

# Compile
result = subprocess.run([cosec_exec, test_file])
if result.returncode != 0:
    print("Test '" + test_file + "' failed to compile")
    sys.exit(1)

# Assemble
result = subprocess.run(["nasm", "-f", "macho64", "out.s"])
if result.returncode != 0:
    print("Test '" + test_file + "' failed to assemble with NASM")
    sys.exit(1)

# Link
result = subprocess.run(["ld", "-L/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/lib", "-lSystem", "out.o"])
if result.returncode != 0:
    print("Test '" + test_file + "' failed to link with ld")
    sys.exit(1)

# Run
result = subprocess.run(["./a.out"])
if result.returncode != expected_output:
    print("Test '" + test_file + "' FAILED")
    sys.exit(1)
else:
    print("Test '" + test_file + "' PASSED")
