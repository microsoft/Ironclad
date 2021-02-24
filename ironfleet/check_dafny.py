import os
import sys
import re

if len(sys.argv) < 2:
    sys.stderr.write("Missing command-line argument\n")
    sys.exit(-1)

filename = sys.argv[1]
fh = open(filename, 'r')
if not fh:
    sys.stderr.write("Cannot open file %s" % (filename))
    sys.exit(-1)

for line in fh.readlines():
    if re.search("[Oo]ut of resource", line):
        sys.stderr.write("Dafny reported an out-of-resource error\n")
        sys.exit(-1)
    if re.search("proof obligations\]\s+errors", line):
        sys.stderr.write("Dafny reported errors not in summary\n")
        sys.exit(-1)

fh.close()
sys.stdout.write("Full check of Dafny output succeeded\n")
sys.exit(0)
