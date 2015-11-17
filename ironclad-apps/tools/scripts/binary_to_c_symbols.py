#!/usr/bin/python

import sys

binaryfile = sys.argv[1]
symbolname = sys.argv[2]
hfile = sys.argv[3]
cfile = sys.argv[4]

ifp = open(binaryfile, "rb")
binaryBytes = ifp.read()
ifp.close()

ofp = open(hfile, "w")
ofp.write("#pragma once\n extern char %s[%d];\n" %(symbolname, len(binaryBytes)))
ofp.close()

ofp = open(cfile, "w")
ofp.write("char %s[%d] = {\n" %(symbolname, len(binaryBytes)))
for b in binaryBytes:
  ofp.write("0x%02x, \n" % ord(b))

ofp.write("};\n")
ofp.close()
