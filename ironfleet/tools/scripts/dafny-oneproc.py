#!/usr/bin/python

import sys
import os
import subprocess
import re

def docmd(*cmd):
    print "cmd:", " ".join(cmd)
    subprocess.call(cmd)
    
def main():
    (thisprog,dfyfile,procname) = sys.argv
    boogieFile = dfyfile.replace(".dfy", ".bpl")
    escapedProcName = procname.replace("_", "__")
    docmd("dafny", "/timeLimit:1", "/noVerify", "/compile:0", "/arith:5", "/print:%s" % boogieFile, dfyfile)

    boogieFileHandle = open(boogieFile, 'r')
    mangledProcName = ''
    for line in boogieFileHandle:
        m = re.search(r'^procedure\s*({:[^}]+}\s*)*(Impl[^\(]+)', line)
	if m:
            procedureName = m.group(2)
            if procedureName.find(escapedProcName) > -1:
                mangledProcName = procedureName
                break
    boogieFileHandle.close()
    if len(mangledProcName) == 0:
        print 'Could not find procedure with substring %s in %s' % (escapedProcName, boogieFile)
        sys.exit(-1)
            
    docmd("dafny", "/timeLimit:30", "/proverOpt:O:nlsat.randomize=false", "/proverOpt:O:pi.warnings=true", "/proverWarnings:1", "/compile:0", "/noCheating:1", "/arith:5", "/proc:%s" % mangledProcName, dfyfile)
    docmd("rm", boogieFile)

main()
