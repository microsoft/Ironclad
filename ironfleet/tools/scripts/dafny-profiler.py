#!/usr/bin/python

import sys
import os
import subprocess
import re
os.environ["PATH"] = "tools/Dafny:"+os.environ["PATH"]

def docmd(*cmd):
    print "cmd:", " ".join(cmd)
    subprocess.call(cmd)
    
def main():
    if not os.path.exists('tools/Dafny'):
        print 'Your current directory is wrong.  You should run this script while your current directory is ironfleet, the root directory.'
        sys.exit(-1)

    (thisprog,dfyfile,procname) = sys.argv
    boogieFile = dfyfile.replace(".dfy", ".bpl")
    escapedProcName = procname.replace("_", "__")
    docmd("dafny", "/timeLimit:1", "/allowGlobals", "/autoTriggers:1", "/ironDafny", "/noVerify", "/noNLarith", "/print:%s" % boogieFile, dfyfile)

    boogieFileHandle = open(boogieFile, 'r')
    mangledProcName = ''
    for line in boogieFileHandle:
        m = re.search(r'^procedure\s*({:timeLimit \d+})?\s*(Impl[^\(]+)', line)
	if m:
            procedureName = m.group(2)
            if procedureName.find(escapedProcName) > -1:
                mangledProcName = procedureName
                break
    if len(mangledProcName) == 0:
        print 'Could not find procedure with substring %s in %s' % (escapedProcName, boogieFile)
        sys.exit(-1)
            
    z3log = "z3.log"
    if (os.path.exists(z3log)):
        os.unlink(z3log)
    docmd("boogie", "/z3opt:nlsat.randomize=false", "/z3opt:pi.warnings=true", "/z3opt:TRACE=true", "/timeLimit:30", "/proc:%s" % mangledProcName, "/trace", boogieFile)

    docmd("nohup", "Z3AxiomProfiler.exe", z3log, "/c:1")

main()
