#!/usr/bin/python

import re, sys, os.path, getopt 
from subprocess import call

def main(argv):
    maxDepth = 1
    parsed_files = []	
    arg_len = len(sys.argv)
    if arg_len < 2:
        print "usage: parse.py <inputfile> [<depth>]"
        sys.exit(2)
    
    arg1 = sys.argv[1]
    if arg_len >= 3:
        maxDepth = int(sys.argv[2])
    else:
        maxDepth = 10000

    thisfile = sys.argv[0]
    actualArg1 = os.path.realpath(arg1)
    currentPath = os.path.dirname(os.path.realpath(thisfile))
    srcPath = os.path.realpath(currentPath + "/../../src")
    #print "maxDepth = ", maxDepth
    with open(currentPath + "/out.dot", "w") as fw:
        fw.write("digraph G {\n")
        parseFile(actualArg1, srcPath, fw, parsed_files, 1, maxDepth)
        fw.write("}\n")
    
    wincurrentpath = currentPath.replace("/cygdrive/c","C:\\")
    call(["dot", "-Tpdf", wincurrentpath + "/out.dot", "-o", wincurrentpath + "/output.pdf"])
    call(["cygstart.exe", currentPath + "/output.pdf"])

def parseFile(filename, srcPath, fw, parsed_files, depth, maxDepth):
    if filename in parsed_files:
        return 
    if depth > maxDepth:
        return

    parsed_files.append(filename)
    #print "Parsing file %s at depth %d, with maxDepth %d" % (filename, depth, maxDepth)
    f = open(filename, "r")
    
    for line in f:
       newfile = parseline(filename,line, srcPath, fw)
       if newfile:
           #print "found included file: " + newfile
           parseFile(newfile, srcPath, fw, parsed_files,depth+1,maxDepth)
    f.close()

def parseline(filename,line, srcPath, fw):
    # print "Parsing line %s" % line
    matchObj = re.match("^include ", line)
    if matchObj:
        index = line.index("\"")
        # print "index =", index, 
        secondindex = line.index("\"", index+1)
        # print "secondindex =", secondindex, 
        substr = line[index+1:secondindex]
	newPath = os.path.dirname(os.path.realpath(os.path.dirname(filename) + "/" + substr))
	newFilename = os.path.basename(substr)
        actualFile = newPath + "/" +newFilename 
	if not re.match("^"+srcPath,actualFile):
            print "invalid file prefix"
            sys.exit(2)
	if re.search("\.s\.dfy$",newFilename):
            nodeshape = "\"" + normalizeFilename(actualFile,srcPath) + "\" [shape=box, style=filled, fillcolor=lightblue]\n"
	    fw.write(nodeshape)
	if re.search("\.s\.dfy$",filename):
            nodeshape = "\"" + normalizeFilename(filename,srcPath) + "\" [shape=box, style=filled, fillcolor=lightblue]\n"
	    fw.write(nodeshape)
        outline = "\"" + normalizeFilename(filename,srcPath) + "\" -> \"" + normalizeFilename(actualFile,srcPath) + "\"\n"
        fw.write(outline)
        return actualFile

def normalizeFilename(filename,srcPath):
    return filename[len(srcPath)+1:]


if __name__ == "__main__":
    main(sys.argv)
