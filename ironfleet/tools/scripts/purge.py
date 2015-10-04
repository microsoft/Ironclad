#!/usr/bin/python

import sys
import os
import time
import fileinput
import re
import argparse
import subprocess

class DafnyFile:
  def __init__(self, filename, verify_time):
    self.filename = filename.replace('\\', '/')

  def __repr__(self):
    return "%s" % (self.filename)

  def is_spec(self):
    return self.filename.endswith(".s.dfy")

def parse_nubuild(nubuild_output_file):
  dafny_files = []
  nubuild_output = open(nubuild_output_file, "r")
  for line in nubuild_output.readlines():
    result = re.search("DafnyVerifyOneVerb\(#\d+,(.*),\) Success\s+([.0-9]+)s", line)
    if result:
      filename = result.group(1)
      time = result.group(2)
      dfile = DafnyFile(filename, time)
      dafny_files += [dfile]
  
  nubuild_output.close()
  return dafny_files

def make_nubuild_set(nubuild_output_file):
  files = parse_nubuild(nubuild_output_file)
  filenames = map(lambda x : os.path.normpath(x.filename), files)
  return set(filenames)

def visit_dir(accumulator, dirname, files):
  for f in files:
    if f.endswith(".dfy"):
      accumulator.add(os.path.normpath(os.path.join(dirname,f)))

def find_all_files(root):
  files = set([])
  os.path.walk(root + "/src/Dafny/", visit_dir, files)
  return files

def find_unused_files(files_present, files_in_use):
  return files_present - files_in_use

def delete_files(files):
  print "Deleting:"
  for f in sorted(files):
    print f
    os.remove(f)

def delete_empty_dirs(path):
  if not os.path.isdir(path):
    return

  files = os.listdir(path)
  for f in files:
    filename = os.path.join(path, f)
    if os.path.isdir(filename):
      delete_empty_dirs(filename)

  files = os.listdir(path)
  if len(files) == 0:
    print "Removing empty folder: %s " % (path)
    os.rmdir(path)

def main():
  parser = argparse.ArgumentParser(description='Purge unused files')
  parser.add_argument('-r', '--root', help="Iron root directory", required=True)
  parser.add_argument('-n', '--nubuild', help="Output from running ./bin_tools/NuBuild/NuBuild.exe BatchDafny src/Dafny/Distributed/apps.dfy.batch", required=True)
  args = parser.parse_args()

  #if args.cache == None or not os.path.exists(args.cache):
  inuse_files = make_nubuild_set(args.nubuild)
  current_files = find_all_files(args.root)

  unused_files = find_unused_files(current_files, inuse_files)

  delete_files(unused_files)

  delete_empty_dirs("src/Dafny")

main()

