#!/usr/bin/python

import sys
import re
import os

# Remove in and out instructions
def banned(line):
  tline = line.strip()

  result = False
  # Don't wait on the serial port
  result = result or (tline.startswith("je") and "waitForSerialPort" in tline)

  # Ban VgaDebugStore lines (very brittle :( )
  result = result or ("edx + 753664" in tline)

  # Ban IO instructions
  result = result or (tline.startswith("in ") or tline.startswith("out "))

  return result

def munge(filename):
  establish_locality_in_progress = False;
  with open(filename) as f:
    for line in f:
      line = line.rstrip()

      # Tack an extern declaration on to the header
      if line == ".model flat":
        print line
        print 'EXTERN ?c_debug_print@@YAXHH@Z : proc'
        print 'EXTERN ?fixup_stack@@YAXXZ : proc'
        print 'EXTERN ?c_exit@@YAXXZ : proc'
        continue

      # Neuter Proc_establish_locality (TPM initialization)
      if line.startswith("_?Proc_establish__locality proc"):
        establish_locality_in_progress = True
        print line
        print "\tret"
      if line.startswith("_?Proc_establish__locality endp"):
        establish_locality_in_progress = False

      # Replace the jump that conditions on the contents of eax with 
      # an unconditional jump.  But first, fixup Windows notion of where our stack will be
      if 'je AppEntryPoint$__L1' in line:
        print '\tcall ?fixup_stack@@YAXXZ'
        print '\tjmp AppEntryPoint$__L1'
        continue

      # Replace calls to TPM-based random with calls to non-TPM random
      if line.strip() == 'call _?Proc_get__random':
        print '\tcall _?Proc_insecure__get__random'
        continue

      # Replace calls to Dafny's debug print with the C version
      if line.strip() == 'call _?Proc_debug__print':
        print '\tcall ?c_debug_print@@YAXHH@Z'
        continue

      # Replace the infinite loop with an exit
      if line.strip() == 'jmp AppEntryPoint$myInfLoop':
        print '\tcall ?c_exit@@YAXXZ'
        continue

      if (establish_locality_in_progress):
        pass
      elif banned(line):
        pass
      else:
        print line

# Extra memory spacing
#Spacer SEGMENT DWORD MEMORY FLAT READ WRITE
#REPEAT 100000;8388608
#QWORD ?
#ENDM
#REPEAT 100000;8388608
#QWORD ?
#ENDM
#REPEAT 100000;8388608
#QWORD ?
#ENDM
#REPEAT 100000;8388608
#QWORD ?
#ENDM
#Spacer ENDS
#

try:
  arg = sys.argv[1]
except:
  sys.stderr.write("Usage: %s <file.asm>\n" % sys.argv[0])
  sys.exit(-1)
munge(arg)

