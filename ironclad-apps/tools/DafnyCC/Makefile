#
# Copyright (c) 2007 Microsoft Corporation.   All rights reserved.
#

MSBUILD=C:\Windows\Microsoft.NET\Framework\v4.0.30319\MSBuild.exe

BIN = ..\..\bin_tools\dafnycc
SRC = .
SPC = ..\DafnySpec

DAFNYCC_SOURCES = \
	$(SPC)\Util.cs \
	$(SPC)\RtlGhost.cs \
	$(SRC)\Rtl.cs \
	$(SRC)\Analyze.cs \
	$(SRC)\RegAlloc.cs \
	$(SPC)\Compile.cs \
	$(SPC)\CompileField.cs \
	$(SPC)\CompileFunction.cs \
	$(SPC)\CompileMethodGhost.cs \
	$(SRC)\CompileMethod.cs \
	$(SPC)\DafnySpec.cs \
	$(SRC)\DafnyCC.cs \

all: dafnycc 

dafnycc: $(BIN) $(BIN)\dafnycc.exe

$(BIN):
	md $(BIN)

$(BIN)\dafnycc.exe: $(DAFNYCC_SOURCES) DafnyCC.sln
	$(MSBUILD) DafnyCC.sln

