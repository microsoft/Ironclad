#
# Copyright (c) 2007 Microsoft Corporation.   All rights reserved.
#

BUILD = ..\..\build
MSBUILD=C:\Windows\Microsoft.NET\Framework\v4.0.30319\MSBuild.exe
#FSC = $(BUILD)\fsc -g
#FSLEX = $(BUILD)\fslex
#FSYACC = $(BUILD)\fsyacc
#OLD_CSC = ..\..\..\base\build\csc.exe
#CSC = %SystemRoot%\Microsoft.NET\Framework\v4.0.30319\csc.exe
#CSC0 = ..\..\..\base\build-private\v4.0.30319\csc.exe
#CSC1 = ..\..\..\base\build-private\v4.0.30319-Windows8.1\csc.exe
OBJ = ..\..\obj_tools\dafnyspec
BIN = ..\..\bin_tools\dafnyspec
SRC = .

DAFNYSPEC_SOURCES = \
	$(SRC)\Util.cs \
	$(SRC)\RtlGhost.cs \
	$(SRC)\Compile.cs \
	$(SRC)\CompileField.cs \
	$(SRC)\CompileFunction.cs \
	$(SRC)\CompileMethodGhost.cs \
	$(SRC)\ParseMain.cs \
	$(SRC)\DafnySpec.cs \

PARSER_SOURCES = \
	$(SRC)\parse_util.fs \
	$(SRC)\parser.fs \

REFS = /r:System.Numerics.dll /r:dafnyspecast.dll /r:$(BIN)\parser.dll

all: dafnyspec

dafnyspec: $(OBJ) $(BIN) $(BIN)\dafnyspec.exe

$(OBJ):
	md $(OBJ)

$(BIN):
	md $(BIN)

$(BIN)\dafnyspec.exe: $(DAFNYSPEC_SOURCES) $(SRC)\DafnySpecAst.cs $(PARSER_SOURCES) $(SRC)\lex.fsl $(SRC)\parse.fsy
	$(MSBUILD) DafnySpec.sln

#$(BIN)\dafnyspecast.dll: $(SRC)\DafnySpecAst.cs
#	$(OLD_CSC) /debug+ /target:library /out:$(BIN)\dafnyspecast.dll	$(SRC)\DafnySpecAst.cs
#
#$(OBJ)\lex.fsi $(OBJ)\lex.fs: $(SRC)\lex.fsl
#	$(FSLEX) $(SRC)\lex.fsl -o $(OBJ)\lex.fs
#
#$(OBJ)\parse.fsi $(OBJ)\parse.fs: $(SRC)\parse.fsy
#	$(FSYACC) -v $(SRC)\parse.fsy -o $(OBJ)\parse.fs
#
#$(BIN)\parser.dll: $(PARSER_SOURCES) $(BIN)\dafnyspecast.dll
#	$(FSC) --standalone --mlcompatibility --target:library -O $(PARSER_SOURCES) -o $(BIN)\parser.dll -r FSharp.PowerPack.dll -r $(BIN)\dafnyspecast.dll
#
#$(BIN)\dafnyspec.exe: $(DAFNYSPEC_SOURCES) $(BIN)\dafnyspecast.dll $(BIN)\parser.dll
#	if exist $(CSC). ($(CSC) /debug+ /out:$(BIN)\dafnyspec.exe /lib:$(BIN) $(DAFNYSPEC_SOURCES) $(REFS).) else ($(CSC0) /debug+ /out:$(BIN)\dafnyspec.exe /lib:$(BIN) $(DAFNYSPEC_SOURCES) $(REFS).)
#
