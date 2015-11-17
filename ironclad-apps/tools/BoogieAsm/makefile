#
# Copyright (c) 2007 Microsoft Corporation.   All rights reserved.
#

BUILD = ..\fsharp
FSC = $(BUILD)\fsc -g
FSLEX = $(BUILD)\fslex
FSYACC = $(BUILD)\fsyacc
CORE = .

CSC = %SystemRoot%\Microsoft.NET\Framework\v4.0.30319\csc.exe
CSC0 = ..\..\..\base\build-private\v4.0.30319\csc.exe
CSC1 = ..\..\..\base\build-private\v4.0.30319-Windows8.1\csc.exe

SRC = \
	$(CORE)\ast.fs \
	$(CORE)\parse_util.fs \
	$(OBJ)\parse.fs \
	$(OBJ)\lex.fs \
	$(CORE)\emit_bpl.fs \
	$(CORE)\main.fs \

all: $(OBJ) $(BIN) $(BIN)\boogieasm.exe $(BIN)\symdiffmerge.exe

$(OBJ):
	md $(OBJ)

$(BIN):
	md $(BIN)

$(OBJ)\lex.fsi $(OBJ)\lex.fs: $(CORE)\lex.fsl
	$(FSLEX) $(CORE)\lex.fsl -o $(OBJ)\lex.fs

$(OBJ)\parse.fsi $(OBJ)\parse.fs: $(CORE)\parse.fsy
	$(FSYACC) -v $(CORE)\parse.fsy -o $(OBJ)\parse.fs

$(BIN)\boogieasm.exe: $(SRC)
	$(FSC) --standalone --mlcompatibility -O $(SRC) -o $(BIN)\boogieasm.exe -r FSharp.PowerPack.dll

$(BIN)\symdiffmerge.exe: SymdiffMerge.cs
	if exist $(CSC). ($(CSC) /debug+ /out:$(BIN)\symdiffmerge.exe SymdiffMerge.cs.) else ($(CSC0) /debug+ /out:$(BIN)\dafnycc.exe SymdiffMerge.cs.)

clean:
	del /q $(BIN)\boogieasm.exe
	del /q $(OBJ)\*.fs
