#
# Copyright (c) 2007 Microsoft Corporation.   All rights reserved.
#

BUILD = ..\fsharp
FSC = $(BUILD)\fsc -g
FSLEX = $(BUILD)\fslex
FSYACC = $(BUILD)\fsyacc
SRC = .

BEAT_SOURCES = \
	$(SRC)\ast.fs \
	$(SRC)\parse_util.fs \
	$(OBJ)\parse.fs \
	$(OBJ)\lex.fs \
	$(SRC)\main.fs \

beat: $(OBJ) $(BIN) $(BIN)\beat.exe

$(OBJ):
	md $(OBJ)

$(BIN):
	md $(BIN)

$(OBJ)\lex.fsi $(OBJ)\lex.fs: $(OBJ) $(SRC)\lex.fsl
	$(FSLEX) $(SRC)\lex.fsl -o $(OBJ)\lex.fs

$(OBJ)\parse.fsi $(OBJ)\parse.fs: $(OBJ) $(SRC)\parse.fsy
	$(FSYACC) -v $(SRC)\parse.fsy -o $(OBJ)\parse.fs

$(BIN)\beat.exe: $(BEAT_SOURCES)
	$(FSC) --standalone --mlcompatibility -O $(BEAT_SOURCES) -o $(BIN)\beat.exe -r FSharp.PowerPack.dll


