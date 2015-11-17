#
# Copyright (c) 2007 Microsoft Corporation.   All rights reserved.
#

BUILD = ..\..\build
FSC = $(BUILD)\fsc -g
FSLEX = $(BUILD)\fslex
OBJ = ..\..\obj_tools\linecount
BIN = ..\..\bin_tools\linecount
CORE = .

SRC = \
	$(CORE)\parse_util.fs \
	$(OBJ)\lex.fs \
	$(CORE)\main.fs \

all: $(OBJ) $(BIN) $(BIN)\linecount.exe

$(OBJ):
	md $(OBJ)

$(BIN):
	md $(BIN)

$(OBJ)\lex.fsi $(OBJ)\lex.fs: $(CORE)\lex.fsl
	$(FSLEX) $(CORE)\lex.fsl -o $(OBJ)\lex.fs

$(BIN)\linecount.exe: $(SRC)
	$(FSC) --standalone --mlcompatibility -O $(SRC) -o $(BIN)\linecount.exe -r FSharp.PowerPack.dll

clean:
	del /q $(BIN)\linecount.exe
	del /q $(OBJ)\*.fs
