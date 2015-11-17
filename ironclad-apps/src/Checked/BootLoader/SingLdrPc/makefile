BUILD = ..\..\..\..\tools\build

AS = $(BUILD)\x86_x86\ml.exe
CC = $(BUILD)\x86_x86\cl.exe
LINK = $(BUILD)\x86_x86\link.exe
AS16 = $(BUILD)\x86_x86\ml.exe
LINK16 = $(BUILD)\x86_x86\link16.exe
BLGEN = $(BUILD)\x86_x86\blgen.exe

# To generate a small version, use: nmake CCFLAGS=/DSMALL_LOADER
CCFLAGS =

MIN_OBJS = \
	$(OBJ)\x86\blcrtasm.obj \
	$(OBJ)\x86\blidt.obj \
	$(OBJ)\x86\blioport.obj \
	$(OBJ)\x86\bllegacy.obj \
	$(OBJ)\x86\blutilasm.obj \
	$(OBJ)\blacpi.obj \
	$(OBJ)\blcdrom.obj \
	$(OBJ)\blcom.obj \
	$(OBJ)\blentry.obj \
	$(OBJ)\blfat.obj \
	$(OBJ)\blflash.obj \
	$(OBJ)\blkd.obj \
	$(OBJ)\blkd1394.obj \
	$(OBJ)\blkdcom.obj \
	$(OBJ)\blmm.obj \
	$(OBJ)\blmps.obj \
	$(OBJ)\blpci.obj \
	$(OBJ)\blpecoff.obj \
	$(OBJ)\blpnp.obj \
	$(OBJ)\blpool.obj \
	$(OBJ)\blpxe.obj \
	$(OBJ)\blsingularity.obj \
	$(OBJ)\blsmap.obj \
	$(OBJ)\blstring.obj \
	$(OBJ)\bltrap.obj \
	$(OBJ)\blutil.obj \
	$(OBJ)\blvesa.obj \
	$(OBJ)\blvideo.obj \

TPM_OBJS = \
	$(OBJ)\tpm\aik.obj \

OBJS = $(MIN_OBJS) $(TPM_OBJS)

all: $(OBJ)\x86 $(OBJ)\tpm $(OBJ)\pxe-loader

dirs: $(OBJ)\x86 $(OBJ)\tpm

pxe-loader: dirs $(OBJ)\pxe-loader

$(OBJ)\x86:
  md $(OBJ)\x86

$(OBJ)\tpm:
  md $(OBJ)\tpm

{x86}.asm{$(OBJ)\x86}.obj:
	$(AS) /nologo /c /DBOOT_X86 /I. /Fl$*.lst /Fo$*.obj $<

{tpm}.cpp{$(OBJ)\tpm}.obj:
	$(CC) $(CCFLAGS) /nologo /c /DBOOT_X86 /GF /Gy /Gr /Zi /Od /Oy- /GS- /Gs65536 /FAsc /Fa$*.cod /Fo$*.obj /Fd$*.pdb $<
	
.cpp{$(OBJ)}.obj:
	$(CC) $(CCFLAGS) /nologo /c /DBOOT_X86 /GF /Gy /Gr /Zi /Od /Oy- /GS- /Gs65536 /FAsc /Fa$*.cod /Fo$*.obj /Fd$*.pdb $<
	
$(OBJ)\blentry16.obj: blentry16.asm bl.inc
	$(AS16) /nologo /DBOOT_X86 /AT /omf /c /I. /Fl$(OBJ)\blentry16.lst /Fo$(OBJ)\blentry16.obj blentry16.asm

$(OBJ)\blentry16.com: $(OBJ)\blentry16.obj
	$(LINK16) /nologo /TINY $(OBJ)\blentry16.obj,$(OBJ)\blentry16.com,$(OBJ)\blentry16.map,,,/ONERROR:NOEXE /NOLOGO

$(OBJ)\pxe-bl.exe: $(OBJS)
	$(LINK) /nologo /debug /out:$(OBJ)\pxe-bl.exe /pdb:$(OBJ)\pxe-bl.pdb $(OBJS) /nodefaultlib /entry:BlEntry /subsystem:native /base:0x40000 /fixed /ignore:4078 /ignore:4254 /merge:.rdata=.data /merge:.data=.text

$(OBJ)\pxe-blentry16.com: $(OBJ)\blentry16.obj
	$(LINK16) /nologo /TINY $(OBJ)\blentry16.obj,$(OBJ)\pxe-blentry16.com,$(OBJ)\pxe-blentry16.map,,,/ONERROR:NOEXE /NOLOGO

$(OBJ)\pxe-loader: $(OBJ)\pxe-bl.exe $(OBJ)\pxe-blentry16.com
	$(BLGEN) $(OBJ)\pxe-blentry16.com $(OBJ)\pxe-bl.exe $(OBJ)\pxe-loader

clean-obj:
	cd $(OBJ)
	del *.com *.map *.lst *.obj *.cod *.pdb *.exe 
	cd x86
	del *.lst *.obj

clean:
	cd $(OBJ)
	del *.com *.map *.lst *.obj *.cod *.pdb *.exe loader pxe-loader
	cd x86
	del *.lst *.obj

