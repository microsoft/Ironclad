;++
;
; Copyright (c) Microsoft Corporation
;
; Module Name:
;
;     bl.inc
;
; Abstract:
;
;     This module contains definitions for the boot loader.
;
; Environment:
;
;     Boot loader.
;
;--

;
; Boot sources.
;

CD_BOOT                 equ     00001h
FAT16_BOOT              equ     00002h
FAT32_BOOT              equ     00003h
PXE_BOOT                equ     00004h
FLASH_BOOT              equ     00005h

;
; Segment selectors.
;

NULL_SELECTOR           equ     000h
RM_VIDEO_SELECTOR       equ     008h
RM_CODE_SELECTOR        equ     010h
RM_DATA_SELECTOR        equ     018h
PM_CODE_SELECTOR        equ     020h
PM_DATA_SELECTOR        equ     028h    
LM_CODE_SELECTOR        equ     030h
LM_DATA_SELECTOR        equ     038h
UM_CODE_SELECTOR        equ     040h
UM_DATA_SELECTOR        equ     048h
PROCESSOR_SELECTOR      equ     050h
UNUSED_SELECTOR         equ     058h
TSS_SELECTOR            equ     060h
        
;
; CR0 flags.
;

CR0_PE                  equ     000000001h
CR0_NE                  equ     000000020h
CR0_PG                  equ     080000000h

;
; CR4 flags.
;

CR4_PSE                 equ     000000010h
CR4_PAE                 equ     000000020h
CR4_PCE                 equ     000000100h
CR4_OSFXSR              equ     000000200h

;
; Initial stack pointer values.
;

RM_INITIAL_SS           equ     01000h
RM_INITIAL_SP           equ     0FFF8h
PM_INITIAL_ESP          equ     000020000h
BL_ENTRY_SP             equ     000080000h

;
; Page table addresses.
;

LM_PML4T_ADDRESS        equ     000021000h
PM_PDPT_ADDRESS         equ     000022000h
PM_PDT_ADDRESS          equ     000023000h

;
; Page table entry flags.
;

PTE_PRESENT             equ     000000001h
PTE_WRITEABLE           equ     000000002h
PTE_ACCESSED            equ     000000020h
PTE_2MB                 equ     000000080h

;
; EFER MSR index. (Long Mode)
;

EFER_MSR_INDEX          equ     0C0000080h

;
; EFER flags. (Long Mode)
;

EFER_LME                equ     000000100h
EFER_NXE                equ     000000800h

;
; Image target address.
;

IMAGE_ADDRESS           equ     000040000h

;
; Boot environment block (BEB).
;

BEB_BASE                equ     00002F000h
BEB_SEG16               equ     02F00h
BEB_OFF16               equ     00000h

BEB     struct

        BootType                dd      ?
        BootDriveNumber         dd      ?
        FlashImage              dd      ?
        SmapAddr                dd      ?
        SmapSize                dd      ?
        LegacyCallAddress       dd      ?
        LegacyReturnAddress     dd      ?
        LegacyReturnCr3         dd      ?
        LegacyCall_OpCode       dd      ?
        LegacyCall_Vector       dd      ?
        LegacyCall_eax          dd      ?
        LegacyCall_ebx          dd      ?
        LegacyCall_ecx          dd      ?
        LegacyCall_edx          dd      ?
        LegacyCall_esi          dd      ?
        LegacyCall_edi          dd      ?
        LegacyCall_ds           dd      ?
        LegacyCall_es           dd      ?
        LegacyCall_eflags       dd      ?
        LegacyCall_FramePtr     dd      ?
        LegacyCall_FrameSize    dd      ?
        LegacyCall_FuncPtr      dd      ?
        ApEntry16               dd      ?
        ApEntry                 dd      ?
        ApStartupLock           dd      ?

BEB     ends

;
; Trap Context
;

BL_TRAP_CONTEXT struct

ifdef BOOT_X86
        
        TrapCr2         dd      ?
        TrapEsp         dd      ?
        TrapEbp         dd      ?
        TrapEdi         dd      ?
        TrapEsi         dd      ?
        TrapEdx         dd      ?
        TrapEcx         dd      ?
        TrapEbx         dd      ?
        TrapEax         dd      ?
        TrapNum         dd      ?
        TrapErr         dd      ?
        TrapEip         dd      ?
        TrapCs0         dd      ?
        TrapEfl         dd      ?
        
endif
        
ifdef BOOT_X64
        
        TrapCr2         dq      ?
        TrapRsp         dq      ?
        TrapR15         dq      ?
        TrapR14         dq      ?
        TrapR13         dq      ?
        TrapR12         dq      ?
        TrapR11         dq      ?
        TrapR10         dq      ?
        TrapR09         dq      ?
        TrapR08         dq      ?
        TrapRbp         dq      ?
        TrapRdi         dq      ?
        TrapRsi         dq      ?
        TrapRdx         dq      ?
        TrapRcx         dq      ?
        TrapRbx         dq      ?
        TrapRax         dq      ?
        TrapNum         dq      ?
        TrapErr         dq      ?
        TrapRip         dq      ?
        TrapCs0         dq      ?
        TrapRfl         dq      ?
        
endif        

BL_TRAP_CONTEXT ends

;
; Legacy call opcodes.
;

LC_NOP                          equ     00000h
LC_INTXX                        equ     00001h
LC_FARCALL                      equ     00002h

;
; PE/COFF structures.
;

;
; typedef struct _IMAGE_DOS_HEADER {      // DOS .EXE header
;     WORD   e_magic;                     // Magic number
;     WORD   e_cblp;                      // Bytes on last page of file
;     WORD   e_cp;                        // Pages in file
;     WORD   e_crlc;                      // Relocations
;     WORD   e_cparhdr;                   // Size of header in paragraphs
;     WORD   e_minalloc;                  // Minimum extra paragraphs needed
;     WORD   e_maxalloc;                  // Maximum extra paragraphs needed
;     WORD   e_ss;                        // Initial (relative) SS value
;     WORD   e_sp;                        // Initial SP value
;     WORD   e_csum;                      // Checksum
;     WORD   e_ip;                        // Initial IP value
;     WORD   e_cs;                        // Initial (relative) CS value
;     WORD   e_lfarlc;                    // File address of relocation table
;     WORD   e_ovno;                      // Overlay number
;     WORD   e_res[4];                    // Reserved words
;     WORD   e_oemid;                     // OEM identifier (for e_oeminfo)
;     WORD   e_oeminfo;                   // OEM information; e_oemid specific
;     WORD   e_res2[10];                  // Reserved words
;     LONG   e_lfanew;                    // File address of new exe header
;   } IMAGE_DOS_HEADER, *PIMAGE_DOS_HEADER;
;

IDH_NT_HEADER_OFFSET            equ     00000003Ch

;
; typedef struct _IMAGE_FILE_HEADER {
;     WORD    Machine;
;     WORD    NumberOfSections;
;     DWORD   TimeDateStamp;
;     DWORD   PointerToSymbolTable;
;     DWORD   NumberOfSymbols;
;     WORD    SizeOfOptionalHeader;
;     WORD    Characteristics;
; } IMAGE_FILE_HEADER, *PIMAGE_FILE_HEADER;
;

IFH_NUMBER_OF_SECTIONS          equ     000000002h
IFH_SIZE_OF_OPTIONAL_HEADER     equ     000000010h

ifdef BOOT_X86

;
; typedef struct _IMAGE_OPTIONAL_HEADER32 {
;     WORD    Magic;
;     BYTE    MajorLinkerVersion;
;     BYTE    MinorLinkerVersion;
;     DWORD   SizeOfCode;
;     DWORD   SizeOfInitializedData;
;     DWORD   SizeOfUninitializedData;
;     DWORD   AddressOfEntryPoint;
;     DWORD   BaseOfCode;
;     DWORD   BaseOfData;
;     DWORD   ImageBase;
;     DWORD   SectionAlignment;
;     DWORD   FileAlignment;
;     WORD    MajorOperatingSystemVersion;
;     WORD    MinorOperatingSystemVersion;
;     WORD    MajorImageVersion;
;     WORD    MinorImageVersion;
;     WORD    MajorSubsystemVersion;
;     WORD    MinorSubsystemVersion;
;     DWORD   Win32VersionValue;
;     DWORD   SizeOfImage;
;     DWORD   SizeOfHeaders;
;     DWORD   CheckSum;
;     WORD    Subsystem;
;     WORD    DllCharacteristics;
;     DWORD   SizeOfStackReserve;
;     DWORD   SizeOfStackCommit;
;     DWORD   SizeOfHeapReserve;
;     DWORD   SizeOfHeapCommit;
;     DWORD   LoaderFlags;
;     DWORD   NumberOfRvaAndSizes;
;     IMAGE_DATA_DIRECTORY DataDirectory[IMAGE_NUMBEROF_DIRECTORY_ENTRIES];
; } IMAGE_OPTIONAL_HEADER32, *PIMAGE_OPTIONAL_HEADER32;
;

IOH32_IMAGE_BASE                equ     00000001Ch

endif

ifdef BOOT_X64

;
; typedef struct _IMAGE_OPTIONAL_HEADER64 {
;     WORD        Magic;
;     BYTE        MajorLinkerVersion;
;     BYTE        MinorLinkerVersion;
;     DWORD       SizeOfCode;
;     DWORD       SizeOfInitializedData;
;     DWORD       SizeOfUninitializedData;
;     DWORD       AddressOfEntryPoint;
;     DWORD       BaseOfCode;
;     ULONGLONG   ImageBase;
;     DWORD       SectionAlignment;
;     DWORD       FileAlignment;
;     WORD        MajorOperatingSystemVersion;
;     WORD        MinorOperatingSystemVersion;
;     WORD        MajorImageVersion;
;     WORD        MinorImageVersion;
;     WORD        MajorSubsystemVersion;
;     WORD        MinorSubsystemVersion;
;     DWORD       Win32VersionValue;
;     DWORD       SizeOfImage;
;     DWORD       SizeOfHeaders;
;     DWORD       CheckSum;
;     WORD        Subsystem;
;     WORD        DllCharacteristics;
;     ULONGLONG   SizeOfStackReserve;
;     ULONGLONG   SizeOfStackCommit;
;     ULONGLONG   SizeOfHeapReserve;
;     ULONGLONG   SizeOfHeapCommit;
;     DWORD       LoaderFlags;
;     DWORD       NumberOfRvaAndSizes;
;     IMAGE_DATA_DIRECTORY DataDirectory[IMAGE_NUMBEROF_DIRECTORY_ENTRIES];
; } IMAGE_OPTIONAL_HEADER64, *PIMAGE_OPTIONAL_HEADER64;
;

IOH64_IMAGE_BASE                equ     000000018h

endif
        
IOH_ADDRESS_OF_ENTRY_POINT      equ     000000010h
IOH_SIZE_OF_HEADERS             equ     00000003Ch

;
; typedef struct _IMAGE_NT_HEADERS32/64 {
;     DWORD Signature;
;     IMAGE_FILE_HEADER FileHeader;
;     IMAGE_OPTIONAL_HEADER32/64 OptionalHeader;
; } IMAGE_NT_HEADERS32/64, *PIMAGE_NT_HEADERS32/64;
;

INH_SIGNATURE                   equ     000000000h
INH_FILE_HEADER                 equ     000000004h
INH_OPTIONAL_HEADER             equ     000000018h

;
; Signatures.
;

IMAGE_DOS_SIGNATURE             equ     05A4Dh          ; MZ
IMAGE_NT_SIGNATURE              equ     000004550h      ; PE00

;
; typedef struct _IMAGE_SECTION_HEADER {
;     BYTE    Name[IMAGE_SIZEOF_SHORT_NAME];
;     union {
;             DWORD   PhysicalAddress;
;             DWORD   VirtualSize;
;     } Misc;
;     DWORD   VirtualAddress;
;     DWORD   SizeOfRawData;
;     DWORD   PointerToRawData;
;     DWORD   PointerToRelocations;
;     DWORD   PointerToLinenumbers;
;     WORD    NumberOfRelocations;
;     WORD    NumberOfLinenumbers;
;     DWORD   Characteristics;
; } IMAGE_SECTION_HEADER, *PIMAGE_SECTION_HEADER;
;

ISH_VIRTUAL_SIZE                equ     000000008h
ISH_VIRTUAL_ADDRESS             equ     00000000Ch
ISH_SIZE_OF_RAW_DATA            equ     000000010h
ISH_POINTER_TO_RAW_DATA         equ     000000014h

IMAGE_SECTION_HEADER_SIZE       equ     000000028h



