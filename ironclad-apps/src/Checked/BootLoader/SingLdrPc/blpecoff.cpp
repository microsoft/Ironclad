//++
//
//  Copyright (c) Microsoft Corporation
//
//  Module Name:
//
//    blpecoff.cpp
//
//  Abstract:
//
//    This module implements PE / COFF support for the boot loader.
//
//--

#include "bl.h"

#define IMAGE_DOS_SIGNATURE                 0x05A4D         // MZ
#define IMAGE_NT_SIGNATURE                  0x000004550     // PE00

typedef struct _IMAGE_DOS_HEADER {      //- DOS .EXE header
    UINT16 e_magic;                     //- Magic number
    UINT16 e_cblp;                      //- Bytes on last page of file
    UINT16 e_cp;                        //- Pages in file
    UINT16 e_crlc;                      //- Relocations
    UINT16 e_cparhdr;                   //- Size of header in paragraphs
    UINT16 e_minalloc;                  //- Minimum extra paragraphs needed
    UINT16 e_maxalloc;                  //- Maximum extra paragraphs needed
    UINT16 e_ss;                        //- Initial (relative) SS value
    UINT16 e_sp;                        //- Initial SP value
    UINT16 e_csum;                      //- Checksum
    UINT16 e_ip;                        //- Initial IP value
    UINT16 e_cs;                        //- Initial (relative) CS value
    UINT16 e_lfarlc;                    //- File address of relocation table
    UINT16 e_ovno;                      //- Overlay number
    UINT16 e_res[4];                    //- Reserved words
    UINT16 e_oemid;                     //- OEM identifier (for e_oeminfo)
    UINT16 e_oeminfo;                   //- OEM information; e_oemid specific
    UINT16 e_res2[10];                  //- Reserved words
    INT32 e_lfanew;                      //- File address of new exe header
} IMAGE_DOS_HEADER, *PIMAGE_DOS_HEADER;


typedef struct _IMAGE_FILE_HEADER {
    UINT16 Machine;
    UINT16 NumberOfSections;
    UINT32 TimeDateStamp;
    UINT32 PointerToSymbolTable;
    UINT32 NumberOfSymbols;
    UINT16 SizeOfOptionalHeader;
    UINT16 Characteristics;
} IMAGE_FILE_HEADER, *PIMAGE_FILE_HEADER;

typedef struct _IMAGE_DATA_DIRECTORY {
    UINT32 VirtualAddress;
    UINT32 Size;
} IMAGE_DATA_DIRECTORY, *PIMAGE_DATA_DIRECTORY;

#define IMAGE_NUMBEROF_DIRECTORY_ENTRIES    16

#define IMAGE_DIRECTORY_ENTRY_BASERELOC     5

#if defined(BOOT_X86)

typedef struct _IMAGE_OPTIONAL_HEADER_32 {
    UINT16 Magic;
    UINT8 MajorLinkerVersion;
    UINT8 MinorLinkerVersion;
    UINT32 SizeOfCode;
    UINT32 SizeOfInitializedData;
    UINT32 SizeOfUninitializedData;
    UINT32 AddressOfEntryPoint;
    UINT32 BaseOfCode;
    UINT32 BaseOfData;
    UINT32 ImageBase;
    UINT32 SectionAlignment;
    UINT32 FileAlignment;
    UINT16 MajorOperatingSystemVersion;
    UINT16 MinorOperatingSystemVersion;
    UINT16 MajorImageVersion;
    UINT16 MinorImageVersion;
    UINT16 MajorSubsystemVersion;
    UINT16 MinorSubsystemVersion;
    UINT32 Win32VersionValue;
    UINT32 SizeOfImage;
    UINT32 SizeOfHeaders;
    UINT32 CheckSum;
    UINT16 Subsystem;
    UINT16 DllCharacteristics;
    UINT32 SizeOfStackReserve;
    UINT32 SizeOfStackCommit;
    UINT32 SizeOfHeapReserve;
    UINT32 SizeOfHeapCommit;
    UINT32 LoaderFlags;
    UINT32 NumberOfRvaAndSizes;
    IMAGE_DATA_DIRECTORY DataDirectory[IMAGE_NUMBEROF_DIRECTORY_ENTRIES];
} IMAGE_OPTIONAL_HEADER32, *PIMAGE_OPTIONAL_HEADER32;

typedef struct _IMAGE_NT_HEADERS32 {
    UINT32 Signature;
    IMAGE_FILE_HEADER FileHeader;
    IMAGE_OPTIONAL_HEADER32 OptionalHeader;
} IMAGE_NT_HEADERS32, *PIMAGE_NT_HEADERS32;

typedef IMAGE_NT_HEADERS32 IMAGE_NT_HEADERS, *PIMAGE_NT_HEADERS;

#elif defined(BOOT_X64)

typedef struct _IMAGE_OPTIONAL_HEADER64 {
    UINT16 Magic;
    UINT8 MajorLinkerVersion;
    UINT8 MinorLinkerVersion;
    UINT32 SizeOfCode;
    UINT32 SizeOfInitializedData;
    UINT32 SizeOfUninitializedData;
    UINT32 AddressOfEntryPoint;
    UINT32 BaseOfCode;
    UINT64 ImageBase;
    UINT32 SectionAlignment;
    UINT32 FileAlignment;
    UINT16 MajorOperatingSystemVersion;
    UINT16 MinorOperatingSystemVersion;
    UINT16 MajorImageVersion;
    UINT16 MinorImageVersion;
    UINT16 MajorSubsystemVersion;
    UINT16 MinorSubsystemVersion;
    UINT32 Win32VersionValue;
    UINT32 SizeOfImage;
    UINT32 SizeOfHeaders;
    UINT32 CheckSum;
    UINT16 Subsystem;
    UINT16 DllCharacteristics;
    UINT64 SizeOfStackReserve;
    UINT64 SizeOfStackCommit;
    UINT64 SizeOfHeapReserve;
    UINT64 SizeOfHeapCommit;
    UINT32 LoaderFlags;
    UINT32 NumberOfRvaAndSizes;
    IMAGE_DATA_DIRECTORY DataDirectory[IMAGE_NUMBEROF_DIRECTORY_ENTRIES];
} IMAGE_OPTIONAL_HEADER64, *PIMAGE_OPTIONAL_HEADER64;

typedef struct _IMAGE_NT_HEADERS64 {
    UINT32 Signature;
    IMAGE_FILE_HEADER FileHeader;
    IMAGE_OPTIONAL_HEADER64 OptionalHeader;
} IMAGE_NT_HEADERS64, *PIMAGE_NT_HEADERS64;

typedef IMAGE_NT_HEADERS64 IMAGE_NT_HEADERS, *PIMAGE_NT_HEADERS;

#endif

#define IMAGE_SIZEOF_SHORT_NAME              8

typedef struct _IMAGE_SECTION_HEADER {
    UINT8 Name[IMAGE_SIZEOF_SHORT_NAME];
    union {
        UINT32 PhysicalAddress;
        UINT32 VirtualSize;
    } Misc;
    UINT32 VirtualAddress;
    UINT32 SizeOfRawData;
    UINT32 PointerToRawData;
    UINT32 PointerToRelocations;
    UINT32 PointerToLinenumbers;
    UINT16 NumberOfRelocations;
    UINT16 NumberOfLinenumbers;
    UINT32 Characteristics;
} IMAGE_SECTION_HEADER, *PIMAGE_SECTION_HEADER;

typedef struct _IMAGE_BASE_RELOCATION {
    UINT32   VirtualAddress;
    UINT32   SizeOfBlock;
    UINT16  TypeOffset[0];
} IMAGE_BASE_RELOCATION, *PIMAGE_BASE_RELOCATION;

#define IMAGE_REL_BASED_ABSOLUTE              0
#define IMAGE_REL_BASED_HIGHLOW               3
#define IMAGE_REL_BASED_DIR64                 10

VOID
BlPeGetVirtualRange(
    PVOID Image,
    PVOID *VirtualBase,
    ULONG_PTR *VirtualSize
    )

//-++
//-
//-  Routine Description:
//-
//-    This function queries the virtual range for the specified image.
//-
//-  Arguments:
//-
//-    Image       - Supplies a pointer to the image.
//-
//-    VirtualBase - Receives the virtual base address of the image.
//-
//-    VirtualSize - Receives the virtual size of the image.
//-
//---

{
    PIMAGE_DOS_HEADER DosHeader;
    UINT32 Index;
    PIMAGE_NT_HEADERS NtHeader;
    PIMAGE_SECTION_HEADER Section;
    UINT32 SectionEnd;

    DosHeader = (PIMAGE_DOS_HEADER) Image;

    if (DosHeader->e_magic != IMAGE_DOS_SIGNATURE) {

        BlRtlPrintf("PECOFF: Invalid image!\n");
        BlRtlHalt();
    }

    NtHeader = (PIMAGE_NT_HEADERS) ((ULONG_PTR) Image + DosHeader->e_lfanew);

    if (NtHeader->Signature != IMAGE_NT_SIGNATURE) {

        BlRtlPrintf("PECOFF: Invalid image!\n");
        BlRtlHalt();
    }

    if (NtHeader->FileHeader.NumberOfSections == 0) {

        BlRtlPrintf("PECOFF: Invalid image!\n");
        BlRtlHalt();
    }

    if ((NtHeader->OptionalHeader.ImageBase % PAGE_SIZE) != 0) {

        BlRtlPrintf("PECOFF: Invalid image!\n");
        BlRtlHalt();
    }

    *VirtualBase = (PVOID) NtHeader->OptionalHeader.ImageBase;
    *VirtualSize = 0;

    Section = (PIMAGE_SECTION_HEADER) (((ULONG_PTR) &NtHeader->OptionalHeader) + NtHeader->FileHeader.SizeOfOptionalHeader);

    for (Index = 0; Index < NtHeader->FileHeader.NumberOfSections; Index += 1) {

        SectionEnd = Section[Index].VirtualAddress + Section[Index].Misc.VirtualSize;

        if (SectionEnd > *VirtualSize) {

            *VirtualSize = SectionEnd;
        }
    }

    *VirtualSize = ROUND_UP_TO_PAGES(*VirtualSize);

    return;
}

VOID
BlPeApplyFixupBlock(
    PIMAGE_BASE_RELOCATION Block,
    ULONG_PTR VirtualBase,
    ULONG_PTR RelocDiff
    )

//-++
//-
//-  Routine Description:
//-
//-    This function applies all of the base fixups in the specified block to the image.
//-
//-  Arguments:
//-
//-    Block       - Supplies a pointer to the base relocation fixup block.
//-
//-    VirtualBase - Supplies the target address of the image.
//-
//-    RelocDiff   - Supplies the offset of the image target address from the base address.
//-
//---

{
    PUINT16 Reloc;
    PUINT16 BlockEnd;
    ULONG_PTR BlockBase;
    ULONG_PTR Target;

    Reloc = Block->TypeOffset;
    BlockEnd = (PUINT16) ( ((PUINT8) Block) + Block->SizeOfBlock);
    BlockBase = VirtualBase + Block->VirtualAddress;

#if PECOFF_VERBOSE

    BlRtlPrintf("PECOFF: Reloc Block %p:\n", Block->VirtualAddress);

#endif

    for (; Reloc < BlockEnd; Reloc++) {

        Target = BlockBase + (*Reloc & 0xfff);

#if PECOFF_VERBOSE

        switch (*Reloc >> 12) {

            case IMAGE_REL_BASED_ABSOLUTE: {

                BlRtlPrintf("PECOFF:  %p: abs:%x \r", (PUINT32) Target, * (PUINT32) Target);
                break;
            }

            case IMAGE_REL_BASED_HIGHLOW: {

                BlRtlPrintf("PECOFF:  %p: r32:%x->%x \r", (PUINT32) Target, * (PUINT32) Target, * (PUINT32) Target + (UINT32) RelocDiff);
                break;
            }

            case IMAGE_REL_BASED_DIR64: {

                BlRtlPrintf("PECOFF:  %p: r64:%lx->%lx \r", (PUINT64) Target, * (PUINT64) Target, * (PUINT64) Target + (UINT64) RelocDiff);
                break;
            }

            default: {

                BlRtlPrintf("PECOFF:  %p: %x ??? \r", (PUINT32) Target, Reloc[0] >> 12);
                break;
            }
        }

#endif

        switch (*Reloc >> 12) {
            case IMAGE_REL_BASED_ABSOLUTE: {

                break;
            }

            case IMAGE_REL_BASED_HIGHLOW: {

                * (PUINT32) Target += (UINT32) RelocDiff;
                break;
            }

            case IMAGE_REL_BASED_DIR64: {

                * (PUINT64 *) Target += (UINT64) RelocDiff;
                break;
            }

            default: {

                BlRtlPrintf("PECOFF: Illegal relocation.\n");
                BlRtlHalt();
            }
        }
    }
}

VOID
BlPeLoadImage(
    PVOID LoadBase,
    UINT32 ImageSize,
    PVOID Image,
    PVOID *EntryPoint,
    BOOLEAN isSLB
    )

//-++
//-
//-  Routine Description:
//-
//-    This function loads the specified image.
//-
//-  Arguments:
//-
//-    Image       - Supplies a pointer to the image to load.
//-
//-    EntryPoint  - Receives a pointer to the entry point of the image.
//-
//---

{
    ULONG_PTR BytesToCopy;
    PIMAGE_DOS_HEADER DosHeader;
    UINT32 Index;
    PIMAGE_NT_HEADERS NtHeader;
    PIMAGE_SECTION_HEADER Section;
    ULONG_PTR VirtualBase;
    ULONG_PTR RelocDiff;

    VirtualBase = (ULONG_PTR) LoadBase;
    DosHeader = (PIMAGE_DOS_HEADER) Image;

    if (DosHeader->e_magic != IMAGE_DOS_SIGNATURE) {

        BlRtlPrintf("PECOFF: Missing MZ!\n");
        BlRtlHalt();
    }

    NtHeader = (PIMAGE_NT_HEADERS) ((ULONG_PTR) Image + DosHeader->e_lfanew);

    if (NtHeader->Signature != IMAGE_NT_SIGNATURE) {

        BlRtlPrintf("PECOFF: Missing PE!\n");
        BlRtlHalt();
    }

    if (NtHeader->FileHeader.NumberOfSections == 0) {

        BlRtlPrintf("PECOFF: No sections!\n");
        BlRtlHalt();
    }

    if ((NtHeader->OptionalHeader.ImageBase % PAGE_SIZE) != 0) {

        BlRtlPrintf("PECOFF: Not page aligned.\n");
        BlRtlHalt();
    }

    if (isSLB && ImageSize > 64*1024) {
        BlRtlPrintf("PECOFF: Image is too large for late launch!\n");
        BlRtlHalt();
    }

    //- Zero out the entire range of memory used by the kernel,
    //- to ensure a consistent measurement during late launch via SKINIT
    BlRtlZeroMemory((PVOID) VirtualBase, ImageSize);

    BlRtlCopyMemory((PVOID) VirtualBase,
                    Image,
                    NtHeader->OptionalHeader.SizeOfHeaders);

    Section = (PIMAGE_SECTION_HEADER) (((ULONG_PTR) &NtHeader->OptionalHeader) + NtHeader->FileHeader.SizeOfOptionalHeader);

    for (Index = 0; Index < NtHeader->FileHeader.NumberOfSections; Index += 1) {

        BlRtlZeroMemory((PVOID) (VirtualBase + Section[Index].VirtualAddress), Section[Index].Misc.VirtualSize);

        if (Section[Index].SizeOfRawData < Section[Index].Misc.VirtualSize) {

            BytesToCopy = Section[Index].SizeOfRawData;

        } else {

            BytesToCopy = Section[Index].Misc.VirtualSize;
        }

        BlRtlCopyMemory((PVOID) (VirtualBase + Section[Index].VirtualAddress),
                        (PVOID) (((ULONG_PTR) Image) + Section[Index].PointerToRawData),
                        BytesToCopy);

#if PECOFF_VERBOSE

        {
            CHAR Temp[IMAGE_SIZEOF_SHORT_NAME + 1];

            BlRtlCopyMemory(Temp,
                            Section[Index].Name,
                            IMAGE_SIZEOF_SHORT_NAME);

            Temp[IMAGE_SIZEOF_SHORT_NAME] = 0;

            BlRtlPrintf("PECOFF: %p ... %p (%p ... %p) %s\n",
                        VirtualBase + Section[Index].VirtualAddress,
                        VirtualBase + Section[Index].VirtualAddress + Section[Index].Misc.VirtualSize - 1,
                        (((ULONG_PTR) Image) + Section[Index].PointerToRawData),
                        (((ULONG_PTR) Image) + Section[Index].PointerToRawData) + BytesToCopy,
                        Temp);
        }

#endif

    }

    RelocDiff = VirtualBase - (ULONG_PTR)NtHeader->OptionalHeader.ImageBase;

    if (RelocDiff != 0) {

        PUINT8 RelocList;
        PUINT8 RelocListEnd;
        PIMAGE_BASE_RELOCATION Block;

        RelocList = (PUINT8) (VirtualBase + NtHeader->OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_BASERELOC].VirtualAddress);
        RelocListEnd = RelocList + NtHeader->OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_BASERELOC].Size;

#if PECOFF_VERBOSE

        BlRtlPrintf("PECOFF: Relocs: %p ... %p\n", RelocList, RelocListEnd);

#endif

        while (RelocList < RelocListEnd) {

            Block = (PIMAGE_BASE_RELOCATION) RelocList;

            BlPeApplyFixupBlock(Block, VirtualBase, RelocDiff);

            RelocList += Block->SizeOfBlock;
        }
    }

    *EntryPoint = (PVOID) (VirtualBase + NtHeader->OptionalHeader.AddressOfEntryPoint);

    if (isSLB) {
        //- Prepare the secure loader image with the necessary header
        //- Make sure the first 32 bits of the image are [31..16] == length and [15..0] == entry point
        *((UINT32*)VirtualBase) = (ImageSize << 16) | (NtHeader->OptionalHeader.AddressOfEntryPoint & 0x0000FFFF);

        BlRtlPrintf("PECOFF: Base: %p  AddressOfEntryPoint: %p ImageSize: %p\n", VirtualBase,  NtHeader->OptionalHeader.AddressOfEntryPoint, ImageSize);
    }
    return;
}

