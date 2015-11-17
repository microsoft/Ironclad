//++
//
//  Copyright (c) Microsoft Corporation
//
//  Module Name:
//
//    blflash.cpp
//
//  Abstract:
//
//    This module implements flash support for the boot loader.
//
//--

#include "bl.h"

struct FLASH_HEADER
{
    UINT8   Label[18];
    UINT8   HeadSize;
    UINT8   SpecSize;
    UINT32  PageSize;
    UINT32  MajorVersion;
    UINT32  MinorVersion;
};

struct FLASH_FILE
{
    UINT32  PathOffset;
    UINT32  DataOffset;
    UINT32  Size;
};

static PUINT8       BlFlashBase = NULL;
static FLASH_FILE * BlFlashImages = NULL;

FLASH_FILE *
BlFlashRecordIsValid(
    FLASH_FILE *Current
    )

//++
//
//  Routine Description:
//
//    Find the next valid flash file record.
//
//  Return Value:
//
//    Pointer to the next valid flash file record, if the query operation was successful.
//    NULL, if there are no remaining valid record.
//
//--

{
    for (;; Current++) {
        if ((Current->DataOffset == 0xffffffff && Current->Size == 0xffffffff) ||
            (Current->DataOffset == 0 && Current->Size == 0)) {
            continue;
        }
        else if (Current->DataOffset == 0xffffffff && Current->Size == 0) {
            return NULL;
        }
        return Current;
    }
}

FLASH_FILE *
BlFlashFindFile(
    PCSTR Path
    )

//++
//
//  Routine Description:
//
//    Find the flash file record matching this path name.
//
//  Arguments:
//
//    Path        - Supplies the path to the file to query.
//
//  Return Value:
//
//    Pointer to the flash file record, if the query operation was successful.
//    NULL, otherwise.
//
//--

{
    for (FLASH_FILE *File = BlFlashImages; File != NULL; File = BlFlashRecordIsValid(File + 1)) {
        if (BlRtlEqualStringI(Path, (PCSTR)(BlFlashBase + File->PathOffset))) {
            return File;
        }
    }
    return NULL;
}


BOOLEAN
BlFlashGetFileSize(
    PCSTR Path,
    PUINT32 FileSize
    )

//++
//
//  Routine Description:
//
//    This function queries the size of the specified file.
//
//  Arguments:
//
//    Path        - Supplies the path to the file to query.
//
//    FileSize    - Receives the size of the file.
//
//  Return Value:
//
//    TRUE, if the query operation was successful.
//    FALSE, otherwise.
//
//--

{
    FLASH_FILE * File = BlFlashFindFile(Path);

    if (File != NULL) {

        *FileSize = File->Size;

        return TRUE;

    }

    return FALSE;
}

//++
//
//  Routine Description:
//
//    This function reads from the specified file.
//
//  Arguments:
//
//    Path            - Supplies the path to the file to read.
//
//    Buffer          - Receives data.
//
//    NumberOfBytes   - Supplies the number of bytes to read.
//
//  Return Value:
//
//    TRUE, if the read operation was successful.
//    FALSE, otherwise.
//
//--

BOOLEAN
BlFlashReadFile(
    PCSTR Path,
    PVOID Buffer,
    UINT32 NumberOfBytes
    )
{
    (void)Path;
    (void)NumberOfBytes;
    (void)Buffer;

    FLASH_FILE * File = BlFlashFindFile(Path);

    if (File != NULL) {

        BlRtlCopyMemory(Buffer, BlFlashBase + File->DataOffset, NumberOfBytes);

        return TRUE;
    }

    return FALSE;
}

VOID
BlFlashInitialize(
    PVOID SearchBegin,
    PVOID SearchLimit
    )
{
    // walk through at 64KB boundaries looking for flash image.
    for (FLASH_HEADER * Search = (FLASH_HEADER *)SearchBegin;
         Search <= (FLASH_HEADER *)SearchLimit;
         Search = (FLASH_HEADER *)(((PUINT8)Search) + 0x10000)) {

        if (!BlRtlEqualStringI((PCSTR)Search->Label, "SingularityFlash!")) {
            continue;
        }
        if (Search->HeadSize != sizeof(FLASH_HEADER)) {
            continue;
        }
        if (Search->SpecSize != sizeof(FLASH_FILE)) {
            continue;
        }
        if (Search->MajorVersion != ~0u || Search->MinorVersion != ~0u) {
            BlRtlPrintf("--- Version %x.%x didn't match\n",
                        Search->MajorVersion, Search->MinorVersion);
            continue;
        }
        if (Search->PageSize != 0x1000) {
            continue;
        }

        BlFlashBase = (PUINT8)Search;
        BlFlashImages = BlFlashRecordIsValid((FLASH_FILE *)(Search + 1));
        break;
    }

    BlFsGetFileSize = BlFlashGetFileSize;
    BlFsReadFile = BlFlashReadFile;
}
