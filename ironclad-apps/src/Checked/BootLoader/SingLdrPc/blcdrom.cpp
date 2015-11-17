//++
//
//  Copyright (c) Microsoft Corporation
//
//  Module Name:
//
//    blcdrom.cpp
//
//  Abstract:
//
//    This module implements CDROM support for the boot loader.
//
//--

#include "bl.h"

#define ISO9660_LOGICAL_BLOCK_SIZE                      2048
#define ISO9660_ROUND_UP_TO_LOGICAL_BLOCKS(X)           (((X) + ISO9660_LOGICAL_BLOCK_SIZE - 1) & (~(ISO9660_LOGICAL_BLOCK_SIZE - 1)))

#define ISO9660_VOLUME_SPACE_DATA_AREA_LBN              16

#define ISO9660_VOLUME_DESCRIPTOR_TYPE_BOOT             0x00
#define ISO9660_VOLUME_DESCRIPTOR_TYPE_PRIMARY          0x01
#define ISO9660_VOLUME_DESCRIPTOR_TYPE_SUPPLEMENTARY    0x02
#define ISO9660_VOLUME_DESCRIPTOR_TYPE_TERMINATOR       0xFF

#define ISO9660_MAX_PATH                                255

#pragma pack(1)

typedef struct _ISO9660_LOGICAL_BLOCK {
    UINT8 Data[ISO9660_LOGICAL_BLOCK_SIZE];
} ISO9660_LOGICAL_BLOCK, *PISO9660_LOGICAL_BLOCK;

C_ASSERT(sizeof(ISO9660_LOGICAL_BLOCK) == ISO9660_LOGICAL_BLOCK_SIZE);

typedef struct _ISO9660_DIRECTORY_RECORD {
    UINT8 DirectoryRecordLength;
    UINT8 ExtendedAttributeRecordLength;
    UINT32 ExtentLocation;
    UINT32 ExtentLocation_BigEndian;
    UINT32 DataLength;
    UINT32 DataLength_BigEndian;
    UINT8 RecordingDateTime[7];
    union {
        struct {
            UINT8 Present:1;
            UINT8 Directory:1;
            UINT8 AssociatedFile:1;
            UINT8 Record:1;
            UINT8 Protection:1;
            UINT8 Reserved:2;
            UINT8 MultiExtent:1;
        } s1;
        UINT8 FileFlags;
    } u1;
    UINT8 FileUnitSize;
    UINT8 InterleaveGapSize;
    UINT16 VolumeSequenceNumber;
    UINT16 VolumeSequenceNumber_BigEndian;
    UINT8 FileIdentifierLength;
    UINT8 FileIdentifier[1];
} ISO9660_DIRECTORY_RECORD, *PISO9660_DIRECTORY_RECORD;

C_ASSERT(sizeof(ISO9660_DIRECTORY_RECORD) == 34);

typedef struct _ISO9660_PRIMARY_VOLUME_DESCRIPTOR {
    UINT8 VolumeDescriptorType;
    UINT8 StandardIdentifier[5];
    UINT8 VolumeDescriptorVersion;
    UINT8 Reserved1;
    UINT8 SystemIdentifier[32];
    UINT8 VolumeIdentifier[32];
    UINT8 Reserved2[8];
    UINT32 VolumeSpaceSize;
    UINT32 VolumeSpaceSize_BigEndian;
    UINT8 Reserved3[32];
    UINT16 VolumeSetSize;
    UINT16 VolumeSetSize_BigEndian;
    UINT16 VolumeSequenceNumber;
    UINT16 VolumeSequenceNumber_BigEndian;
    UINT16 LogicalBlockSize;
    UINT16 LogicalBlockSize_BigEndian;
    UINT32 PathTableSize;
    UINT32 PathTableSize_BigEndian;
    UINT32 PathTableLocation[2];
    UINT32 PathTableLocation_BigEndian[2];
    ISO9660_DIRECTORY_RECORD RootDirectory;
    UINT8 VolumeSetIdentifier[128];
    UINT8 PublisherIdentifier[128];
    UINT8 DataPreparerIdentifier[128];
    UINT8 ApplicationIdentifier[128];
    UINT8 CopyrightFileIdentifier[37];
    UINT8 AbstractFileIdentifier[37];
    UINT8 BibliographicFileIdentifier[37];
    UINT8 VolumeCreationDateTime[17];
    UINT8 VolumeModificationDateTime[17];
    UINT8 VolumeExpirationDateTime[17];
    UINT8 VolumeEffectiveDateTime[17];
    UINT8 FileStructureVersion;
    UINT8 Reserved4;
    UINT8 ReservedForApplication[512];
    UINT8 Reserved5[653];
} ISO9660_PRIMARY_VOLUME_DESCRIPTOR, *PISO9660_PRIMARY_VOLUME_DESCRIPTOR;

C_ASSERT(sizeof(ISO9660_PRIMARY_VOLUME_DESCRIPTOR) == ISO9660_LOGICAL_BLOCK_SIZE);

typedef struct _ISO9660_SUPPLEMENTARY_VOLUME_DESCRIPTOR {
    UINT8 VolumeDescriptorType;
    UINT8 StandardIdentifier[5];
    UINT8 VolumeDescriptorVersion;
    UINT8 VolumeFlags;
    UINT8 SystemIdentifier[32];
    UINT8 VolumeIdentifier[32];
    UINT8 Reserved2[8];
    UINT32 VolumeSpaceSize;
    UINT32 VolumeSpaceSize_BigEndian;
    UINT8 EscapeSequences[32];
    UINT16 VolumeSetSize;
    UINT16 VolumeSetSize_BigEndian;
    UINT16 VolumeSequenceNumber;
    UINT16 VolumeSequenceNumber_BigEndian;
    UINT16 LogicalBlockSize;
    UINT16 LogicalBlockSize_BigEndian;
    UINT32 PathTableSize;
    UINT32 PathTableSize_BigEndian;
    UINT32 PathTableLocation[2];
    UINT32 PathTableLocation_BigEndian[2];
    ISO9660_DIRECTORY_RECORD RootDirectory;
    UINT8 VolumeSetIdentifier[128];
    UINT8 PublisherIdentifier[128];
    UINT8 DataPreparerIdentifier[128];
    UINT8 ApplicationIdentifier[128];
    UINT8 CopyrightFileIdentifier[37];
    UINT8 AbstractFileIdentifier[37];
    UINT8 BibliographicFileIdentifier[37];
    UINT8 VolumeCreationDateTime[17];
    UINT8 VolumeModificationDateTime[17];
    UINT8 VolumeExpirationDateTime[17];
    UINT8 VolumeEffectiveDateTime[17];
    UINT8 FileStructureVersion;
    UINT8 Reserved4;
    UINT8 ReservedForApplication[512];
    UINT8 Reserved5[653];
} ISO9660_SUPPLEMENTARY_VOLUME_DESCRIPTOR, *PISO9660_SUPPLEMENTARY_VOLUME_DESCRIPTOR;

C_ASSERT(sizeof(ISO9660_SUPPLEMENTARY_VOLUME_DESCRIPTOR) == ISO9660_LOGICAL_BLOCK_SIZE);

typedef struct _ISO9660_VOLUME_DESCRIPTOR {
    union {
        UINT8 VolumeDescriptorType;
        ISO9660_PRIMARY_VOLUME_DESCRIPTOR Primary;
        ISO9660_SUPPLEMENTARY_VOLUME_DESCRIPTOR Supplementary;
    } u1;
} ISO9660_VOLUME_DESCRIPTOR, *PISO9660_VOLUME_DESCRIPTOR;

C_ASSERT(sizeof(ISO9660_VOLUME_DESCRIPTOR) == ISO9660_LOGICAL_BLOCK_SIZE);

#pragma pack()

UINT8 BlCdDriveId;
INT13_DRIVE_PARAMETERS BlCdDriveParameters;
ISO9660_VOLUME_DESCRIPTOR BlCdVolumeDescriptor;

ISO9660_LOGICAL_BLOCK BlCdTemporaryBlock[32];
UINT16 BlCdTemporaryBlockCount = sizeof(BlCdTemporaryBlock) / sizeof(BlCdTemporaryBlock[0]);

VOID
BlCdReadLogicalBlock(
    UINT32 LogicalBlockNumber,
    UINT32 NumberOfBlocks,
    PISO9660_LOGICAL_BLOCK LogicalBlock
    )

//++
//
//  Routine Description:
//
//    This function reads the specified logical block.
//
//  Arguments:
//
//    LogicalBlockNumber  - Supplies the number of the logical block to read.
//
//    NumberOfBlocks      - Supplies the number of blocks to read.
//
//    LogicalBlock        - Receives logical block data.
//
//--

{
    UINT16 ChunkSize;
    BOOLEAN Result;

    while (NumberOfBlocks > 0) {

        if (NumberOfBlocks < BlCdTemporaryBlockCount) {

            ChunkSize = (UINT16) NumberOfBlocks;

        } else {

            ChunkSize = BlCdTemporaryBlockCount;
        }

        Result = BlRtlReadDrive(BlCdDriveId,
                                LogicalBlockNumber,
                                ChunkSize,
                                BlCdTemporaryBlock);

        if (Result == FALSE) {

            BlRtlPrintf("CDROM: I/O Error: DriveID=0x%02x LBN=%u Count=%u\n",
                        BlCdDriveId,
                        LogicalBlockNumber,
                        ChunkSize);

            BlRtlHalt();
        }

        BlRtlCopyMemory(LogicalBlock,
                        BlCdTemporaryBlock,
                        ChunkSize * sizeof(ISO9660_LOGICAL_BLOCK));

        LogicalBlockNumber += ChunkSize;
        LogicalBlock += ChunkSize;
        NumberOfBlocks -= ChunkSize;
    }

    return;
}

BOOLEAN
BlCdFindDirectoryRecord(
    PCSTR Path,
    PISO9660_DIRECTORY_RECORD DirectoryRecord
    )

//++
//
//  Routine Description:
//
//    This function finds the directory record for the specified path.
//
//  Arguments:
//
//    Path                - Supplies the path to look up.
//
//    DirectoryRecord     - Receives directory record.
//
//  Return Value:
//
//    TRUE, if directory record was found.
//    FALSE, otherwise.
//
//--

{
    PISO9660_LOGICAL_BLOCK DirectoryData;
    UINT32 DirectoryDataIndex;
    ULONG_PTR DirectoryDataLimit;
    UINT32 DirectoryDataExtentStart;
    UINT32 DirectoryDataExtentSize;
    PISO9660_DIRECTORY_RECORD Entry;
    UINT32 Index;
    PCSTR NextToken;
    PCSTR Separator;
    CHAR Temp[ISO9660_MAX_PATH];
    CHAR Token[ISO9660_MAX_PATH];
    UINT32 TokenSize;

    DirectoryDataExtentStart = BlCdVolumeDescriptor.u1.Supplementary.RootDirectory.ExtentLocation;
    DirectoryDataExtentSize = ROUND_UP_TO_POWER2(BlCdVolumeDescriptor.u1.Supplementary.RootDirectory.DataLength, ISO9660_LOGICAL_BLOCK_SIZE) / ISO9660_LOGICAL_BLOCK_SIZE;

    NextToken = Path;

    for (;;) {

        BLASSERT(DirectoryDataExtentStart > ISO9660_VOLUME_SPACE_DATA_AREA_LBN);

        BLASSERT(DirectoryDataExtentSize > 0);

        BLASSERT((*NextToken != 0) && (*NextToken != '/'));

        Separator = NextToken;

        while ((*Separator != '/') && (*Separator != 0)) {

            Separator += 1;
        }

        TokenSize = (UINT32) (Separator - NextToken);

        for (Index = 0; Index < TokenSize; Index += 1) {

            Token[Index] = BlRtlConvertCharacterToUpperCase(NextToken[Index]);
        }

        Token[TokenSize] = 0;

        DirectoryData = (PISO9660_LOGICAL_BLOCK) BlPoolAllocateBlock(DirectoryDataExtentSize * ISO9660_LOGICAL_BLOCK_SIZE);
        DirectoryDataLimit = (ULONG_PTR) DirectoryData + (DirectoryDataExtentSize * ISO9660_LOGICAL_BLOCK_SIZE);

        BlCdReadLogicalBlock(DirectoryDataExtentStart,
                             DirectoryDataExtentSize,
                             DirectoryData);

        Entry = NULL;

        for (DirectoryDataIndex = 0; (Entry == NULL) && (DirectoryDataIndex < DirectoryDataExtentSize); DirectoryDataIndex += 1) {

            Entry = (PISO9660_DIRECTORY_RECORD) &DirectoryData[DirectoryDataIndex];

            for (;;) {

                if (Entry->DirectoryRecordLength == 0) {

                    Entry = NULL;
                    break;
                }

                if (Entry->FileIdentifierLength == (TokenSize * 2)) {

                    for (Index = 0; Index < TokenSize; Index += 1) {

                        Temp[Index] = BlRtlConvertCharacterToUpperCase(Entry->FileIdentifier[(Index * 2) + 1]);
                    }

                    if (BlRtlCompareMemory(Temp, Token, TokenSize) != FALSE) {

                        break;
                    }
                }

                Entry = (PISO9660_DIRECTORY_RECORD) ROUND_UP_TO_POWER2((((ULONG_PTR) Entry) + Entry->DirectoryRecordLength), 2);

                if ((ULONG_PTR) Entry >= DirectoryDataLimit) {

                    Entry = NULL;
                    break;
                }
            }
        }

        if (Entry == NULL) {

            BlPoolFreeBlock(DirectoryData);

            return FALSE;
        }

        if (*Separator == 0) {

            BlRtlCopyMemory(DirectoryRecord,
                            Entry,
                            sizeof(ISO9660_DIRECTORY_RECORD));

            BlPoolFreeBlock(DirectoryData);

            return TRUE;
        }

        if (Entry->u1.s1.Directory == FALSE) {

            BlPoolFreeBlock(DirectoryData);

            return FALSE;
        }

        DirectoryDataExtentStart = Entry->ExtentLocation;
        DirectoryDataExtentSize = ROUND_UP_TO_POWER2(Entry->DataLength, ISO9660_LOGICAL_BLOCK_SIZE) / ISO9660_LOGICAL_BLOCK_SIZE;
        NextToken = Separator + 1;

        BlPoolFreeBlock(DirectoryData);
    }
}

BOOLEAN
BlCdGetFileSize(
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
    ISO9660_DIRECTORY_RECORD DirectoryRecord;

    if (BlCdFindDirectoryRecord(Path, &DirectoryRecord) == FALSE) {

        BlRtlPrintf("CdGetFileSize: [%s] FAILED 1\n", Path);

        return FALSE;
    }

    if (DirectoryRecord.u1.s1.Directory != FALSE) {

        BlRtlPrintf("CdGetFileSize: [%s] FAILED 2\n", Path);

        return FALSE;
    }

    *FileSize = DirectoryRecord.DataLength;
    return TRUE;
}

BOOLEAN
BlCdReadFile(
    PCSTR Path,
    PVOID Buffer,
    UINT32 NumberOfBytes
    )

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

{
    ISO9660_LOGICAL_BLOCK Block;
    UINT32 ChunkOffset;
    UINT32 ChunkSize;
    ISO9660_DIRECTORY_RECORD DirectoryRecord;
    PUINT8 Next;
    UINT32 Offset = 0;

    if (BlCdFindDirectoryRecord(Path, &DirectoryRecord) == FALSE) {

        return FALSE;
    }

    if (DirectoryRecord.u1.s1.Directory != FALSE) {

        return FALSE;
    }

    if (NumberOfBytes > DirectoryRecord.DataLength) {

        return FALSE;
    }

    if (NumberOfBytes == 0) {

        return TRUE;
    }

    Next = (PUINT8) Buffer;

    //
    // Handle full-read blocks in a single step.
    //

    if (NumberOfBytes >= ISO9660_LOGICAL_BLOCK_SIZE) {

        ChunkSize = NumberOfBytes - (NumberOfBytes % ISO9660_LOGICAL_BLOCK_SIZE);

        BlCdReadLogicalBlock(DirectoryRecord.ExtentLocation,
                             ChunkSize / ISO9660_LOGICAL_BLOCK_SIZE,
                             (PISO9660_LOGICAL_BLOCK) Next);

        Next += ChunkSize;
        Offset += ChunkSize;
        NumberOfBytes -= ChunkSize;
    }

    //
    // Check if the ending block is a partial read.
    //

    BLASSERT(NumberOfBytes < ISO9660_LOGICAL_BLOCK_SIZE);

    if (NumberOfBytes > 0) {

        BlCdReadLogicalBlock(DirectoryRecord.ExtentLocation + (Offset / ISO9660_LOGICAL_BLOCK_SIZE),
                             1,
                             &Block);

        BlRtlCopyMemory(Next,
                        Block.Data,
                        NumberOfBytes);
    }

    return TRUE;
}

VOID
BlCdInitialize(
    UINT8 DriveId
    )

//++
//
//  Routine Description:
//
//    This function initializes CDROM support.
//
//  Arguments:
//
//    DriveId     - Supplies CDROM drive ID.
//
//  --

{
    UINT32 LogicalBlockNumber;

    BlCdDriveId = DriveId;

    if (BlRtlGetDriveParameters(BlCdDriveId, &BlCdDriveParameters) == FALSE) {

        BlRtlPrintf("CDROM: Unable to get drive parameters!\n");
        BlRtlHalt();
    }

    if (BlCdDriveParameters.BytesPerSector != ISO9660_LOGICAL_BLOCK_SIZE) {

        BlRtlPrintf("CDROM: Unexpected sector size!\n");
        BlRtlHalt();
    }

    //
    // Locate Joliet volume descriptor.
    //

    LogicalBlockNumber = ISO9660_VOLUME_SPACE_DATA_AREA_LBN;

    for (;;) {

        BlCdReadLogicalBlock(LogicalBlockNumber,
                             1,
                             (PISO9660_LOGICAL_BLOCK) &BlCdVolumeDescriptor);

        if ((BlCdVolumeDescriptor.u1.VolumeDescriptorType == ISO9660_VOLUME_DESCRIPTOR_TYPE_SUPPLEMENTARY) &&
            (BlCdVolumeDescriptor.u1.Supplementary.EscapeSequences[0] == 0x25) &&
            (BlCdVolumeDescriptor.u1.Supplementary.EscapeSequences[1] == 0x2F) &&
            (BlCdVolumeDescriptor.u1.Supplementary.EscapeSequences[2] == 0x45)){

            break;
        }

        if (BlCdVolumeDescriptor.u1.VolumeDescriptorType == ISO9660_VOLUME_DESCRIPTOR_TYPE_TERMINATOR) {

            BlRtlPrintf("CDROM: Unable to find Joliet volume descriptor.\n");
            BlRtlHalt();
        }

        LogicalBlockNumber += 1;
    }

    BlFsGetFileSize = BlCdGetFileSize;
    BlFsReadFile = BlCdReadFile;

    return;
}

