//++
//
//  Copyright (c) Microsoft Corporation
//
//  Module Name:
//
//    blpxe.cpp
//
//  Abstract:
//
//    This module implements PXE support for the boot loader.
//
//--

#include "bl.h"

#pragma pack(1)

typedef struct _IP_ADDRESS {
    union {
        UINT32 Value;
        UINT8 Array[4];
    };
} IP_ADDRESS, *PIP_ADDRESS;

#define DHCP_OPTION_CODE_PAD            0
#define DHCP_OPTION_CODE_COMMAND_LINE   8

typedef struct _DHCP_OPTION_HEADER {
    UINT8 Code;
    UINT8 Length;
} DHCP_OPTION_HEADER, *PDHCP_OPTION_HEADER;

#define BOOTP_REPLY_OPCODE_REPLY        2

typedef struct _BOOTP_REPLY {
    UINT8 OpCode;
    UINT8 HardwareAddressType;
    UINT8 HardwareAddressLength;
    UINT8 Hops;
    UINT32 TransactionId;
    UINT16 SecondsSinceAddressAcquisition;
    UINT16 Flags;
    IP_ADDRESS ClientIP;
    IP_ADDRESS YourIP;
    IP_ADDRESS ServerIP;
    IP_ADDRESS GatewayIP;
    UINT8 ClientMAC[16];
    UINT8 ServerHostName[64];
    UINT8 BootFileName[128];
    UINT8 Magic[4];
    UINT8 Data[1500];
} BOOTP_REPLY, *PBOOTP_REPLY;

typedef struct _PXE_INSTALLATION_CHECK {
    UINT8 Signature[6];
    UINT16 Version;
    UINT8 Length;
    UINT8 Checksum;
    FAR_POINTER RealModeEntry;
    UINT32 ProtectedModeEntry;
    UINT16 ProtectedModeSelector;
    UINT16 StackSegment;
    UINT16 StackSize;
    UINT16 BCCodeSegment;
    UINT16 BCCodeSize;
    UINT16 BCDataSegment;
    UINT16 BCDataSize;
    UINT16 UNDIDataSegment;
    UINT16 UNDIDataSize;
    UINT16 UNDICodeSegment;
    UINT16 UNDICOdeSize;
    FAR_POINTER ExtendedInformation;
} PXE_INSTALLATION_CHECK, *PPXE_INSTALLATION_CHECK;

C_ASSERT(sizeof(PXE_INSTALLATION_CHECK) == 0x2C);

typedef struct _PXE_SEGMENT_DESCRIPTOR {
    UINT16 Selector;
    UINT32 Base;
    UINT16 Size;
} PXE_SEGMENT_DESCRIPTOR, *PPXE_SEGMENT_DESCRIPTOR;

C_ASSERT(sizeof(PXE_SEGMENT_DESCRIPTOR) == 8);

typedef struct _PXE_EXTENDED_INFORMATION {
    UINT8 Signature[4];
    UINT8 Length;
    UINT8 Checksum;
    UINT8 Version;
    UINT8 Reserved1;
    FAR_POINTER UNDIROMID;
    FAR_POINTER BaseROMID;
    FAR_POINTER Entry16;
    FAR_POINTER Entry32;
    FAR_POINTER StatusCallout;
    UINT8 Reserved2;
    UINT8 SegmentDescriptorCount;
    UINT16 FirstSelector;
    PXE_SEGMENT_DESCRIPTOR Stack;
    PXE_SEGMENT_DESCRIPTOR UNDIData;
    PXE_SEGMENT_DESCRIPTOR UNDICode;
    PXE_SEGMENT_DESCRIPTOR UNDICodeWrite;
    PXE_SEGMENT_DESCRIPTOR BCData;
    PXE_SEGMENT_DESCRIPTOR BCCode;
    PXE_SEGMENT_DESCRIPTOR BCCOdeWrite;
} PXE_EXTENDED_INFORMATION, *PPXE_EXTENDED_INFORMATION;

C_ASSERT(sizeof(PXE_EXTENDED_INFORMATION) == 0x58);

#define PXE_STATUS_SUCCESS              0

typedef UINT16 PXE_STATUS;

#define PXE_OPCODE_TFTP_READ_FILE       0x0023
#define PXE_OPCODE_TFTP_GET_FILE_SIZE   0x0025
#define PXE_OPCODE_GET_CACHED_INFO      0x0071

#define PXE_PACKET_TYPE_DHCP_ACK        2
#define PXE_PACKET_TYPE_CACHED_REPLY    3

typedef struct _PXE_GET_CACHED_INFO {
    PXE_STATUS Status;
    UINT16 PacketType;
    UINT16 BufferSize;
    FAR_POINTER Buffer;
    UINT16 BufferLimit;
} PXE_GET_CACHED_INFO, *PPXE_GET_CACHED_INFO;

typedef struct _PXE_TFTP_GET_FILE_SIZE {
    PXE_STATUS Status;
    IP_ADDRESS ServerIP;
    IP_ADDRESS GatewayIP;
    UINT8 FileName[128];
    UINT32 FileSize;
} PXE_TFTP_GET_FILE_SIZE, *PPXE_TFTP_GET_FILE_SIZE;

#define PXE_TFTP_READ_FILE_RETRY_COUNT  5

typedef struct _PXE_TFTP_READ_FILE {
    PXE_STATUS Status;
    UINT8 FileName[128];
    UINT32 BufferSize;
    UINT32 Buffer;
    IP_ADDRESS ServerIP;
    IP_ADDRESS GatewayIP;
    IP_ADDRESS MulticastIP;
    UINT16 ClientMulticastPort;
    UINT16 ServerMulticastPort;
    UINT16 OpenTimeout;
    UINT16 ReopenDelay;
} PXE_TFTP_READ_FILE, *PPXE_TFTP_READ_FILE;

typedef struct _PXE_API_PACKET {
    union {
        PXE_GET_CACHED_INFO GetCachedInfo;
        PXE_TFTP_GET_FILE_SIZE TFTPGetFileSize;
        PXE_TFTP_READ_FILE TFTPReadFile;
    } u1;
} PXE_API_PACKET, *PPXE_API_PACKET;

#pragma pack()

PXE_API_PACKET BlPxeApiPacket;
BOOTP_REPLY BlPxeBootpReply;
UINT16 BlPxeCallFrame[16];
FAR_POINTER BlPxeEntry16;
PPXE_EXTENDED_INFORMATION BlPxeExtendedInformation;
PPXE_INSTALLATION_CHECK BlPxeInstallationCheck;

VOID
BlPxeCallPxeApi(
    UINT16 OpCode,
    PVOID Packet
    )

//++
//
//  Routine Description:
//
//    This function calls the PXE API.
//
//  Arguments:
//
//    OpCode  - Supplies the operation to perform.
//
//    Packet  - Supplies a pointer to te packet describing the operation details.
//
//--

{
    BL_LEGACY_CALL_CONTEXT Context;
    FAR_POINTER FarPointer;

    BlRtlZeroMemory(&Context, sizeof(BL_LEGACY_CALL_CONTEXT));

    if (BlPxeExtendedInformation != NULL) {

        BlPxeCallFrame[0] = OpCode;
        BlRtlConvertLinearPointerToFarPointer(Packet, (PFAR_POINTER) &BlPxeCallFrame[1]);

        BlRtlCallLegacyFunction(BlPxeExtendedInformation->Entry16.Segment,
                                BlPxeExtendedInformation->Entry16.Offset,
                                BlPxeCallFrame,
                                3 * sizeof(UINT16),
                                &Context,
                                &Context);

    } else {

        BlRtlConvertLinearPointerToFarPointer(Packet, &FarPointer);

        Context.ebx = OpCode;
        Context.es = FarPointer.Segment;
        Context.edi = FarPointer.Offset;

        BlRtlCallLegacyFunction(BlPxeInstallationCheck->RealModeEntry.Segment,
                                BlPxeInstallationCheck->RealModeEntry.Offset,
                                NULL,
                                0,
                                &Context,
                                &Context);
    }

    return;
}

VOID
BlPxeGetBootpReply(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function gets the BOOTP reply received by PXE.
//
//--

{
    PPXE_GET_CACHED_INFO GetCachedInfo;
    UINT32 Index;
    ULONG_PTR Limit;
    ULONG_PTR Next;
    PDHCP_OPTION_HEADER Option;

    GetCachedInfo = &BlPxeApiPacket.u1.GetCachedInfo;

    //
    // Get the discover reply packet received from the boot server.
    //

    BlRtlZeroMemory(GetCachedInfo, sizeof(PXE_GET_CACHED_INFO));
    GetCachedInfo->PacketType = PXE_PACKET_TYPE_CACHED_REPLY;
    BlRtlConvertLinearPointerToFarPointer(&BlPxeBootpReply, &GetCachedInfo->Buffer);
    GetCachedInfo->BufferSize = sizeof(BlPxeBootpReply);

    BlPxeCallPxeApi(PXE_OPCODE_GET_CACHED_INFO, GetCachedInfo);

    if (GetCachedInfo->Status != PXE_STATUS_SUCCESS) {

        BlRtlPrintf("PXE: Get PXE_REPLY failed: 0x%04x!\n", GetCachedInfo->Status);
        BlRtlHalt();
    }

    //
    // If the discover reply packet does not have the BOOTP reply opcode, then get the DHCP ACK packet.
    //

    if (BlPxeBootpReply.OpCode != BOOTP_REPLY_OPCODE_REPLY) {

        BlRtlZeroMemory(GetCachedInfo, sizeof(PXE_GET_CACHED_INFO));
        GetCachedInfo->PacketType = PXE_PACKET_TYPE_DHCP_ACK;
        BlRtlConvertLinearPointerToFarPointer(&BlPxeBootpReply, &GetCachedInfo->Buffer);
        GetCachedInfo->BufferSize = sizeof(BlPxeBootpReply);

        BlPxeCallPxeApi(PXE_OPCODE_GET_CACHED_INFO, GetCachedInfo);

        if (GetCachedInfo->Status != PXE_STATUS_SUCCESS) {

            BlRtlPrintf("PXE: Get DHCP_ACK failed 0x%04x!\n", GetCachedInfo->Status);
            BlRtlHalt();
        }
    }

    //
    // If neither discover reply packet nor the DHCP ACK packet contains the BOOTP reply opcode, then PXE boot is not possible.
    //

    if (BlPxeBootpReply.OpCode != BOOTP_REPLY_OPCODE_REPLY) {

        BlRtlPrintf("PXE: Invalid BOOTP_REPLY packet!\n");
        BlRtlHalt();
    }

#if PXE_VERBOSE

    BlRtlPrintf("PXE: IP=%u.%u.%u.%u DHCP=%u.%u.%u.%u GATEWAY=%u.%u.%u.%u\n",
                BlPxeBootpReply.ClientIP.Array[0],
                BlPxeBootpReply.ClientIP.Array[1],
                BlPxeBootpReply.ClientIP.Array[2],
                BlPxeBootpReply.ClientIP.Array[3],
                BlPxeBootpReply.ServerIP.Array[0],
                BlPxeBootpReply.ServerIP.Array[1],
                BlPxeBootpReply.ServerIP.Array[2],
                BlPxeBootpReply.ServerIP.Array[3],
                BlPxeBootpReply.GatewayIP.Array[0],
                BlPxeBootpReply.GatewayIP.Array[1],
                BlPxeBootpReply.GatewayIP.Array[2],
                BlPxeBootpReply.GatewayIP.Array[3]
                );

#endif

    Limit = ((ULONG_PTR) &BlPxeBootpReply) + GetCachedInfo->BufferSize;
    Next = (ULONG_PTR) (&BlPxeBootpReply.Data);

    while (Next < Limit) {

        Option = (PDHCP_OPTION_HEADER) Next;

        switch (Option->Code) {

            case DHCP_OPTION_CODE_PAD: {

                Next += 1;

                break;
            }

            case DHCP_OPTION_CODE_COMMAND_LINE: {

                if (((Next + sizeof(DHCP_OPTION_HEADER)) < Limit) &&
                    ((Next + sizeof(DHCP_OPTION_HEADER) + Option->Length) < Limit)) {

                    BlCommandLine = (PWCHAR)BlPoolAllocateBlock((Option->Length + 1) * sizeof(WCHAR));

                    for (Index = 0; Index < Option->Length; Index += 1) {

                        BlCommandLine[Index] = (WCHAR) (((PCHAR) (Option + 1))[Index]);
                    }

                    BlCommandLine[Option->Length] = 0;

#if PXE_VERBOSE

                    BlRtlPrintf("PXE: CMD=[%s]\n", BlCommandLine);

#endif
                }

                Next = Limit;

                break;
            }

            default: {

                Next += (sizeof(DHCP_OPTION_HEADER) + Option->Length);
            }
        }
    }

    return;
}

BOOLEAN
BlPxeGetFileSize(
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
    PPXE_TFTP_GET_FILE_SIZE GetFileSize;
    UINT32 PathLength;

    GetFileSize = &BlPxeApiPacket.u1.TFTPGetFileSize;

    BlRtlZeroMemory(GetFileSize, sizeof(PXE_TFTP_GET_FILE_SIZE));

    PathLength = BlRtlStringLength(Path);

    if (PathLength >= sizeof(GetFileSize->FileName)) {

        return FALSE;

    }

    GetFileSize->ServerIP = BlPxeBootpReply.ServerIP;
    GetFileSize->GatewayIP = BlPxeBootpReply.GatewayIP;

    BlRtlCopyMemory(GetFileSize->FileName, Path, PathLength);

    GetFileSize->FileName[PathLength] = 0;

    BlPxeCallPxeApi(PXE_OPCODE_TFTP_GET_FILE_SIZE, GetFileSize);

    if (GetFileSize->Status != PXE_STATUS_SUCCESS) {

        return FALSE;
    }

    *FileSize = GetFileSize->FileSize;

    return TRUE;
}

BOOLEAN
BlPxeReadFile(
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
    UINT32 Index;
    UINT32 PathLength;
    PPXE_TFTP_READ_FILE ReadFile;

    BLASSERT((((ULONG_PTR) Buffer) + NumberOfBytes) > ((ULONG_PTR) Buffer));

    BLASSERT((((ULONG_PTR) Buffer) + NumberOfBytes) <= 0xFFFFFFFF);

    ReadFile = &BlPxeApiPacket.u1.TFTPReadFile;

    PathLength = BlRtlStringLength(Path);

    if (PathLength >= sizeof(ReadFile->FileName)) {

#if PXE_VERBOSE

        BlRtlPrintf("PXE: Path is too long [%s]\n", Path);

#endif

        return FALSE;
    }

    for (Index = 0; Index < PXE_TFTP_READ_FILE_RETRY_COUNT; Index += 1) {

        BlRtlZeroMemory(ReadFile, sizeof(PXE_TFTP_READ_FILE));

        BlRtlCopyMemory(ReadFile->FileName,
                        Path,
                        PathLength);

        ReadFile->FileName[PathLength] = 0;

        ReadFile->BufferSize = NumberOfBytes;
        ReadFile->Buffer = (UINT32) (ULONG_PTR) Buffer;
        ReadFile->ServerIP = BlPxeBootpReply.ServerIP;
        ReadFile->GatewayIP = BlPxeBootpReply.GatewayIP;

        BlPxeCallPxeApi(PXE_OPCODE_TFTP_READ_FILE, ReadFile);

        if (ReadFile->Status == PXE_STATUS_SUCCESS) {

            break;
        }

#if PXE_VERBOSE

        BlRtlPrintf("PXE: TFTP_READ failed: 0x%04x! [%u / %u]\n",
                    ReadFile->Status,
                    Index + 1,
                    PXE_TFTP_READ_FILE_RETRY_COUNT);

#endif

    }

    return TRUE;
}

VOID
BlPxeInitialize(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function initializes PXE support.
//
//--

{
    BL_LEGACY_CALL_CONTEXT Context;
    FAR_POINTER FarPointer;
    PPXE_INSTALLATION_CHECK InstallationCheck;
    ULONG_PTR Limit;
    ULONG_PTR Next;

    BlRtlZeroMemory(&Context, sizeof(Context));

    Context.eax = 0x5650;

    BlRtlCallLegacyInterruptService(0x1A,
                                    &Context,
                                    &Context);

    if (((Context.eflags & RFLAGS_CF) == 0) && ((Context.eax & 0xFFFF) == 0x564E)) {

        FarPointer.Segment = (UINT16) Context.es;
        FarPointer.Offset = (UINT16) (Context.ebx & 0xFFFF);

#if PXE_VERBOSE

        BlRtlPrintf("PXE: INT1A/5650h => [ES:BX = %04x:%04x]\n",
                    FarPointer.Segment,
                    FarPointer.Offset);

#endif

        BlPxeInstallationCheck = (PPXE_INSTALLATION_CHECK)
            BlRtlConvertFarPointerToLinearPointer(&FarPointer);

    } else {

        Next = 0xA0000;
        Limit = 0x10000;

        BlPxeInstallationCheck = NULL;

        do {

            Next -= 16;

            InstallationCheck = (PPXE_INSTALLATION_CHECK) Next;

            if ((InstallationCheck->Length >= sizeof(PXE_INSTALLATION_CHECK)) &&
                (InstallationCheck->Signature[0] == 'P') &&
                (InstallationCheck->Signature[1] == 'X') &&
                (InstallationCheck->Signature[2] == 'E') &&
                (InstallationCheck->Signature[3] == 'N') &&
                (InstallationCheck->Signature[4] == 'V') &&
                (InstallationCheck->Signature[5] == '+') &&
                (BlRtlComputeChecksum8(InstallationCheck, InstallationCheck->Length) == 0)) {

                BlPxeInstallationCheck = InstallationCheck;

                break;
            }

        } while (Next > Limit);
    }

    if (BlPxeInstallationCheck == NULL) {

        BlRtlPrintf("PXE: Unable to find PXE!\n");
        BlRtlHalt();
    }

    if (BlPxeInstallationCheck->Version < 0x201) {

#if PXE_VERBOSE

        BlRtlPrintf("PXE: Using PXENV+.\n");

#endif

        BlPxeEntry16 = BlPxeInstallationCheck->RealModeEntry;

    } else {

#if PXE_VERBOSE

        BlRtlPrintf("PXE: Using !PXE.\n");

#endif

        BlPxeExtendedInformation = (PPXE_EXTENDED_INFORMATION)
            BlRtlConvertFarPointerToLinearPointer(&BlPxeInstallationCheck->ExtendedInformation);

        if (!((BlPxeExtendedInformation->Length >= sizeof(PXE_EXTENDED_INFORMATION)) &&
              (BlPxeExtendedInformation->Signature[0] == '!') &&
              (BlPxeExtendedInformation->Signature[1] == 'P') &&
              (BlPxeExtendedInformation->Signature[2] == 'X') &&
              (BlPxeExtendedInformation->Signature[3] == 'E') &&
              (BlRtlComputeChecksum8(BlPxeExtendedInformation, BlPxeExtendedInformation->Length) == 0))) {

            BlRtlPrintf("PXE: !PXE is invalid!\n");
            BlRtlHalt();
        }

        BlPxeEntry16 = BlPxeExtendedInformation->Entry16;
    }

#if PXE_VERBOSE

    BlRtlPrintf("PXE: PXENV+ @ %p\n"
                "PXE: !PXE   @ %p\n"
                "PXE: Entry16 @ %04x:%04x\n",
                BlPxeInstallationCheck,
                BlPxeExtendedInformation,
                BlPxeEntry16.Segment,
                BlPxeEntry16.Offset);

#endif

    BlPxeGetBootpReply();

    BlFsGetFileSize = BlPxeGetFileSize;
    BlFsReadFile = BlPxeReadFile;

    return;
}
