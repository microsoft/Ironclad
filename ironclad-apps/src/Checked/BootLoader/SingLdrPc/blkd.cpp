//++
//
//  Copyright (c) Microsoft Corporation
//
//  Module Name:
//
//    blkd.cpp
//
//  Abstract:
//
//    This module implements KD support for the boot loader.
//
//--

#include "bl.h"

UINT32 BlKdNextPacketId;

VOID
BlKdSpin(
    VOID
    )

//++
//
//  Routine Description:
//
//    Provide user feedback that we are waiting on the kernel debugger.
//
//--

{
    static UINT8 state = 0;

    //
    // Write the spinner character to the top left corner of the screen.
    //

    *((UINT16 *)(ULONG_PTR)0xb809e) = 0x2f00 + ("+-|*" [state++ & 0x3]);
}

UINT32
BlKdComputeChecksum(
    PCVOID Buffer,
    UINT32 Length
    )

//++
//
//  Routine Description:
//
//    This function computes the checksum of a KD buffer.
//
//  Arguments:
//
//    Buffer  - Supplies a pointer to the buffer.
//
//    Length  - Supplies the length of the buffer.
//
//  Return Value:
//
//    Checksum value for the specified buffer.
//
//--

{
    UINT32 Checksum;
    UINT32 Index;

    Checksum = 0;

    for (Index = 0; Index < Length; Index += 1) {

        Checksum += ((PCHAR)Buffer)[Index];
    }

    return Checksum;
}

BOOLEAN
BlKdPrintString(
    PCSTR String
    )

//++
//
//  Routine Description:
//
//    This function prints the specified string to the KD.
//
//  Arguments:
//
//    String  - Supplies a pointer to the string to print.
//
//  Return Value:
//
//    TRUE, if operation was successful.
//    FALSE, otherwise.
//
//--

{
    KD_DEBUG_IO Packet;
    UINT32 StringLength;

    StringLength = BlRtlStringLength(String);

    if (StringLength >= 0xFFFF) {

        return FALSE;
    }

    BlRtlZeroMemory(&Packet, sizeof(Packet));

    Packet.ApiNumber = KD_API_PRINT_STRING;
    Packet.u1.PrintString.LengthOfString = StringLength;

    if (BlKdComPort != 0) {

        return BlKdComSendPacket(KD_PACKET_TYPE_KD_DEBUG_IO,
                                 &Packet,
                                 sizeof(Packet),
                                 String,
                                 (UINT16) StringLength + 1);

    }
    else if (BlPciOhci1394BaseAddress != 0) {

        return BlKd1394SendPacket(KD_PACKET_TYPE_KD_DEBUG_IO,
                                  &Packet,
                                  sizeof(Packet),
                                  String,
                                  (UINT16) StringLength + 1);

    }

    return FALSE;
}

BOOLEAN
BlKdPrintf(
    PCSTR Format,
    ...
    )

//++
//
//  Routine Description:
//
//    This function prints out a string to KD.
//
//  Arguments:
//
//    Format          - Supplies the format string.
//
//    ...             - Supplies the input parameters.
//
//  Return Value:
//
//    TRUE, if operation was successful.
//    FALSE, otherwise.
//
//--

{
    va_list ArgumentList;
    CHAR Buffer[4096];

    va_start(ArgumentList, Format);

    if (BlRtlFormatString(Buffer,
                          sizeof(Buffer),
                          Format,
                          ArgumentList) == FALSE) {

        return FALSE;
    }

    BlKdPrintString(Buffer);

    return TRUE;
}

VOID
BlKdInitialize(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function initializes KD support for the boot loader.
//
//--

{
    //
    // Try serial first.
    //

    if (BlKdComConnect() != FALSE) {

#if KD_VERBOSE

        BlVideoPrintf("KD: Connected to COM%u\n", BlKdComPort);

#endif

        return;
    }

    //
    // Try the 1394 transport next.
    //

    if (BlKd1394Connect() != FALSE) {

#if KD_VERBOSE

        BlVideoPrintf("KD: Connected to 1394:%u\n", 0);

#endif

        return;
    }

    return;
}
