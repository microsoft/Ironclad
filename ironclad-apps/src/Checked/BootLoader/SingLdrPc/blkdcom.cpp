//++
//
//  Copyright (c) Microsoft Corporation
//
//  Module Name:
//
//    blkdcom.cpp
//
//  Abstract:
//
//    This module implements the com port transport for KD.
//
//--

#include "bl.h"

#define KD_DELAY_LOOP                       0x00010000

#define KD_INITIAL_PACKET_ID                0x80800000
#define KD_SYNC_PACKET_ID                   0x00000800

#define KD_PACKET_TRAILING_BYTE             0xAA

struct {
    KD_PACKET Header;
    UINT8 Data[PAGE_SIZE - sizeof(KD_PACKET)];
} BlKdStaticPacket;

UINT8 BlKdComPort;

BOOLEAN
BlKdComReceiveByte(
    PUINT8 Byte
    )

//++
//
//  Routine Description:
//
//    This function receives a byte from the KD.
//
//  Arguments:
//
//    Byte    - Receives the byte from KD.
//
//  Return Value:
//
//    TRUE, if receive operation was successful.
//    FALSE, otherwise.
//
//--

{
    volatile UINT32 Count;

    if (BlKdComPort != 0) {

        Count = KD_DELAY_LOOP;

        while (Count > 0) {

            if (BlComDataAvailable(BlKdComPort) != FALSE) {

                *Byte = BlComReceiveByte(BlKdComPort);

                return TRUE;
            }

            Count -= 1;
        }

#if KD_VERBOSE

        BlVideoPrintf("KD: Receive timeout!\n");

#endif

        return FALSE;
    }

    return FALSE;
}

BOOLEAN
BlKdComSendData(
    PCVOID Buffer,
    UINT32 Length
    )

//++
//
//  Routine Description:
//
//    This function sends data to the KD.
//
//  Arguments:
//
//    Buffer  - Supplies a pointer to the buffer to send.
//
//    Length  - Supplies the length of the  buffer to send.
//
//  Return Value:
//
//    TRUE, if send operation was successful.
//    FALSE, otherwise.
//
//--

{
    UINT32 Index;

    for (Index = 0; Index < Length; Index += 1) {

        if (BlComSendByte(BlKdComPort, ((PUINT8) Buffer)[Index]) == FALSE) {

            return FALSE;
        }
    }

    return TRUE;
}

BOOLEAN
BlKdComReceiveData(
    PVOID Buffer,
    UINT32 Length
    )

//++
//
//  Routine Description:
//
//    This function receives data from the KD.
//
//  Arguments:
//
//    Buffer  - Receives data.
//
//    Length  - Supplies the length of the buffer to receive.
//
//  Return Value:
//
//    TRUE, if receive operation was successful.
//    FALSE, otherwise.
//
//--

{
    UINT32 Index;

    for (Index = 0; Index < Length; Index += 1) {

        if (BlKdComReceiveByte(&(((PUINT8) Buffer)[Index])) == FALSE) {

            return FALSE;
        }
    }

    return TRUE;
}

BOOLEAN
BlKdComSendControlPacket(
    UINT16 PacketType,
    UINT32 PacketId
    )

//++
//
//  Routine Description:
//
//    This function sends a control packet to the KD.
//
//  Arguments:
//
//    PacketType  - Supplies the packet type.
//
//    PacketId    - Supplies the packet ID.
//
//  Return Value:
//
//    TRUE, if send operation was successful.
//    FALSE, otherwise.
//
//--

{
    KD_PACKET Header;

    BlRtlZeroMemory(&Header, sizeof(Header));

    Header.PacketLeader = KD_CONTROL_PACKET_LEADER;
    Header.PacketType = PacketType;
    Header.PacketId = PacketId;

    if (BlKdComSendData(&Header, sizeof(Header)) == FALSE) {

        return FALSE;
    }

#if KD_VERBOSE

    BlVideoPrintf("KD: Sent type %u control packet.\n", PacketType);

#endif

    return TRUE;
}

BOOLEAN
BlKdComReceivePacket(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function receives the next packet from the KD.
//
//  Return Value:
//
//    TRUE, if receive operation was successful.
//    FALSE, otherwise.
//
//--

{
    PKD_PACKET Header;
    UINT8 TrailingByte;

    Header = &BlKdStaticPacket.Header;

Retry:

    for (;;) {

        if (BlKdComReceiveData(&Header->PacketLeader, sizeof(Header->PacketLeader)) == FALSE) {

            return FALSE;
        }

        if (Header->PacketLeader == KD_PACKET_LEADER) {

            break;
        }

        if (Header->PacketLeader == KD_CONTROL_PACKET_LEADER) {

            break;
        }
    }

    if (BlKdComReceiveData(&Header->PacketType, sizeof(Header->PacketType)) == FALSE) {

        return FALSE;
    }

    if (BlKdComReceiveData(&Header->ByteCount, sizeof(Header->ByteCount)) == FALSE) {

        return FALSE;
    }

    if (BlKdComReceiveData(&Header->PacketId, sizeof(Header->PacketId)) == FALSE) {

        return FALSE;
    }

    if (BlKdComReceiveData(&Header->Checksum, sizeof(Header->Checksum)) == FALSE) {

        return FALSE;
    }

    if (Header->ByteCount > sizeof(BlKdStaticPacket.Data)) {

        goto Retry;
    }

    if (Header->ByteCount > 0) {

        if (BlKdComReceiveData(BlKdStaticPacket.Data, Header->ByteCount) == FALSE) {

            return FALSE;
        }

        if (BlKdComReceiveByte(&TrailingByte) == FALSE) {

            return FALSE;
        }

        if (TrailingByte != KD_PACKET_TRAILING_BYTE) {

            goto Retry;
        }
    }

#if KD_VERBOSE

    BlVideoPrintf("KD: Received type %u packet.\n", Header->PacketType);

#endif

    return TRUE;
}

BOOLEAN
BlKdComSendPacket(
    UINT16 PacketType,
    PCVOID Header,
    UINT16 HeaderSize,
    PCVOID Data,
    UINT16 DataSize
    )

//++
//
//  Routine Description:
//
//    This function sends a packet to the KD.
//
//  Arguments:
//
//    PacketType  - Supplies the type of the packet to send.
//
//    Header      - Supplies a pointer to the header.
//
//    HeaderSize  - Supplies the size of the header.
//
//    Data        - Supplies a pointer to the data.
//
//    DataSize    - Supplies the size of the data.
//
//  Return Value:
//
//    TRUE, if send operation was successful.
//    FALSE, otherwise.
//
//--

{
    UINT16 ByteCount;
    UINT32 Checksum;
    KD_PACKET Packet;

    BLASSERT(HeaderSize > 0);

Resend:

    //
    // Calculate byte count and checksum.
    //

    ByteCount = HeaderSize;
    Checksum = BlKdComputeChecksum(Header, HeaderSize);

    if (Data != NULL) {

        BLASSERT(DataSize > 0);

        ByteCount = ByteCount + DataSize;
        Checksum += BlKdComputeChecksum(Data, DataSize);
    }

    //
    // Send packet.
    //

    Packet.PacketLeader = KD_PACKET_LEADER;
    Packet.PacketId = BlKdNextPacketId;
    Packet.PacketType = PacketType;
    Packet.ByteCount = ByteCount;
    Packet.Checksum = Checksum;

    if (BlKdComSendData(&Packet, sizeof(Packet)) == FALSE) {

        return FALSE;
    }

    if (BlKdComSendData(Header, HeaderSize) == FALSE) {

        return FALSE;
    }

    if (Data != NULL) {

        if (BlKdComSendData(Data, DataSize) == FALSE) {

            return FALSE;
        }
    }

    if (BlComSendByte(BlKdComPort, KD_PACKET_TRAILING_BYTE) == FALSE) {

        return FALSE;
    }

#if KD_VERBOSE

    BlVideoPrintf("KD: Sent type %u packet.\n", Packet.PacketType);

#endif

    //
    // Update packet ID.
    //

    BlKdNextPacketId &= (~KD_SYNC_PACKET_ID);
    BlKdNextPacketId ^= 1;

    if (BlKdComReceivePacket() != FALSE) {

        switch (BlKdStaticPacket.Header.PacketType) {

            case KD_PACKET_TYPE_KD_RESET: {

#if KD_VERBOSE

                BlVideoPrintf("KD: Received RESET after send.\n");

#endif

                BlKdComSendControlPacket(KD_PACKET_TYPE_KD_RESET, 0);

                goto Resend;
            }

            case KD_PACKET_TYPE_KD_RESEND: {

#if KD_VERBOSE

                BlVideoPrintf("KD: Received RESEND after send.\n");

#endif

                goto Resend;
            }
        }
    }

    return TRUE;
}

BOOLEAN
BlKdComConnect(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function tries to connect to the KD through a COM port.
//
//  Return Value:
//
//    TRUE, if connection was successful.
//    FALSE, otherwise.
//
//--

{
    UINT8 Index;
    BOOLEAN Present[COM_MAX_PORT + 1];
    UINT32 Retry;


    //
    // Find all COM ports on the system.
    //

    for (Index = 1; Index <= COM_MAX_PORT; Index += 1) {

        Present[Index] = BlComInitialize(Index, 115200);

#if KD_VERBOSE

        BlVideoPrintf("KD: COM%u %s\n",
                      Index,
                      Present[Index] ? "found." : "not found.");

#endif

    }

    //
    // Set initial packet ID.
    //

    BlKdNextPacketId = KD_INITIAL_PACKET_ID | KD_SYNC_PACKET_ID;

    for (Retry = 0; Retry < KD_RETRY_COUNT; Retry += 1) {

        for (Index = 1; Index <= COM_MAX_PORT; Index += 1) {

            if (Present[Index] != FALSE) {

#if KD_VERBOSE

                BlVideoPrintf("KD: Trying COM%u ...\n", Index);

#endif

                BlKdComPort = Index;

                BlKdComSendControlPacket(KD_PACKET_TYPE_KD_RESET, 0);

                if (BlKdComReceivePacket() != FALSE) {

                    return TRUE;
                }
            }
        }
    }

    BlKdComPort = 0;

    return FALSE;
}
