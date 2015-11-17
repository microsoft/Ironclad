//++
//
//  Copyright (c) Microsoft Corporation
//
//  Module Name:
//
//    blkd1394.cpp
//
//  Abstract:
//
//    This module implements the 1394 transport for KD.
//
//--

#include "bl.h"
#include "blkd1394.h"

#if defined(BOOT_X64)

BOOLEAN
BlKd1394InitHardware(
    UINT16 Channel,
    PVOID IoRegion
    )
{
    return FALSE;
}

BOOLEAN
BlKd1394Connect(
    VOID
    )
{
    return FALSE;
}

BOOLEAN
BlKd1394SendPacket(
    UINT16 PacketType,
    PCVOID Header,
    UINT16 HeaderSize,
    PCVOID Data,
    UINT16 DataSize)
{
    return FALSE;
}

#else // !defined(BOOT_X64)

#define PACKET_READY        0x00000000  // Aka STATUS_SUCCESS
#define PACKET_PENDING      0x00000103  // Aka STATUS_PENDING

//
// Change these macros to debug the debugger transport.
//

#define KDDBG if (0) BlVideoPrintf
#define KDDBG2 if (0) BlVideoPrintf

//
//  These structures are accessed directly by the host using RDMA.
//

#define DEBUG_BUS1394_MAX_PACKET_SIZE       4000

#define DEBUG_1394_MAJOR_VERSION            0x1
#define DEBUG_1394_MINOR_VERSION            0x0
#define DEBUG_1394_CONFIG_TAG               0xBABABABA

typedef struct _DEBUG_1394_SEND_PACKET {
    UINT32               TransferStatus;
    UINT32               PacketHeader[4];
    UINT32               Length;
    UINT8               Packet[DEBUG_BUS1394_MAX_PACKET_SIZE];
    UINT8               Padding[72];
} DEBUG_1394_SEND_PACKET;

C_ASSERT(sizeof(DEBUG_1394_SEND_PACKET) == 4096);

typedef struct _DEBUG_1394_RECEIVE_PACKET {
    UINT32               TransferStatus;
    UINT32               Length;
    UINT8               Packet[DEBUG_BUS1394_MAX_PACKET_SIZE];
    UINT8               Padding[88];
} DEBUG_1394_RECEIVE_PACKET;

C_ASSERT(sizeof(DEBUG_1394_RECEIVE_PACKET) == 4096);

typedef struct _DEBUG_1394_CONFIG {
    UINT32               Tag;
    UINT16              MajorVersion;
    UINT16              MinorVersion;
    UINT32               Id;
    UINT32               BusPresent;
    UINT64           SendPacket;
    UINT64           ReceivePacket;
} DEBUG_1394_CONFIG;

C_ASSERT(sizeof(DEBUG_1394_CONFIG) == 32);

typedef struct _DEBUG_1394_DATA {
    UINT32                       CromBuffer[248];    // our config ROM - must be 1k aligned
    DEBUG_1394_CONFIG           Config;             // our config for this session
    DEBUG_1394_SEND_PACKET      SendPacket;         // our send packet (isoch packet)
    DEBUG_1394_RECEIVE_PACKET   ReceivePacket;      // our receive packet
} DEBUG_1394_DATA;

C_ASSERT(sizeof(DEBUG_1394_DATA) == 1024 + 4096 + 4096);

//
// Timing constants.
//

#define TIMEOUT_COUNT                   100000
#define MAX_REGISTER_READS              400000

//
// Static Data Structures
//

static DEBUG_1394_DATA *            Kd1394Data = NULL;
static volatile OHCI_REGISTER_MAP * KdRegisters = NULL;

UINT32
BlKd1394StallExecution(
    UINT32 LoopCount
    )

//++
//
//  Routine Description:
//
//    Stall for a finite time to allow hardware to respond.
//
//  Arguments:
//
//    LoopCount    - Number of times to run the outer loop.
//
//  Return Value:
//
//    Ignored.
//
//--

{
    volatile UINT32 b;
    volatile UINT32 k;
    volatile UINT32 i;

    b = 1;

    for (k = 0; k < LoopCount; k++) {

        BlKdSpin();

        for (i = 1; i < 10000; i++) {

            b = b * (i>>k);
        }
    }
    return b;
}

UINT32
BlKd1394ByteSwap(
    UINT32 Source
    )

//++
//
//  Routine Description:
//
//    Reverse the order of byte in the UINT32.
//
//  Arguments:
//
//    Source    - 32-bit UINT32 value.
//
//  Return Value:
//
//    The input value with byte pairs 0:3 and 1:2 swapped.
//
//--

{
    return (((Source)              << (8 * 3)) |
            ((Source & 0x0000FF00) << (8 * 1)) |
            ((Source & 0x00FF0000) >> (8 * 1)) |
            ((Source)              >> (8 * 3)));
}

UINT32
BlKd1394Crc16(
    UINT32 Data,
    UINT32 Check
    )

//++
//
//  Routine Description:
//
//    Derive the 16-bit CRC as defined by IEEE 1212 clause 8.1.5. (ISO/IEC 13213)
//    First edition 1994-10-05.
//
//  Arguments:
//
//    Data - UINT32 data to derive CRC from.
//
//    Check - check value.
//
//  Return Value:
//
//    The 16-bit CRC.
//
//--

{
    UINT32 Next = Check;
    INT32 Shift;

    for (Shift = 28; Shift >= 0; Shift -= 4) {
        UINT32 Sum;

        Sum = ((Next >> 12) ^ (Data >> Shift)) & 0xf;
        Next = (Next << 4) ^ (Sum << 12) ^ (Sum << 5) ^ (Sum);
    }
    return (Next & 0xFFFF);
}

UINT16
BlKd1394CalculateCrc(
    UINT32 *Quadlet,
    UINT32 Length
    )

//++
//
//  Routine Description:
//
//    Calculate a CRC for the pointer to the Quadlet data.
//
//  Arguments:
//
//    Quadlet - Pointer to data to CRC.
//
//    Length  - Length of data to CRC.
//
//  Return Value:
//
//    The 16-bit CRC.
//
//--

{
    UINT32 Temp = 0;
    UINT32 Index;

    Temp = 0;

    for (Index = 0; Index < Length; Index++) {

        Temp = BlKd1394Crc16(Quadlet[Index], Temp);
    }

    return (UINT16)Temp;
}

BOOLEAN
BlKd1394InitHardware(
    UINT16 Channel,
    PVOID IoRegion
    )

//++
//
//  Routine Description:
//
//    Initialize the 1394 hardware and connect it to KD.
//
//  Arguments:
//
//    Channel     - KD 1394 Channel.  Default is channel 0, but can be changed if 1394 is shared.
//
//    IoRegion    - Pointer to the 1394 registers mapped into our address space.
//
//  Return Value:
//
//    The 16-bit CRC.
//
//--

{
    UINT32 ulVersion;
    UINT8 MajorVersion;
    HC_CONTROL_REGISTER HCControl;
    UINT32 retry;
    LINK_CONTROL_REGISTER LinkControl;
    NODE_ID_REGISTER NodeId;
    BUS_OPTIONS_REGISTER BusOptions;
    CONFIG_ROM_INFO ConfigRomHeader;
    IMMEDIATE_ENTRY CromEntry;
    DIRECTORY_INFO DirInfo;
    PHY_CONTROL_REGISTER PhyControl;
    UINT8 Data;
    volatile OHCI_REGISTER_MAP * Registers;

#if KD_VERBOSE

    BlVideoPrintf("1394: IoRegion: %p\n", IoRegion);

#endif

    //
    // Note: Kd1394Data must be in the low 32-bits of address space due to
    //       limits on valid 1394 DMA addresses.  It must also be contiguous.
    //       It must be in the low 24-bits of address space to statisfy KD.
    //

    Kd1394Data = (DEBUG_1394_DATA *) BlSingularityOhci1394Buffer;
    BlRtlZeroMemory(Kd1394Data, sizeof(*Kd1394Data));

    //
    // Get our base address.
    //

    Registers = (volatile OHCI_REGISTER_MAP *)IoRegion;

    //
    // Initialize our config info for host debugger to read.
    //

    Kd1394Data->Config.Tag = DEBUG_1394_CONFIG_TAG;
    Kd1394Data->Config.MajorVersion = DEBUG_1394_MAJOR_VERSION;
    Kd1394Data->Config.MinorVersion = DEBUG_1394_MINOR_VERSION;
    Kd1394Data->Config.Id = Channel;
    Kd1394Data->Config.BusPresent = FALSE;
    Kd1394Data->Config.SendPacket = (UINT64) &Kd1394Data->SendPacket;
    Kd1394Data->Config.ReceivePacket = (UINT64) &Kd1394Data->ReceivePacket;

    //
    // Get the transport version.
    //

    ulVersion = Registers->Version.all;
    MajorVersion = (UINT8)(ulVersion >> 16);

    //
    // Make sure we have a valid version.
    //

    if (MajorVersion != 1) { // INVESTIGATE

#if KD_VERBOSE

        BlVideoPrintf("1394: MajorVersion != 1\n");

#endif

        return FALSE;
    }

    //
    // Soft reset to initialize the controller.
    //

    HCControl.all = 0;
    HCControl.SoftReset = TRUE;
    Registers->HCControlSet.all = HCControl.all;

    //
    // wait until reset completes.
    //

    retry = 1000; // ??

    do {

        HCControl.all = Registers->HCControlSet.all;

        BlKd1394StallExecution(1);

    } while ((HCControl.SoftReset) && (--retry));

    if (retry == 0) {

#if KD_VERBOSE

        BlVideoPrintf("1394: Reset failed\n");

#endif

        return FALSE;
    }

    //
    // Enable link to phy communication.
    //

    HCControl.all = 0;
    HCControl.Lps = TRUE;
    Registers->HCControlSet.all = HCControl.all;

    BlKd1394StallExecution(20);

    //
    // Initialize HCControl register
    // Send data in little-endian order (i.e. do byte swap).
    //

    HCControl.all = 0;
    HCControl.NoByteSwapData = TRUE;
    Registers->HCControlClear.all = HCControl.all;

    //
    // Enable posted writes.
    //

    HCControl.all = 0;
    HCControl.PostedWriteEnable = TRUE;
    Registers->HCControlSet.all = HCControl.all;

    //
    // Setup the link control.
    //

    LinkControl.all = 0;
    LinkControl.CycleTimerEnable = TRUE;
    LinkControl.CycleMaster = TRUE;
    LinkControl.RcvPhyPkt = TRUE;
    LinkControl.RcvSelfId = TRUE;
    Registers->LinkControlClear.all = LinkControl.all;

    LinkControl.all = 0;
    LinkControl.CycleTimerEnable = TRUE;
    LinkControl.CycleMaster = TRUE;
    Registers->LinkControlSet.all = LinkControl.all;

    //
    // Set the bus number (hardcoded to 0x3FF) - ??? what about node id??
    //

    NodeId.all = 0;
    NodeId.BusId = (UINT16)0x3FF;
    Registers->NodeId.all = NodeId.all;

    //
    // Do something with the crom...
    //

    //
    // 0xf0000404 - bus id register
    //
    Kd1394Data->CromBuffer[1] = 0x31333934;

    //
    // 0xf0000408 - bus options register
    //

    BusOptions.all = BlKd1394ByteSwap(Registers->BusOptions.all);
    BusOptions.Pmc = FALSE;
    BusOptions.Bmc = FALSE;
    BusOptions.Isc = FALSE;
    BusOptions.Cmc = FALSE;
    BusOptions.Irmc = FALSE;
    BusOptions.g = 1;
    Kd1394Data->CromBuffer[2] = BlKd1394ByteSwap(BusOptions.all);

    //
    // 0xf000040c - global unique id hi
    //

    Kd1394Data->CromBuffer[3] = Registers->GuidHi;

    //
    // 0xf0000410 - global unique id lo
    //

    Kd1394Data->CromBuffer[4] = Registers->GuidLo;

    //
    // 0xf0000400 - config ROM header - set last to calculate CRC!
    //

    ConfigRomHeader.all = 0;
    ConfigRomHeader.CRI_Info_Length = 4;
    ConfigRomHeader.CRI_CRC_Length = 4;
    ConfigRomHeader.CRI_CRC_Value = BlKd1394CalculateCrc(&Kd1394Data->CromBuffer[1],
                                                         ConfigRomHeader.CRI_CRC_Length);
    Kd1394Data->CromBuffer[0] = ConfigRomHeader.all;

    Kd1394Data->CromBuffer[6] = 0xC083000C; // 0xf0000418 - node capabilities
    Kd1394Data->CromBuffer[7] = 0xF2500003; // 0xf000041C - module vendor id

    //
    // KD's state machine looks for 1c w/ 50f2, 1d w/ 02, then 1e w/ address.
    //

    Kd1394Data->CromBuffer[8] = 0xF250001C; // 0xf0000420 - extended key (for KD)
    Kd1394Data->CromBuffer[9] = 0x0200001D; // 0xf0000424 - debug key (for KD)

    //
    // 0xf0000428 - debug value (for KD)
    //

    CromEntry.all = (UINT32)(ULONG_PTR) &Kd1394Data->Config;
    CromEntry.IE_Key = 0x1E;
    Kd1394Data->CromBuffer[10] = BlKd1394ByteSwap(CromEntry.all);

    //
    // 0xf0000414 - root directory header - set last to calculate CRC!
    //

    DirInfo.all = 0;
    DirInfo.DI_Length = 5;
    DirInfo.DI_CRC = BlKd1394CalculateCrc(&Kd1394Data->CromBuffer[6], DirInfo.DI_Length);
    Kd1394Data->CromBuffer[5] = BlKd1394ByteSwap(DirInfo.all);

    //
    // Write the first few registers.
    //

    Registers->ConfigRomHeader.all = Kd1394Data->CromBuffer[0];
    Registers->BusId = Kd1394Data->CromBuffer[1];
    Registers->BusOptions.all = Kd1394Data->CromBuffer[2];
    Registers->GuidHi = Kd1394Data->CromBuffer[3];
    Registers->GuidLo = Kd1394Data->CromBuffer[4];

    //
    // Set our crom.
    //

    Registers->ConfigRomMap = (UINT32)(ULONG_PTR) &Kd1394Data->CromBuffer;

    //
    // Disable all interrupts, we use polling for the debugger transport.
    //

    Registers->IntMaskClear.all = 0xFFFFFFFF;

    //
    // Enable the link.
    //

    HCControl.all = 0;
    HCControl.LinkEnable = TRUE;
    Registers->HCControlSet.all = HCControl.all;

    BlKd1394StallExecution(1000);

    //
    // Enable access filters to all nodes.
    //

    Registers->AsynchReqFilterLoSet = 0xFFFFFFFF;
    Registers->AsynchReqFilterHiSet = 0xFFFFFFFF;
    Registers->PhyReqFilterHiSet = 0xFFFFFFFF;
    Registers->PhyReqFilterLoSet = 0xFFFFFFFF;

    //
    // Hard reset on the bus (so KD will look for us).
    //

    PhyControl.all = 0;
    PhyControl.RdReg = TRUE;
    PhyControl.RegAddr = 1;
    Registers->PhyControl.all = PhyControl.all;

    retry = MAX_REGISTER_READS;

    do {

        PhyControl.all = Registers->PhyControl.all;

    } while ((!PhyControl.RdDone) && --retry);

    if (retry == 0) {

#if KD_VERBOSE

        BlVideoPrintf("1394: Bus read failed.\n");

#endif

        return FALSE;
    }

    Data = ((UINT8)PhyControl.RdData | PHY_INITIATE_BUS_RESET);

    PhyControl.all = 0;
    PhyControl.WrReg = TRUE;
    PhyControl.RegAddr = 1;
    PhyControl.WrData = Data;
    Registers->PhyControl.all = PhyControl.all;

    retry = MAX_REGISTER_READS;

    do {

        PhyControl.all = Registers->PhyControl.all;

    } while (PhyControl.WrReg && --retry);

    if (retry == 0) {

#if KD_VERBOSE

        BlVideoPrintf("1394: Hard reset of bus failed\n");

#endif

        return FALSE;
    }

#if KD_VERBOSE

    BlVideoPrintf("1394: Hardware init succeeded.\n");

#endif

    KdRegisters = Registers;

    return TRUE;
}

VOID
BlKd1394EnablePhysicalAccess(
    VOID
    )
{
    HC_CONTROL_REGISTER HCControl;
    INT_EVENT_MASK_REGISTER IntEvent;

    //
    // See if ohci1394 is being loaded...
    //

    HCControl.all = KdRegisters->HCControlSet.all;
    if (!HCControl.LinkEnable || !HCControl.Lps || HCControl.SoftReset) {

        KDDBG("1394: EnablePhysicalAccess HCControl=%08x!\n", HCControl.all);

        return;
    }

    //
    // If the bus reset interrupt is not cleared, we have to clear it...
    //

    IntEvent.all = KdRegisters->IntEventSet.all;
    if (IntEvent.BusReset) {

        KDDBG("1394: EnablePhysicalAccess IntEvent =%08x!\n", IntEvent.all);

        IntEvent.all = 0;
        IntEvent.BusReset = 1;
        KdRegisters->IntEventClear.all = IntEvent.all;
    }

    //
    // Re-enable physical access as it may be necessary.
    //

    KdRegisters->AsynchReqFilterHiSet = 0xFFFFFFFF;
    KdRegisters->AsynchReqFilterLoSet = 0xFFFFFFFF;
    KdRegisters->PhyReqFilterHiSet = 0xFFFFFFFF;
    KdRegisters->PhyReqFilterLoSet = 0xFFFFFFFF;

    return;
}

BOOLEAN
BlKd1394SendPacket(
    UINT16 PacketType,
    PCVOID Header,
    UINT16 HeaderSize,
    PCVOID Data,
    UINT16 DataSize)

//++
//
//  Routine Description:
//
//    This routine sends a packet to the host machine that is running the kernel debugger and
//    waits for an ACK.
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
    KD_PACKET PacketHeader;
    UINT32 Retries;
    UINT32 count;
    volatile UINT32 *pStatus;

    KDDBG2("BlKd1394SendPacket\n");

    //
    // Abort if the hardware hasn't been initialized.
    //

    if (KdRegisters == NULL) {

        return FALSE;
    }

    //
    // Initialize the packet header.
    //

    PacketHeader.PacketLeader = KD_PACKET_LEADER;
    PacketHeader.ByteCount = HeaderSize + DataSize;
    PacketHeader.PacketType = PacketType;
    PacketHeader.PacketId = BlKdNextPacketId++;
    PacketHeader.Checksum = (BlKdComputeChecksum(Header, HeaderSize) +
                             BlKdComputeChecksum(Data, DataSize));

    //
    // Setup our send packet.
    //

    BlRtlZeroMemory(&Kd1394Data->SendPacket, sizeof(DEBUG_1394_SEND_PACKET));
    Kd1394Data->SendPacket.Length = 0;  // Redundant.

    //
    // Copy our packet header into the transmit region.
    //

    BlRtlCopyMemory(&Kd1394Data->SendPacket.PacketHeader[0], &PacketHeader, sizeof(KD_PACKET));

    //
    // Setup our message header.
    //

    if (HeaderSize > 0) {

        BlRtlCopyMemory(&Kd1394Data->SendPacket.Packet[0], Header, HeaderSize);
        Kd1394Data->SendPacket.Length = HeaderSize;
    }

    //
    // Setup our message data.
    //

    if (DataSize > 0) {

        BlRtlCopyMemory(&Kd1394Data->SendPacket.Packet[Kd1394Data->SendPacket.Length], Data, DataSize);
        Kd1394Data->SendPacket.Length += DataSize;
    }

    //
    // Mark the packet as ready for processing by host.
    //

    Kd1394Data->SendPacket.TransferStatus = PACKET_PENDING;

    //
    // Wait for our packet to be acknowledged by the host.
    //

    for (Retries = KD_RETRY_COUNT; Retries > 0; Retries--) {

        KDDBG2("LOOP %d [SendPacket=%p %08x %08x %08x %02x %02x %02x %02x]\n",
               Retries,
               &Kd1394Data->SendPacket,
               Kd1394Data->SendPacket.TransferStatus,
               * (UINT32*) &Kd1394Data->SendPacket.PacketHeader,
               Kd1394Data->SendPacket.Length,
               Kd1394Data->SendPacket.Packet[0],
               Kd1394Data->SendPacket.Packet[1],
               Kd1394Data->SendPacket.Packet[2],
               Kd1394Data->SendPacket.Packet[3]);

        //
        // make sure our link is enabled..
        //

        BlKd1394EnablePhysicalAccess();

        pStatus = &Kd1394Data->ReceivePacket.TransferStatus;

        //
        // now sit here and poll for a response from the host machine
        //

        for (count = 0; count < TIMEOUT_COUNT; count++) {

            //
            // make sure our link is enabled..
            //

            BlKd1394EnablePhysicalAccess();
            BlKdSpin();

            //
            // Check to see if the host has ACK'd our packet.
            //

            if (Kd1394Data->SendPacket.TransferStatus != PACKET_PENDING) {
                return TRUE;
            }

            //
            // While in this loop check if the host has submitted a new request.
            // If they did, ACK it, and retry.
            //

            if (*pStatus == PACKET_PENDING) {

                //
                // ACK the packet from the debugger so it will accept our packet.
                //

                *pStatus = PACKET_READY;
            }
        }
    }

    return FALSE;
}

BOOLEAN
BlKd1394Connect(
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
    //
    // Abort if there is no 1394 hardware.
    //

    if (BlPciOhci1394BaseAddress == 0) {

        return FALSE;
    }

    //
    // Initialize the underlying hardware.
    //

    if (BlKd1394InitHardware(0, (PVOID)(ULONG_PTR) BlPciOhci1394BaseAddress)) {

        KD_DEBUG_IO Packet;

        //
        // Send a test packet to verify the debugger is attached.
        //

        BlRtlZeroMemory(&Packet, sizeof(Packet));

        Packet.ApiNumber = KD_API_PRINT_STRING;
        Packet.u1.PrintString.LengthOfString = 0;

        if (BlKd1394SendPacket(KD_PACKET_TYPE_KD_DEBUG_IO, &Packet, sizeof(Packet), L"1394!\n", 7)) {

            return TRUE;
        }
    }

    BlPciOhci1394BaseAddress = 0;

    return FALSE;
}

#endif // !defined(BOOT_X64)
