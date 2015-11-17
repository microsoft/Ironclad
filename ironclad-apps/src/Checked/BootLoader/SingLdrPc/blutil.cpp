//++
//
//  Copyright (c) Microsoft Corporation
//
//  Module Name:
//
//    blutil.cpp
//
//  Abstract:
//
//    This module implements utility functions for the boot loader environment.
//
//--

#include "bl.h"

VOID
BlReturnToLegacyMode(
    VOID
    );

VOID
BlRtlInitializeListHead(
    PLIST_ENTRY Head
    )

//++
//
//  Routine Description:
//
//    This function initializes the specified list head.
//
//  Arguments:
//
//    Head    - Supplies a pointer to the list head to initialize.
//
//--

{
    Head->Flink = Head->Blink = Head;
}

BOOLEAN
BlRtlIsListEmpty(
    PLIST_ENTRY Head
    )

//++
//
//  Routine Description:
//
//    This function checks if the specified list is empty.
//
//  Arguments:
//
//    Head    - Supplies a pointer to the list head.
//
//  Return Value:
//
//    TRUE, if the list is empty.
//    FALSE, otherwise.
//
//--

{
    return (BOOLEAN) (Head->Flink == Head);
}

BOOLEAN
BlRtlRemoveEntryList(
    PLIST_ENTRY Entry
    )

//++
//
//  Routine Description:
//
//    This function removes the specified entry from the list.
//
//  Arguments:
//
//    Entry   - Supplies a pointer to the entry to remove.
//
//  Return Value:
//
//    TRUE, if this was the last entry in the list.
//    FALSE, otherwise.
//
//--

{
    PLIST_ENTRY Blink;
    PLIST_ENTRY Flink;

    Blink = Entry->Blink;
    Flink = Entry->Flink;

    BLASSERT(Blink != Entry);
    BLASSERT(Flink != Entry);

    Blink->Flink = Flink;
    Flink->Blink = Blink;

    return (BOOLEAN) (Flink == Blink);
}

PLIST_ENTRY
BlRtlRemoveHeadList(
    PLIST_ENTRY Head
    )

//++
//
//  Routine Description:
//
//    This function removes an entry from the head of the specified list.
//
//  Arguments:
//
//    Head    - Supplies a pointer to the list to remove from.
//
//  Return Value:
//
//    A pointer to the removed entry.
//
//--

{
    PLIST_ENTRY Entry;
    PLIST_ENTRY Flink;

    BLASSERT(BlRtlIsListEmpty(Head) == FALSE);

    Entry = Head->Flink;
    Flink = Entry->Flink;

    Head->Flink = Flink;
    Flink->Blink = Head;

    return Entry;
}

PLIST_ENTRY
BlRtlRemoveTailList(
    PLIST_ENTRY Head
    )

//++
//
//  Routine Description:
//
//    This function removes an entry from the tail of the specified list.
//
//  Arguments:
//
//    Head    - Supplies a pointer to the list to remove from.
//
//  Return Value:
//
//    A pointer to the removed entry.
//
//--

{
    PLIST_ENTRY Blink;
    PLIST_ENTRY Entry;

    BLASSERT(BlRtlIsListEmpty(Head) == FALSE);

    Entry = Head->Blink;
    Blink = Entry->Blink;

    Head->Blink = Blink;
    Blink->Flink = Head;

    return Entry;
}

VOID
BlRtlInsertTailList(
    PLIST_ENTRY Head,
    PLIST_ENTRY Entry
    )

//++
//
//  Routine Description:
//
//    This function inserts the specified entry to the tail of the specified list.
//
//  Arguments:
//
//    Head    - Supplies a pointer to the list to insert to.
//
//    Entry   - Supplies a pointer to the entry to insert.
//
//--

{
    PLIST_ENTRY Blink;

    Blink = Head->Blink;

    Entry->Flink = Head;
    Entry->Blink = Blink;

    Head->Blink = Entry;
    Blink->Flink = Entry;
}

VOID
BlRtlInsertHeadList(
    PLIST_ENTRY Head,
    PLIST_ENTRY Entry
    )

//++
//
//  Routine Description:
//
//    This function inserts the specified entry to the head of the specified list.
//
//  Arguments:
//
//    Head    - Supplies a pointer to the list to insert to.
//
//    Entry   - Supplies a pointer to the entry to insert.
//
//--

{
    PLIST_ENTRY Flink;

    Flink = Head->Flink;

    Entry->Flink = Flink;
    Entry->Blink = Head;

    Head->Flink = Entry;
    Flink->Blink = Entry;
}

VOID
BlRtlConvertLinearPointerToFarPointer(
    PVOID LinearPointer,
    PFAR_POINTER FarPointer
    )

//++
//
//  Routine Description:
//
//    This function converts the specified linear pointer to a legacy far pointer.
//
//  Arguments:
//
//    LinearPointer   - Supplies the linear pointer to convert.
//
//    FarPointer      - Receives the legacy far pointer.
//
//--

{
    BLASSERT((ULONG_PTR) LinearPointer < LEGACY_MEMORY_LIMIT);

    FarPointer->Segment = (UINT16) (((ULONG_PTR) LinearPointer) >> 4);
    FarPointer->Offset = (((UINT16) (ULONG_PTR) LinearPointer) & 0xF);
}

PVOID
BlRtlConvertFarPointerToLinearPointer(
    PFAR_POINTER FarPointer
    )

//++
//
//  Routine Description:
//
//    This function converts the specified legacy far pointer to a linear pointer.
//
//  Arguments:
//
//    FarPointer      - Supplies the legacy far pointer to convert.
//
//  Return Value:
//
//    Linear pointer matching the specified legacy far pointer.
//
//--

{

    return (PVOID) (((ULONG_PTR) FarPointer->Segment << 4) + ((ULONG_PTR) FarPointer->Offset));
}

VOID
BlRtlZeroMemory(
    PVOID Buffer,
    ULONG_PTR Length
    )

//++
//
//  Routine Description:
//
//    This function zeroes the specified buffer.
//
//  Arguments:
//
//    Buffer  - Supplies a pointer to the buffer to zero.
//
//    Length  - Supplies the length of the buffer.
//
//--

{
    PUINT8 Limit;
    PUINT8 Next;

    Next = (PUINT8) Buffer;
    Limit = Next + Length;

    while (Next < Limit) {

        *Next = 0;
        Next += 1;
    }
}

VOID
BlRtlCopyMemory(
    PVOID Destination,
    PCVOID Source,
    ULONG_PTR Length
    )

//++
//
//  Routine Description:
//
//    This function copies data from the source buffer to the destination buffer.
//
//  Arguments:
//
//    Destination - Receives copied data.
//
//    Source      - Supplies data to copy.
//
//    Length      - Supplies the length of the data to copy.
//
//--

{
    ULONG_PTR DestinationEnd;
    ULONG_PTR DestinationStart;
    ULONG_PTR Index;
    ULONG_PTR SourceEnd;
    ULONG_PTR SourceStart;

    if (Length == 0) {

        return;
    }

    SourceStart = (ULONG_PTR) Source;
    SourceEnd = SourceStart + Length;
    DestinationStart = (ULONG_PTR) Destination;
    DestinationEnd = DestinationStart + Length;

    //
    // If the higher part of the source buffer intersects with the destination
    // buffer, then perform a reverse copy. Otherwise, perform a regular copy.
    //

    if ((SourceStart < DestinationStart) && (SourceEnd > DestinationStart)) {

        Index = Length;

        do {

            Index -= 1;

            ((PUINT8) Destination)[Index] = ((PUINT8) Source)[Index];

        } while (Index > 0);

    } else {

        for (Index = 0; Index < Length; Index += 1) {

            ((PUINT8) Destination)[Index] = ((PUINT8) Source)[Index];
        }
    }
}

BOOLEAN
BlRtlCompareMemory(
    PCVOID Buffer1,
    PCVOID Buffer2,
    ULONG_PTR Length
    )

//++
//
//  Routine Description:
//
//    This function compares the data in the supplied buffers.
//
//  Arguments:
//
//    Buffer1     - Supplies the first buffer.
//
//    Buffer2     - Supplies the second buffer.
//
//    Length      - Supplies the number of bytes to compare.
//
//  Return Value:
//
//    TRUE, if buffers contain identical data.
//    FALSE, otherwise.
//
//--

{
    ULONG_PTR Index;

    for (Index = 0; Index < Length; Index += 1) {

        if (((PUINT8) Buffer1)[Index] != ((PUINT8) Buffer2)[Index]) {

            return FALSE;
        }
    }

    return TRUE;
}

VOID
BlRtlMakeLegacyCall(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function switches back to legacy mode, makes the call
//    specified in the BEB, and returns back to normal mode.
//
//--

{
    //
    // Return to legacy mode.
    //

    BlReturnToLegacyMode();

    //
    // Re-enable A20 gate -- this is absolutely necessary, because some
    // legacy calls (such as some PXE implementations) modify A20 state.
    //

    BlMmEnableA20Gate();
}

VOID
BlRtlCallLegacyInterruptService(
    UINT8 Vector,
    PBL_LEGACY_CALL_CONTEXT Input,
    PBL_LEGACY_CALL_CONTEXT Output
    )

//++
//
//  Routine Description:
//
//    This function calls the specified legacy interrupt service.
//
//  Arguments:
//
//    Vector  - Supplies the legacy interrupt service vector to call.
//
//    Input   - Supplies a pointer to the input context for the call.
//
//    Output  - Supplies a pointer to the output context to fill after the call.
//
//--

{
    PBEB Beb;

    Beb = BlGetBeb();

    Beb->LegacyCall_OpCode = LC_INTXX;
    Beb->LegacyCall_Vector = Vector;
    Beb->LegacyCall_ax = Input->eax;
    Beb->LegacyCall_bx = Input->ebx;
    Beb->LegacyCall_cx = Input->ecx;
    Beb->LegacyCall_dx = Input->edx;
    Beb->LegacyCall_si = Input->esi;
    Beb->LegacyCall_di = Input->edi;
    Beb->LegacyCall_ds = Input->ds;
    Beb->LegacyCall_es = Input->es;

    BlRtlMakeLegacyCall();

    Output->eax = Beb->LegacyCall_ax;
    Output->ebx = Beb->LegacyCall_bx;
    Output->ecx = Beb->LegacyCall_cx;
    Output->edx = Beb->LegacyCall_dx;
    Output->esi = Beb->LegacyCall_si;
    Output->edi = Beb->LegacyCall_di;
    Output->ds = Beb->LegacyCall_ds;
    Output->es = Beb->LegacyCall_es;
    Output->eflags = Beb->LegacyCall_flags;
}

VOID
BlRtlCallLegacyFunction(
    UINT16 CodeSegment16,
    UINT16 CodeOffset16,
    PVOID CallFrame,
    UINT32 CallFrameSize,
    PBL_LEGACY_CALL_CONTEXT Input,
    PBL_LEGACY_CALL_CONTEXT Output
    )

//++
//
//  Routine Description:
//
//    This function calls the specified legacy function.
//
//  Arguments:
//
//    CodeSegment16   - Supplies the 16-bit segment value for the function to call.
//
//    CodeOffset16    - Supplies the 16-bit offset value for the function to call.
//
//    CallFrame       - Supplies a pointer to the call frame.
//
//    CallFrameSize   - Supplies the size of the call frame.
//
//    Input           - Supplies the input context for the call.
//
//    Output          - Receives the output context after the call.
//
//--

{
    PBEB Beb;

    BLASSERT((ULONG_PTR) CallFrame < LEGACY_MEMORY_LIMIT);

    BLASSERT(((ULONG_PTR) CallFrame + CallFrameSize) < LEGACY_MEMORY_LIMIT);

    Beb = BlGetBeb();

    Beb->LegacyCall_OpCode = LC_FARCALL;
    Beb->LegacyCall_FuncPtr.Segment = CodeSegment16;
    Beb->LegacyCall_FuncPtr.Offset = CodeOffset16;
    BlRtlConvertLinearPointerToFarPointer(CallFrame, &Beb->LegacyCall_FramePtr);
    Beb->LegacyCall_FrameSize = CallFrameSize;
    Beb->LegacyCall_ax = Input->eax;
    Beb->LegacyCall_bx = Input->ebx;
    Beb->LegacyCall_cx = Input->ecx;
    Beb->LegacyCall_dx = Input->edx;
    Beb->LegacyCall_si = Input->esi;
    Beb->LegacyCall_di = Input->edi;
    Beb->LegacyCall_ds = Input->ds;
    Beb->LegacyCall_es = Input->es;

    BlRtlMakeLegacyCall();

    Output->eax = Beb->LegacyCall_ax;
    Output->ebx = Beb->LegacyCall_bx;
    Output->ecx = Beb->LegacyCall_cx;
    Output->edx = Beb->LegacyCall_dx;
    Output->esi = Beb->LegacyCall_si;
    Output->edi = Beb->LegacyCall_di;
    Output->ds = Beb->LegacyCall_ds;
    Output->es = Beb->LegacyCall_es;
    Output->eflags = Beb->LegacyCall_flags;
}

VOID
BlRtlHaltInternal(
    PCSTR FileName,
    UINT32 LineNumber
    )

//++
//
//  Routine Description:
//
//    This function halts execution.
//
//  Arguments:
//
//    FileName   - file associated with call site.
//
//    LineNumber - line associated with call site.
//
//--

{
    BlRtlPrintf("BL: Halt! %s(%d)\n", FileName, LineNumber);

    for (;;) {
        ;
    }
}

VOID
BlRtlAssertFailedPtr(
    PCSTR FileName,
    UINT32 LineNumber,
    ULONG_PTR Param
    )

//++
//
//  Routine Description:
//
//    This function halts execution.
//
//  Arguments:
//
//    FileName   - file associated with call site.
//
//    LineNumber - line associated with call site.
//
//--

{
    BlRtlPrintf("BL: Assert failed! %s(%d) (%p)\n", FileName, LineNumber, Param);

    for (;;) {
        ;
    }
}

VOID
BlRtlAssertFailed(
    PCSTR FileName,
    UINT32 LineNumber
    )

//++
//
//  Routine Description:
//
//    This function halts execution.
//
//  Arguments:
//
//    FileName   - file associated with call site.
//
//    LineNumber - line associated with call site.
//
//--

{
    BlRtlAssertFailedPtr(FileName, LineNumber, 0);
}

UINT8
BlRtlComputeChecksum8(
    PCVOID Buffer,
    UINT32 Size
    )

//++
//
//  Routine Description:
//
//    This function computes the 8-bit checksum of the specified buffer.
//
//  Arguments:
//
//    Buffer  - Supplies a pointer to the buffer.
//
//    Size    - Supplies the size of the buffer.
//
//  Return Value:
//
//    8-bit check sum of the specified buffer.
//
//--

{
    UINT8 Checksum;
    UINT32 Index;

    Checksum = 0;

    for (Index = 0; Index < Size; Index += 1) {

        Checksum = Checksum + ((PUINT8) Buffer)[Index];
    }

    return Checksum;
}

BOOLEAN
BlRtlGetDriveParameters(
    UINT8 DriveId,
    PINT13_DRIVE_PARAMETERS DriveParameters
    )

//++
//
//  Routine Description:
//
//    This function gets the parameters for the specified drive.
//
//  Arguments:
//
//    DriveId         - Supplies the ID of the drive to query.
//
//    DriveParameters - Receives drive parameters.
//
//  Return Value:
//
//    TRUE, if query operation was successful.
//    FALSE, otherwise.
//
//--

{
    BL_LEGACY_CALL_CONTEXT Context;
    FAR_POINTER FarPointer;

    BlRtlZeroMemory(DriveParameters, sizeof(INT13_DRIVE_PARAMETERS));

    DriveParameters->StructureSize = sizeof(INT13_DRIVE_PARAMETERS);

    BlRtlConvertLinearPointerToFarPointer(DriveParameters, &FarPointer);

    BlRtlZeroMemory(&Context, sizeof(Context));

    Context.eax = 0x4800;
    Context.edx = DriveId;
    Context.ds = FarPointer.Segment;
    Context.esi = FarPointer.Offset;

    BlRtlCallLegacyInterruptService(0x13,
                                    &Context,
                                    &Context);

    if (((Context.eflags & RFLAGS_CF) != 0) || ((Context.eax & 0xFF00) != 0)) {

        return FALSE;
    }

    return TRUE;
}

#pragma pack(1)

typedef struct _INT13_DISK_ADDRESS_PACKET {
    UINT8 PacketSize;
    UINT8 Reserved;
    UINT16 NumberOfBlocks;
    FAR_POINTER Buffer;
    UINT64 FirstBlock;
} INT13_DISK_ADDRESS_PACKET, *PINT13_DISK_ADDRESS_PACKET;

C_ASSERT(sizeof(INT13_DISK_ADDRESS_PACKET) == 0x10);

#pragma pack()

INT13_DISK_ADDRESS_PACKET BlInt13AddressPacket;

BOOLEAN
BlRtlReadDrive(
    UINT8 DriveId,
    UINT64 FirstBlock,
    UINT16 NumberOfBlocks,
    PVOID Buffer
    )

//++
//
//  Routine Description:
//
//    This function reads from the specified drive region.
//
//  Arguments:
//
//    DriveId         - Supplies the ID of the drive to read from.
//
//    FirstBlock      - Supplies the first block to read.
//
//    NumberOfBlocks  - Supplies the number of blocks to read.
//
//    Buffer          - Receives data.
//
//  Return Value:
//
//    TRUE, if read operation was successful.
//    FALSE, otherwise.
//
//--

{
    FAR_POINTER AddressPacketPointer;
    BL_LEGACY_CALL_CONTEXT Context;

    BlRtlZeroMemory(&BlInt13AddressPacket, sizeof(BlInt13AddressPacket));
    BlRtlZeroMemory(&Context, sizeof(Context));

    BLASSERT(((ULONG_PTR) &BlInt13AddressPacket) < LEGACY_MEMORY_LIMIT);
    BLASSERT((ULONG_PTR) Buffer < LEGACY_MEMORY_LIMIT);

    BlInt13AddressPacket.PacketSize = sizeof(BlInt13AddressPacket);
    BlInt13AddressPacket.FirstBlock = FirstBlock;
    BlInt13AddressPacket.NumberOfBlocks = NumberOfBlocks;
    BlRtlConvertLinearPointerToFarPointer(Buffer, &BlInt13AddressPacket.Buffer);

    BlRtlConvertLinearPointerToFarPointer(&BlInt13AddressPacket, &AddressPacketPointer);

    Context.eax = 0x4200;
    Context.edx = DriveId;
    Context.ds = AddressPacketPointer.Segment;
    Context.esi = AddressPacketPointer.Offset;

    BlRtlCallLegacyInterruptService(0x13,
                                    &Context,
                                    &Context);

    if (((Context.eflags & RFLAGS_CF) != 0) || ((Context.eax & 0xFF00) != 0)) {

        return FALSE;
    }

    return TRUE;
}

BOOLEAN
(*BlFsGetFileSize)(
    PCSTR Path,
    PUINT32 FileSize
    );

BOOLEAN
(*BlFsReadFile)(
    PCSTR Path,
    PVOID Buffer,
    UINT32 NumberOfBytes
    );

#define CMOS_CONTROL_REGISTER           0x0070
#define CMOS_DATA_REGISTER              0x0071

#define CMOS_SECONDS_REGISTER           0x00
#define CMOS_MINUTES_REGISTER           0x02
#define CMOS_HOURS_REGISTER             0x04
#define CMOS_DAYS_REGISTER              0x07
#define CMOS_MONTHS_REGISTER            0x08
#define CMOS_YEARS_REGISTER             0x09
#define CMOS_STATUS_REGISTER_A          0x0A
#define CMOS_STATUS_REGISTER_B          0x0B
#define CMOS_SHUTDOWN_REGISTER          0x0F

#define CMOS_CLOCK_IN_BINARY            0x04
#define CMOS_ENABLE_PERIODIC_TIMER      0x40
#define CMOS_RATE_MASK                  0x0F
#define CMOS_DEFAULT_RATE               0x06

UINT8
BlCmosReadRegister(
    UINT8 Register
    )

//++
//
//  Routine Description:
//
//    This function reads from the specified CMOS register.
//
//  Arguments:
//
//    Register    - Supplies the CMOS register to read from.
//
//  Return Value:
//
//    Value read from the specified CMOS register.
//
//--

{
    BlRtlWritePort8(CMOS_CONTROL_REGISTER, Register);

    return BlRtlReadPort8(CMOS_DATA_REGISTER);
}

VOID
BlCmosWriteRegister(
    UINT8 Register,
    UINT8 Value
    )

//++
//
//  Routine Description:
//
//    This function writes to the specified CMOS register.
//
//  Arguments:
//
//    Register    - Supplies the CMOS register to write to.
//
//    Value       - Supplies the value to write.
//
//--

{
    BlRtlWritePort8(CMOS_CONTROL_REGISTER, Register);

    BlRtlWritePort8(CMOS_DATA_REGISTER, Value);
}

VOID
BlRtlResetSystem(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function resets the system.
//
//--

{
    BL_LEGACY_CALL_CONTEXT Context;
    UINT8 Value;

    //
    // Issue a no-op legacy operation to restore legacy context.
    //

    BlGetBeb()->LegacyCall_OpCode = LC_NOP;
    BlRtlMakeLegacyCall();

    //
    // Disable periodic interrupt.
    //

    Value = BlCmosReadRegister(CMOS_STATUS_REGISTER_B);
    Value &= ~CMOS_ENABLE_PERIODIC_TIMER;
    BlCmosWriteRegister(CMOS_STATUS_REGISTER_B, Value);

    //
    // Set default rate.
    //

    Value = BlCmosReadRegister(CMOS_STATUS_REGISTER_A);
    Value &= ~CMOS_RATE_MASK;
    Value |= CMOS_DEFAULT_RATE;
    BlCmosWriteRegister(CMOS_STATUS_REGISTER_A, Value);

    //
    // Set reset reason.
    //

    BlCmosWriteRegister(CMOS_SHUTDOWN_REGISTER, 0);

    //
    // Try to reset using ACPI.
    //

    BlRtlPrintf("BL: Attempting reset with ACPI.\n");

    BlAcpiResetSystem();

    //
    // If the ACPI call returned, then it indicates that ACPI reset is
    // not supported, so try to reset with the keyboard controller.
    //

    BlRtlPrintf("BL: Attempting reset with keyboard controller.\n");

    BL_KEYBOARD_WRITE_COMMAND(BL_KEYBOARD_COMMAND_PULSE_RESET_BIT);

    //
    // Issue INT19 as last resort.
    //

    BlRtlZeroMemory(&Context, sizeof(Context));

    BlRtlCallLegacyInterruptService(0x19,
                                    &Context,
                                    &Context);

    for (;;) {

    }
}

VOID
BlRtlShutdownSystem(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function shuts down the system.
//
//--

{
    BL_LEGACY_CALL_CONTEXT Context;
    UINT32 Index;

    //
    // AIFIX: Add ACPI shutdown logic here.
    //

    BlRtlPrintf("BL: Attempting system shutdown through APM.\n");

    //
    // APM installation check.
    //

#if APM_VERBOSE

    BlRtlPrintf("APM: INT15/5300h [Installation Check]\n");

#endif

    BlRtlZeroMemory(&Context, sizeof(Context));

    Context.eax = 0x5300;

    BlRtlCallLegacyInterruptService(0x15,
                                    &Context,
                                    &Context);

    if (((Context.eflags & RFLAGS_CF) != 0) || (Context.ebx != 0x504D)) {

        BlRtlPrintf("APM: Not available!\n");
        BlRtlHalt();
    }

#if APM_VERBOSE

    BlRtlPrintf("APM: Found APM v%u.%u.\n",
                (Context.eax >> 8) & 0xFF,
                Context.eax && 0xFF);

#endif

    //
    // Connect real-mode interface.
    //

#if APM_VERBOSE

    BlRtlPrintf("APM: INT15/5301h [Connect Real-Mode Interface]\n");

#endif

    BlRtlZeroMemory(&Context, sizeof(Context));

    Context.eax = 0x5301;

    BlRtlCallLegacyInterruptService(0x15,
                                    &Context,
                                    &Context);

    if ((Context.eflags & RFLAGS_CF) != 0) {

        BlRtlPrintf("APM: INT15/5301h failed!\n");
        BlRtlHalt();
    }

    //
    // Set APM driver version.
    //

#if APM_VERBOSE

    BlRtlPrintf("APM: INT15/530Eh [Set APM Driver Version]\n");

#endif

    BlRtlZeroMemory(&Context, sizeof(Context));

    Context.eax = 0x530E;
    Context.ecx = 0x0102;

    BlRtlCallLegacyInterruptService(0x15,
                                    &Context,
                                    &Context);

    if ((Context.eflags & RFLAGS_CF) != 0) {

        BlRtlPrintf("APM: INT15/530Eh failed!\n");
        BlRtlHalt();
    }

#if APM_VERBOSE

    BlRtlPrintf("APM: INT15/5307h [Shutdown]\n");

#endif

    //
    // Announce shutdown.
    //
    // Note that the lab infrastructure searches for this string
    // when attempting to determine if the host successfully
    // reached shutdown.
    //

    BlRtlPrintf("APM: Power-off via APM.\n");

    //
    // Issue APM shutdown command.
    //

    Context.eax = 0x5307;
    Context.ebx = 1;
    Context.ecx = 3;

    BlRtlCallLegacyInterruptService(0x15,
                                    &Context,
                                    &Context);

    for (;;) {

    }
}

UINT8
BlRtlConvertBcdToBinary8(
    UINT8 BcdValue
    )

//++
//
//  Routine Description:
//
//    This function converts the specified 8-bit BCD value to binary.
//
//  Arguments:
//
//    BcdValue    - Supplies the BCD value to convert.
//
//  Return Value:
//
//    Binary value matching the specified BCD value.
//
//--

{
    return (((BcdValue >> 4) & 0xF) * 10) + (BcdValue & 0xF);
}

VOID
BlRtlGetCurrentTime(
    PBL_TIME Time
    )

//++
//
//  Routine Description:
//
//    This function queries the current time.
//
//  Arguments:
//
//    Time    - Receives current time.
//
//--

{
    //
    // Query CMOS RTC.
    //

    Time->Year = BlCmosReadRegister(CMOS_YEARS_REGISTER);
    Time->Month = BlCmosReadRegister(CMOS_MONTHS_REGISTER);
    Time->Day = BlCmosReadRegister(CMOS_DAYS_REGISTER);
    Time->Hour = BlCmosReadRegister(CMOS_HOURS_REGISTER);
    Time->Minute = BlCmosReadRegister(CMOS_MINUTES_REGISTER);
    Time->Second = BlCmosReadRegister(CMOS_SECONDS_REGISTER);

    //
    // If the clock is in BCD format, then convert it to binary.
    //

    if ((BlCmosReadRegister(CMOS_STATUS_REGISTER_B) & CMOS_CLOCK_IN_BINARY) == 0) {

        Time->Year = BlRtlConvertBcdToBinary8((UINT8) Time->Year);
        Time->Month = BlRtlConvertBcdToBinary8(Time->Month);
        Time->Day = BlRtlConvertBcdToBinary8(Time->Day);
        Time->Hour = BlRtlConvertBcdToBinary8(Time->Hour);
        Time->Minute = BlRtlConvertBcdToBinary8(Time->Minute);
        Time->Second = BlRtlConvertBcdToBinary8(Time->Second);
    }
}

