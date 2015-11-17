//++
//
//  Copyright (c) Microsoft Corporation
//
//  Module Name:
//
//    blmps.cpp
//
//  Abstract:
//
//    This module implements MPS support for the boot loader environment.
//
//--


#include "bl.h"

//
// MPS Floating Pointer Structure (FPS)
//

typedef struct _MPS_FPS {
    CHAR Signature[4];
    UINT32 ConfigurationTableAddress;
    UINT8 Length;
    UINT8 Revision;
    UINT8 Checksum;
    UINT8 FeatureByte[5];
} MPS_FPS, *PMPS_FPS;

C_ASSERT(sizeof(MPS_FPS) == 16);

PVOID BlMpsFps;

PMPS_FPS
BlMpsLocateFpsInRange(
    ULONG_PTR Start,
    ULONG_PTR End
    )

//++
//
//  Routine Description:
//
//    This function locates the MPS FPS structure in the specified range.
//
//  Arguments:
//
//    Start   - Supplies the start address of the range to locate in.
//
//    End     - Supplies the end address of the range to locate in.
//
//  Return Value:
//
//    MPS FPS structure, if located.
//    NULL, otherwise.
//
//--

{
    PMPS_FPS Fps;

    Start = ROUND_UP_TO_POWER2(Start, 16);
    End &= ~((ULONG_PTR) 15);

    while (Start < End) {

        Fps = (PMPS_FPS) Start;

        if ((Fps->Signature[0] == '_') &&
            (Fps->Signature[1] == 'M') &&
            (Fps->Signature[2] == 'P') &&
            (Fps->Signature[3] == '_') &&
            (BlRtlComputeChecksum8(Fps, Fps->Length * 16) == 0)) {

            return Fps;
        }

        Start += 16;
    }

    return NULL;
}

PMPS_FPS
BlMpsLocateFps(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function locates the MPS FPS structure.
//
//  Return Value:
//
//    MPS FPS structure, if located.
//    NULL, otherwise.
//
//--

{
    PMPS_FPS Fps;

    //
    // Look for FPS in the first KB of the EBDA first.
    //

    Fps = BlMpsLocateFpsInRange((ULONG_PTR) BlMmExtendedBiosDataArea, (ULONG_PTR) BlMmExtendedBiosDataArea + 1024);

    if (Fps != NULL) {

        return Fps;
    }

    //
    // Look for FPS in the 639KB - 640KB range.
    //

    Fps = BlMpsLocateFpsInRange(639 * 1024, 640 * 1024);

    if (Fps != NULL) {

        return Fps;
    }

    //
    // Look for FPS in the BIOS ROM range (0xF0000 - 0xFFFFF).
    //

    Fps = BlMpsLocateFpsInRange(0xF0000, 0x100000);

    if (Fps != NULL) {

        return Fps;
    }

    //
    // If FPS is not located, then return NULL.
    //

    return NULL;
}

VOID
BlMpsInitialize(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function initializes MPS support for the boot loader.
//
//--

{
    PMPS_FPS Fps;

    Fps = BlMpsLocateFps();

    if (Fps == NULL) {

#if MPS_VERBOSE

        BlRtlPrintf("MPS: MPS not supported!\n");

#endif

        return;
    }

#if MPS_VERBOSE

    BlRtlPrintf("MPS: Found version 1.%u.\n", Fps->Revision);

#endif

    BlMpsFps = Fps;

    return;
}



