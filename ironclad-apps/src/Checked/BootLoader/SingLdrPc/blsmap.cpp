//++
//
//  Copyright (c) Microsoft Corporation
//
//  Module Name:
//
//    blsmap.cpp
//
//  Abstract:
//
//    This module implements system memory map (SMAP) support for the boot loader.
//
//--


#include "bl.h"

BL_SMAP BlSystemMemoryMap;

#if SMAP_VERBOSE

PCHAR
BlSmapTypeString(
    UINT32 Type
    )

//++
//
//  Routine Description:
//
//    This function returns the specified memory type string.
//
//  Arguments:
//
//    Type    - Supplies the memory type.
//
//  Return Value:
//
//    Memory type string.
//
//--

{
    switch (Type) {

        case BL_SMAP_AVAILABLE: {

            return "Available";
        }

        case BL_SMAP_RESERVED: {

            return "Reserved";
        }

        case BL_SMAP_ACPI_RECLAIM: {

            return "ACPI Reclaim";
        }

        case BL_SMAP_ACPI_NVS: {

            return "ACPI NVS";
        }

        default: {

            return "*UNKNOWN*";
        }
    }
}

#endif

VOID
BlSmapInitialize(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function initializes the system memory map.
//
//--

{
    UINT32 Index;
    PBEB Beb;

    Beb = BlGetBeb();

    if (Beb->SmapAddr != 0) {
        PUINT8 pb = (PUINT8)Beb->SmapAddr;
        UINT32 cb = Beb->SmapSize;

        for (Index = 0; Index < cb / 20; Index++) {
            PUINT8 pn = pb + Index * 20;
            BlRtlCopyMemory((PVOID)&BlSystemMemoryMap.Entry[Index],
                            (PVOID)(pb + Index * 20), 20);
#if 0
            BlVideoPrintf("%4d: %p %p %8x\n",
                          Index,
                          ((UINT64 *)(pn + 0))[0],
                          ((UINT64 *)(pn + 8))[0],
                          ((UINT32 *)(pn + 16))[0]);
#endif
        }
        BlSystemMemoryMap.EntryCount = Index;
    }
    else {
        ULONG_PTR Address;
        BL_LEGACY_CALL_CONTEXT Context;
        UINT32 ContinuationValue;

        Index = 0;
        ContinuationValue = 0;

        for (;;) {

            BLASSERT(Index < (sizeof(BlSystemMemoryMap.Entry) / sizeof(BlSystemMemoryMap.Entry[0])));

            BlRtlZeroMemory(&Context, sizeof(Context));

            Context.eax = 0xE820;
            Context.edx = 0x534D4150;    // 'SMAP'
            Context.ebx = ContinuationValue;
            Context.ecx = 20;

            Address = (ULONG_PTR) &BlSystemMemoryMap.Entry[Index];
            Context.es = (UINT32) (Address >> 4);
            Context.edi = (UINT32) (Address & 0xF);

            BlRtlCallLegacyInterruptService(0x15,
                                            &Context,
                                            &Context);

            if (((Context.eflags & RFLAGS_CF) != 0) || (Context.eax != 0x534D4150)) {

                BlRtlPrintf("SMAP: INT 15/E820 failed!\n");
                BlRtlHalt();
            }

            Index += 1;

            ContinuationValue = Context.ebx;

            if (ContinuationValue == 0) {

                break;
            }
        }

        BlSystemMemoryMap.EntryCount = Index;
    }

#if SMAP_VERBOSE

    BlRtlPrintf("SMAP: %u entries\n", BlSystemMemoryMap.EntryCount);

    for (Index = 0; Index < BlSystemMemoryMap.EntryCount; Index += 1) {

        BlRtlPrintf("SMAP:  %016I64x ... %016I64x %s\n",
                    BlSystemMemoryMap.Entry[Index].Base,
                    BlSystemMemoryMap.Entry[Index].Base + BlSystemMemoryMap.Entry[Index].Size - 1,
                    BlSmapTypeString(BlSystemMemoryMap.Entry[Index].Type));
    }

#endif

    return;
}

