//++
//
//  Copyright (c) Microsoft Corporation
//
//  Module Name:
//
//    blentry.cpp
//
//  Abstract:
//
//    This module implements the entry point for the boot loader.
//
//--

#include "bl.h"

//#define VESA_ENABLED 1

#define BL_BOOT_STACK_SIZE  0x10000

PVOID BlBootStackLimit;
PVOID BlBootStackBase;

VOID
BlApEntry(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function implements the non-legacy entry point for application processors.
//
//--

{
    BlSingularityApEntry();

    BlRtlHalt();
}

VOID
BlInitialize(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function initializes the boot loader.
//
//--

{
    PBEB Beb;

    Beb = BlGetBeb();

    //
    // Check boot type and perform any necessary source specific initialization.
    //

    BlRtlPrintf("Booting from ");

    switch (Beb->BootType) {

        case BL_CD_BOOT: {

            BlRtlPrintf("CD in drive 0x%02x.\n\n", Beb->BootDriveNumber);

            BlCdInitialize((UINT8) Beb->BootDriveNumber);

            break;
        }

        case BL_FAT16_BOOT: {

            BlRtlPrintf("FAT16 on drive 0x%02x.\n\n", Beb->BootDriveNumber);

            BlFatInitialize((UINT8) Beb->BootDriveNumber, MBR_FAT16LBA);

            break;
        }

        case BL_FAT32_BOOT: {

            BlRtlPrintf("FAT32 on drive 0x%02x.\n\n", Beb->BootDriveNumber);

            BlFatInitialize((UINT8) Beb->BootDriveNumber, MBR_FAT32LBA);

            break;
        }

        case BL_PXE_BOOT: {

            BlRtlPrintf("network.\n");

            BlPxeInitialize();

            break;
        }

        case BL_FLASH_BOOT: {

            BlRtlPrintf("Flash.\n");

            BlFlashInitialize((PVOID)Beb->FlashImage, (PVOID)Beb->FlashImage);

            break;
        }

        default: {

            BlRtlPrintf("unknown source!\n");

            BlRtlHalt();
        }
    }

    //
    // Initialize PNP BIOS support.
    //

    if (Beb->BootType != BL_FLASH_BOOT) {

        BlPnpInitialize();

    }

    //
    // Initialize MPS support.
    //

    BlMpsInitialize();

    //
    // Initialize ACPI support.
    //

    if (Beb->BootType != BL_FLASH_BOOT) {

        BlAcpiInitialize();

    }
    else {

        BlAcpiNumberOfProcessors = 1;

    }

    //
    // Set AP entry address.
    //

    Beb->ApEntry = (UINT32) (ULONG_PTR) BlApEntry;

    //
    // Initialize Singularity.
    //

    if (BlCommandLine == NULL) {

        BlCommandLine = L"";
    }

    BlSingularityInitialize(BlAcpiNumberOfProcessors,
                            &Beb->ApEntry16,
                            &Beb->ApStartupLock);
}

#if defined(BOOT_X86)

#define PLATFORM_STRING                 "x86"

#elif defined(BOOT_X64)

#define PLATFORM_STRING                 "x64"

#endif

BL_TIME BlStartTime;

VOID
BlEntry(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function implements the non-legacy entry point for the boot loader.
//
//--

{
    PBEB Beb;

    Beb = BlGetBeb();

    //
    // Initialize the trap table.
    //
    BlTrapEnable();

    //
    // Initialize video.
    //

    BlVideoInitialize();

    //
    // Print the welcome banner.
    //

    BlRtlPrintf("Singularity %s Boot Loader [%s %s]\n"
                "\n",
                PLATFORM_STRING,
                __DATE__,
                __TIME__);

    //
    // Capture boot start time.
    //

    if (Beb->BootType != BL_FLASH_BOOT) {

        BlRtlGetCurrentTime(&BlStartTime);

    }

    //
    // Initialize memory management (ring transitions must follow this call).
    //

    BlMmInitializeSystem();

    //
    // Initialize PCI support (probe for 1394 interfaces for KD).
    //

    if (Beb->BootType != BL_FLASH_BOOT) {

        BlPciInitialize();

    }

    //
    // Initialize KD.
    //

    BlRtlPrintf("Looking for debugger.\n");
//    BlKdInitialize();

    //
    // Print the welcome banner.
    //

    BlRtlPrintf("Boot Time: %02u/%02u/%02u %02u:%02u:%02u\n",
                BlStartTime.Month,
                BlStartTime.Day,
                BlStartTime.Year,
                BlStartTime.Hour,
                BlStartTime.Minute,
                BlStartTime.Second);

    //
    // Initialize VESA support.
    //

#if VESA_ENABLED

    BlVesaInitialize();

#endif

    //
    // Allocate and switch to the boot stack.
    //

    BlBootStackLimit = (PVOID) (ULONG_PTR) BlMmAllocatePhysicalRegion(BL_BOOT_STACK_SIZE, BL_MM_PHYSICAL_REGION_BOOT_STACK);
    BlBootStackBase = (PVOID) ((ULONG_PTR) BlBootStackLimit + BL_BOOT_STACK_SIZE);

    BlMmSwitchStack(BlBootStackBase, BlInitialize);
}
