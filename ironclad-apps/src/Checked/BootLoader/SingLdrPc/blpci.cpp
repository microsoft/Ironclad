//++
//
//  Copyright (c) Microsoft Corporation
//
//  Module Name:
//
//    blpci.cpp
//
//  Abstract:
//
//    This module implements PCI support for the boot loader environment.
//
//--


#include "bl.h"

#define PCI_MAX_BUSES                   128
#define PCI_MAX_DEVICES                 32
#define PCI_MAX_FUNCTIONS               8

#define PCI_ADDRESS_PORT                0x0CF8
#define PCI_DATA_PORT                   0x0CFC

#define PCI_INVALID_VENDORID            0xFFFF

#define PCI_MULTI_FUNCTION              0x80
#define PCI_TYPE_MASK                   0x7F
#define PCI_DEVICE                      0x00
#define PCI_BRIDGE                      0x01

#define PCI_DEVICE_BASE_ADDRESS_COUNT   6

#define PCI_BASE_ADDRESS_MEMORY         0
#define PCI_BASE_ADDRESS_IO             1

#define PCI_BASE_ADDRESS_MEMORY_32      0
#define PCI_BASE_ADDRESS_MEMORY_32_1MB  1
#define PCI_BASE_ADDRESS_MEMORY_64      2

#define PCI_BASE_ADDRESS_SHIFT          4
#define PCI_BASE_ADDRESS_FLAGS_MASK     0xF

#pragma pack(1)

typedef struct _PCI_CONFIGURATION_SPACE_HEADER {
    UINT16 VendorId;
    UINT16 DeviceId;
    UINT16 Command;
    UINT16 Status;
    UINT8 RevisionId;
    UINT8 ProgrammingInterface;
    UINT8 SubClass;
    UINT8 BaseClass;
    UINT8 CacheLineSize;
    UINT8 LatencyTimer;
    UINT8 HeaderType;
    UINT8 BIST;

    union {

        struct {
            UINT32 BaseAddressRegister[PCI_DEVICE_BASE_ADDRESS_COUNT];
            UINT32 CardBusCISPointer;
            UINT16 SubsystemVendorId;
            UINT16 SubsystemId;
            UINT32 ExpansionRomBaseAddress;
            UINT32 Reserved[2];
            UINT8 InterruptLine;
            UINT8 InterruptPin;
            UINT8 MinimumGrant;
            UINT8 MaximumLatency;
            UINT8 __End;
        } Device;

        UINT8 DynamicStart;
    } u1;

} PCI_CONFIGURATION_SPACE_HEADER, *PPCI_CONFIGURATION_SPACE_HEADER;

C_ASSERT(FIELD_OFFSET(PCI_CONFIGURATION_SPACE_HEADER, u1.DynamicStart) == 0x10);
C_ASSERT(FIELD_OFFSET(PCI_CONFIGURATION_SPACE_HEADER, u1.Device.__End) == 0x40);

typedef struct _PCI_CONFIG_ADDRESS {

    union {

        struct {
            UINT32 Zero:2;
            UINT32 RegisterNumber:6;
            UINT32 FunctionNumber:3;
            UINT32 DeviceNumber:5;
            UINT32 BusNumber:8;
            UINT32 Reserved:7;
            UINT32 Enable:1;
        } s1;

        UINT32 Value;
    } u1;
} PCI_CONFIG_ADDRESS, *PPCI_CONFIG_ADDRESS;

C_ASSERT(sizeof(PCI_CONFIG_ADDRESS) == sizeof(UINT32));

typedef struct _PCI_BASE_ADDRESS {

    union {

        struct {
            UINT32 Type:1;
        } Common;

        struct {
            UINT32 Zero:1;
            UINT32 Type:2;
            UINT32 Prefetch:1;
            UINT32 Base:28;
        } Memory;

        struct {
            UINT64 Zero:1;
            UINT64 Type:2;
            UINT64 Prefetch:1;
            UINT64 Base:60;
        } Memory64;

        struct {
            UINT32 One:1;
            UINT32 Reserved:1;
            UINT32 Base:30;
        } Io;
    } u1;
} PCI_BASE_ADDRESS, *PPCI_BASE_ADDRESS;

C_ASSERT(sizeof(((PPCI_BASE_ADDRESS) 0)->u1.Memory) == sizeof(UINT32));
C_ASSERT(sizeof(((PPCI_BASE_ADDRESS) 0)->u1.Memory64) == sizeof(UINT64));
C_ASSERT(sizeof(((PPCI_BASE_ADDRESS) 0)->u1.Io) == sizeof(UINT32));

#pragma pack()

PCI_INSTALLATION_CHECK BlPciInstallationCheck;
UINT32 BlPciOhci1394BaseAddress;

BOOLEAN
BlPciCheckBios(
    PPCI_INSTALLATION_CHECK PciInstallationCheck
    )

//++
//
//  Routine Description:
//
//    This function checks for the presence of PCI BIOS.
//
//  Arguments:
//
//    PciInstallationCheck    - Receives PCI BIOS information.
//
//  Return Value:
//
//    TRUE, if PCI BIOS is present.
//    FALSE, otherwise.
//
//--

{
    BL_LEGACY_CALL_CONTEXT Context;

    //
    // Call PCI detection service.
    //

    BlRtlZeroMemory(&Context, sizeof(Context));

    Context.eax = 0xB101;

    BlRtlCallLegacyInterruptService(0x1A,
                                    &Context,
                                    &Context);

    //
    // If CF is set, AH is not zero, or if the signature is not ' ICP', then
    // there is no PCI BIOS.
    //

    if (((Context.eflags & RFLAGS_CF) != 0) ||
        (((Context.eax >> 8) & 0xFF) != 0) ||
        (Context.edx != 0x20494350)) {

        return FALSE;
    }

    //
    // Populate the provided installation check structure and return success.
    //

    PciInstallationCheck->Eax = Context.eax;
    PciInstallationCheck->Ebx = Context.ebx;
    PciInstallationCheck->Ecx = Context.ecx;
    PciInstallationCheck->Edx = Context.edx;
    PciInstallationCheck->HardwareCharacteristics = (UINT8) (Context.eax & 0xFF);
    PciInstallationCheck->LastBusNumber = (UINT8) (Context.ecx & 0xFF);
    PciInstallationCheck->MajorVersion = (UINT8) ((Context.ebx >> 8) & 0xFF);
    PciInstallationCheck->MinorVersion = (UINT8) (Context.ebx & 0xFF);
    PciInstallationCheck->ProtectedModeEntryPoint = Context.edi;

    return TRUE;
}

UINT32
BlPciReadConfigurationRegister(
    UINT8 BusNumber,
    UINT8 DeviceNumber,
    UINT8 FunctionNumber,
    UINT8 RegisterNumber
    )

//++
//
//  Routine Description:
//
//    This function reads from the specified PCI configuration register.
//
//  Arguments:
//
//    BusNumber       - Supplies the PCI bus number.
//
//    DeviceNumber    - Supplies the PCI device number.
//
//    FunctionNumber  - Supplies the PCI function number.
//
//    RegisterNumber  - Supplies the PCI configuration register number.
//
//  Return Value:
//
//    The value of the configuration register.
//
//--

{
    PCI_CONFIG_ADDRESS ConfigAddress;
    UINT32 Value;

    BLASSERT(DeviceNumber < PCI_MAX_DEVICES);
    BLASSERT(FunctionNumber < PCI_MAX_FUNCTIONS);
    BLASSERT((RegisterNumber % sizeof(UINT32)) == 0);

    BlRtlZeroMemory(&ConfigAddress, sizeof(ConfigAddress));

    ConfigAddress.u1.s1.BusNumber = BusNumber;
    ConfigAddress.u1.s1.DeviceNumber = DeviceNumber;
    ConfigAddress.u1.s1.FunctionNumber = FunctionNumber;
    ConfigAddress.u1.s1.RegisterNumber = RegisterNumber >> 2;
    ConfigAddress.u1.s1.Enable = 1;

    BlRtlWritePort32(PCI_ADDRESS_PORT, ConfigAddress.u1.Value);

    Value = BlRtlReadPort32(PCI_DATA_PORT);

    return Value;
}

VOID
BlPciWriteConfigurationRegister(
    UINT8 BusNumber,
    UINT8 DeviceNumber,
    UINT8 FunctionNumber,
    UINT8 RegisterNumber,
    UINT32 Value
    )

//++
//
//  Routine Description:
//
//    This function writes to the specified PCI configuration register.
//
//  Arguments:
//
//    BusNumber       - Supplies the PCI bus number.
//
//    DeviceNumber    - Supplies the PCI device number.
//
//    FunctionNumber  - Supplies the PCI function number.
//
//    RegisterNumber  - Supplies the PCI configuration register number.
//
//    Value           - Supplies the value to write.
//
//--

{
    PCI_CONFIG_ADDRESS ConfigAddress;

    BLASSERT(DeviceNumber < PCI_MAX_DEVICES);
    BLASSERT(FunctionNumber < PCI_MAX_FUNCTIONS);
    BLASSERT((RegisterNumber % sizeof(UINT32)) == 0);

    BlRtlZeroMemory(&ConfigAddress, sizeof(ConfigAddress));

    ConfigAddress.u1.s1.BusNumber = BusNumber;
    ConfigAddress.u1.s1.DeviceNumber = DeviceNumber;
    ConfigAddress.u1.s1.FunctionNumber = FunctionNumber;
    ConfigAddress.u1.s1.RegisterNumber = RegisterNumber >> 2;
    ConfigAddress.u1.s1.Enable = 1;

    BlRtlWritePort32(PCI_ADDRESS_PORT, ConfigAddress.u1.Value);

    BlRtlWritePort32(PCI_DATA_PORT, Value);

    return;
}

VOID
BlPciReadConfigurationSpace(
    UINT8 BusNumber,
    UINT8 DeviceNumber,
    UINT8 FunctionNumber,
    UINT8 RegisterNumber,
    PVOID Buffer,
    UINT16 BufferSize
    )

//++
//
//  Routine Description:
//
//    This function reads the specified PCI configuration space range.
//
//  Arguments:
//
//    BusNumber       - Supplies the PCI bus number.
//
//    DeviceNumber    - Supplies the PCI device number.
//
//    FunctionNumber  - Supplies the PCI function number.
//
//    RegisterNumber  - Supplies the PCI configuration register number.
//
//    Buffer          - Receives configuration data.
//
//    BufferSize      - Supplies the number of bytes to read.
//
//--

{
    UINT16 Count;
    UINT16 Index;

    BLASSERT((RegisterNumber % sizeof(UINT32)) == 0);
    BLASSERT((BufferSize % sizeof(UINT32)) == 0);

    Count = BufferSize / sizeof(UINT32);

    for (Index = 0; Index < Count; Index += 1) {

        ((PUINT32) Buffer)[Index] = BlPciReadConfigurationRegister(BusNumber,
                                                                  DeviceNumber,
                                                                  FunctionNumber,
                                                                  (UINT8) (RegisterNumber + (Index * sizeof(UINT32))));
    }

    return;
}

VOID
BlPciScanDevices(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function scans all PCI buses on the system.
//
//--

{
    UINT64 Address;
    PPCI_BASE_ADDRESS BaseAddress;
    UINT8 BaseAddressRegister;
    UINT8 BusNumber;
    PCI_CONFIGURATION_SPACE_HEADER Config;
    UINT8 DeviceNumber;
    UINT8 FunctionNumber;
    UINT8 Index;
    UINT8 NodeType;
    UINT32 OldValue;
    UINT32 Size;

    for (BusNumber = 0; BusNumber <= BlPciInstallationCheck.LastBusNumber; BusNumber += 1) {

        for (DeviceNumber = 0; DeviceNumber < PCI_MAX_DEVICES; DeviceNumber += 1) {

            for (FunctionNumber = 0; FunctionNumber < PCI_MAX_FUNCTIONS; FunctionNumber += 1) {

                BlRtlZeroMemory(&Config, sizeof(Config));

                Config.VendorId = PCI_INVALID_VENDORID;

                BlPciReadConfigurationSpace(BusNumber,
                                            DeviceNumber,
                                            FunctionNumber,
                                            0,
                                            &Config,
                                            FIELD_OFFSET(PCI_CONFIGURATION_SPACE_HEADER, u1.DynamicStart));

                if ((Config.VendorId == PCI_INVALID_VENDORID) || (Config.VendorId == 0)) {

                    continue;
                }

                NodeType = Config.HeaderType & PCI_TYPE_MASK;

                switch (NodeType) {

                    case PCI_DEVICE: {

#if PCI_VERBOSE

                        BlRtlPrintf("PCI: %02x:%02x:%02x: Device %04x:%04x [BC=%02x SC=%02x PI=%02x]\n",
                                    BusNumber,
                                    DeviceNumber,
                                    FunctionNumber,
                                    Config.VendorId,
                                    Config.DeviceId,
                                    Config.BaseClass,
                                    Config.SubClass,
                                    Config.ProgrammingInterface
                                    );

#endif

                        BlPciReadConfigurationSpace(BusNumber,
                                                    DeviceNumber,
                                                    FunctionNumber,
                                                    FIELD_OFFSET(PCI_CONFIGURATION_SPACE_HEADER, u1.DynamicStart),
                                                    &Config.u1.DynamicStart,
                                                    FIELD_OFFSET(PCI_CONFIGURATION_SPACE_HEADER, u1.Device.__End) - FIELD_OFFSET(PCI_CONFIGURATION_SPACE_HEADER, u1.DynamicStart));

                        for (Index = 0; Index < PCI_DEVICE_BASE_ADDRESS_COUNT; Index += 1) {

                            BaseAddress = (PPCI_BASE_ADDRESS) &Config.u1.Device.BaseAddressRegister[Index];
                            BaseAddressRegister = (UINT8) FIELD_OFFSET(PCI_CONFIGURATION_SPACE_HEADER, u1.Device.BaseAddressRegister[Index]);
                            Address = 0;

                            switch (BaseAddress->u1.Common.Type) {

                                case PCI_BASE_ADDRESS_MEMORY: {

                                    SATISFY_OVERZEALOUS_COMPILER(Size = 0);

                                    switch (BaseAddress->u1.Memory.Type) {

                                        case PCI_BASE_ADDRESS_MEMORY_32:
                                        case PCI_BASE_ADDRESS_MEMORY_32_1MB: {

                                            Address = BaseAddress->u1.Memory.Base << PCI_BASE_ADDRESS_SHIFT;

                                            OldValue = Config.u1.Device.BaseAddressRegister[Index];

                                            BlPciWriteConfigurationRegister(BusNumber,
                                                                            DeviceNumber,
                                                                            FunctionNumber,
                                                                            BaseAddressRegister,
                                                                            (UINT32) -1);

                                            Size = BlPciReadConfigurationRegister(BusNumber,
                                                                                  DeviceNumber,
                                                                                  FunctionNumber,
                                                                                  BaseAddressRegister);

                                            BlPciWriteConfigurationRegister(BusNumber,
                                                                            DeviceNumber,
                                                                            FunctionNumber,
                                                                            BaseAddressRegister,
                                                                            OldValue);

                                            Size &= ~(PCI_BASE_ADDRESS_FLAGS_MASK);

                                            Size = (~Size) + 1;

                                            break;
                                        }

                                        case PCI_BASE_ADDRESS_MEMORY_64: {

                                            Address = BaseAddress->u1.Memory64.Base << PCI_BASE_ADDRESS_SHIFT;

                                            OldValue = Config.u1.Device.BaseAddressRegister[Index];

                                            BlPciWriteConfigurationRegister(BusNumber,
                                                                            DeviceNumber,
                                                                            FunctionNumber,
                                                                            BaseAddressRegister,
                                                                            (UINT32) -1);

                                            Size = BlPciReadConfigurationRegister(BusNumber,
                                                                                  DeviceNumber,
                                                                                  FunctionNumber,
                                                                                  BaseAddressRegister);

                                            BlPciWriteConfigurationRegister(BusNumber,
                                                                            DeviceNumber,
                                                                            FunctionNumber,
                                                                            BaseAddressRegister,
                                                                            OldValue);

                                            Size &= ~(PCI_BASE_ADDRESS_FLAGS_MASK);

                                            Size = (~Size) + 1;

                                            Index += 1;

                                            break;
                                        }
                                    }

                                    if (Address != 0) {

                                        BLASSERT(Size > 0);

#if PCI_VERBOSE

                                        BlRtlPrintf("PCI: %02x:%02x:%02x: IO Memory [%016I64x ... %016I64x]\n",
                                                    BusNumber,
                                                    DeviceNumber,
                                                    FunctionNumber,
                                                    Address,
                                                    Address + Size - 1);

#endif

                                        if ((Address >= LEGACY_MEMORY_LIMIT) &&
                                            ((Address + Size) > Address) &&
                                            ((Address + Size) <= 0x100000000UI64)
                                            ) {

                                            BlMmMapVirtualRange((PVOID) (ULONG_PTR) Address,
                                                                (PVOID) (ULONG_PTR) Address,
                                                                Size,
                                                                TRUE,
                                                                (BOOLEAN) BaseAddress->u1.Memory.Prefetch,
                                                                FALSE);
                                        }

                                        //
                                        // Check if this memory range maps OHCI 1394 registers.
                                        //

                                        if ((Config.BaseClass == 0x0C) &&
                                            (Config.SubClass == 0x00) &&
                                            (Config.ProgrammingInterface == 0x10) &&
                                            (BlPciOhci1394BaseAddress == 0)) {

                                            BlPciOhci1394BaseAddress = (UINT32) Address;
                                        }
                                    }

                                    break;
                                }
                            }
                        }

                        break;
                    }

                    case PCI_BRIDGE: {

#if PCI_VERBOSE

                        BlRtlPrintf("PCI: %02x:%02x:%02x: Bridge %04x:%04x\n",
                                    BusNumber,
                                    DeviceNumber,
                                    FunctionNumber,
                                    Config.VendorId,
                                    Config.DeviceId);

#endif

                        break;
                    }
                }

                if ((Config.HeaderType & PCI_MULTI_FUNCTION) == 0) {

                    break;
                }
            }
        }
    }
}
VOID
BlPciInitialize(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function initializes PCI support.
//
//--

{
    if (BlPciCheckBios(&BlPciInstallationCheck) == FALSE) {

        BlRtlPrintf("pci: PCI BIOS not detected!\n");
        BlRtlHalt();
    }

#if PCI_VERBOSE

    BlRtlPrintf("PCI: PCI BIOS detected.\n"
                "PCI:   Version         : %u.%u\n"
                "PCI:   Last Bus Number : %u\n",
                BlPciInstallationCheck.MajorVersion,
                BlPciInstallationCheck.MinorVersion,
                BlPciInstallationCheck.LastBusNumber);

#endif

    BlPciScanDevices();

    return;
}
