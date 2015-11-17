//++
//
//  Copyright (c) Microsoft Corporation
//
//  Module Name:
//
//    blacpi.cpp
//
//  Abstract:
//
//    This module implements ACPI support for the boot loader environment.
//
//  Environment:
//
//    Boot loader.
//
//--

#include "bl.h"

#pragma pack(1)

//
// Generic Address Structure (GAS)
//

#define ACPI_GAS_MEMORY                 0
#define ACPI_GAS_IO                     1
#define ACPI_GAS_PCI                    2

#define ACPI_GAS_ACCESS_SIZE_UNDEFINED  0
#define ACPI_GAS_ACCESS_SIZE_BYTE       1
#define ACPI_GAS_ACCESS_SIZE_WORD       2
#define ACPI_GAS_ACCESS_SIZE_DWORD      3
#define ACPI_GAS_ACCESS_SIZE_QWORD      4

typedef struct _ACPI_GAS {
    UINT8 AddressSpaceId;
    UINT8 RegisterBitWidth;
    UINT8 RegisterBitOffset;
    UINT8 AccessSize;
    UINT64 Address;
} ACPI_GAS, *PACPI_GAS;

C_ASSERT(sizeof(ACPI_GAS) == 12);

//
// Root System Description Pointer (RSDP)
//

typedef struct _ACPI_RSDP {
    CHAR Signature[8];
    UINT8 Checksum;
    CHAR OemId[6];
    UINT8 Revision;
    UINT32 RsdtAddress;
    UINT32 Length;
    UINT64 XsdtAddress;
    UINT8 ExtendedChecksum;
    UINT8 Reserved[3];
} ACPI_RSDP, *PACPI_RSDP;

C_ASSERT(sizeof(ACPI_RSDP) == 36);

//
// Root System Description Table (RSDT)
//

typedef struct _ACPI_RSDT {
    UINT8 Signature[4];
    UINT32 Length;
    UINT8 Revision;
    UINT8 Checksum;
    UINT8 OemId[6];
    UINT8 OemTableId[8];
    UINT32 OemRevision;
    UINT32 CreatorId;
    UINT32 CreatorRevision;
    UINT32 Entry[];
} ACPI_RSDT, *PACPI_RSDT;

C_ASSERT(sizeof(ACPI_RSDT) == 36);

//
// Multiple APIC Description Table (MADT)
//

typedef struct _ACPI_MADT {
    UINT8 Signature[4];
    UINT32 Length;
    UINT8 Revision;
    UINT8 Checksum;
    UINT8 OemId[6];
    UINT8 OemTableId[8];
    UINT32 OemRevision;
    UINT32 CreatorId;
    UINT32 CreatorRevision;
    UINT32 LocalApicAddress;
    UINT32 Flags;
    UINT8 ApicStructures[];
} ACPI_MADT, *PACPI_MADT;

C_ASSERT(sizeof(ACPI_MADT) == 44);

#define ACPI_APIC_TYPE_PROCESSOR_LOCAL  0

typedef struct _ACPI_MADT_ENTRY {
    UINT8 Type;
    UINT8 Length;
} ACPI_MADT_ENTRY, *PACPI_MADT_ENTRY;

typedef struct _ACPI_PROCESSOR_LOCAL_APIC {
    UINT8 Type;
    UINT8 Length;
    UINT8 AcpiProcessorId;
    UINT8 ApicId;
    union {
        struct {
            UINT32 Enabled:1;
            UINT32 Reserved:31;
        } s1;
        UINT32 Flags;
    } u1;
} ACPI_PROCESSOR_LOCAL_APIC, *PACPI_PROCESSOR_LOCAL_APIC;

C_ASSERT(sizeof(ACPI_PROCESSOR_LOCAL_APIC) == 8);

//
//System Resource Affinity Table (SRAT)
//

typedef struct _ACPI_SRAT {
    UINT8 Signature[4];
    UINT32 Length;
    UINT8 Revision;
    UINT8 Checksum;
    UINT8 OemId[6];
    UINT8 OemTableId[8];
    UINT32 OemRevision;
    UINT32 CreatorId;
    UINT32 CreatorRevision;
    UINT8 Reserved[12];
    UINT8 SratStructures[];
} ACPI_SRAT, *PACPI_SRAT;

C_ASSERT(sizeof(ACPI_SRAT) == 48);

#define ACPI_SRAT_TYPE_PROC_AFFINITY_ENTRY 0
#define ACPI_SRAT_TYPE_MEM_AFFINITY_ENTRY 1

typedef ACPI_MADT_ENTRY ACPI_SRAT_ENTRY;
typedef PACPI_MADT_ENTRY PACPI_SRAT_ENTRY;

typedef struct _ACPI_SRAT_PROC_AFFINITY_ENTRY {
    UINT8 Type;
    UINT8 Length;
    UINT8 ProximityDomainLowEightBits;
    UINT8 ApicID;
    UINT32 Flags;
    UINT8 LocalApicEid;
    UINT8 ProximityDomainHighTwentyFourBits[3];
    UINT32 Reserved;
} ACPI_SRAT_PROC_AFFINITY_ENTRY, *PACPI_SRAT_PROC_AFFINITY_ENTRY;

typedef struct _ACPI_SRAT_MEM_AFFINITY_ENTRY {
    UINT8 Type;
    UINT8 Length;
    UINT32 ProximityDomain;
    UINT8 Reserved[2];
    UINT32 BaseAddressLow;
    UINT32 BaseAddressHigh;
    UINT32 LengthLow;
    UINT32 LengthHigh;
    UINT32 Reserved2;
    UINT32 Flags;
    UINT8 Reserved3[8];
} ACPI_SRAT_MEM_AFFINITY_ENTRY, *PACPI_SRAT_MEM_AFFINITY_ENTRY;

//
// Fixed ACPI Description Table (FADT)
//

#define ACPI_FADT_FLAGS_RESET_SUPPORTED 0x400

typedef struct _ACPI_FADT {
    UINT8 Signature[4];
    UINT32 Length;
    UINT8 Revision;
    UINT8 Checksum;
    UINT8 OemId[6];
    UINT8 OemTableId[8];
    UINT32 OemRevision;
    UINT32 CreatorId;
    UINT32 CreatorRevision;
    UINT8 Data1[112-36];
    UINT32 Flags;
    ACPI_GAS ResetRegister;
    UINT8 ResetValue;
    UINT8 Data2[244-129];
} ACPI_FADT, *PACPI_FADT;

C_ASSERT(FIELD_OFFSET(ACPI_FADT, Flags) == 112);
C_ASSERT(FIELD_OFFSET(ACPI_FADT, ResetRegister) == 116);
C_ASSERT(FIELD_OFFSET(ACPI_FADT, ResetValue) == 128);
C_ASSERT(sizeof(ACPI_FADT) == 244);

#pragma pack()

PACPI_FADT BlAcpiFadt;
PACPI_MADT BlAcpiMadt;
UINT32 BlAcpiNumberOfProcessors;
PACPI_RSDP BlAcpiRsdp;
PVOID BlAcpiRsdpAddress;
PACPI_RSDT BlAcpiRsdt;
PACPI_SRAT BlAcpiSrat;

PACPI_RSDP
BlAcpiLocateRsdp(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function locates the ACPI RSDP structure.
//
//  Return Value:
//
//    ACPI RSDP structure, if located.
//    NULL, otherwise.
//
//--

{
    ULONG_PTR End;
    PACPI_RSDP Rsdp;
    ULONG_PTR Start;

    Start = 0xE0000;
    End = 0x100000;

    while (Start < End) {

        Rsdp = (PACPI_RSDP) Start;

        if ((Rsdp->Signature[0] == 'R') &&
            (Rsdp->Signature[1] == 'S') &&
            (Rsdp->Signature[2] == 'D') &&
            (Rsdp->Signature[3] == ' ') &&
            (Rsdp->Signature[4] == 'P') &&
            (Rsdp->Signature[5] == 'T') &&
            (Rsdp->Signature[6] == 'R') &&
            (Rsdp->Signature[7] == ' ') &&
            (BlRtlComputeChecksum8(Rsdp, 20) == 0)
            ) {

            return Rsdp;
        }

        Start += 0x10;
    }

    Start = (ULONG_PTR) BlMmExtendedBiosDataArea;
    End = Start + 0x10000;

    while (Start < End) {

        Rsdp = (PACPI_RSDP) Start;

        if ((Rsdp->Signature[0] == 'R') &&
            (Rsdp->Signature[1] == 'S') &&
            (Rsdp->Signature[2] == 'D') &&
            (Rsdp->Signature[3] == ' ') &&
            (Rsdp->Signature[4] == 'P') &&
            (Rsdp->Signature[5] == 'T') &&
            (Rsdp->Signature[6] == 'R') &&
            (Rsdp->Signature[7] == ' ') &&
            (BlRtlComputeChecksum8(Rsdp, 20) == 0)
            ) {

            return Rsdp;
        }

        Start += 0x10;
    }

    return NULL;
}

PACPI_RSDT
BlAcpiLocateRsdt(
    PACPI_RSDP Rsdp
    )

//++
//
//  Routine Description:
//
//    This function locates the ACPI RSDT structure.
//
//  Arguments:
//
//    Rsdp    - Supplies a pointer to the ACPI RSDP structure.
//
//  Return Value:
//
//    ACPI RSDT structure, if located.
//    NULL, otherwise.
//
//--

{
    PACPI_RSDT Rsdt;

    Rsdt = (PACPI_RSDT) (ULONG_PTR) Rsdp->RsdtAddress;

    if (Rsdt == NULL) {

        return NULL;
    }

    if ((Rsdt->Signature[0] == 'R') &&
        (Rsdt->Signature[1] == 'S') &&
        (Rsdt->Signature[2] == 'D') &&
        (Rsdt->Signature[3] == 'T') &&
        (Rsdt->Length >= sizeof(ACPI_RSDT)) &&
        (BlRtlComputeChecksum8(Rsdt, Rsdt->Length) == 0)) {

        return Rsdt;
    }

    return NULL;
}

PACPI_MADT
BlAcpiLocateMadt(
    PACPI_RSDT Rsdt
    )

//++
//
//  Routine Description:
//
//    This function locates the ACPI MADT structure.
//
//  Arguments:
//
//    Rsdt    - Supplies a pointer to the ACPI RSDT structure.
//
//  Return Value:
//
//    ACPI MADT structure, if located.
//    NULL, otherwise.
//
//--

{
    UINT32 Index;
    PACPI_MADT Madt;
    UINT32 NumberOfTables;

    NumberOfTables = (Rsdt->Length - FIELD_OFFSET(ACPI_RSDT, Entry)) / sizeof(Rsdt->Entry[0]);

    for (Index = 0; Index < NumberOfTables; Index += 1) {

        Madt = (PACPI_MADT) (ULONG_PTR) Rsdt->Entry[Index];

        if ((Madt->Signature[0] == 'A') &&
            (Madt->Signature[1] == 'P') &&
            (Madt->Signature[2] == 'I') &&
            (Madt->Signature[3] == 'C') &&
            (Madt->Length >= sizeof(ACPI_MADT)) &&
            (BlRtlComputeChecksum8(Madt, Madt->Length) == 0)) {

            return Madt;
        }
    }

    return NULL;
}

PACPI_SRAT
BlAcpiLocateSrat(
    PACPI_RSDT Rsdt
    )

//++
//
//  Routine Description:
//
//    This function locates the ACPI SRAT structure.
//
//  Arguments:
//
//    Rsdt    - Supplies a pointer to the ACPI RSDT structure.
//
//  Return Value:
//
//    ACPI SRAT structure, if located.
//    NULL, otherwise.
//
//--

{
    UINT32 Index;
    PACPI_SRAT Srat;
    UINT32 NumberOfTables;

    NumberOfTables = (Rsdt->Length - FIELD_OFFSET(ACPI_RSDT, Entry)) / sizeof(Rsdt->Entry[0]);

    for (Index = 0; Index < NumberOfTables; Index += 1) {

        Srat = (PACPI_SRAT) (ULONG_PTR) Rsdt->Entry[Index];

        if ((Srat->Signature[0] == 'S') &&
            (Srat->Signature[1] == 'R') &&
            (Srat->Signature[2] == 'A') &&
            (Srat->Signature[3] == 'T') &&
            (Srat->Length >= sizeof(ACPI_SRAT)) &&
            (BlRtlComputeChecksum8(Srat, Srat->Length) == 0)) {
#if ACPI_VERBOSE
                BlRtlPrintf("ACPI: Found SRAT Table\n");
#endif

            return Srat;
        }
    }

    return NULL;
}

VOID
BlAcpiDumpSratEntries(
    VOID
    )
//++
//
//  Routine Description:
//
//    This function prints out the SRAT table.
//--
{
    PACPI_SRAT_ENTRY Entry;
    PCHAR Limit;
    PACPI_SRAT_PROC_AFFINITY_ENTRY ProcAffinityEntry;
    PACPI_SRAT_MEM_AFFINITY_ENTRY MemAffinityEntry;
    PCHAR Next;
    UINT32 hbits;
    UINT32 totalbits;

    if (BlAcpiSrat == NULL) {
        BlRtlPrintf("ACPI: No Srat??\n");
        return;
    }
#if ACPI_VERBOSE
    BlRtlPrintf("SRAT:\n");
#endif

    Next = (PCHAR) &BlAcpiSrat->SratStructures[0];
    Limit = ((PCHAR) BlAcpiSrat) + BlAcpiSrat->Length;

    while (Next < Limit) {

        Entry = (PACPI_SRAT_ENTRY) Next;

        if ((Entry->Type == ACPI_SRAT_TYPE_PROC_AFFINITY_ENTRY) &&
            (Entry->Length >= sizeof(ACPI_SRAT_PROC_AFFINITY_ENTRY))) {

            ProcAffinityEntry = (PACPI_SRAT_PROC_AFFINITY_ENTRY) Next;
#if ACPI_VERBOSE
            BlRtlPrintf(" Processor:\n");
#endif
            hbits = 0;
            hbits += ProcAffinityEntry->ProximityDomainHighTwentyFourBits[0] << 24;
            hbits += ProcAffinityEntry->ProximityDomainHighTwentyFourBits[1] << 16;
            hbits += ProcAffinityEntry->ProximityDomainHighTwentyFourBits[2] << 8;
            totalbits = hbits | ProcAffinityEntry->ProximityDomainLowEightBits;
#if ACPI_VERBOSE
            BlRtlPrintf("  HighDomain 0x%06x LowDomain 0x%02x totalbits 0x%08x\n",
                        hbits, ProcAffinityEntry->ProximityDomainLowEightBits,
                        totalbits);
            BlRtlPrintf("  ApicID: %d flags 0x%08x\n", ProcAffinityEntry->ApicID,
                        ProcAffinityEntry->Flags);
#endif
        }
        else if ((Entry->Type == ACPI_SRAT_TYPE_MEM_AFFINITY_ENTRY) &&
                   (Entry->Length >= sizeof(ACPI_SRAT_MEM_AFFINITY_ENTRY))) {

            MemAffinityEntry = (PACPI_SRAT_MEM_AFFINITY_ENTRY) Next;
#if ACPI_VERBOSE
            BlRtlPrintf(" Memory:\n");
            BlRtlPrintf("  BaseAddress 0x%08x.%08x ..  0x%08x.%08x",
                        MemAffinityEntry->BaseAddressHigh, MemAffinityEntry->BaseAddressLow,
                        MemAffinityEntry->LengthHigh, MemAffinityEntry->LengthLow);
            BlRtlPrintf("  Domain %d  Flags 0x%08x\n",
                        MemAffinityEntry->ProximityDomain,
                        MemAffinityEntry->Flags);
#endif
        }

        Next += Entry->Length;
    }
}

UINT32
BlAcpiGetNumberOfProcessors(
    VOID
    )
//++
//
//  Routine Description:
//
//    This function returns the number of processors.
//
//  Return Value:
//
//    Number of processors.
//
//--

{
    PACPI_MADT_ENTRY Entry;
    PCHAR Limit;
    PACPI_PROCESSOR_LOCAL_APIC LocalApic;
    PCHAR Next;
    UINT32 NumberOfProcessors;

    if (BlAcpiMadt == NULL) {

        return 1;
    }

    Next = (PCHAR) &BlAcpiMadt->ApicStructures[0];
    Limit = ((PCHAR) BlAcpiMadt) + BlAcpiMadt->Length;
    NumberOfProcessors = 0;

    while (Next < Limit) {

        Entry = (PACPI_MADT_ENTRY) Next;

        if ((Entry->Type == ACPI_APIC_TYPE_PROCESSOR_LOCAL) &&
            (Entry->Length >= sizeof(ACPI_PROCESSOR_LOCAL_APIC))) {

            LocalApic = (PACPI_PROCESSOR_LOCAL_APIC) Next;

            if (LocalApic->u1.s1.Enabled != FALSE) {

#if ACPI_VERBOSE

                BlRtlPrintf("ACPI: AcpiProcessorId=%u , LocalApicId=%u\n",
                            LocalApic->AcpiProcessorId,
                            LocalApic->ApicId);

#endif

                NumberOfProcessors += 1;
            }
        }

        Next += Entry->Length;
    }

    return NumberOfProcessors;
}

PACPI_FADT
BlAcpiLocateFadt(
    PACPI_RSDT Rsdt
    )

//++
//
//  Routine Description:
//
//    This function locates the ACPI FADT structure.
//
//  Arguments:
//
//    Rsdt    - Supplies a pointer to the ACPI RSDT structure.
//
//  Return Value:
//
//    ACPI FADT structure, if located.
//    NULL, otherwise.
//
//--

{
    PACPI_FADT Fadt;
    UINT32 Index;
    UINT32 NumberOfTables;

    NumberOfTables = (Rsdt->Length - FIELD_OFFSET(ACPI_RSDT, Entry)) / sizeof(Rsdt->Entry[0]);

    for (Index = 0; Index < NumberOfTables; Index += 1) {

        Fadt = (PACPI_FADT) (ULONG_PTR) Rsdt->Entry[Index];

        if ((Fadt->Signature[0] == 'F') &&
            (Fadt->Signature[1] == 'A') &&
            (Fadt->Signature[2] == 'C') &&
            (Fadt->Signature[3] == 'P') &&
            (BlRtlComputeChecksum8(Fadt, Fadt->Length) == 0)) {

            return Fadt;
        }
    }

    return NULL;
}

VOID
BlAcpiResetSystem(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function resets the system through the ACPI reset register.
//
//--

{
    if ((BlAcpiFadt->Revision < 2) ||
        (BlAcpiFadt->Length < (FIELD_OFFSET(ACPI_FADT, ResetValue) + sizeof(UINT8))) ||
        ((BlAcpiFadt->Flags & ACPI_FADT_FLAGS_RESET_SUPPORTED) == 0)
        ) {

#if ACPI_VERBOSE

        BlRtlPrintf("ACPI: Reset register is not supported! [FADT v%u]\n", BlAcpiFadt->Revision);

#endif

        return;
    }

#if ACPI_VERBOSE

    BlRtlPrintf("ACPI: Reset register type is %u.\n", BlAcpiFadt->ResetRegister.AddressSpaceId);

#endif

    switch (BlAcpiFadt->ResetRegister.AddressSpaceId) {

        case ACPI_GAS_IO: {

            BlRtlWritePort8((UINT16) BlAcpiFadt->ResetRegister.Address, BlAcpiFadt->ResetValue);

            break;
        }
    }
}

VOID
BlAcpiInitialize(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function initializes ACPI support for the boot loader.
//
//--

{
    BlAcpiRsdp = BlAcpiLocateRsdp();

    if (BlAcpiRsdp == NULL) {

        BlRtlPrintf("ACPI: No RSDP!\n");
        BlRtlHalt();
    }

    BlAcpiRsdpAddress = (PVOID) BlAcpiRsdp;

    BlAcpiRsdt = BlAcpiLocateRsdt(BlAcpiRsdp);

    if (BlAcpiRsdt == NULL) {

        BlRtlPrintf("ACPI: No RSDT!\n");
        BlRtlHalt();
    }

    BlAcpiFadt = BlAcpiLocateFadt(BlAcpiRsdt);

    if (BlAcpiFadt == NULL) {

        BlRtlPrintf("ACPI: No FADT!\n");
        //BlRtlHalt();
    }

    BlAcpiMadt = BlAcpiLocateMadt(BlAcpiRsdt);

    if (BlAcpiMadt == NULL) {

        BlAcpiNumberOfProcessors = 1;

    } else {

        BlAcpiNumberOfProcessors = BlAcpiGetNumberOfProcessors();
    }

    if (BlAcpiNumberOfProcessors == 0) {

        BlRtlPrintf("ACPI: No local APIC!\n");
        BlRtlHalt();
    }

    BlAcpiSrat = BlAcpiLocateSrat(BlAcpiRsdt);
    if (BlAcpiSrat != NULL) {
        BlAcpiDumpSratEntries();
    }


#if ACPI_VERBOSE

    BlRtlPrintf("ACPI: RSDP @ %p\n"
                "ACPI: RSDT @ %p\n"
                "ACPI: FADT @ %p [Revision=%u , Length=%u]\n"
                "ACPI: MADT @ %p\n"
                "ACPI: %u processor(s)\n",
                BlAcpiRsdp,
                BlAcpiRsdt,
                BlAcpiFadt,
                BlAcpiFadt->Revision,
                BlAcpiFadt->Length,
                BlAcpiMadt,
                BlAcpiNumberOfProcessors);

#endif

    //
    // Map APIC page uncached.
    //

    if ((BlAcpiMadt != NULL) && (BlAcpiMadt->LocalApicAddress != 0)) {

#if ACPI_VERBOSE

        BlRtlPrintf("ACPI: APIC mapped @ %p.\n", BlAcpiMadt->LocalApicAddress);

#endif

        BlMmMapVirtualRange((PVOID) (ULONG_PTR) BlAcpiMadt->LocalApicAddress,
                            (PVOID) (ULONG_PTR) BlAcpiMadt->LocalApicAddress,
                            PAGE_SIZE,
                            TRUE,
                            FALSE,
                            FALSE);
    }
}
