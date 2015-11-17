//++
//
//  Copyright (c) Microsoft Corporation
//
//  Module Name:
//
//    blmm.cpp
//
//  Abstract:
//
//    This module implements memory management for the boot loader.
//
//--

#include "bl.h"

LIST_ENTRY BlMmPhysicalRegionList;

struct {
    BL_MM_PHYSICAL_REGION StaticArray[16];
    LIST_ENTRY FreeList;
} BlMmPhysicalRegionLookaside;

GDTR BlMmInitialGdtr;

ULONG_PTR BlMmLegacyCr3;
ULONG_PTR BlMmBootCr3;

typedef struct _BL_MM_PAGE_TABLE {
    UINT64 Entry[512];
} BL_MM_PAGE_TABLE, *PBL_MM_PAGE_TABLE;

#if defined(BOOT_X64)

__declspec(align(PAGE_SIZE)) BL_MM_PAGE_TABLE BlMmPml4Table[1];

#endif

__declspec(align(PAGE_SIZE)) BL_MM_PAGE_TABLE BlMmPdpTable[1];
__declspec(align(PAGE_SIZE)) BL_MM_PAGE_TABLE BlMmPdTable[4];
__declspec(align(PAGE_SIZE)) BL_MM_PAGE_TABLE BlMmPgTable[1];

PVOID BlMmExtendedBiosDataArea;

VOID
BlMmCompactPhysicalRegionList(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function compacts the physical region list by coalescing adjacent
//    regions of the same type.
//
//--

{
    PBL_MM_PHYSICAL_REGION Current;
    PLIST_ENTRY Head;
    PBL_MM_PHYSICAL_REGION Next;

    Head = &BlMmPhysicalRegionList;

    if (BlRtlIsListEmpty(Head) != FALSE) {

        return;
    }

    Current = CONTAINING_RECORD(Head->Flink,
                                BL_MM_PHYSICAL_REGION,
                                Entry);

    for (;;) {

        BLASSERT(Current->Size > 0);

        BLASSERT(Current->Start + Current->Size == Current->Limit);

        BLASSERT((Current->Type >= BL_MM_PHYSICAL_REGION_MIN_TYPE) && (Current->Type <= BL_MM_PHYSICAL_REGION_MAX_TYPE));

        if (Current->Entry.Flink == Head) {

            break;
        }

        Next = CONTAINING_RECORD(Current->Entry.Flink,
                                 BL_MM_PHYSICAL_REGION,
                                 Entry);

        BLASSERT(Next->Start >= Current->Limit);

        if ((Next->Start == Current->Limit) &&
            (Next->Type == Current->Type)) {

            Current->Limit = Next->Limit;
            Current->Size = Current->Limit - Current->Start;

            BlRtlRemoveEntryList(&Next->Entry);

            BlRtlInsertTailList(&BlMmPhysicalRegionLookaside.FreeList, &Next->Entry);

            continue;
        }

        Current = Next;
    }
}

VOID
BlMmInsertPhysicalRegion(
    PBL_MM_PHYSICAL_REGION Region
    )

//++
//
//  Routine Description:
//
//    This function inserts a new physical region to the physical region list.
//
//  Arguments:
//
//    Region  - Supplies a pointer to the region to insert.
//
//--

{
    PLIST_ENTRY Entry;
    PLIST_ENTRY Head;
    PBL_MM_PHYSICAL_REGION Next;

    Head = &BlMmPhysicalRegionList;
    Entry = Head->Flink;

    while (Entry != Head) {

        Next = CONTAINING_RECORD(Entry,
                                 BL_MM_PHYSICAL_REGION,
                                 Entry);

        if (Next->Start > Region->Start) {

            break;
        }

        Entry = Entry->Flink;
    }

    BlRtlInsertTailList(Entry, &Region->Entry);

    BlMmCompactPhysicalRegionList();

    return;
}

VOID
BlMmCreatePhysicalRegion(
    UINT64 Start,
    UINT64 Size,
    UINT32 Type
    )

//++
//
//  Routine Description:
//
//    This function creates a physical region descriptor.
//
//  Arguments:
//
//    Start   - Supplies the start address of the region.
//
//    Size    - Supplies the size of the region.
//
//    Type    - Supplies the type of the region.
//
//--

{
    PLIST_ENTRY Entry;
    PLIST_ENTRY Head;
    UINT64 Limit;
    PBL_MM_PHYSICAL_REGION Region;

    BLASSERT((Start % PAGE_SIZE) == 0);
    BLASSERT(Size > 0);
    BLASSERT((Size % PAGE_SIZE) == 0);
    BLASSERT(Type >= BL_MM_PHYSICAL_REGION_MIN_TYPE);
    BLASSERT(Type <= BL_MM_PHYSICAL_REGION_MAX_TYPE);

    Limit = Start + Size;

    BLASSERT(Limit > Start);

    Head = &BlMmPhysicalRegionList;
    Entry = Head->Flink;

    while (Entry != Head) {

        Region = CONTAINING_RECORD(Entry,
                                   BL_MM_PHYSICAL_REGION,
                                   Entry);

        if ((Start < Region->Limit) && (Limit > Region->Start)) {

            BlRtlPrintf("MM: Physical region collision!\n");
            BlRtlHalt();
        }

        Entry = Entry->Flink;
    }

    Entry = Head->Flink;

    while (Entry != Head) {

        Region = CONTAINING_RECORD(Entry,
                                   BL_MM_PHYSICAL_REGION,
                                   Entry);

        if (Start < Region->Start) {

            break;
        }

        Entry = Entry->Flink;
    }

    BLASSERT(BlRtlIsListEmpty(&BlMmPhysicalRegionLookaside.FreeList) == FALSE);

    Region = CONTAINING_RECORD(BlRtlRemoveHeadList(&BlMmPhysicalRegionLookaside.FreeList),
                               BL_MM_PHYSICAL_REGION,
                               Entry);

    Region->Start = Start;
    Region->Size = Size;
    Region->Limit = Limit;
    Region->Type = Type;

    BlMmInsertPhysicalRegion(Region);

    return;
}

UINT64
BlMmAllocatePhysicalRegion(
    UINT32 Size,
    UINT32 Type
    )

//++
//
//  Routine Description:
//
//    This function allocates a physical region from the lowest available and
//    sufficient free region.
//
//  Arguments:
//
//    Size    - Supplies the size of the region to allocate.
//
//    Type    - Supplies the type of the region to allocate.
//
//  Return Value:
//
//    The physical address of the allocated region.
//
//--

{
    PLIST_ENTRY Entry;
    PBL_MM_PHYSICAL_REGION FreeRegion;
    PLIST_ENTRY Head;
    PBL_MM_PHYSICAL_REGION Region;

    BLASSERT(Size > 0);
    BLASSERT(Type != BL_MM_PHYSICAL_REGION_FREE);

    SATISFY_OVERZEALOUS_COMPILER(Region = NULL);

    Size = ROUND_UP_TO_PAGES(Size);

    Head = &BlMmPhysicalRegionList;
    Entry = Head->Blink;

    while (Entry != Head) {

        Region = CONTAINING_RECORD(Entry,
                                   BL_MM_PHYSICAL_REGION,
                                   Entry);

        if ((Region->Type == BL_MM_PHYSICAL_REGION_FREE) &&
            (Region->Size >= Size) &&
            (Region->Limit < 0x100000000UI64)) {

            break;
        }

        Entry = Entry->Blink;
    }

    if (Entry == Head) {

        BlRtlPrintf("MM: Unable to allocate %x bytes!\n", Size);
        BlRtlHalt();
    }

    if (Region->Size == Size) {

        Region->Type = Type;
        return Region->Start;
    }

    FreeRegion = Region;

    BLASSERT(BlRtlIsListEmpty(&BlMmPhysicalRegionLookaside.FreeList) == FALSE);

    Region = CONTAINING_RECORD(BlRtlRemoveHeadList(&BlMmPhysicalRegionLookaside.FreeList),
                               BL_MM_PHYSICAL_REGION,
                               Entry);

    Region->Start = FreeRegion->Limit - Size;
    FreeRegion->Limit -= Size;
    FreeRegion->Size -= Size;

    Region->Size = Size;
    Region->Limit = Region->Start + Region->Size;
    Region->Type = Type;

    BlRtlZeroMemory((PVOID) (ULONG_PTR) Region->Start, (ULONG_PTR) (UINT32) Region->Size);

    BlMmInsertPhysicalRegion(Region);

    return Region->Start;
}

BOOLEAN
BlMmAllocateSpecificPhysicalRegion(
    UINT64 Base,
    UINT64 Size,
    UINT32 Type
    )

//++
//
//  Routine Description:
//
//    This function allocates a specific physical region.
//
//  Arguments:
//
//    Base    - Supplies the base physical address of the region to allocate.
//
//    Size    - Supplies the size of the region to allocate.
//
//    Type    - Supplies the type of the region to allocate.
//
//  Return Value:
//
//    TRUE, if allocation was successful.
//    FALSE, otherwise.
//
//--

{
    UINT64 End;
    PLIST_ENTRY Entry;
    PLIST_ENTRY Head;
    PBL_MM_PHYSICAL_REGION NextRegion;
    PBL_MM_PHYSICAL_REGION PreviousRegion;
    PBL_MM_PHYSICAL_REGION Region;
    UINT64 Start;

    BLASSERT((Base % PAGE_SIZE) == 0);

    BLASSERT(Size > 0);

    BLASSERT((Size % PAGE_SIZE) == 0);

    BLASSERT(Type != BL_MM_PHYSICAL_REGION_FREE);

    SATISFY_OVERZEALOUS_COMPILER(Region = NULL);

    Start = Base;
    End = Start + Size;

    Head = &BlMmPhysicalRegionList;

    for (Entry = Head->Flink; Entry != Head; Entry = Entry->Flink) {

        Region = CONTAINING_RECORD(Entry,
                                   BL_MM_PHYSICAL_REGION,
                                   Entry);

        if ((Start >= Region->Start) && (End <= Region->Limit)) {

            break;
        }
    }

    if (Entry == Head) {

        return FALSE;
    }

    if (Region->Type != BL_MM_PHYSICAL_REGION_FREE) {

        return FALSE;
    }

    PreviousRegion = NULL;
    NextRegion = NULL;

    if (Region->Start < Start) {

        BLASSERT(BlRtlIsListEmpty(&BlMmPhysicalRegionLookaside.FreeList) == FALSE);

        PreviousRegion = CONTAINING_RECORD(BlRtlRemoveHeadList(&BlMmPhysicalRegionLookaside.FreeList),
                                           BL_MM_PHYSICAL_REGION,
                                           Entry);

        PreviousRegion->Start = Region->Start;
        PreviousRegion->Size = Start - Region->Start;
        PreviousRegion->Limit = Start;
        PreviousRegion->Type = BL_MM_PHYSICAL_REGION_FREE;
    }

    if (Region->Limit > End) {

        BLASSERT(BlRtlIsListEmpty(&BlMmPhysicalRegionLookaside.FreeList) == FALSE);

        NextRegion = CONTAINING_RECORD(BlRtlRemoveHeadList(&BlMmPhysicalRegionLookaside.FreeList),
                                       BL_MM_PHYSICAL_REGION,
                                       Entry);

        NextRegion->Start = End;
        NextRegion->Size = Region->Limit - End;
        NextRegion->Limit = Region->Limit;
        NextRegion->Type = BL_MM_PHYSICAL_REGION_FREE;
    }

    Region->Start = Start;
    Region->Size = Size;
    Region->Limit = End;
    Region->Type = Type;

    if (PreviousRegion != NULL) {

        BlMmInsertPhysicalRegion(PreviousRegion);
    }

    if (NextRegion != NULL) {

        BlMmInsertPhysicalRegion(NextRegion);
    }

    return TRUE;
}

BOOLEAN
BlMmFindFreePhysicalRegion(
    PUINT64 Base,
    PUINT64 Size
    )

//++
//
//  Routine Description:
//
//    This function finds a free physical region.
//
//  Arguments:
//
//    Base    - Receives the base address of the free region.
//
//    Size    - Receives the size of the free region.
//
//  Return Value:
//
//    TRUE, if a free region was found.
//    FALSE, otherwise.
//
//--

{
    PLIST_ENTRY Entry;
    PLIST_ENTRY Head;
    PBL_MM_PHYSICAL_REGION Region;

    Head = &BlMmPhysicalRegionList;

    for (Entry = Head->Flink; Entry != Head; Entry = Entry->Flink) {

        Region = CONTAINING_RECORD(Entry,
                                   BL_MM_PHYSICAL_REGION,
                                   Entry);

        if (Region->Type == BL_MM_PHYSICAL_REGION_FREE) {

            *Base = Region->Start;
            *Size = Region->Size;
            return TRUE;
        }
    }

    return FALSE;
}

BOOLEAN
BlMmGetNextPhysicalRegion(
    PVOID *Handle,
    PUINT64 Base,
    PUINT64 Size,
    PUINT32 Type
    )

//++
//
//  Routine Description:
//
//    This function is used to enumerate physical regions.
//
//  Arguments:
//
//    Handle  - Supplies a pointer to the last handle (or NULL to start
//              enumeration) on entry.
//              Receives the next handle (if any) on exit.
//
//    Base    - Receives the base address of the next region.
//
//    Size    - Receives the size of the next region.
//
//    Type    - Receives the type of the next region.
//
//  Return Value:
//
//    TRUE, if there is a next region.
//    FALSE, otherwise.
//
//--

{
    PLIST_ENTRY Entry;
    PLIST_ENTRY Head;
    PBL_MM_PHYSICAL_REGION Region;

    Head = &BlMmPhysicalRegionList;

    if (*Handle == NULL) {

        Entry = Head;

    } else {

        Entry = (PLIST_ENTRY) *Handle;
    }

    Entry = Entry->Flink;

    if (Entry == Head) {

        return FALSE;
    }

    Region = CONTAINING_RECORD(Entry,
                               BL_MM_PHYSICAL_REGION,
                               Entry);

    *Handle = &Region->Entry;
    *Base = Region->Start;
    *Size = Region->Size;
    *Type = Region->Type;

    return TRUE;
}

PCHAR
BlMmPhysicalRegionTypeString(
    UINT32 Type
    )

//++
//
//  Routine Description:
//
//    This function returns the specified physical region type string.
//
//  Arguments:
//
//    Type    - Supplies the physical region type.
//
//  Return Value:
//
//    String representation for the specified type.
//
//--

{

#define CASE(X) case BL_MM_PHYSICAL_REGION_##X: return #X;

    switch (Type) {

        CASE(FREE)
        CASE(BIOS)
        CASE(BOOT_LOADER)
        CASE(SMAP_RESERVED)
        CASE(DISTRO)
        CASE(KERNEL_IMAGE)
        CASE(NATIVE_PLATFORM)
        CASE(NATIVE_PROCESSOR)
        CASE(LOG_RECORD)
        CASE(LOG_TEXT)
        CASE(KERNEL_STACK)
        CASE(CONTEXT)
        CASE(TASK)
        CASE(SINGULARITY)
        CASE(BOOT_STACK)
        CASE(SINGULARITY_SMAP)
    }

#undef CASE

    BLASSERT(FALSE);
    return NULL;
}

VOID
BlMmDumpPhysicalRegionList(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function dumps the list of physical regions.
//
//--

{
    PLIST_ENTRY Entry;
    PLIST_ENTRY Head;
    PBL_MM_PHYSICAL_REGION Region;

    BlRtlPrintf("MM: Physical Region:\n");

    Head = &BlMmPhysicalRegionList;

    for (Entry = Head->Flink; Entry != Head; Entry = Entry->Flink) {

        Region = CONTAINING_RECORD(Entry, BL_MM_PHYSICAL_REGION, Entry);

        BlRtlPrintf("MM:   %016I64x...%016I64x %s\n",
                    Region->Start,
                    Region->Limit,
                    BlMmPhysicalRegionTypeString(Region->Type));
    }

    BlRtlPrintf("\n");

    return;
}

//
// AIFIX: Switch from identity mapping to dynamic mapping.
//

VOID
BlMmInitializePageTables(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function initializes boot loader page tables that identity map the first 4GB of memory.
//
//--

{
    UINT64 Index;
    UINT64 *Pde;
    UINT64 PdtBase;
    UINT64 *Pdpe;
    UINT64 PdptBase;

#if defined(BOOT_X64)

    UINT64 *Pml4e;
    UINT64 Pml4tBase;

#endif

    UINT64 *Pte;
    UINT64 PtBase;

#if defined(BOOT_X64)

    Pml4tBase = (UINT64) (ULONG_PTR) BlMmPml4Table;

#endif

    PdptBase = (UINT64) (ULONG_PTR) BlMmPdpTable;
    PdtBase = (UINT64) (ULONG_PTR) BlMmPdTable;
    PtBase = (UINT64) (ULONG_PTR) BlMmPgTable;

#if defined(BOOT_X64)

    Pml4e = (UINT64 *) (PVOID) Pml4tBase;

#endif

    Pdpe = (UINT64 *) (PVOID) (ULONG_PTR) PdptBase;
    Pde = (UINT64 *) (PVOID) (ULONG_PTR) PdtBase;
    Pte = (UINT64 *) (PVOID) (ULONG_PTR) PtBase;

#if defined(BOOT_X64)

    Pml4e[0] = PdptBase | PAGE_PRESENT | PAGE_WRITEABLE | PAGE_ACCESSED;

#endif

    for (Index = 0; Index < 4; Index += 1) {

        Pdpe[Index] = (PdtBase + (Index * PAGE_SIZE)) | PAGE_PRESENT;

#if defined(BOOT_X64)

        Pdpe[Index] |= PAGE_WRITEABLE | PAGE_ACCESSED;

#endif

    }

    Pde[0] = PtBase | PAGE_PRESENT | PAGE_WRITEABLE | PAGE_ACCESSED;

    for (Index = 1; Index < 512; Index += 1) {

        Pte[Index] = (Index << 12) | PAGE_PRESENT | PAGE_WRITEABLE | PAGE_ACCESSED;
    }

    for (Index = 1; Index < 2048; Index += 1) {

        Pde[Index] = (Index << 21) | PAGE_PRESENT | PAGE_WRITEABLE | PAGE_ACCESSED | PAGE_2MB;
    }

#if defined(BOOT_X86)

    BlMmBootCr3 = (ULONG_PTR) PdptBase;

#elif defined(BOOT_X64)

    BlMmBootCr3 = Pml4tBase;

#endif

    BlMmSetCr3(BlMmBootCr3);

    BlGetBeb()->LegacyReturnCr3 = (UINT32) BlMmBootCr3;

#if MM_VERBOSE

    BlRtlPrintf("MM: 4GB identity map [CR3=%p]\n", BlMmBootCr3);

#endif

    return;
}

VOID
BlMmMapVirtualPage(
    PVOID VirtualAddress,
    PVOID PhysicalAddress,
    BOOLEAN Writeable,
    BOOLEAN Cacheable,
    BOOLEAN WriteThrough
    )

//++
//
//  Routine Description:
//
//    This function maps the specified virtual page.
//
//  Arguments:
//
//    VirtualAddress  - Supplies the virtual address to map.
//
//    PhysicalAddress - Supplies the physical address to map to.
//
//    Writeable       - Supplies whether the page is writeable.
//
//    Cacheable       - Supplies whether the page is cacheable.
//
//    WriteThrough    - Supplies whether the page is write-through.
//
//--

{
    UINT64 Entry;
    UINT32 Index;
    UINT64 LargePageAddress;
    PUINT64 PdBase;
    UINT32 PdIndex;
    PUINT64 PdpBase;
    UINT32 PdpIndex;
    UINT64 PhysicalPageNumber;
    PUINT64 PtBase;
    UINT32 PtIndex;
    ULONG_PTR VirtualPageNumber;

    BLASSERT((((ULONG_PTR) VirtualAddress) & 0xFFF) == 0);

    BLASSERT((((ULONG_PTR) PhysicalAddress) & 0xFFF) == 0);

#if defined(BOOT_X64)

    BLASSERT((ULONG_PTR) VirtualAddress < 0x100000000UI64);

#endif

    //
    // Compute virtual page number, page directory pointer, page directory, and page table indices.
    //

    VirtualPageNumber = ((ULONG_PTR) VirtualAddress) / PAGE_SIZE;

    PdpIndex = (UINT32) ((VirtualPageNumber >> 18) & 0x1FF);
    PdIndex = (UINT32) ((VirtualPageNumber >> 9) & 0x1FF);
    PtIndex = (UINT32) (VirtualPageNumber & 0x1FF);

    //
    // Look up page directory base address.
    //

    PdpBase = &BlMmPdpTable[0].Entry[0];

    PdBase = (PUINT64) (ULONG_PTR) (PdpBase[PdpIndex] & (~(0xFFFUI64)));

    //
    // If the specified page is currently being mapped with large pages, then split it into 4K mappings.
    //

    if ((PdBase[PdIndex] & PAGE_2MB) != 0) {

        PtBase = (PUINT64) (ULONG_PTR) BlMmAllocatePhysicalRegion(PAGE_SIZE, BL_MM_PHYSICAL_REGION_BOOT_LOADER);

        LargePageAddress = (PdBase[PdIndex] & (~(0xFFFUI64)));

        BLASSERT(((LargePageAddress >> 12) & 0x1FF) == 0);

        //
        // Create page table entries to map the region in 4K pages.
        //

        for (Index = 0; Index < 512; Index += 1) {

            PtBase[Index] = (LargePageAddress + (Index * PAGE_SIZE)) | PAGE_PRESENT | PAGE_WRITEABLE | PAGE_ACCESSED;
        }

        //
        // Update page directory entry.
        //

        PdBase[PdIndex] = ((UINT64) (ULONG_PTR) PtBase) | PAGE_PRESENT | PAGE_WRITEABLE | PAGE_ACCESSED;

        //
        // Flush TLB.
        //

        BlMmSetCr3(BlMmBootCr3);
    }

    //
    // Update page mapping.
    //

    PtBase = (PUINT64) (ULONG_PTR) (PdBase[PdIndex] & (~(0xFFFUI64)));

    PhysicalPageNumber = ((ULONG_PTR) PhysicalAddress) >> 12;

    Entry = (PhysicalPageNumber << 12) | PAGE_PRESENT;

    if (Writeable != FALSE) {

        Entry |= PAGE_WRITEABLE;
    }

    if (Cacheable == FALSE) {

        Entry |= PAGE_CACHEDISABLE;

    } else if (WriteThrough != FALSE) {

        Entry |= PAGE_WRITETHROUGH;
    }

    PtBase[PtIndex] = Entry;

    //
    // Flush TLB.
    //

    BlMmSetCr3(BlMmBootCr3);

    return;
}

VOID
BlMmMapVirtualRange(
    PVOID VirtualAddress,
    PVOID PhysicalAddress,
    ULONG_PTR Size,
    BOOLEAN Writeable,
    BOOLEAN Cacheable,
    BOOLEAN WriteThrough
    )

//++
//
//  Routine Description:
//
//    This function maps the specified virtual range.
//
//  Arguments:
//
//    VirtualAddress  - Supplies the virtual address to map.
//
//    PhysicalAddress - Supplies the physical address to map to.
//
//    Size            - Supplies the size of the mapping.
//
//    Writeable       - Supplies whether the page is writeable.
//
//    Cacheable       - Supplies whether the page is cacheable.
//
//    WriteThrough    - Supplies whether the page is write-through.
//
//--

{
    ULONG_PTR PhysicalNext;
    ULONG_PTR VirtualLimit;
    ULONG_PTR VirtualNext;

    VirtualNext = (ULONG_PTR) VirtualAddress;
    VirtualLimit = VirtualNext + Size;

    VirtualNext &= (~((ULONG_PTR) 0xFFF));
    VirtualLimit = ROUND_UP_TO_PAGES(VirtualLimit);

    PhysicalNext = (ULONG_PTR) PhysicalAddress;
    PhysicalNext &= (~((ULONG_PTR) 0xFFF));

    while (VirtualNext < VirtualLimit) {

        BlMmMapVirtualPage((PVOID) VirtualNext,
                           (PVOID) PhysicalNext,
                           Writeable,
                           Cacheable,
                           WriteThrough);

        VirtualNext += PAGE_SIZE;
        PhysicalNext += PAGE_SIZE;
    }

    return;
}

VOID
BlMmInitializeCodeSegment(
    PCODE_SEGMENT CodeSegment
    )

//++
//
//  Routine Description:
//
//    This function initializes the specified code segment.
//
//  Arguments:
//
//    CodeSegment - Supplies a pointer to the code segment to initialize.
//
//--

{
    BlRtlZeroMemory(CodeSegment, sizeof(CODE_SEGMENT));

    CodeSegment->Accessed = 1;
    CodeSegment->Readable = 1;
    CodeSegment->Code = 1;
    CodeSegment->S = 1;
    CodeSegment->Present = 1;
    CodeSegment->Long = 1;

    return;
}

VOID
BlMmInitializeDataSegment(
    PDATA_SEGMENT DataSegment,
    UINT32 Base,
    UINT32 Limit
    )

//++
//
//  Routine Description:
//
//    This function initializes the specified data segment.
//
//  Arguments:
//
//    DataSegment - Supplies a pointer to the data segment to initialize.
//
//    Base        - Supplies the base address of the data segment.
//
//    Limit       - Supplies the limit of the data segment.
//
//--

{
    BlRtlZeroMemory(DataSegment, sizeof(DATA_SEGMENT));

    DataSegment->Accessed = 1;
    DataSegment->Writable = 1;
    DataSegment->S = 1;
    DataSegment->Present = 1;
    DataSegment->Big = 1;

    DataSegment->Base_23_0 = Base & 0xFFFFFF;
    DataSegment->Base_31_24 = Base >> 24;

    if (Limit <= 0xFFFFF) {

        DataSegment->Limit_15_0 = Limit & 0xFFFF;
        DataSegment->Limit_19_16 = (Limit >> 16) & 0xF;

    } else {

        DataSegment->Granularity = 1;
        DataSegment->Limit_15_0 = (Limit >> 12) & 0xFFFF;
        DataSegment->Limit_19_16 = (Limit >> 28) & 0xF;
    }

    return;
}

VOID
BlMmInitializeSystemSegment(
    PSYSTEM_SEGMENT SystemSegment,
    UINT32 Type,
    ULONG_PTR Base,
    UINT32 Limit
    )

//++
//
//  Routine Description:
//
//    This function initializes the specified system segment.
//
//  Arguments:
//
//    SystemSegment   - Supplies a pointer to the system segment to initialize.
//
//    Type            - Supplies the type of the system segment.
//
//    Base            - Supplies the base address of the system segment.
//
//    Limit           - Supplies the limit of the system segment.
//
//--

{
    BlRtlZeroMemory(SystemSegment, sizeof(SYSTEM_SEGMENT));

    SystemSegment->Type = (Type & 0xF);
    SystemSegment->Present = 1;

    SystemSegment->Base_23_0 = Base & 0xFFFFFF;
    SystemSegment->Base_31_24 = (Base >> 24) & 0xFF;

#if defined(BOOT_X64)

    SystemSegment->Base_63_32 = Base >> 32;

#endif

    if (Limit <= 0xFFFFF) {

        SystemSegment->Limit_15_0 = Limit & 0xFFFF;
        SystemSegment->Limit_19_16 = (Limit >> 16) & 0xF;

    } else {

        SystemSegment->Granularity = 1;
        SystemSegment->Limit_15_0 = (Limit >> 12) & 0xFFFF;
        SystemSegment->Limit_19_16 = (Limit >> 28) & 0xF;
    }

    return;
}

#if !defined(BOOT_PXE)
VOID
BlMmEnableA20Gate(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function enables A20 gate.
//
//--

{
    BL_KEYBOARD_WRITE_OUTPUT_PORT(BL_KEYBOARD_A20_ENABLE);

    BL_KEYBOARD_WRITE_COMMAND(BL_KEYBOARD_COMMAND_PULSE_OUTPUT_PORT);

    return;
}
#endif

PVOID
BlMmGetExtendedBiosDataArea(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function gets the address of the extended BIOS data area.
//
//  Return Value:
//
//    Address of the extended BIOS data area.
//
//--

{
    UINT16 Segment;

    Segment = *((PUINT16) (ULONG_PTR) 0x40E);

    return (PVOID) (((ULONG_PTR) Segment) << 4);
}

VOID
BlMmInitializeSystem(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function initializes boot loader memory management.
//
//--

{
    UINT64 Delta;
    UINT32 Index;
    PBL_MM_PHYSICAL_REGION PhysicalRegion;
    PBL_SMAP_ENTRY SmapEntry;

#if !defined(BOOT_PXE)
    //
    // Enable A20 gate.
    //

    BlMmEnableA20Gate();
#endif

    //
    // Get extended BIOS data area.
    //

    BlMmExtendedBiosDataArea = BlMmGetExtendedBiosDataArea();

    //
    // Get legacy CR3 value;
    //

    BlMmLegacyCr3 = BlMmGetCr3();

    //
    // Get initial GDTR.
    //

    BlMmGetGdtr(&BlMmInitialGdtr);

    //
    // Initialize memory map.
    //

    BlSmapInitialize();

    //
    // Create physical region lookaside.
    //

    BlRtlInitializeListHead(&BlMmPhysicalRegionList);

    BlRtlInitializeListHead(&BlMmPhysicalRegionLookaside.FreeList);

    for (Index = 0; Index < (sizeof(BlMmPhysicalRegionLookaside.StaticArray) / sizeof(BlMmPhysicalRegionLookaside.StaticArray[0])); Index += 1) {

        BlRtlInsertTailList(&BlMmPhysicalRegionLookaside.FreeList, &BlMmPhysicalRegionLookaside.StaticArray[Index].Entry);
    }

    //
    // Initialize page tables.
    //

    BlMmInitializePageTables();

    //
    // Create reserved BIOS region.
    //

    BlMmCreatePhysicalRegion(0,
                             BL_MM_BIOS_SIZE,
                             BL_MM_PHYSICAL_REGION_BIOS);

    //
    // Create free regions based on SMAP.
    //

    for (Index = 0; Index < BlSystemMemoryMap.EntryCount; Index += 1) {

        SmapEntry = &BlSystemMemoryMap.Entry[Index];

        //
        // Don't use any memory below 1MB (BIOS area) and above 2GB (Singularity uses MSB for marking and such).
        //

        if ((SmapEntry->Type == BL_SMAP_AVAILABLE) &&
            (SmapEntry->Base >= BL_MM_BIOS_SIZE) &&
            (SmapEntry->Base < 0x80000000UI64)
            ) {

            if ((SmapEntry->Base % PAGE_SIZE) != 0) {

                Delta = PAGE_SIZE - (SmapEntry->Base % PAGE_SIZE);
                SmapEntry->Base += Delta;
                SmapEntry->Size -= Delta;
            }

            SmapEntry->Size &= (~(0xFFFUI64));

            if ((SmapEntry->Base + SmapEntry->Size) > 0x80000000UI64) {

                SmapEntry->Size = 0x80000000UI64 - SmapEntry->Base;
            }

            if (SmapEntry->Size > 0) {

                BlMmCreatePhysicalRegion(SmapEntry->Base,
                                         SmapEntry->Size,
                                         BL_MM_PHYSICAL_REGION_FREE);
            }
        }
    }

    //
    // Initialize pool.
    //

    BlPoolInitialize();

    //
    // Add more entries to the physical region lookaside.
    //

    for (Index = 0; Index < 256; Index += 1) {

        PhysicalRegion = (PBL_MM_PHYSICAL_REGION)
            BlPoolAllocateBlock(sizeof(BL_MM_PHYSICAL_REGION));

        BlRtlInsertTailList(&BlMmPhysicalRegionLookaside.FreeList, &PhysicalRegion->Entry);
    }

    return;
}
