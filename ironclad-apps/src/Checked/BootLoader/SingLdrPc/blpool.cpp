//++
//
//  Copyright (c) Microsoft Corporation
//
//  Module Name:
//
//    blpool.cpp
//
//  Abstract:
//
//    This module implements pool support for the boot loader environment.
//
//--

#include "bl.h"

#define BL_POOL_FREE                    1
#define BL_POOL_BUSY                    2

#define BL_POOL_GRANULARITY             256

C_ASSERT((BL_POOL_GRANULARITY & (BL_POOL_GRANULARITY - 1)) == 0);

#define BL_POOL_ROUND_UP(X)             ROUND_UP_TO_POWER2(X, BL_POOL_GRANULARITY)

#define BL_POOL_SEGMENT_SIZE            (8 * PAGE_SIZE)

C_ASSERT((BL_POOL_SEGMENT_SIZE & (BL_POOL_SEGMENT_SIZE - 1)) == 0);

#define BL_POOL_SEGMENT_ROUND_UP(X)     ((X + (BL_POOL_SEGMENT_SIZE - 1)) & (~(BL_POOL_SEGMENT_SIZE - 1)))

#if defined(BOOT_X86)

#define BL_POOL_BLOCK_MAGIC1            0x01020304
#define BL_POOL_BLOCK_MAGIC2            0x05060708

#elif defined(BOOT_X64)

#define BL_POOL_BLOCK_MAGIC1            0x0102030405060708UI64
#define BL_POOL_BLOCK_MAGIC2            0x090A0B0C0D0E0F10UI64

#endif

typedef struct _BL_POOL_BLOCK {
    ULONG_PTR Magic1;
    LIST_ENTRY Entry;
    ULONG_PTR Size;
    ULONG_PTR State;
    PVOID Allocator;
    ULONG_PTR Pad;
    ULONG_PTR Magic2;
} BL_POOL_BLOCK, *PBL_POOL_BLOCK;

C_ASSERT((sizeof(BL_POOL_BLOCK) % 16) == 0);

#if defined(BOOT_X86)

#define BL_POOL_SEGMENT_MAGIC1          0xFFFEFDFC
#define BL_POOL_SEGMENT_MAGIC2          0xFBFAF9F8

#elif defined(BOOT_X64)

#define BL_POOL_SEGMENT_MAGIC1          0xFFFEFDFCFBFAF9F8UI64
#define BL_POOL_SEGMENT_MAGIC2          0xF7F6F5F4F3F2F1F0UI64

#endif

typedef struct _BL_POOL_SEGMENT {
    ULONG_PTR Magic1;
    LIST_ENTRY Entry;
    ULONG_PTR Size;
    ULONG_PTR Start;
    ULONG_PTR Limit;
    LIST_ENTRY BlockList;
    ULONG_PTR Magic2;
} BL_POOL_SEGMENT, *PBL_POOL_SEGMENT;

LIST_ENTRY BlPoolSegmentList;

VOID
BlPoolInitialize(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function initializes boot loader pool.
//
//--

{
    BlRtlInitializeListHead(&BlPoolSegmentList);

#if POOL_VERBOSE

    BlRtlPrintf("POOL: Segment list @ %p.\n", &BlPoolSegmentList);

#endif

    return;
}

#if DEBUG

VOID
BlPoolDump(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function dumps boot loader pool.
//
//--

{
    PBL_POOL_BLOCK Block;
    PLIST_ENTRY BlockEntry;
    PLIST_ENTRY BlockHead;
    PBL_POOL_SEGMENT Segment;
    PLIST_ENTRY SegmentEntry;
    PLIST_ENTRY SegmentHead;

    BlRtlPrintf("POOL: BlDumpPool: <StartOfDump>\n");

    SegmentHead = &BlPoolSegmentList;

    for (SegmentEntry = SegmentHead->Flink; SegmentEntry != SegmentHead; SegmentEntry = SegmentEntry->Flink) {

        Segment = CONTAINING_RECORD(SegmentEntry,
                                    BL_POOL_SEGMENT,
                                    Entry);

        BlRtlPrintf("POOL: BlDumpPool: Segment @ %p\n", Segment);

        BlockHead = &Segment->BlockList;

        for (BlockEntry = BlockHead->Flink; BlockEntry != BlockHead; BlockEntry = BlockEntry->Flink) {

            Block = CONTAINING_RECORD(BlockEntry,
                                      BL_POOL_BLOCK,
                                      Entry);

            BlRtlPrintf("POOL: BlDumpPool:   Entry %p ... %p [%u]\n",
                        Block,
                        (ULONG_PTR) Block + Block->Size,
                        Block->State);
        }
    }

    BlRtlPrintf("pool: BlDumpPool: <EndOfDump>\n");

    return;
}

#endif

VOID
BlPoolVerify(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function verifies boot loader pool.
//
//--

{
    PBL_POOL_BLOCK Block;
    PLIST_ENTRY BlockEntry;
    PLIST_ENTRY BlockHead;
    PBL_POOL_BLOCK NextBlock;
    PBL_POOL_SEGMENT Segment;
    PLIST_ENTRY SegmentEntry;
    PLIST_ENTRY SegmentHead;

    SegmentHead = &BlPoolSegmentList;

    BLASSERT(SegmentHead->Flink->Blink == SegmentHead);
    BLASSERT(SegmentHead->Blink->Flink == SegmentHead);

    for (SegmentEntry = SegmentHead->Flink; SegmentEntry != SegmentHead; SegmentEntry = SegmentEntry->Flink) {

        Segment = CONTAINING_RECORD(SegmentEntry,
                                    BL_POOL_SEGMENT,
                                    Entry);

        BLASSERT_PTR(Segment->Magic1 == BL_POOL_SEGMENT_MAGIC1, Segment);
        BLASSERT_PTR(Segment->Magic2 == BL_POOL_SEGMENT_MAGIC2, Segment);

        BLASSERT_PTR(Segment->Entry.Flink->Blink == &Segment->Entry, Segment);
        BLASSERT_PTR(Segment->Entry.Blink->Flink == &Segment->Entry, Segment);


        BlockHead = &Segment->BlockList;

        for (BlockEntry = BlockHead->Flink; BlockEntry != BlockHead; BlockEntry = BlockEntry->Flink) {

            Block = CONTAINING_RECORD(BlockEntry,
                                      BL_POOL_BLOCK,
                                      Entry);

            BLASSERT_PTR(Block->Magic1 == BL_POOL_BLOCK_MAGIC1, Block);
            BLASSERT_PTR(Block->Magic2 == BL_POOL_BLOCK_MAGIC2, Block);

            BLASSERT_PTR((Block->State == BL_POOL_FREE) || ((Block->State == BL_POOL_BUSY)), Block);

            BLASSERT_PTR(((ULONG_PTR) Block % BL_POOL_GRANULARITY) == 0, Block);

            BLASSERT_PTR(Block->Size > sizeof(BL_POOL_BLOCK), Block);
            BLASSERT_PTR((Block->Size % BL_POOL_GRANULARITY) == 0, Block);

            if (Block->Entry.Flink != BlockHead) {

                NextBlock = CONTAINING_RECORD(Block->Entry.Flink,
                                              BL_POOL_BLOCK,
                                              Entry);

                BLASSERT_PTR(((ULONG_PTR) Block + Block->Size) == ((ULONG_PTR) NextBlock), Block);
            }

            BLASSERT_PTR(Block->Entry.Flink->Blink == &Block->Entry, Block);
            BLASSERT_PTR(Block->Entry.Blink->Flink == &Block->Entry, Block);
        }
    }

    return;
}

VOID
BlPoolGrow(
    UINT32 Size
    )

//++
//
//  Routine Description:
//
//    This function grows the pool.
//
//  Arguments:
//
//    Size    - Supplies the growth size.
//
//--

{
    PBL_POOL_BLOCK Block;
    PBL_POOL_SEGMENT Segment;

    BlPoolVerify();

    BLASSERT(Size > 0);

    Size = ROUND_UP_TO_PAGES(Size);

    Segment = (PBL_POOL_SEGMENT) (ULONG_PTR) BlMmAllocatePhysicalRegion(Size, BL_MM_PHYSICAL_REGION_BOOT_LOADER);

    BlRtlZeroMemory(Segment, Size);

    Segment->Magic1 = BL_POOL_SEGMENT_MAGIC1;
    Segment->Magic2 = BL_POOL_SEGMENT_MAGIC2;
    Segment->Start = (ULONG_PTR) Segment;
    Segment->Size = Size;
    Segment->Limit = Segment->Start + Segment->Size;
    BlRtlInitializeListHead(&Segment->BlockList);

    Block = (PBL_POOL_BLOCK) (BL_POOL_ROUND_UP(((ULONG_PTR) (Segment + 1))));
    Block->Magic1 = BL_POOL_BLOCK_MAGIC1;
    Block->Magic2 = BL_POOL_BLOCK_MAGIC2;
    Block->Size = Segment->Limit - (ULONG_PTR) Block;
    Block->State = BL_POOL_FREE;
    Block->Allocator = NULL;

    BlRtlInsertTailList(&Segment->BlockList, &Block->Entry);

    BlRtlInsertTailList(&BlPoolSegmentList, &Segment->Entry);

    BlPoolVerify();

    return;
}

PVOID
BlPoolAllocateBlock(
    UINT32 Size
    )

//++
//
//  Routine Description:
//
//    This function allocates from the boot loader pool.
//
//  Arguments:
//
//    Size    - Supplies the number of bytes to allocate.
//
//  Return Value:
//
//    A pointer to the allocated buffer.
//
//--

{
    PBL_POOL_BLOCK Block;
    PLIST_ENTRY BlockEntry;
    PLIST_ENTRY BlockHead;
    UINT32 GrowthSize;
    PBL_POOL_BLOCK NewBlock;
    PBL_POOL_SEGMENT Segment;
    PLIST_ENTRY SegmentEntry;
    PLIST_ENTRY SegmentHead;

    BlPoolVerify();

    BLASSERT(Size > 0);

    Size += sizeof(BL_POOL_BLOCK);
    Size = BL_POOL_ROUND_UP(Size);

    SegmentHead = &BlPoolSegmentList;

    for (;;) {

        for (SegmentEntry = SegmentHead->Flink; SegmentEntry != SegmentHead; SegmentEntry = SegmentEntry->Flink) {

            Segment = CONTAINING_RECORD(SegmentEntry,
                                        BL_POOL_SEGMENT,
                                        Entry);

            BlockHead = &Segment->BlockList;

            for (BlockEntry = BlockHead->Flink; BlockEntry != BlockHead; BlockEntry = BlockEntry->Flink) {

                Block = CONTAINING_RECORD(BlockEntry,
                                          BL_POOL_BLOCK,
                                          Entry);

                if ((Block->State == BL_POOL_FREE) && (Block->Size >= Size)) {

                    if (Block->Size > Size) {

                        NewBlock = (PBL_POOL_BLOCK) ((ULONG_PTR) Block + Size);

                        BlRtlZeroMemory(NewBlock, sizeof(BL_POOL_BLOCK));

                        NewBlock->Magic1 = BL_POOL_BLOCK_MAGIC1;
                        NewBlock->Magic2 = BL_POOL_BLOCK_MAGIC2;
                        NewBlock->Size = Block->Size - Size;
                        NewBlock->State = BL_POOL_FREE;
                        NewBlock->Allocator = NULL;

                        BlRtlInsertHeadList(&Block->Entry, &NewBlock->Entry);

                        Block->Size = Size;
                    }

                    Block->State = BL_POOL_BUSY;
                    Block->Allocator = _ReturnAddress();

                    BlRtlZeroMemory(Block + 1, Block->Size - sizeof(BL_POOL_BLOCK));

                    BlPoolVerify();

                    return (Block + 1);
                }
            }
        }

        GrowthSize = BL_POOL_SEGMENT_ROUND_UP(Size);

        BlPoolGrow(GrowthSize);
    }
}

VOID
BlPoolFreeBlock(
    PVOID P
    )

//++
//
//  Routine Description:
//
//    This function frees the specified pool block.
//
//  Arguments:
//
//    P   - Supplies a pointer to the block to free.
//
//--

{
    PBL_POOL_BLOCK Block;

    BlPoolVerify();

    BLASSERT(((ULONG_PTR) P % __alignof(BL_POOL_BLOCK)) == 0);

    Block = ((PBL_POOL_BLOCK) P) - 1;

    BLASSERT(((ULONG_PTR) Block % BL_POOL_GRANULARITY) == 0);

    BLASSERT(Block->State == BL_POOL_BUSY);

    Block->State = BL_POOL_FREE;
    Block->Allocator = NULL;

    //
    // AIFIX: Check for adjacent free blocks and coalesce.
    //

    BlPoolVerify();

    return;
}
