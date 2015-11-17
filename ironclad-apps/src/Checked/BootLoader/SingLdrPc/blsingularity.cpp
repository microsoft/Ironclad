//-++
//-
//-  Copyright (c) Microsoft Corporation
//-
//-  Module Name:
//-
//-    blsingularity.cpp
//-
//-  Abstract:
//-
//-    This module initializes and boots Singularity.
//-
//--


#include "bl.h"
#include "tpm/aik.h"

#define SINGULARITY_DISTRO_INI_PATH     "safeos/boot.ini"
#define SINGULARITY_LOG_RECORD_SIZE     0x20000
#define SINGULARITY_LOG_TEXT_SIZE       0x20000
#define SINGULARITY_KERNEL_STACK_SIZE   0xC0000

//-
//- Define halclass style basic definitions and macros.
//-

typedef ULONG_PTR       PTR_TYPE;

typedef LONG_PTR        SPTR_TYPE;
typedef ULONG_PTR       UPTR_TYPE;

#define OFFSETOF        FIELD_OFFSET

#define STATIC_ASSERT   C_ASSERT

//-
//- Include halclasswin.h for Singularity definitions.
//-

#define SINGULARITY_LOADER      1

#pragma pack(1)
#include "platform.h"
#pragma pack()

C_ASSERT(FIELD_OFFSET(Struct_Microsoft_Singularity_Isal_IX_DescriptorTable_Gdt, rc) == RM_CODE_SELECTOR);
C_ASSERT(FIELD_OFFSET(Struct_Microsoft_Singularity_Isal_IX_DescriptorTable_Gdt, rd) == RM_DATA_SELECTOR);
C_ASSERT(FIELD_OFFSET(Struct_Microsoft_Singularity_Isal_IX_DescriptorTable_Gdt, pc) == PM_CODE_SELECTOR);
C_ASSERT(FIELD_OFFSET(Struct_Microsoft_Singularity_Isal_IX_DescriptorTable_Gdt, pd) == PM_DATA_SELECTOR);
C_ASSERT(FIELD_OFFSET(Struct_Microsoft_Singularity_Isal_IX_DescriptorTable_Gdt, lc) == LM_CODE_SELECTOR);
C_ASSERT(FIELD_OFFSET(Struct_Microsoft_Singularity_Isal_IX_DescriptorTable_Gdt, ld) == LM_DATA_SELECTOR);
C_ASSERT(FIELD_OFFSET(Struct_Microsoft_Singularity_Isal_IX_DescriptorTable_Gdt, pp) == PROCESSOR_SELECTOR);
C_ASSERT(FIELD_OFFSET(Struct_Microsoft_Singularity_Isal_IX_DescriptorTable_Gdt, tss) == TSS_SELECTOR);

Class_Microsoft_Singularity_Hal_Platform *BlPlatform;
Class_Microsoft_Singularity_Hal_Cpu *BlCpuArray;

typedef struct _BL_DISTRO_FILE {
    LIST_ENTRY Entry;
    UINT32 Size;
    CHAR Path[1024];
    PVOID Data;
} BL_DISTRO_FILE, *PBL_DISTRO_FILE;

typedef struct _BL_DISTRO {
    UINT32 NumberOfFiles;
    UINT32 TotalSize;
    LIST_ENTRY FileList;
    PVOID Data;
} BL_DISTRO, PBL_DISTRO;

BL_DISTRO BlDistro;
PBL_DISTRO_FILE BlKernelFile;

PVOID BlKernelBase;
ULONG_PTR BlKernelSize;

UINT32
(*BlKernelEntryPoint)(
    Class_Microsoft_Singularity_Hal_Platform *Platform,
    Class_Microsoft_Singularity_Hal_Cpu *Cpu
    );



PBL_SMAP BlSingularitySmap;
PWCHAR BlCommandLine;
Struct_Microsoft_Singularity_Io_FileImage *BlSingularityFileImageTable;
UINT32 BlSingularityFileImageTableSize;

//
// OHCI 1394 buffer for Singularity KD.
//
// AIFIX: Currently, this buffer needs to be allocated in low memory, because
// Singularity KD does not connect if it is allocated in high memory.
//

__declspec(align(PAGE_SIZE)) UINT8 BlSingularityOhci1394Buffer[3 * PAGE_SIZE];

VOID
BlSingularityLoadDistro(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function loads the distro.
//
//--

{
    UINT32 BytesRead;
    UINT32 CharactersConsumed;
    PBL_DISTRO_FILE DistroFile;
    UINT32 DummySize;
    PLIST_ENTRY Entry;
    UINT32 FilesRead;
    PLIST_ENTRY Head;
    PCHAR NewLine;
    PCHAR Next;
    UINT32 Size;
    PCHAR Temp;
    PVOID BlIniFileData;
    UINT32 BlIniFileSize;

    BlDistro.NumberOfFiles = 0;
    BlRtlInitializeListHead(&BlDistro.FileList);

    //-
    //- Read the distro INI file.
    //-

    if (BlFsGetFileSize(SINGULARITY_DISTRO_INI_PATH, &BlIniFileSize) == FALSE) {

        BlRtlPrintf("BL: Unable to get INI file!\n");
        BlRtlHalt();
    }

    BlIniFileData = BlPoolAllocateBlock(BlIniFileSize + 1);

    if (BlFsReadFile(SINGULARITY_DISTRO_INI_PATH, BlIniFileData, BlIniFileSize) == FALSE) {

        BlRtlPrintf("BL: Unable to read INI file!\n");
        BlRtlHalt();
    }

    //-
    //- Parse INI file and build distro file list.
    //-

    NewLine = (PCHAR) BlIniFileData;

    for (;;) {

        Next = NewLine;
        NewLine = Next + 1;

        while ((*NewLine != 0) && (*NewLine != '\r') && (*NewLine != '\n')) {

            NewLine += 1;
        }

        if (*NewLine == 0) {

            break;
        }

        while ((*NewLine == '\r') || (*NewLine == '\n')) {

            *NewLine = 0;
            NewLine += 1;
        }

        Next = (PCHAR)BlRtlFindSubstring(Next, "Size=");

        if (Next == NULL) {

            continue;
        }

        Next += 5;

        if (BlRtlParsePositiveDecimal(Next,
                                      &Size,
                                      &CharactersConsumed) == FALSE) {

          ParseFailure:
            BlRtlPrintf("BL: Error parsing distro INI file!\n");
            BlRtlHalt();
        }

        Next = (PCHAR)BlRtlFindSubstring(Next, "Path=");

        if (Next == NULL) {

            goto ParseFailure;
        }

        Next += 5;

        if (*Next == 0) {

            goto ParseFailure;
        }

        DistroFile = (PBL_DISTRO_FILE) BlPoolAllocateBlock(sizeof(BL_DISTRO_FILE));

        BLASSERT((NewLine - Next) < sizeof(DistroFile->Path));

        Temp = (PCHAR)Next;

        while (Temp != NewLine) {

            if (*Temp == '\\') {

                *Temp = '/';
            }

            Temp += 1;
        }

        BlRtlCopyMemory(DistroFile->Path, Next, NewLine - Next);

        //-
        //- By convention with DistroBuiderl, the first file with a size of zero is
        //- really the INI file, so we need to set its size.
        //-
        if (Size == 0) {
            Size = BlIniFileSize;
        }

        DistroFile->Size = Size;

        BlDistro.NumberOfFiles += 1;
        BlDistro.TotalSize += Size;

        BlRtlInsertTailList(&BlDistro.FileList, &DistroFile->Entry);
    }

    //-
    //- Read distro files.
    //-

    BlDistro.Data = (PVOID) BlMmAllocatePhysicalRegion(ROUND_UP_TO_PAGES(BlDistro.TotalSize), BL_MM_PHYSICAL_REGION_DISTRO);

#if DISTRO_VERBOSE

    BlKdPrintf("DISTRO: Reading distro (%u files , %u bytes).\n",
               BlDistro.NumberOfFiles,
               BlDistro.TotalSize);

#endif

    FilesRead = 0;
    BytesRead = 0;

    Next = (PCHAR) BlDistro.Data;
    Head = &BlDistro.FileList;

    for (Entry = Head->Flink; Entry != Head; Entry = Entry->Flink) {

        DistroFile = CONTAINING_RECORD(Entry, BL_DISTRO_FILE, Entry);

        DistroFile->Data = Next;

        BLASSERT(DistroFile->Path[0] == '/');

#if DISTRO_VERBOSE

        BlKdPrintf("DISTRO: %s [%u bytes]\n",
                   DistroFile->Path,
                   DistroFile->Size);

#endif

        if (BlFsReadFile(&DistroFile->Path[1], DistroFile->Data, DistroFile->Size) == FALSE) {

            BlRtlPrintf("\n"
                        "BL: Error reading %s!\n",
                        DistroFile->Path);

            BlRtlHalt();
        }

        Next += DistroFile->Size;

        FilesRead += 1;
        BytesRead += DistroFile->Size;

        BlVideoPrintf("\rReading distro files ... %u / %u [%u / %u]",
                      FilesRead,
                      BlDistro.NumberOfFiles,
                      BytesRead,
                      BlDistro.TotalSize);

    }

    BlVideoPrintf("\n");

    //-
    //- If this is a network boot, then signal the PXE server to exit.
    //- This is the only mechanism to notify the server that the boot succeeded.
    //-

    if (BlGetBeb()->BootType == BL_PXE_BOOT) {

        BlFsGetFileSize("end.:", &DummySize);
    }

    //-
    //- Switch distro range to read-only.
    //-

    BlMmMapVirtualRange(BlDistro.Data,
                        BlDistro.Data,
                        BlDistro.TotalSize,
                        FALSE,
                        TRUE,
                        FALSE);

    //-
    //- Build file image table.
    //-

    BlSingularityFileImageTable = (Struct_Microsoft_Singularity_Io_FileImage *) BlPoolAllocateBlock(BlDistro.NumberOfFiles * sizeof(Struct_Microsoft_Singularity_Io_FileImage));

    for (Entry = Head->Flink; Entry != Head; Entry = Entry->Flink) {

        DistroFile = CONTAINING_RECORD(Entry, BL_DISTRO_FILE, Entry);

        BlSingularityFileImageTable[BlSingularityFileImageTableSize].Address = (ULONG_PTR) DistroFile->Data;
        BlSingularityFileImageTable[BlSingularityFileImageTableSize].Size = DistroFile->Size;
        BlSingularityFileImageTableSize += 1;
    }

    return;
}

VOID
BlSingularityLoadKernelImage(
    VOID
    )

//-++
//-
//-  Routine Description:
//-
//-    This function loads the kernel image.
//-
//---

{
    BLASSERT(BlRtlIsListEmpty(&BlDistro.FileList) == FALSE);

    //-
    //- Kernel is the first entry in the distro file list.
    //-

    BlKernelFile = CONTAINING_RECORD(BlDistro.FileList.Flink,
                                     BL_DISTRO_FILE,
                                     Entry);

    //-
    //- Get the virtual range for the kernel image.
    //-

    BlPeGetVirtualRange(BlKernelFile->Data, &BlKernelBase, &BlKernelSize);

    BLASSERT(((UINT64) BlKernelBase % PAGE_SIZE) == 0);

    BLASSERT((BlKernelSize % PAGE_SIZE) == 0);

    //-
    //- Allocate a physical region for the kernel image, since pages are identity mapped at boot.
    //-
    // AIFIX: This needs to be be made dynamic!
    //

    if (BlMmAllocateSpecificPhysicalRegion((UINT64) BlKernelBase,
                                           BlKernelSize,
                                           BL_MM_PHYSICAL_REGION_KERNEL_IMAGE) == FALSE) {

        BlMmDumpPhysicalRegionList();

        BlRtlHalt();
    }

#if SINGULARITY_VERBOSE

    BlRtlPrintf("BL: Loading kernel ... [%p ... %p]\n",
                BlKernelBase,
                (ULONG_PTR) BlKernelBase + BlKernelSize - 1);

#endif

    BlPeLoadImage(BlKernelBase, BlKernelSize, BlKernelFile->Data, (PVOID *) &BlKernelEntryPoint, TRUE);

}


ULONG_PTR
BlSingularityLoadAppImage(
    VOID
    )

//-++
//-
//-  Routine Description:
//-
//-    This function loads the kernel image.
//-
//---

{
    PBL_DISTRO_FILE BlAppFile;

    PVOID BlAppBase;
    ULONG_PTR BlAppSize;
    ULONG_PTR BlAppEntryPoint;


    BLASSERT(BlRtlIsListEmpty(&BlDistro.FileList) == FALSE);

    //-
    //- App is the second entry in the distro file list.
    //-

    BlAppFile = CONTAINING_RECORD(BlDistro.FileList.Flink->Flink,
                                     BL_DISTRO_FILE,
                                     Entry);

    //-
    //- Get the virtual range for the kernel image.
    //-

    BlPeGetVirtualRange(BlAppFile->Data, &BlAppBase, &BlAppSize);

    BLASSERT(((UINT64) BlAppBase % PAGE_SIZE) == 0);

    BLASSERT((BlAppSize % PAGE_SIZE) == 0);

    //-
    //- Allocate a physical region for the app image, since pages are identity mapped at boot.
    //-
    // AIFIX: This needs to be be made dynamic!
    //
    BlRtlPrintf("BL: Loading app... [%p ... %p]\n",
                BlAppBase,
                (ULONG_PTR) BlAppBase + BlAppSize - 1);

    if (BlMmAllocateSpecificPhysicalRegion((UINT64) BlAppBase,
                                           BlAppSize,
                                           BL_MM_PHYSICAL_REGION_SINGULARITY) == FALSE) {
      
      BlRtlPrintf("BL: Loading app... failed\n"); 
        BlMmDumpPhysicalRegionList();

        BlRtlHalt();
    }

#if SINGULARITY_VERBOSE

    BlRtlPrintf("BL: Loading app... [%p ... %p]\n",
                BlAppBase,
                (ULONG_PTR) BlAppBase + BlAppSize - 1);

#endif

    BlPeLoadImage(BlAppBase, BlAppSize, BlAppFile->Data, (PVOID *) &BlAppEntryPoint, FALSE);

    return BlAppEntryPoint;
}



//
// AIFIX: Fix task page definition.
//

#if defined(BOOT_X86)

typedef Struct_Microsoft_Singularity_Isal_IX_TSS BL_TASK_SEGMENT;

#elif defined(BOOT_X64)

typedef Struct_Microsoft_Singularity_Isal_IX_TSS64 BL_TASK_SEGMENT;

#endif

typedef struct _BL_PROCESSOR {
    UINT32 Index;
    Class_Microsoft_Singularity_Hal_Cpu *Cpu;
    PVOID KernelStack;
    ULONG_PTR KernelStackSize;
    PVOID ContextPage;
    PVOID BasePage;
    BL_TASK_SEGMENT *TaskPage;
} BL_PROCESSOR, *PBL_PROCESSOR;

PBL_PROCESSOR BlProcessor;
UINT32 BlProcessorCount;

VOID
BlSingularityInitializeProcessor(
    UINT32 Index
    )

//-++
//-
//-  Routine Description:
//-
//-    This function initializes the specified processor.
//-
//-  Arguments:
//-
//-    Index   - Supplies the index of the processor to initialize.
//-
//---

{
    Class_Microsoft_Singularity_Hal_Cpu *Processor;

    //-
    //- Initialize native processor structure.
    //-

    Processor = BlProcessor[Index].Cpu;
    Processor->Size = sizeof(Class_Microsoft_Singularity_Hal_Cpu);
    Processor->Id = Index;
#if 0
    Processor->ApicId  = Index;
#endif
    Processor->KernelStackLimit = (ULONG_PTR) BlProcessor[Index].KernelStack;
    //    Processor->KernelStackBegin = Processor->KernelStackLimit + SINGULARITY_KERNEL_STACK_SIZE;
    Processor->KernelStackBegin = Processor->KernelStackLimit + BlProcessor[Index].KernelStackSize;
    Processor->CpuRecordPage = (ULONG_PTR) BlProcessor[Index].BasePage;

    //-
    //- Initialize task structure.
    //-

    BlProcessor[Index].TaskPage->io_bitmap_offset = sizeof(BL_TASK_SEGMENT);

    //-
    //- Initialize segments.
    //-

    BlRtlZeroMemory(&Processor->segments, sizeof(Processor->segments));

    Processor->segments.gdtPtr.addr = (ULONG_PTR) &Processor->segments.gdt;
    Processor->segments.gdtPtr.limit = sizeof(Processor->segments.gdt) - 1;

    BlRtlCopyMemory(&Processor->segments.gdt.pc,
                    (PVOID) (BlMmInitialGdtr.Base + PM_CODE_SELECTOR),
                    sizeof(CODE_SEGMENT));

    BlRtlCopyMemory(&Processor->segments.gdt.pd,
                    (PVOID) (BlMmInitialGdtr.Base + PM_DATA_SELECTOR),
                    sizeof(CODE_SEGMENT));

#if defined(BOOT_X64)
    BlRtlCopyMemory(&Processor->segments.gdt.lc,
                    (PVOID) (BlMmInitialGdtr.Base + LM_CODE_SELECTOR),
                    sizeof(CODE_SEGMENT));

    BlRtlCopyMemory(&Processor->segments.gdt.ld,
                    (PVOID) (BlMmInitialGdtr.Base + LM_DATA_SELECTOR),
                    sizeof(CODE_SEGMENT));
#endif

    BlMmInitializeDataSegment((PDATA_SEGMENT) &Processor->segments.gdt.pp,
                              (UINT32) (ULONG_PTR) BlProcessor[Index].ContextPage,
                              PAGE_SIZE - 1);

    BlMmInitializeSystemSegment((PSYSTEM_SEGMENT) &Processor->segments.gdt.tss,
                                SSDT_AVAILABLE_TSS,
                                (ULONG_PTR) BlProcessor[Index].TaskPage,
                                sizeof(BL_TASK_SEGMENT) - 1);

    return;
}

UINT32 BlSingularityProcessorToStart;

//- Test whether SKINIT is possible on this machine
UINT8
TestForSKINIT()
{
    //- First check for max extended capabilities we're allowed to query
    UINT32 result = BlGetCpuidEax(0x80000000);

    if (result >= 0x80000001) {
      result = BlGetCpuidEcx(0x80000001);   //- Query the SVM-related capabilities
      if (result & 0x00001000) {    //- Check for SKINIT in the 12th bit
        return 1;
      } else {
        BlRtlPrintf("CPUID returned: %p\n", result);
      }
    } else {
      BlRtlPrintf("Result of extended query too small.\n");
    }
    return 0;
}

#ifdef SMALL_LOADER
UINT8
PrepTPM(ULONG_PTR SKINIT_base)
{
  return 0;
}
#else // !SMALL_LOADER
UINT8
PrepTPM(ULONG_PTR SKINIT_base)
{
    UINT32 locality = 3;
    UINT32 SKINIT_args = 0;
    
    //- Deposit the TPM's AIK at app's base+size+0x1F000+sSize+dSize
    //-SKINIT_args = (UINT32)330000 + 1024*1024 + 0x1F000 + 1024 + 1024;
    //- Deposit the TPM's AIK at loader's base+?CodeSpace+0x1F000(for DEV)+sSize+dSize
    SKINIT_args = (UINT32)SKINIT_base + 193 * 1024 + 4; // +4 since app entry point is at 0 
    UINT32* SKINIT_args_words = (UINT32*)SKINIT_args;
    SKINIT_args_words[0] = sizeof(aik);

    BlRtlPrintf("AIK of size: %p \n", SKINIT_args_words[0]);

    unsigned char* arg_ptr = (unsigned char*)(SKINIT_args + 4);
    for (int i = 0; i < sizeof(aik); i++) {
      arg_ptr[i] = aik[i];
//	  BlRtlPrintf("%02x ", ((unsigned int)aik[i]) & 0xff);
//	  if (((i+1)%24)==0)
//	  {
//		  BlRtlPrintf("\n");
//	  }
    }
//	BlRtlPrintf("\n");
    arg_ptr += sizeof(aik);

    return 0;
}
#endif // SMALL_LOADER

UINT32
BlSingularityCallKernel(
    UINT32 Index
    )

//-++
//-
//-  Routine Description:
//-
//-    This function calls the kernel.
//-
//-  Arguments:
//-
//-    Index   - Supplies the index of the current processor.
//-
//-  Return Value:
//-
//-    Kernel exit code.
//-
//---

{
    UINT32 ExitCode;
    ULONG_PTR SKINIT_base;

#if SINGULARITY_VERBOSE


    BlRtlPrintf("\fBL: Processor[%d]: Starting Singularity ...\n",
                Index
                );

    BlRtlPrintf("BL:   Cpu  = %p\n",
                BlProcessor[Index].Cpu
                );


    BlRtlPrintf("BL:   GDT  =[%p...%p]\n",
                BlProcessor[Index].Cpu->segments.gdtPtr.addr,
                BlProcessor[Index].Cpu->segments.gdtPtr.addr + BlProcessor[Index].Cpu->segments.gdtPtr.limit
                );


    BlRtlPrintf("BL:   stack=[%p...%p]\n",
                BlProcessor[Index].Cpu->KernelStackLimit,
                BlProcessor[Index].Cpu->KernelStackBegin
                );

#endif

    BlMmSetGdtr((PGDTR) &BlProcessor[Index].Cpu->segments.gdtPtr.limit);

#if defined(BOOT_X86)

    BlMmSetFs(PROCESSOR_SELECTOR);

#elif defined(BOOT_X64)

    BlMmSetGs(PROCESSOR_SELECTOR);

#endif

    BlMmSetCr3(BlMmBootCr3);

    BlRtlPrintf("BL:  kernel=[%p ... %p]\n",
                BlKernelBase, (ULONG_PTR) BlKernelBase + BlKernelSize - 1);
    BlRtlPrintf("BL:   entry= %p\n", BlKernelEntryPoint);

    //- Compute the 64K aligned address
    SKINIT_base = (ULONG_PTR)((UINT32)BlKernelEntryPoint) & ~(0x00010000 - 1);
    BlRtlPrintf("SL Base:   entry= %p\n", SKINIT_base);
    BlRtlPrintf("SL Header:   entry= %p\n", *(UINT32*)SKINIT_base);

//-    BlRtlPrintf("Stopping here\n");
//-    while (1) {}

    //- Load the app too
    ULONG_PTR AppEntry = BlSingularityLoadAppImage();

    //- Deposit the app's entry point at base+190k
    UINT32 app_args = (UINT32)SKINIT_base + 193 * 1024;
    UINT32* app_args_words = (UINT32*)app_args;
    app_args_words[0] = (UINT32)AppEntry;

    DisablePaging(42);

    //- Invoke SKINIT instead of calling into the kernel directly
    if (TestForSKINIT()) {
      if (PrepTPM(SKINIT_base)) {    
        BlRtlPrintf("Prepping the TPM failed.  Halting...\n");
        BlRtlHalt();
      }
      DEBUG_MSG("Executing SKINIT for real.  See you on the other side!\n");
      BlRealSKINIT(SKINIT_base);  
    } else {
      //- Assume we're in a VM, so don't bother with the TPM
      DEBUG_MSG("Faking SKINIT for testing purposes.\n");
      BlFakeSKINIT(SKINIT_base);  
    }

    //- Should never reach here!
    BlRtlPrintf("Wasn't expecting to see this...\n");

    ExitCode = BlKernelEntryPoint(BlPlatform, BlProcessor[Index].Cpu);

    BlMmSetGdtr(&BlMmInitialGdtr);

    BlVideoInitialize();

    return ExitCode;
}

VOID
BlSingularityEnterKernel(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function enters Singularity.
//
//--

{
    UINT32 ExitCode;
    PVOID LocalVariable;
    UINT32 Index;

    Index = BlSingularityProcessorToStart;

    BLASSERT(((ULONG_PTR) &LocalVariable) >= BlProcessor[Index].Cpu->KernelStackLimit);

    BLASSERT(((ULONG_PTR) &LocalVariable) < BlProcessor[Index].Cpu->KernelStackBegin);

    //
    // The bootstrap processor runs in a loop calling kernel entry point and performing warm boot
    // when the kernel returns. The application processors do not return from the kernel call and are
    // reinitialized with SIPIs by the kernel after a warm boot.
    //

    if (Index == 0) {

        for (;;) {
            BlMmDumpPhysicalRegionList();
            ExitCode = BlSingularityCallKernel(Index);

#if SINGULARITY_VERBOSE

            BlRtlPrintf("BL: Processor[%02x]: Kernel exited with 0x%08x.\n",
                        Index,
                        ExitCode);

#endif

            BlPlatform->BootCount += 1;

            BlRtlZeroMemory(BlKernelBase, BlKernelSize);

            BlPeLoadImage(BlKernelBase, BlKernelSize, BlKernelFile->Data, (PVOID *) &BlKernelEntryPoint, FALSE);
        }

    }
    else {

        ExitCode = BlSingularityCallKernel(Index);

        BlRtlPrintf("BL: AP returned from kernel call!\n");

        BlRtlHalt();
    }

    return;
}

VOID
BlSingularityExit(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function exits Singularity and performs the "kill action" requested by the kernel.
//
//--

{
    BlMmSetGdtr(&BlMmInitialGdtr);

    BlVideoInitialize();

    switch (BlPlatform->KillAction) {

        case Class_Microsoft_Singularity_Hal_Platform_EXIT_AND_SHUTDOWN: {

            BlRtlPrintf("BL: Kernel requested shutdown.\n");

            BlRtlShutdownSystem();

            break;
        }

        case Class_Microsoft_Singularity_Hal_Platform_EXIT_AND_RESTART: {

            BlRtlPrintf("BL: Kernel requested restart.\n");

            BlRtlResetSystem();

            break;
        }

        case Class_Microsoft_Singularity_Hal_Platform_EXIT_AND_HALT: {

            BlRtlPrintf("BL: Kernel requested halt.\n");

            BlRtlHalt();

            break;
        }

        case Class_Microsoft_Singularity_Hal_Platform_EXIT_AND_WARMBOOT: {

            BlRtlPrintf("BL: Kernel requested warmboot.\n");

            BlPlatform->BootCount += 1;

            BlRtlZeroMemory(BlKernelBase, BlKernelSize);

            BlPeLoadImage(BlKernelBase, BlKernelSize, BlKernelFile->Data, (PVOID *) &BlKernelEntryPoint, FALSE);

            BlSingularityProcessorToStart = 0;

            BlMmSwitchStack((PVOID) BlProcessor[0].Cpu->KernelStackBegin, BlSingularityEnterKernel);

            break;
        }

        default: {

            BlRtlPrintf("BL: Unrecognized kill action 0x%08x!\n", BlPlatform->KillAction);

            BlRtlHalt();
        }
    }
}


unsigned int IsApicPresent (void)
{
    unsigned int reg_edx = BlGetCpuidEdx(1);

    return ((reg_edx >> 9) & 0x1);
}

#define INITIAL_APIC_ID_BITS 0xFF000000 // EBX[31:24] unique APIC ID
// Returns the 8-bit unique Initial APIC ID for the processor this
// code is actually running on.  The default value returned is 0xFF if
// Hyper-Threading Technology is not supported.
// Taken from intel application note Ap-485 "Intel Processor Identification and the CPUID instruction"
unsigned char GetAPIC_ID (void)
{
    unsigned int reg_ebx = BlGetCpuidEbx(1);

    return (unsigned char) ((reg_ebx & INITIAL_APIC_ID_BITS) >> 24);
}

VOID
BlSingularityInitialize(
    UINT32 NumberOfProcessors,
    PFAR_POINTER ApEntry16,
    PFAR_POINTER ApStartupLock
    )

//++
//
//  Routine Description:
//
//    This function initializes Singularity.
//
//  Arguments:
//
//    NumberOfProcessors  - Supplies the number of processors on the system.
//
//    ApEntry6            - Supplies a pointer to the 16-bit entry point for
//                          application processors on a multi-processor system.
//
//    ApStartupLock       - Supplies a pointer to the lock used for AP startup
//                          synchronization.
//
//--

{
    UINT64 Base;
    UINT32 Index;
    PVOID PhysicalRegionHandle;
    UINT64 Size;
    UINT32 Type;
    UINT8 id;
    UINT64 HighAddress;
    UINT64 TempAddress;
    UINT64 StackStart;
    UINT64 PlayStart;
    int i;
    char* p;

    //
    // Allocate processor array and set processor count.
    //

    BlProcessor = (PBL_PROCESSOR) BlPoolAllocateBlock(sizeof(BL_PROCESSOR) * NumberOfProcessors);
    BlProcessorCount = NumberOfProcessors;

    //
    // Load distro.
    //

    BlSingularityLoadDistro();

    //
    // Load kernel image.
    //

    BlSingularityLoadKernelImage();

    //
    // Allocate native platform structure.
    //

    BlPlatform = (Class_Microsoft_Singularity_Hal_Platform *) BlMmAllocatePhysicalRegion(ROUND_UP_TO_PAGES(sizeof(Class_Microsoft_Singularity_Hal_Platform)), BL_MM_PHYSICAL_REGION_NATIVE_PLATFORM);

    BlPlatform->Size = sizeof(Class_Microsoft_Singularity_Hal_Platform);

    if (IsApicPresent()) {
        BlPlatform->hasApic = 1;
    }
    else {
        BlPlatform->hasApic = 0;
    }

    //
    // Set offsets for per-cpu and per-thread pointers.
    //

    BlPlatform->CpuRecordPointerOffset = 0;
    BlPlatform->ThreadRecordPointerOffset = sizeof(PTR_TYPE);

    //
    // Set boot time.
    //

    if (BlStartTime.Year != 0) {
        BlPlatform->BootYear = 2000 + BlStartTime.Year;
        BlPlatform->BootMonth = BlStartTime.Month;
        BlPlatform->BootDay = BlStartTime.Day;
        BlPlatform->BootHour = BlStartTime.Hour;
        BlPlatform->BootMinute = BlStartTime.Minute;
        BlPlatform->BootSecond = BlStartTime.Second;
    }

    //
    // Set processor count.
    //

    BlPlatform->CpuRealCount = NumberOfProcessors;
    BlPlatform->CpuMaxCount = NumberOfProcessors;

    //
    // Set MPS floating pointer structure address.
    //

    BlPlatform->MpFloat32 = (UINT32) (ULONG_PTR) BlMpsFps;

    //
    // Set kernel range.
    //

    BlPlatform->KernelDllBase = (ULONG_PTR) BlKernelBase;
    BlPlatform->KernelDllFirstPage = (ULONG_PTR) BlKernelBase;
    BlPlatform->KernelDllSize = BlKernelSize;

    //
    // Set command line.
    //

    BlPlatform->CommandLine32 = (ULONG_PTR) BlCommandLine;
    BlPlatform->CommandLineCount = BlRtlStringLengthW(BlCommandLine);

    //
    // Set PNP node list address.
    //

    BlPlatform->PnpNodesAddr32 = (ULONG_PTR) BlPnpSystemDeviceNodeList;
    BlPlatform->PnpNodesSize32 = BlPnpSystemDeviceNodeListSize;

    //
    // Set ISA information.
    //

    BlPlatform->IsaCsns = BlPnpIsaConfiguration.NumberOfCardSelectNumbers;
    BlPlatform->IsaReadPort = BlPnpIsaConfiguration.DataReadPort;

    //
    // Set PCI BIOS information.
    //

    BlPlatform->PciBiosAX = BlPciInstallationCheck.Eax;
    BlPlatform->PciBiosBX = BlPciInstallationCheck.Ebx;
    BlPlatform->PciBiosCX = BlPciInstallationCheck.Ecx;
    BlPlatform->PciBiosEDX = BlPciInstallationCheck.Edx;

    //
    // Set VESA information.
    //

    BlPlatform->VesaBuffer = BlVesaVideoBuffer;

    //
    // Set ACPI information.
    //

    BlPlatform->AcpiRoot32 = (ULONG_PTR) BlAcpiRsdpAddress;

    //
    // Set file image table.
    //

    BlPlatform->FileImageTableBase32 = (ULONG_PTR) BlSingularityFileImageTable;
    BlPlatform->FileImageTableEntries = BlSingularityFileImageTableSize;

    //
    // Allocate log record and text buffers.
    //

    BlPlatform->LogRecordBuffer = (ULONG_PTR) BlMmAllocatePhysicalRegion(SINGULARITY_LOG_RECORD_SIZE, BL_MM_PHYSICAL_REGION_LOG_RECORD);
    BlPlatform->LogRecordSize = SINGULARITY_LOG_RECORD_SIZE;

    BlPlatform->LogTextBuffer = (ULONG_PTR) BlMmAllocatePhysicalRegion(SINGULARITY_LOG_TEXT_SIZE, BL_MM_PHYSICAL_REGION_LOG_TEXT);
    BlPlatform->LogTextSize = SINGULARITY_LOG_TEXT_SIZE;

    //
    // Set debugger settings.
    //

    if (BlKdComPort != 0) {

        BlPlatform->DebuggerType = Class_Microsoft_Singularity_Hal_Platform_DEBUGGER_SERIAL;
        BlPlatform->DebugBasePort = BlComBasePort[BlKdComPort];

    }
    else if (BlPciOhci1394BaseAddress != 0) {

        BlRtlPrintf("Got 1394 debugger base address!\n");
        BlPlatform->DebuggerType = Class_Microsoft_Singularity_Hal_Platform_DEBUGGER_1394;
        BlPlatform->Ohci1394Base = BlPciOhci1394BaseAddress;
        BlPlatform->Ohci1394BufferAddr32 = (ULONG_PTR) BlSingularityOhci1394Buffer;
        BlPlatform->Ohci1394BufferSize32 = sizeof(BlSingularityOhci1394Buffer);

    }
    else {

        BlRtlPrintf("Debugger OFF\n");
        BlPlatform->DebuggerType = Class_Microsoft_Singularity_Hal_Platform_DEBUGGER_NONE;

    }

    BlPlatform->TwiddleSpinBase = 0xb8000;

    //
    // Set exit routine.
    //

    BlPlatform->Kill32 = (ULONG_PTR) BlSingularityExit;

    //
    // Set entry routine and startup lock address for application processors.
    //

    BlPlatform->MpEnter32 = (ULONG_PTR) BlRtlConvertFarPointerToLinearPointer(ApEntry16);
    BlPlatform->MpStartupLock32 = (ULONG_PTR) BlRtlConvertFarPointerToLinearPointer(ApStartupLock);

    //
    // Allocate native processor structures.
    //

    BlCpuArray =
        (Class_Microsoft_Singularity_Hal_Cpu *) BlMmAllocatePhysicalRegion(ROUND_UP_TO_PAGES(sizeof(Class_Microsoft_Singularity_Hal_Cpu) * NumberOfProcessors), BL_MM_PHYSICAL_REGION_NATIVE_PROCESSOR);

    BlPlatform->Cpus = (ULONG_PTR) BlCpuArray;

    //
    // Allocate per-processor resources upfront.
    //

    for (Index = 0; Index < NumberOfProcessors; Index += 1) {

        BlProcessor[Index].Index = Index;
        BlProcessor[Index].Cpu = &BlCpuArray[Index];
        BlProcessor[Index].ContextPage = (PVOID) BlMmAllocatePhysicalRegion(2 * PAGE_SIZE, BL_MM_PHYSICAL_REGION_CONTEXT);
        BlProcessor[Index].BasePage = (PVOID) ((ULONG_PTR) BlProcessor[Index].ContextPage + PAGE_SIZE);
        BlProcessor[Index].TaskPage = (BL_TASK_SEGMENT *) BlMmAllocatePhysicalRegion(PAGE_SIZE, BL_MM_PHYSICAL_REGION_TASK);
    }

    //
    // Allocate kernel stack for the bootstrap processor.
    //

    StackStart = BlMmAllocatePhysicalRegion(SINGULARITY_KERNEL_STACK_SIZE,
                        BL_MM_PHYSICAL_REGION_KERNEL_STACK);
    if (0 == StackStart) {
    BlRtlPrintf("Failed to allocate kernel stack.\n", StackStart);
    BlRtlHalt();
    }

    BlRtlPrintf("Allocated kernel stack at 0x%016I64x\n", StackStart);

    BlProcessor[0].KernelStack = (PVOID) (StackStart);
    BlProcessor[0].Cpu->DomainBsp = TRUE;

    BlPlatform->OutgoingMessage   = 0;
    BlPlatform->OutgoingCount     = 0;
    BlPlatform->IncomingFree      = 0;
    BlPlatform->IncomingFreeCount = 0;
    BlPlatform->IncomingMessage   = 0;
    BlPlatform->IncomingCount     = 0;
    BlPlatform->OutgoingFree      = 0;
    BlPlatform->OutgoingFreeCount = 0;
    BlPlatform->MaxBufferLength   = 0;

    BlProcessor[0].KernelStackSize = SINGULARITY_KERNEL_STACK_SIZE;

    //
    // Initialize the first processor structure.
    //

    BlSingularityInitializeProcessor(0);

    //
    // Allocate memory map for Singularity.
    //

    BlSingularitySmap = (PBL_SMAP) BlMmAllocatePhysicalRegion(sizeof(BL_SMAP), BL_MM_PHYSICAL_REGION_SINGULARITY_SMAP);

    //
    // Claim all remaining physical memory for Singularity.
    //

//    while (BlMmFindFreePhysicalRegion(&Base, &Size) != FALSE) {
//
//        BlMmAllocateSpecificPhysicalRegion(Base, Size, BL_MM_PHYSICAL_REGION_SINGULARITY);
//    }

    //
    // Generate memory map for Singularity.
    //

    BlRtlZeroMemory(BlSingularitySmap, sizeof(BL_SMAP));

    BlPlatform->PhysicalBase = (ULONG_PTR) -1;

    PhysicalRegionHandle = NULL;

    while (BlMmGetNextPhysicalRegion(&PhysicalRegionHandle,
                                     &Base,
                                     &Size,
                                     &Type) != FALSE) {

        if ((Type == BL_MM_PHYSICAL_REGION_SINGULARITY) ||
            (Type == BL_MM_PHYSICAL_REGION_KERNEL_IMAGE) ||
            (Type == BL_MM_PHYSICAL_REGION_NATIVE_PLATFORM) ||
            (Type == BL_MM_PHYSICAL_REGION_NATIVE_PROCESSOR) ||
            (Type == BL_MM_PHYSICAL_REGION_KERNEL_STACK)
            ) {

            if (Type == BL_MM_PHYSICAL_REGION_SINGULARITY) {
                BlSingularitySmap->Entry[BlSingularitySmap->EntryCount].Base = Base;
                BlSingularitySmap->Entry[BlSingularitySmap->EntryCount].Size = Size;
                BlSingularitySmap->Entry[BlSingularitySmap->EntryCount].Type = BL_SMAP_AVAILABLE;
            }
            else if (Type == BL_MM_PHYSICAL_REGION_KERNEL_IMAGE ||
                      (Type == BL_MM_PHYSICAL_REGION_NATIVE_PLATFORM) ||
                      (Type == BL_MM_PHYSICAL_REGION_NATIVE_PROCESSOR)) {
                BlSingularitySmap->Entry[BlSingularitySmap->EntryCount].Base = Base;
                BlSingularitySmap->Entry[BlSingularitySmap->EntryCount].Size = Size;
                BlSingularitySmap->Entry[BlSingularitySmap->EntryCount].Type = BL_SMAP_KERNEL_NONGC;
            }
            else if (Type == BL_MM_PHYSICAL_REGION_KERNEL_STACK) {
                BlSingularitySmap->Entry[BlSingularitySmap->EntryCount].Base = Base;
                BlSingularitySmap->Entry[BlSingularitySmap->EntryCount].Size = Size;
                BlSingularitySmap->Entry[BlSingularitySmap->EntryCount].Type = BL_SMAP_KERNEL_STACK;
            }
            else {
                BlRtlPrintf("UNKNOWN TYPE MEMORY??? %d\n", Type);
            }
            if (Base < BlPlatform->PhysicalBase) {
                BlPlatform->PhysicalBase = (ULONG_PTR) Base;
            }
            BlSingularitySmap->EntryCount += 1;
        }
        else {
#if MM_VERBOSE
            BlRtlPrintf("Building SMAP marking type %s nongc\n", BlMmPhysicalRegionTypeString(Type));
#endif
            BlSingularitySmap->Entry[BlSingularitySmap->EntryCount].Base = Base;
            BlSingularitySmap->Entry[BlSingularitySmap->EntryCount].Size = Size;
            BlSingularitySmap->Entry[BlSingularitySmap->EntryCount].Type = BL_SMAP_KERNEL_NONGC;
            BlSingularitySmap->EntryCount += 1;
        }
    }

    BlPlatform->Smap32 = (ULONG_PTR) (PVOID) BlSingularitySmap->Entry;
    BlPlatform->SmapCount = BlSingularitySmap->EntryCount;

#if MM_VERBOSE

    BlMmDumpPhysicalRegionList();

#endif

    //
    // Start processor 0.
    //

    BlSingularityProcessorToStart = 0;

    BlMmSwitchStack((PVOID) BlProcessor[0].Cpu->KernelStackBegin, BlSingularityEnterKernel);

    return;
}

VOID
BlSingularityApEntry(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function implements the entry point for application processors.
//
//--

{
    UINT32 Index;

    UINT8 MyIdChar;
    UINT32 MyId;
    UINT32 MyStack;
    Class_Microsoft_Singularity_Hal_Cpu *Processor;
    //    BlRtlPrintf("In Ap Entry\n");

    //    BlRtlPrintf("Non AP processor booting\n");
    Index = BlPlatform->MpBootInfo.TargetCpu;

    if (Index == 0) {

        // BlRtlPrintf("BL: BSP entered AP code!\n");
        BlRtlHalt();
    }

#if SINGULARITY_VERBOSE

    BlRtlPrintf("BL: Initializing processor %u of %u. [Max=%u]\n",
                Index + 1,
                BlPlatform->CpuRealCount,
                BlPlatform->CpuMaxCount);

#endif

    BlProcessor[Index].KernelStack = (PVOID) BlPlatform->MpBootInfo.KernelStackLimit;
    BlProcessor[Index].Cpu->DomainBsp = FALSE;
    BlProcessor[Index].KernelStackSize = BlPlatform->MpBootInfo.KernelStackBegin - BlPlatform->MpBootInfo.KernelStackLimit;

    BlSingularityInitializeProcessor(Index);

    BlSingularityProcessorToStart = Index;

    BlMmSwitchStack((PVOID) BlProcessor[Index].Cpu->KernelStackBegin, BlSingularityEnterKernel);

    return;
}
