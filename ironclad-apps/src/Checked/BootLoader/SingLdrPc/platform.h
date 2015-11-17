typedef __int64 Gdte;
typedef unsigned char byte;
typedef unsigned short ushort;
typedef unsigned uint;
typedef unsigned __int64 ulong;
typedef ULONG_PTR UIntPtr;

const int Class_Microsoft_Singularity_Hal_Platform_EXIT_AND_RESTART     = 0x1fff;
const int Class_Microsoft_Singularity_Hal_Platform_EXIT_AND_SHUTDOWN    = 0x1ffe;
const int Class_Microsoft_Singularity_Hal_Platform_EXIT_AND_WARMBOOT    = 0x1ffd;
const int Class_Microsoft_Singularity_Hal_Platform_EXIT_AND_HALT        = 0x1ffc;
const int            Class_Microsoft_Singularity_Hal_Platform_DEBUGGER_NONE       = 0;
const int            Class_Microsoft_Singularity_Hal_Platform_DEBUGGER_SERIAL     = 1;
const int            Class_Microsoft_Singularity_Hal_Platform_DEBUGGER_1394       = 2;

struct Class_Microsoft_Singularity_MpBootInfo
{
    uint     signature;
    UIntPtr  KernelStackBegin;
    UIntPtr  KernelStack;
    UIntPtr  KernelStackLimit;
    volatile int TargetCpu;
};

struct Struct_Microsoft_Singularity_Isal_IX_DescriptorTable_Gdt
{
    Gdte     nul;    // Null segment
    Gdte    pv;     // 16-bit video, used in boot loader only
    Gdte    rc;     // 16-bit code, used to align with RM code in boot loader
    Gdte    rd;     // 16-bit data, used to align with RM data in boot loader
    Gdte    pc;     // 32-bit code
    Gdte    pd;     // 32-bit data
    Gdte    lc;     // 64-bit code
    Gdte    ld;     // 64-bit data
    Gdte     uc;     // User mode code - used in paging mode only
    Gdte     ud;     // User mode data - used in paging mode only
    Gdte     pp;     // Kernel mode per-processor data
    Gdte     nn;     // Unused
    Gdte        tss;        // Currently executing task segment
};

struct Struct_Microsoft_Singularity_Isal_IX_Gdtp
{
    ushort     pad;
    ushort     limit;
    uint       addr;
};

struct Struct_Microsoft_Singularity_Isal_IX_DescriptorTable
{
    Struct_Microsoft_Singularity_Isal_IX_DescriptorTable_Gdt              gdt;
    Struct_Microsoft_Singularity_Isal_IX_Gdtp             gdtPtr;
};

struct Class_Microsoft_Singularity_Hal_Cpu
{
    int        Size;
    int        Id;
    UIntPtr     CpuRecordPage;
    UIntPtr     KernelStackLimit; // lower bounds of stack
    UIntPtr     KernelStackBegin; // upper bounds of stack
    int         DomainBsp;
    Struct_Microsoft_Singularity_Isal_IX_DescriptorTable                     segments;
    bool halted;
};

struct Class_Microsoft_Singularity_Hal_Platform
{
    // Size of instance; this is a versioning/consistency check
    int         Size;
    uint        BootYear;
    uint        BootMonth;
    uint        BootDay;
    uint        BootHour;
    uint        BootMinute;
    uint        BootSecond;
    int         CpuMaxCount;
    int         CpuRealCount;
    int         BootCount;
    UIntPtr     Smap32;
    int         SmapCount;
    UIntPtr     PhysicalBase;
    uint*OutgoingMessage;
    int* OutgoingCount;
    uint*IncomingFree;       //previously sent messages that cane be safely freed
    int* IncomingFreeCount;
    uint*IncomingMessage;    //messages bound for this kernel
    int* IncomingCount;
    uint*OutgoingFree;       // messages that this kernel has processed
    int* OutgoingFreeCount;
    uint        MaxBufferLength;
     uint       thisDestinationId;
     uint       hasApic;
    UIntPtr     BootAllocatedMemory;
    UIntPtr     BootAllocatedMemorySize;
    UIntPtr     CommandLine32;
    int         CommandLineCount;
    int  CpuRecordPointerOffset;
    int  ThreadRecordPointerOffset;
    UIntPtr     LogRecordBuffer;
    UIntPtr     LogRecordSize;
    UIntPtr     LogTextBuffer;
    UIntPtr     LogTextSize;
    UIntPtr     KernelDllBase;
    UIntPtr     KernelDllSize;
    UIntPtr     KernelDllFirstPage; // first page may be disjoint on CE
    UIntPtr     MiniDumpBase;
    UIntPtr     MiniDumpLimit;
    int         DebuggerType;
//    protected Cpu               bootCpu;
    uint     RecSize;
    ushort   DebugBasePort;
    ushort   DebugSpinBase;
    uint     TwiddleSpinBase;
    ulong    Info32;
    ulong    Kill32;
    uint     KillAction;
    ulong    DumpAddr32;
    ulong    FileImageTableBase32;
    uint     FileImageTableEntries;
    uint     DumpSize32;
    ulong    DumpRemainder;
    ulong    DumpLimit;
    ulong    NativeContext;
    ulong    Cpus;
    ushort   BiosPicMask;
    byte     BiosWarmResetCmos;
    uint     BiosWarmResetVector;
    uint     Info16;
    ulong    IdtEnter0;
    ulong    IdtEnter1;
    ulong    IdtEnterN;
    ulong    IdtTarget;
    ulong    Pdpt32;
    ulong    KernelPdpt64;
    ulong    Undump;
    uint     PciBiosAX;
    uint     PciBiosBX;
    uint     PciBiosCX;
    uint     PciBiosEDX;
    ulong    AcpiRoot32;
    ulong    PnpNodesAddr32;
    uint     PnpNodesSize32;
    ulong    SmbiosRoot32;
    ulong    DmiRoot32;
    uint     IsaCsns;
    ushort   IsaReadPort;
    uint     Ebda32;
    uint     MpFloat32;
    ulong    Ohci1394Base;
    ulong    Ohci1394BufferAddr32;
    uint     Ohci1394BufferSize32;
    ulong    VesaBuffer;
    ulong    MpEnter32;          // Entry point
    uint     MpCpuCount;         // No of AP's booted
    uint     MpStatus32;         // Error indicator
    ulong    MpStartupLock32;    // Pointer to MP init lock var
    Class_Microsoft_Singularity_MpBootInfo   MpBootInfo;
//    private Cpu[]   processors;
//    private HalDevices devices;
};

struct Struct_Microsoft_Singularity_Io_FileImage
{
    UIntPtr Address;
    uint    Size;
};

struct Struct_Microsoft_Singularity_Isal_IX_TSS
{
    ushort     previous_tss;
    ushort     pad0;

    uint       esp0;
    ushort     ss0;
    ushort     pad1;

    uint       esp1;
    ushort     ss1;
    ushort     pad2;

    uint       esp2;
    ushort     ss2;
    ushort     pad3;

    uint       cr3;
    uint       eip;
    uint       eflags;

    uint       eax;
    uint       ecx;
    uint       edx;
    uint       ebx;
    uint       esp;
    uint       ebp;
    uint       esi;
    uint       edi;

    ushort     es;
    ushort     pades;
    ushort     cs;
    ushort     padcs;
    ushort     ss;
    ushort     padss;
    ushort     ds;
    ushort     padds;
    ushort     fs;
    ushort     padfs;
    ushort     gs;
    ushort     padgs;

    ushort     ldt;
    ushort     padldt;
    ushort     trap_bit;
    ushort     io_bitmap_offset;
};
