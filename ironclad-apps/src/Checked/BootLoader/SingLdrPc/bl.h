//++
//
//  Copyright (c) Microsoft Corporation
//
//  Module Name:
//
//    bl.h
//
//  Abstract:
//
//    This module contains definitions for the boot loader.
//
//  Environment:
//
//    Boot loader.
//
//--

#pragma once

#pragma warning(disable:4127)           // conditional expression is constant
#pragma warning(disable:4152)           // function/data pointer conversion in expression
#pragma warning(disable:4200)           // zero-sized array in struct/union
#pragma warning(disable:4201)           // nameless struct/union
#pragma warning(disable:4214)           // bit field types other than int

//
// Constants for selectively enabling verbose debug output.
//

#define ACPI_VERBOSE                    0
#define APM_VERBOSE                     0
#define CDROM_VERBOSE                   0
#define COM_VERBOSE                     0
#define DISTRO_VERBOSE                  1
#define FAT_VERBOSE                     0
#define KD_VERBOSE                      0
#define MM_VERBOSE                      0
#define MPS_VERBOSE                     0
#define PCI_VERBOSE                     0
#define PECOFF_VERBOSE                  1
#define PNP_VERBOSE                     0
#define POOL_VERBOSE                    0
#define PXE_VERBOSE                     0
#define SINGULARITY_VERBOSE             0
#define SMAP_VERBOSE                    0

#define DEBUG_MSG(msg)              \
{                                   \
  UINT32 my_debug_cntr = 0;         \
  while (my_debug_cntr < 1<<31) {   \
    if (my_debug_cntr == 0) {       \
      BlRtlPrintf(msg);             \
    }                               \
    my_debug_cntr += 1;             \
  }                                 \
}


//
// Basic platform constants.
//

#define PAGE_SIZE                       4096
#define LEGACY_MEMORY_LIMIT             0x100000

//
// Compile-time assertion support.
//

#define C_ASSERT(e) typedef char __C_ASSERT__[(e)?1:-1]

//
// Basic integer types.
//

typedef char                CHAR;
typedef unsigned char       UCHAR;

typedef char                INT8;
typedef unsigned char       UINT8;
typedef short               INT16;
typedef unsigned short      UINT16;
typedef long                INT32;
typedef unsigned long       UINT32;
typedef __int64             INT64;
typedef unsigned __int64    UINT64;

#if defined(BOOT_X86)

typedef INT32               LONG_PTR;
typedef UINT32              ULONG_PTR;

#elif defined (BOOT_X64)

typedef INT64               LONG_PTR;
typedef UINT64              ULONG_PTR;

#endif


//
// Basic boolean type.
//

typedef unsigned char       BOOLEAN;

//
// Basic pointer types.
//

typedef void                VOID;
typedef VOID *              PVOID;
typedef const VOID *        PCVOID;
typedef CHAR *              PCHAR;
typedef INT8 *              PINT8;
typedef UINT8 *             PUINT8;
typedef INT16 *             PINT16;
typedef UINT16 *            PUINT16;
typedef INT32 *             PINT32;
typedef UINT32 *            PUINT32;
typedef INT64 *             PINT64;
typedef UINT64 *            PUINT64;
typedef LONG_PTR *          PLONG_PTR;
typedef ULONG_PTR *         PULONG_PTR;
typedef BOOLEAN             PBOOLEAN;

//
// Wide character types.
//

typedef wchar_t             WCHAR;
typedef WCHAR *             PWCHAR;
typedef const WCHAR *       PCWSTR;
typedef const CHAR *        PCSTR;

//
// Structure macros.
//

#define FIELD_OFFSET(Type, Field)               ((UINT32) (ULONG_PTR) &(((Type *) 0)->Field))
#define CONTAINING_RECORD(Address, Type, Field) ((Type *) ((ULONG_PTR) (Address) - FIELD_OFFSET(Type, Field)))
#define ARRAY_SIZE(Array)                       (sizeof(Array) / sizeof(Array[0]))

//
// Macros for rounding up.
//

#define ROUND_UP_TO_POWER2(X, P)        (((X) + ((P) - 1)) & (~((P) - 1)))
#define ROUND_UP_TO_PAGES(X)            ROUND_UP_TO_POWER2(X, PAGE_SIZE)

//
// The following macro is used to satisfy the compiler. Note that the
// expressions/statements passed to this macro are not necessary for
// correctness, but without them the compiler cannot compile with W4.
//

#define SATISFY_OVERZEALOUS_COMPILER(X) X

//
// Function modifiers.
//

#define FORCEINLINE         __forceinline

//
// Basic constants.
//

#define FALSE               0
#define TRUE                1
#define NULL                0

//
// va support (from vadefs.h).
//

typedef char *va_list;

#if defined(BOOT_X86)

#define _ADDRESSOF(v)   ( &(v) )
#define _INTSIZEOF(n)   ( (sizeof(n) + sizeof(int) - 1) & ~(sizeof(int) - 1) )

#define _crt_va_start(ap,v)  ( ap = (va_list)_ADDRESSOF(v) + _INTSIZEOF(v) )
#define _crt_va_arg(ap,t)    ( *(t *)((ap += _INTSIZEOF(t)) - _INTSIZEOF(t)) )
#define _crt_va_end(ap)      ( ap = (va_list)0 )

#elif defined(BOOT_X64)

extern "C" void __cdecl __va_start(va_list *, ...);

#define _crt_va_start(ap, x) ( __va_start(&ap, x) )
#define _crt_va_arg(ap, t)   \
    ( ( sizeof(t) > sizeof(__int64) || ( sizeof(t) & (sizeof(t) - 1) ) != 0 ) \
        ? **(t **)( ( ap += sizeof(__int64) ) - sizeof(__int64) ) \
        :  *(t  *)( ( ap += sizeof(__int64) ) - sizeof(__int64) ) )
#define _crt_va_end(ap)      ( ap = (va_list)0 )

#endif

#define va_start    _crt_va_start
#define va_arg      _crt_va_arg
#define va_end      _crt_va_end

UINT32
DisablePaging(
    UINT32 arg
    );

//
// Runtime assertion support.
//

BOOLEAN
BlRtlPrintf(
    PCSTR Format,
    ...
    );

VOID
BlRtlHaltInternal(
    PCSTR FileName,
    UINT32 LineNumber
    );

VOID
BlRtlAssertFailed(
    PCSTR FileName,
    UINT32 LineNumber
    );

VOID
BlRtlAssertFailedPtr(
    PCSTR FileName,
    UINT32 LineNumber,
    ULONG_PTR Param
    );

#define BlRtlHalt() BlRtlHaltInternal(__FILE__, __LINE__)

#define BLASSERT(X)                                 \
    if (!(X)) {                                     \
        BlRtlAssertFailed(__FILE__, __LINE__);      \
    }

#define BLASSERT_PTR(X, P)                                          \
    if (!(X)) {                                                     \
        BlRtlAssertFailedPtr(__FILE__, __LINE__, (ULONG_PTR) (P));  \
    }

//
// Linked list support.
//

typedef struct _LIST_ENTRY {
   struct _LIST_ENTRY *Flink;
   struct _LIST_ENTRY *Blink;
} LIST_ENTRY, *PLIST_ENTRY;

VOID
BlRtlInitializeListHead(
    PLIST_ENTRY Head
    );

BOOLEAN
BlRtlIsListEmpty(
    PLIST_ENTRY Head
    );

BOOLEAN
BlRtlRemoveEntryList(
    PLIST_ENTRY Entry
    );

PLIST_ENTRY
BlRtlRemoveHeadList(
    PLIST_ENTRY Head
    );

PLIST_ENTRY
BlRtlRemoveTailList(
    PLIST_ENTRY Head
    );

VOID
BlRtlInsertTailList(
    PLIST_ENTRY Head,
    PLIST_ENTRY Entry
    );

VOID
BlRtlInsertHeadList(
    PLIST_ENTRY Head,
    PLIST_ENTRY Entry
    );

//
// Legacy far pointer support.
//

typedef struct _FAR_POINTER {
    UINT16 Offset;
    UINT16 Segment;
} FAR_POINTER, *PFAR_POINTER;

C_ASSERT(sizeof(FAR_POINTER) == sizeof(UINT32));

VOID
BlRtlConvertLinearPointerToFarPointer(
    PVOID LinearPointer,
    PFAR_POINTER FarPointer
    );

PVOID
BlRtlConvertFarPointerToLinearPointer(
    PFAR_POINTER FarPointer
    );

//
// Boot environment block.
//

typedef struct _BEB {
    UINT32 BootType;
    UINT32 BootDriveNumber;
    UINT32 FlashImage;
    UINT32 SmapAddr;
    UINT32 SmapSize;
    UINT32 LegacyCallAddress;
    UINT32 LegacyReturnAddress;
    UINT32 LegacyReturnCr3;
    UINT32 LegacyCall_OpCode;
    UINT32 LegacyCall_Vector;
    UINT32 LegacyCall_ax;
    UINT32 LegacyCall_bx;
    UINT32 LegacyCall_cx;
    UINT32 LegacyCall_dx;
    UINT32 LegacyCall_si;
    UINT32 LegacyCall_di;
    UINT32 LegacyCall_ds;
    UINT32 LegacyCall_es;
    UINT32 LegacyCall_flags;
    FAR_POINTER LegacyCall_FramePtr;
    UINT32 LegacyCall_FrameSize;
    FAR_POINTER LegacyCall_FuncPtr;
    FAR_POINTER ApEntry16;
    UINT32 ApEntry;
    FAR_POINTER ApStartupLock;
} BEB, *PBEB;

#define BEB_BASE                        ((ULONG_PTR) 0x2F000)

FORCEINLINE
PBEB
BlGetBeb(
    VOID
    )

//++
//
//Routine Description:
//
//  This function returns a pointer to the boot environment block.
//
//Return Value:
//
//  Pointer to the boot environment block.
//
//--

{
    return ((PBEB) BEB_BASE);
}

//
// Boot sources.
//

#define BL_CD_BOOT      1
#define BL_FAT16_BOOT   2
#define BL_FAT32_BOOT   3
#define BL_PXE_BOOT     4
#define BL_FLASH_BOOT   5

//
// Legacy call context.
//

typedef struct _BL_LEGACY_CALL_CONTEXT {
    UINT32 eax;
    UINT32 ebx;
    UINT32 ecx;
    UINT32 edx;
    UINT32 esi;
    UINT32 edi;
    UINT32 ds;
    UINT32 es;
    UINT32 eflags;
} BL_LEGACY_CALL_CONTEXT, *PBL_LEGACY_CALL_CONTEXT;

//
// Legacy call opcodes.
//

#define LC_NOP                          0x0000
#define LC_INTXX                        0x0001
#define LC_FARCALL                      0x0002

//
// RFLAGS.
//

#define RFLAGS_CF                       0x0001

//
// Utility functions.
//

VOID
BlRtlZeroMemory(
    PVOID Buffer,
    ULONG_PTR Length
    );

VOID
BlRtlCopyMemory(
    PVOID Destination,
    PCVOID Source,
    ULONG_PTR Length
    );

BOOLEAN
BlRtlCompareMemory(
    PCVOID Buffer1,
    PCVOID Buffer2,
    ULONG_PTR Length
    );

VOID
BlRtlCallLegacyInterruptService(
    UINT8 Vector,
    PBL_LEGACY_CALL_CONTEXT Input,
    PBL_LEGACY_CALL_CONTEXT Output
    );

VOID
BlRtlCallLegacyFunction(
    UINT16 CodeSegment16,
    UINT16 CodeOffset16,
    PVOID CallFrame,
    UINT32 CallFrameSize,
    PBL_LEGACY_CALL_CONTEXT Input,
    PBL_LEGACY_CALL_CONTEXT Output
    );

UINT8
BlRtlComputeChecksum8(
    PCVOID Buffer,
    UINT32 Size
    );

UINT32
BlGetCpuidEax(
    UINT32 reg
    );

UINT32
BlGetCpuidEbx(
    UINT32 reg
    );

UINT32
BlGetCpuidEcx(
    UINT32 reg
    );

UINT32
BlGetCpuidEdx(
    UINT32 reg
    );

//
// Constants and macros for accessing the keyboard controller.
//

#define BL_KEYBOARD_STATUS_PORT                 0x0064
#define BL_KEYBOARD_COMMAND_PORT                0x0064
#define BL_KEYBOARD_DATA_PORT                   0x0060

#define BL_KEYBOARD_STATUS_INPUT_BUFFER_FULL    0x02

#define BL_KEYBOARD_COMMAND_WRITE_OUTPUT_PORT   0xD1
#define BL_KEYBOARD_COMMAND_PULSE_RESET_BIT     0xFE
#define BL_KEYBOARD_COMMAND_PULSE_OUTPUT_PORT   0xFF

#define BL_KEYBOARD_A20_ENABLE                  0xDF

#define BL_KEYBOARD_WAIT_FOR_IDLE()                                                                 \
    while ((BlRtlReadPort8(BL_KEYBOARD_STATUS_PORT) & BL_KEYBOARD_STATUS_INPUT_BUFFER_FULL) != 0) { \
    }

#define BL_KEYBOARD_WRITE_COMMAND(X)                                                                \
    {                                                                                               \
        BL_KEYBOARD_WAIT_FOR_IDLE();                                                                \
        BlRtlWritePort8(BL_KEYBOARD_COMMAND_PORT, (X));                                             \
        BL_KEYBOARD_WAIT_FOR_IDLE();                                                                \
    }

#define BL_KEYBOARD_WRITE_OUTPUT_PORT(X)                                                            \
    {                                                                                               \
        BL_KEYBOARD_WAIT_FOR_IDLE();                                                                \
        BlRtlWritePort8(BL_KEYBOARD_COMMAND_PORT, BL_KEYBOARD_COMMAND_WRITE_OUTPUT_PORT);           \
        BL_KEYBOARD_WAIT_FOR_IDLE();                                                                \
        BlRtlWritePort8(BL_KEYBOARD_DATA_PORT, (X));                                                \
        BL_KEYBOARD_WAIT_FOR_IDLE();                                                                \
    }

VOID
BlRtlResetSystem(
    VOID
    );

VOID
BlRtlShutdownSystem(
    VOID
    );

//
// Drive access routines.
//

#pragma pack(1)

typedef struct _INT13_DRIVE_PARAMETERS {
    UINT16 StructureSize;
    UINT16 InformationFlags;
    UINT32 NumberOfCylinders;
    UINT32 NumberOfHeads;
    UINT32 SectorsPerTrack;
    UINT64 TotalNumberOfSectors;
    UINT16 BytesPerSector;
} INT13_DRIVE_PARAMETERS, *PINT13_DRIVE_PARAMETERS;

C_ASSERT(sizeof(INT13_DRIVE_PARAMETERS) == 0x1A);

#pragma pack()

BOOLEAN
BlRtlGetDriveParameters(
    UINT8 DriveId,
    PINT13_DRIVE_PARAMETERS DriveParameters
    );

BOOLEAN
BlRtlReadDrive(
    UINT8 DriveId,
    UINT64 FirstBlock,
    UINT16 NumberOfBlocks,
    PVOID Buffer
    );

//
// I/O port access routines.
//

UINT8
BlRtlReadPort8(
    UINT16 Port
    );

UINT32
BlRtlReadPort32(
    UINT16 Port
    );

VOID
BlRtlWritePort8(
    UINT16 Port,
    UINT8 Value
    );

VOID
BlRtlWritePort32(
    UINT16 Port,
    UINT32 Value
    );

//
// String support.
//

CHAR
BlRtlConvertCharacterToUpperCase(
    CHAR C
    );

PCSTR
BlRtlFindSubstring(
    PCSTR String,
    PCSTR Substring
    );

BOOLEAN
BlRtlParsePositiveDecimal(
    PCSTR String,
    PUINT32 Number,
    PUINT32 CharactersConsumed
    );

BOOLEAN
BlRtlFormatString(
    PCHAR Output,
    UINT32 OutputSize,
    PCSTR Format,
    va_list ArgumentList
    );

UINT32
BlRtlStringLength(
    PCSTR String
    );

UINT32
BlRtlStringLengthW(
    PCWSTR String
    );

BOOLEAN
BlRtlEqualStringN(
    PCSTR String1,
    PCSTR String2,
    UINT32 Count
    );

BOOLEAN
BlRtlEqualStringI(
    PCSTR String1,
    PCSTR String2
    );

//
// Video support.
//

VOID
BlVideoPrintString(
    PCSTR String
    );

BOOLEAN
BlVideoPrintf(
    PCSTR Format,
    ...
    );

VOID
BlVideoInitialize(
    VOID
    );

//
// COM port support.
//

#define COM_MAX_PORT                    4

extern const UINT16 BlComBasePort[COM_MAX_PORT + 1];

BOOLEAN
BlComInitialize(
    UINT8 PortNumber,
    UINT32 BaudRate
    );

BOOLEAN
BlComSendByte(
    UINT8 PortNumber,
    UINT8 Byte
    );

BOOLEAN
BlComDataAvailable(
    UINT8 PortNumber
    );

UINT8
BlComReceiveByte(
    UINT8 PortNumber
    );

//
// KD support.
//

#define KD_RETRY_COUNT                      16

#define KD_PACKET_LEADER                    0x30303030
#define KD_CONTROL_PACKET_LEADER            0x69696969

#define KD_PACKET_TYPE_KD_DEBUG_IO          3
#define KD_PACKET_TYPE_KD_RESEND            5       // Packet-control type
#define KD_PACKET_TYPE_KD_RESET             6       // Packet-control type

#define KD_API_PRINT_STRING                 0x00003230

typedef struct _KD_PACKET {
    UINT32 PacketLeader;
    UINT16 PacketType;
    UINT16 ByteCount;
    UINT32 PacketId;
    UINT32 Checksum;
} KD_PACKET, *PKD_PACKET;

typedef struct _KD_PRINT_STRING {
    UINT32 LengthOfString;
} KD_PRINT_STRING, *PKD_PRINT_STRING;

typedef struct _KD_GET_STRING {
    UINT32 LengthOfPromptString;
    UINT32 LengthOfStringRead;
} KD_GET_STRING, *PKD_GET_STRING;

typedef struct _KD_DEBUG_IO {
    UINT32 ApiNumber;
    UINT16 ProcessorLevel;
    UINT16 Processor;
    union {
        KD_PRINT_STRING PrintString;
        KD_GET_STRING GetString;
    } u1;
} KD_DEBUG_IO, *PKD_DEBUG_IO;

extern UINT8 BlSingularityOhci1394Buffer[3 * PAGE_SIZE];

extern UINT8 BlKdComPort;

extern UINT32 BlKdNextPacketId;

VOID
BlKdInitialize(
    VOID
    );

VOID
BlKdSpin(
    VOID
    );

BOOLEAN
BlKdPrintString(
    PCSTR String
    );

BOOLEAN
BlKdPrintf(
    PCSTR Format,
    ...
    );

UINT32
BlKdComputeChecksum(
    PCVOID Buffer,
    UINT32 Length
    );

BOOLEAN
BlKd1394Connect(
    VOID
    );

BOOLEAN
BlKd1394SendPacket(
    UINT16 PacketType,
    PCVOID Header,
    UINT16 HeaderSize,
    PCVOID Data,
    UINT16 DataSize
    );

BOOLEAN
BlKdComConnect(
    VOID
    );

BOOLEAN
BlKdComSendPacket(
    UINT16 PacketType,
    PCVOID Header,
    UINT16 HeaderSize,
    PCVOID Data,
    UINT16 DataSize
    );

//
// System memory map (SMAP) support.
//

#define BL_SMAP_AVAILABLE        1
#define BL_SMAP_RESERVED         2
#define BL_SMAP_ACPI_RECLAIM     3
#define BL_SMAP_ACPI_NVS         4
#define BL_SMAP_UNUSABLE         5
#define BL_SMAP_KERNEL_NONGC     6
#define BL_SMAP_KERNEL_STACK     7

typedef struct _BL_SMAP_ENTRY {
    UINT64 Base;
    UINT64 Size;
    UINT32 Type;
    UINT32 ExtendedAttributes;
} BL_SMAP_ENTRY, *PBL_SMAP_ENTRY;

#define BL_MAX_SMAP_ENTRIES 128

typedef struct _BL_SMAP {
    BL_SMAP_ENTRY Entry[BL_MAX_SMAP_ENTRIES];
    UINT32 EntryCount;
} BL_SMAP, *PBL_SMAP;

extern BL_SMAP BlSystemMemoryMap;

VOID
BlSmapInitialize(
    VOID
    );

//
// Pool support.
//

VOID
BlPoolInitialize(
    VOID
    );

PVOID
BlPoolAllocateBlock(
    UINT32 Size
    );

VOID
BlPoolFreeBlock(
    PVOID P
    );

//
// PNP BIOS support.
//

#pragma pack(1)

typedef struct _PNP_INSTALLATION_CHECK {
    CHAR Signature[4];
    UINT8 Version;
    UINT8 Length;
    UINT16 ControlField;
    UINT8 Checksum;
    UINT32 EventNotificationFlagAddress;
    UINT16 RealModeCodeOffset16;
    UINT16 RealModeCodeSegment16;
    UINT16 ProtectedModeCodeOffset16;
    UINT32 ProtectedModeCodeSegmentBase32;
    UINT32 OEMDeviceId;
    UINT16 RealModeDataSegment16;
    UINT32 ProtectedModeDataSegmentBase32;
} PNP_INSTALLATION_CHECK, *PPNP_INSTALLATION_CHECK;

C_ASSERT(sizeof(PNP_INSTALLATION_CHECK) == 0x21);

typedef struct _PNP_SYSTEM_DEVICE_NODE {
    UINT16 Size;
    UINT8 Handle;
    UINT32 ProductId;
    UINT8 DeviceTypeCode[3];
    UINT16 DeviceNodeAttributes;
} PNP_SYSTEM_DEVICE_NODE, *PPNP_SYSTEM_DEVICE_NODE;

typedef struct _PNP_ISA_CONFIGURATION {
    UINT8 Revision;
    UINT8 NumberOfCardSelectNumbers;
    UINT16 DataReadPort;
    UINT16 Reserved;
} PNP_ISA_CONFIGURATION, *PPNP_ISA_CONFIGURATION;

#pragma pack()

extern PPNP_SYSTEM_DEVICE_NODE BlPnpSystemDeviceNodeList;
extern UINT32 BlPnpSystemDeviceNodeListSize;
extern PNP_ISA_CONFIGURATION BlPnpIsaConfiguration;

VOID
BlPnpInitialize(
    VOID
    );

//
// PCI support.
//

typedef struct _PCI_INSTALLATION_CHECK {
    UINT32 Eax;
    UINT32 Ebx;
    UINT32 Ecx;
    UINT32 Edx;
    UINT8 HardwareCharacteristics;
    UINT8 MajorVersion;
    UINT8 MinorVersion;
    UINT8 LastBusNumber;
    UINT32 ProtectedModeEntryPoint;
} PCI_INSTALLATION_CHECK, *PPCI_INSTALLATION_CHECK;

extern PCI_INSTALLATION_CHECK BlPciInstallationCheck;
extern UINT32 BlPciOhci1394BaseAddress;

VOID
BlPciInitialize(
    VOID
    );

//
// ACPI support.
//

extern UINT32 BlAcpiNumberOfProcessors;
extern PVOID BlAcpiRsdpAddress;

VOID
BlAcpiInitialize(
    VOID
    );

VOID
BlAcpiResetSystem(
    VOID
    );

//
// Segment management.
//

#define NULL_SELECTOR                0x0000
#define RM_VIDEO_SELECTOR            0x0008
#define RM_CODE_SELECTOR             0x0010
#define RM_DATA_SELECTOR             0x0018
#define PM_CODE_SELECTOR             0x0020
#define PM_DATA_SELECTOR             0x0028
#define LM_CODE_SELECTOR             0x0030
#define LM_DATA_SELECTOR             0x0038
#define UM_CODE_SELECTOR             0x0040
#define UM_DATA_SELECTOR             0x0048
#define PROCESSOR_SELECTOR           0x0050
#define UNUSED_SELECTOR              0x0058
#define TSS_SELECTOR                 0x0060

typedef struct _CODE_SEGMENT {
    UINT64 Limit_15_0:16;
    UINT64 Base_23_0:24;
    UINT64 Accessed:1;
    UINT64 Readable:1;
    UINT64 Conforming:1;
    UINT64 Code:1;
    UINT64 S:1;
    UINT64 Dpl:2;
    UINT64 Present:1;
    UINT64 Limit_19_16:4;
    UINT64 Unused:1;
    UINT64 Long:1;
    UINT64 Default:1;
    UINT64 Granularity:1;
    UINT64 Base_31_24:8;
} CODE_SEGMENT, *PCODE_SEGMENT;

typedef struct _DATA_SEGMENT {
    UINT64 Limit_15_0:16;
    UINT64 Base_23_0:24;
    UINT64 Accessed:1;
    UINT64 Writable:1;
    UINT64 Expansion:1;
    UINT64 Code:1;
    UINT64 S:1;
    UINT64 Dpl:2;
    UINT64 Present:1;
    UINT64 Limit_19_16:4;
    UINT64 Unused:1;
    UINT64 Reserved:1;
    UINT64 Big:1;
    UINT64 Granularity:1;
    UINT64 Base_31_24:8;
} DATA_SEGMENT, *PDATA_SEGMENT;

#define SSDT_AVAILABLE_TSS  0x09
#define SSDT_BUSY_TSS       0x0B

typedef struct _SYSTEM_SEGMENT {
    UINT64 Limit_15_0:16;
    UINT64 Base_23_0:24;
    UINT64 Type:4;
    UINT64 S:1;
    UINT64 Dpl:2;
    UINT64 Present:1;
    UINT64 Limit_19_16:4;
    UINT64 Unused:1;
    UINT64 Reserved1:2;
    UINT64 Granularity:1;
    UINT64 Base_31_24:8;
#if defined(BOOT_X64)
    UINT64 Base_63_32:32;
    UINT64 Reserved2:32;
#endif
} SYSTEM_SEGMENT, *PSYSTEM_SEGMENT;

#pragma pack(1)

typedef struct _GDTR {
    UINT16 Limit;
    UINT64 Base;
} GDTR, *PGDTR;

C_ASSERT(sizeof(GDTR) == 10);

typedef struct _IDTR {
    UINT16 Limit;
    UINT64 Base;
} IDTR, *PIDTR;

C_ASSERT(sizeof(IDTR) == 10);

#pragma pack()

extern GDTR BlMmInitialGdtr;

ULONG_PTR
BlMmGetCr3(
    VOID
    );

VOID
BlMmSetCr3(
    ULONG_PTR Value
    );

VOID
BlFakeSKINIT(
    ULONG_PTR Value
    );

VOID
BlRealSKINIT(
    ULONG_PTR Value
    );

#if defined(BOOT_X86)

UINT16
BlMmGetFs(
    VOID
    );

VOID
BlMmSetFs(
    UINT16 Value
    );

#elif defined(BOOT_X64)

UINT16
BlMmGetGs(
    VOID
    );

VOID
BlMmSetGs(
    UINT16 Value
    );

#endif

VOID
BlMmSwitchStack(
    PVOID Stack,
    PVOID Function
    );

VOID
BlMmGetGdtr(
    PGDTR Gdtr
    );

VOID
BlMmSetGdtr(
    PGDTR Gdtr
    );

VOID
BlMmInitializeCodeSegment(
    PCODE_SEGMENT CodeSegment
    );

VOID
BlMmInitializeDataSegment(
    PDATA_SEGMENT DataSegment,
    UINT32 Base,
    UINT32 Limit
    );

VOID
BlMmInitializeSystemSegment(
    PSYSTEM_SEGMENT SystemSegment,
    UINT32 Type,
    ULONG_PTR Base,
    UINT32 Limit
    );

//
// Memory management.
//

#define PAGE_PRESENT                        ((UINT64) 0x01)
#define PAGE_WRITEABLE                      ((UINT64) 0x02)
#define PAGE_WRITETHROUGH                   ((UINT64) 0x08)
#define PAGE_CACHEDISABLE                   ((UINT64) 0x10)
#define PAGE_ACCESSED                       ((UINT64) 0x20)
#define PAGE_2MB                            ((UINT64) 0x80)

#define BL_MM_PHYSICAL_REGION_MIN_TYPE                      0x00000001
#define BL_MM_PHYSICAL_REGION_FREE                          0x00000001
#define BL_MM_PHYSICAL_REGION_BIOS                          0x00000002
#define BL_MM_PHYSICAL_REGION_BOOT_LOADER                   0x00000003
#define BL_MM_PHYSICAL_REGION_SMAP_RESERVED                 0x00000004
#define BL_MM_PHYSICAL_REGION_DISTRO                        0x00000005
#define BL_MM_PHYSICAL_REGION_KERNEL_IMAGE                  0x00000006
#define BL_MM_PHYSICAL_REGION_NATIVE_PLATFORM               0x00000007
#define BL_MM_PHYSICAL_REGION_NATIVE_PROCESSOR              0x00000008
#define BL_MM_PHYSICAL_REGION_LOG_RECORD                    0x00000009
#define BL_MM_PHYSICAL_REGION_LOG_TEXT                      0x0000000A
#define BL_MM_PHYSICAL_REGION_KERNEL_STACK                  0x0000000B
#define BL_MM_PHYSICAL_REGION_CONTEXT                       0x0000000C
#define BL_MM_PHYSICAL_REGION_TASK                          0x0000000D
#define BL_MM_PHYSICAL_REGION_SINGULARITY                   0x0000000E
#define BL_MM_PHYSICAL_REGION_BOOT_STACK                    0x0000000F
#define BL_MM_PHYSICAL_REGION_SINGULARITY_SMAP              0x00000010
#define BL_MM_PHYSICAL_REGION_MAX_TYPE                      0x00000010

#define BL_MM_BIOS_SIZE                         (1024 * 1024)

typedef struct _BL_MM_PHYSICAL_REGION {
    LIST_ENTRY Entry;
    UINT64 Start;
    UINT64 Size;
    UINT64 Limit;
    UINT32 Type;
} BL_MM_PHYSICAL_REGION, *PBL_MM_PHYSICAL_REGION;

extern ULONG_PTR BlMmBootCr3;

VOID
BlMmEnableA20Gate(
    VOID
    );

VOID
BlMmInitializeSystem(
    VOID
    );

PCHAR
BlMmPhysicalRegionTypeString(
    UINT32 Type
    );

UINT64
BlMmAllocatePhysicalRegion(
    UINT32 Size,
    UINT32 Type
    );

BOOLEAN
BlMmAllocateSpecificPhysicalRegion(
    UINT64 Base,
    UINT64 Size,
    UINT32 Type
    );

BOOLEAN
BlMmFindFreePhysicalRegion(
    PUINT64 Base,
    PUINT64 Size
    );

BOOLEAN
BlMmGetNextPhysicalRegion(
    PVOID *Handle,
    PUINT64 Base,
    PUINT64 Size,
    PUINT32 Type
    );

VOID
BlMmDumpPhysicalRegionList(
    VOID
    );

VOID
BlMmMapVirtualPage(
    PVOID VirtualAddress,
    PVOID PhysicalAddress,
    BOOLEAN Writeable,
    BOOLEAN Cacheable,
    BOOLEAN WriteThrough
    );

VOID
BlMmMapVirtualRange(
    PVOID VirtualAddress,
    PVOID PhysicalAddress,
    ULONG_PTR Size,
    BOOLEAN Writeable,
    BOOLEAN Cacheable,
    BOOLEAN WriteThrough
    );

extern PVOID BlMmExtendedBiosDataArea;

//
// File system support.
//

extern
BOOLEAN
(*BlFsGetFileSize)(
    PCSTR Path,
    PUINT32 FileSize
    );

extern
BOOLEAN
(*BlFsReadFile)(
    PCSTR Path,
    PVOID Buffer,
    UINT32 NumberOfBytes
    );

//
// CDROM support.
//

VOID
BlCdInitialize(
    UINT8 DriveId
    );

//
// FAT support.
//

#define MBR_FAT32LBA                    0x0C
#define MBR_FAT16LBA                    0x0E

VOID
BlFatInitialize(
    UINT8 DriveId,
    UINT8 FatType
    );

//
// Flash support.
//

VOID
BlFlashInitialize(
    PVOID SearchBegin,
    PVOID SearchLimit
    );

//
// PXE support.
//

VOID
BlPxeInitialize(
    VOID
    );

//
// PE/COFF support.
//

VOID
BlPeGetVirtualRange(
    PVOID Image,
    PVOID *VirtualBase,
    ULONG_PTR *VirtualSize
    );

VOID
BlPeLoadImage(
    PVOID LoadBase,
    UINT32 ImageSize,
    PVOID Image,
    PVOID *EntryPoint,
    BOOLEAN isSLB
    );

//
// RTC support.
//

typedef struct _BL_TIME {
    UINT32 Year;
    UINT8 Month;
    UINT8 Day;
    UINT8 Hour;
    UINT8 Minute;
    UINT8 Second;
} BL_TIME, *PBL_TIME;

VOID
BlRtlGetCurrentTime(
    PBL_TIME Time
    );

extern BL_TIME BlStartTime;

//
// MPS support.
//

VOID
BlMpsInitialize(
    VOID
    );

extern PVOID BlMpsFps;

//
// VESA Support.
//

BOOLEAN
BlVesaInitialize(
    VOID
    );

extern ULONG_PTR BlVesaVideoBuffer;

//
// Call stack support.
//

#if defined(BOOT_X86)

PVOID
BlRtlGetEbp(
    VOID
    );

#elif defined(BOOT_X64)

PVOID
BlRtlGetRbp(
    VOID
    );

#endif

VOID
BlRtlCaptureCallStack(
    PVOID *FrameArray,
    UINT32 FrameCount
    );

//
// Trap Support.
//

typedef struct _BL_TRAP_CONTEXT {

#if defined(BOOT_X86)

    UINT32  Cr2;
    UINT32  Esp;
    UINT32  Ebp;
    UINT32  Edi;
    UINT32  Esi;
    UINT32  Edx;
    UINT32  Ecx;
    UINT32  Ebx;
    UINT32  Eax;
    UINT32  Num;
    UINT32  Err;
    UINT32  Eip;
    UINT32  Cs0;
    UINT32  Efl;

#elif defined (BOOT_X64)

    UINT64  Cr2;
    UINT64  Rsp;
    UINT64  R15;
    UINT64  R14;
    UINT64  R13;
    UINT64  R12;
    UINT64  R11;
    UINT64  R10;
    UINT64  R9;
    UINT64  R8;
    UINT64  Rbp;
    UINT64  Rdi;
    UINT64  Rsi;
    UINT64  Rdx;
    UINT64  Rcx;
    UINT64  Rbx;
    UINT64  Rax;
    UINT64  Num;
    UINT64  Err;
    UINT64  Rip;
    UINT64  Cs0;
    UINT64  Rfl;

#endif

} BL_TRAP_CONTEXT, *PBL_TRAP_CONTEXT;

typedef struct _IDTE {

    UINT16  Offset0To15;
    UINT16  Selector;
    UINT8   Flags;
    UINT8   Access;
    UINT16  Offset16To31;

#if defined(BOOT_X64)

    UINT32  Offset32To63;
    UINT32  Reserved;

#endif

} IDTE, *PIDTE;


VOID
BlTrapEnable(
    VOID
    );

VOID
BlTrapEnter(
    VOID
    );

VOID
BlTrapFatal(
    UINT32 Trap,
    PBL_TRAP_CONTEXT Context
    );

VOID
BlTrapSetIdtr(
    PIDTR Idtr
    );


//
// Singularity bridge.
//

extern PWCHAR BlCommandLine;

VOID
BlSingularityInitialize(
    UINT32 NumberOfProcessors,
    PFAR_POINTER ApEntry16,
    PFAR_POINTER ApStartupLock
    );

VOID
BlSingularityApEntry(
    VOID
    );

extern "C" void * _ReturnAddress(void);

#pragma intrinsic(_ReturnAddress)

