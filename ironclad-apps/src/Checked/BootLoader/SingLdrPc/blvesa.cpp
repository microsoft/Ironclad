//++
//
//  Copyright (c) Microsoft Corporation
//
//  Module Name:
//
//    blvesa.cpp
//
//  Abstract:
//
//    This module implements VESA grahics support for the boot loader.
//
//--

#include "bl.h"

#pragma pack(1)

typedef union __declspec(align(16)) _BL_VESA_INFO {
    struct {
        UINT8   Signature[4];
        UINT16  Version;
        FAR_POINTER Oem;    // LPCHAR
        UINT8   Capabilities[4];
        FAR_POINTER Modes;  // LPUSHORT
        UINT16  Memory;
    };
    UINT8 Raw[1024];
} BL_VESA_INFO, *PBL_VESA_INFO;

typedef union __declspec(align(16)) _BL_VESA_MODE {
    struct {
        UINT16  Attributes;
        UINT8   WindowA;
        UINT8   WindowB;
        UINT16  Granularity;
        UINT16  Size;
        UINT16  WindowASegment;
        UINT16  WindowBSegment;
        FAR_POINTER WindowFuncPtr;  // LPUCHAR
        UINT16  BytesPerLine;
        UINT16  XRes;
        UINT16  YRes;
        UINT8   XCharSize;
        UINT8   YCharSize;
        UINT8   Planes;
        UINT8   BitsPerPixel;
        UINT8   Banks;
        UINT8   MemoryModel;
        UINT8   BankSize;
        UINT8   ImagePages;
        UINT8   Reserved;
        UINT8   RedMaskSize;
        UINT8   RedFieldPos;
        UINT8   GreenMaskSize;
        UINT8   GreenFieldPos;
        UINT8   BlueMaskSize;
        UINT8   BlueFieldPos;
        UINT8   ReservedMaskSize;
        UINT8   ReservedFieldPos;
        UINT8   DirectColorInfo;

        // VBE 2.0
        UINT32   PhysBasePtr;
        UINT32   Reserved1;
        UINT16  Reserved2;
    };
    UINT8 Raw[1024];
} BL_VESA_MODE, *PBL_VESA_MODE;

#pragma pack()

BL_VESA_INFO BlVesaInfo;
BL_VESA_MODE BlVesaMode;
ULONG_PTR BlVesaVideoBuffer;

UINT32
BlVesaInvoke(
    UINT32 Ax,
    UINT32 Bx,
    UINT32 Cx,
    PVOID Buffer
    )
{
    ULONG_PTR Address;
    BL_LEGACY_CALL_CONTEXT Context;

    BlRtlZeroMemory(&Context, sizeof(Context));

    Context.eax = Ax;
    Context.ebx = Bx;
    Context.ecx = Cx;

    Address = (ULONG_PTR)Buffer;
    Context.es = (UINT32)(Address >> 4);
    Context.edi = (UINT32)(Address & 0xF);

    BlRtlCallLegacyInterruptService(0x10, &Context, &Context);

    return Context.eax;
}

BOOLEAN
BlVesaInitialize(
    VOID
    )
{
    UINT32 Returned;
    PUINT16 ModeList;
    UINT16 Mode;
    ULONG_PTR Video;

    //
    // Determine if a VESA video card is enabled.
    //

    BlRtlZeroMemory(&BlVesaInfo, sizeof(BlVesaInfo));

    Returned = BlVesaInvoke(0x4f00, 0, 0, &BlVesaInfo);

    if (Returned != 0x4f ||
        BlVesaInfo.Signature[0] != 'V' ||
        BlVesaInfo.Signature[1] != 'E' ||
        BlVesaInfo.Signature[2] != 'S' ||
        BlVesaInfo.Signature[3] != 'A' ||
        BlVesaInfo.Version < 0x200) {

        BlRtlPrintf("VESA: No VESA found.\n");
        return FALSE;
    }

    //
    // Print the VESA identification information.
    //

    BlRtlPrintf("VESA: %c%c%c%c V%x %s (%d MB)\n",
                BlVesaInfo.Signature[0],
                BlVesaInfo.Signature[1],
                BlVesaInfo.Signature[2],
                BlVesaInfo.Signature[3],
                BlVesaInfo.Version,
                (PCHAR) BlRtlConvertFarPointerToLinearPointer(&BlVesaInfo.Oem),
                BlVesaInfo.Memory / 16);

    //
    // Search list of modes for 1024 x 768 x 16.
    //

    ModeList = (PUINT16) BlRtlConvertFarPointerToLinearPointer((PFAR_POINTER) &BlVesaInfo.Modes);

    for (; *ModeList != 0xffff; ModeList++) {

        Mode = *ModeList;

        //
        // Query for the mode information.
        //

        BlRtlZeroMemory(&BlVesaMode, sizeof(BlVesaMode));

        Returned = BlVesaInvoke(0x4f01, 0, Mode, &BlVesaMode);

        if (Returned != 0x4f || BlVesaMode.BitsPerPixel > 8) {

            BlRtlPrintf("VESA: Mode %03x: Attr=%04x, Addr=%p Res=%dx%dx%d\n",
                        Mode,
                        BlVesaMode.Attributes,
                        (ULONG_PTR)BlVesaMode.PhysBasePtr,
                        BlVesaMode.XRes,
                        BlVesaMode.YRes,
                        BlVesaMode.BitsPerPixel);

            //
            // See if one of the modes suport 1024 x 768 x 16 bits.
            //

            if (BlVesaMode.XRes == 1024 &&
                BlVesaMode.YRes == 768 &&
                BlVesaMode.BitsPerPixel == 16) {

                Video = (ULONG_PTR)BlVesaMode.PhysBasePtr;
                BlRtlZeroMemory(&BlVesaMode, sizeof(BlVesaMode));

                if (Mode >= 0x100) {

                    Returned = BlVesaInvoke(0x4f02, 0x4000 | Mode, 0, &BlVesaMode);
                }
                else {

                    Returned = BlVesaInvoke(0x4f02, Mode, 0, &BlVesaMode);
                }

                if (Returned != 0x4f) {

                    BlRtlPrintf("    Couldn't enable Linear Frame Buffer.\n");
                    continue;
                }

                BlRtlPrintf("VESA: Select 1024 x 768 x 16 @ %p\n", Video);
                BlVesaVideoBuffer = Video;
            }
        }
    }

    if (BlVesaVideoBuffer != 0) {

        PUINT16 Buffer = (PUINT16)BlVesaVideoBuffer;
        INT32 i = 0;

        for (; i < 1 * 1024; i++) {

            Buffer[i] = 0xf800;
        }

        for (; i < 2 * 1024; i++) {

            Buffer[i] = 0x07e0;
        }

        for (; i < 3 * 1024; i++) {

            Buffer[i] = 0x001f;
        }

        for (; i < 4 * 1024; i++) {

            Buffer[i] = 0xffff;
        }
    }

    return FALSE;
}

