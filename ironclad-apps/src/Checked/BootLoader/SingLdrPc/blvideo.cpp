//++
//
//  Copyright (c) Microsoft Corporation
//
//  Module Name:
//
//    blvideo.cpp
//
//  Abstract:
//
//    This module implements basic video support for the boot loader.
//
//--

#include "bl.h"

#define BL_VIDEO_ROW_COUNT              50
#define BL_VIDEO_COL_COUNT              80
#define BL_VIDEO_DEFAULT_ATTRIBUTE      0x1F00

#define BL_VIDEO_REGISTER_INDEX_PORT    0x3D4
#define BL_VIDEO_REGISTER_DATA_PORT     0x3D5

#define BL_VIDEO_REGISTER_CURSOR_LOW    0x0F
#define BL_VIDEO_REGISTER_CURSOR_HIGH   0x0E

#define BL_VIDEO_BASE_ADDRESS           ((ULONG_PTR) 0x000B8000)

PUINT16 BlVideoBuffer = (PUINT16) BL_VIDEO_BASE_ADDRESS;
UINT16 BlVideoCursorPosition;
UINT16 BlVideoDefaultAttribute = BL_VIDEO_DEFAULT_ATTRIBUTE;

VOID
BlVideoSetCursorPosition(
    UINT16 X,
    UINT16 Y
    )

//++
//
//  Routine Description:
//
//    This function sets the cursor position.
//
//  Arguments:
//
//    X   - Supplies the X coordinate for the cursor.
//
//    Y   - Supplies the Y coordinate for the cursor.
//
//--

{
    BlVideoCursorPosition = (Y * BL_VIDEO_COL_COUNT) + X;

    BlRtlWritePort8(BL_VIDEO_REGISTER_INDEX_PORT, BL_VIDEO_REGISTER_CURSOR_HIGH);
    BlRtlWritePort8(BL_VIDEO_REGISTER_DATA_PORT, (UINT8) (BlVideoCursorPosition >> 8));

    BlRtlWritePort8(BL_VIDEO_REGISTER_INDEX_PORT, BL_VIDEO_REGISTER_CURSOR_LOW);
    BlRtlWritePort8(BL_VIDEO_REGISTER_DATA_PORT, (UINT8) (BlVideoCursorPosition & 0xFF));
}

VOID
BlVideoGetCursorPosition(
    PUINT16 X,
    PUINT16 Y
    )

//++
//
//  Routine Description:
//
//    This function gets the cursor position.
//
//  Arguments:
//
//    X   - Supplies a pointer to the variable that will receive the X coordinate.
//
//    Y   - Supplies a pointer to the variable that will receive the Y coordinate.
//
//--

{
    *X = BlVideoCursorPosition % BL_VIDEO_COL_COUNT;
    *Y = BlVideoCursorPosition / BL_VIDEO_COL_COUNT;
}

VOID
BlVideoWriteCurrentCharacter(
    UINT8 Character
    )

//++
//
//  Routine Description:
//
//    This function writes the current character (i.e. the character under the cursor).
//
//  Arguments:
//
//    Character   - Supplies the character to write.
//
//--

{
    UINT16 X;
    UINT16 Y;

    BlVideoGetCursorPosition(&X, &Y);

    BlVideoBuffer[(Y * BL_VIDEO_COL_COUNT) + X] = BlVideoDefaultAttribute | Character;
}

VOID
BlVideoScrollUpWindow(
    UINT8 NumberOfLines
    )

//++
//
//  Routine Description:
//
//    This function scrolls up the specified window.
//
//  Arguments:
//
//    NumberOfLines   - Supplies the number of lines to scroll.
//
//--

{
    UINT16 Delta;
    UINT16 Index;
    UINT16 Limit;

    Limit = BL_VIDEO_COL_COUNT * BL_VIDEO_ROW_COUNT;

    Delta = NumberOfLines * BL_VIDEO_COL_COUNT;

    if (Delta > Limit) {

        Delta = Limit;
    }

    for (Index = Delta; Index < Limit; Index += 1) {

        BlVideoBuffer[Index - Delta] = BlVideoBuffer[Index];
    }

    for (Index = Limit - Delta; Index < Limit; Index += 1) {

        BlVideoBuffer[Index] = BlVideoDefaultAttribute | ' ';
    }
}

VOID
BlVideoPrintCharacter(
    UINT8 Character
    )

//++
//
//  Routine Description:
//
//    This function prints the specified character and advances the cursor.
//
//  Arguments:
//
//    Character   - Supplies the character to print.
//
//--

{
    UINT16 X;
    UINT16 Y;

    BlVideoGetCursorPosition(&X, &Y);

    switch (Character) {

        case '\f': {

            X = 0;
            Y = 0;
            BlVideoInitialize();
            break;
        }

        case '\r': {

            X = 0;
            break;
        }

        case '\n': {

            X = BL_VIDEO_COL_COUNT;
            break;
        }

        default: {

            BlVideoWriteCurrentCharacter(Character);
            X += 1;
        }
    }



    if (X == BL_VIDEO_COL_COUNT) {

        X = 0;
        Y += 1;
    }

    if (Y == BL_VIDEO_ROW_COUNT) {

        BlVideoScrollUpWindow(1);

        Y = BL_VIDEO_ROW_COUNT - 1;
    }

    BlVideoSetCursorPosition(X, Y);
}

VOID
BlVideoPrintString(
    PCSTR String
    )

//++
//
//  Routine Description:
//
//    This function prints the specified string and advances the cursor.
//
//  Arguments:
//
//    String  - Supplies a pointer to the string to print.
//
//--

{
    PCSTR Next;

    Next = String;

    while (*Next != 0) {

        BlVideoPrintCharacter(*Next);
        Next += 1;
    }
}

BOOLEAN
BlVideoPrintf(
    PCSTR Format,
    ...
    )

//++
//
//  Routine Description:
//
//    This function prints out a string.
//
//  Arguments:
//
//    Format          - Supplies the format string.
//
//    ...             - Supplies the input parameters.
//
//  Return Value:
//
//    TRUE, if operation was successful.
//    FALSE, otherwise.
//
//--

{
    va_list ArgumentList;
    CHAR Buffer[4096];

    va_start(ArgumentList, Format);

    if (BlRtlFormatString(Buffer,
                          sizeof(Buffer),
                          Format,
                          ArgumentList) == FALSE) {

        return FALSE;
    }

    BlVideoPrintString(Buffer);

    return TRUE;
}

VOID
BlVideoInitialize(
    VOID
    )

//++
//
//  Routine Description:
//
//    This function initializes video support for the boot loader.
//
//--

{
    UINT16 Index;
    UINT16 Limit;

    Limit = BL_VIDEO_COL_COUNT * BL_VIDEO_ROW_COUNT;

    for (Index = 0; Index < Limit; Index += 1) {

        BlVideoBuffer[Index] = BlVideoDefaultAttribute | ' ';
    }

    BlVideoSetCursorPosition(0, 0);
}

