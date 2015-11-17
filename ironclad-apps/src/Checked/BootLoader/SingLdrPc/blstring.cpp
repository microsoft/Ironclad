//++
//
//  Copyright (c) Microsoft Corporation
//
//  Module Name:
//
//    blstring.cpp
//
//  Abstract:
//
//    This module implements string functions for the boot loader environment.
//
//--

#include "bl.h"

#define ABS(X)                          (((X) < 0) ? (-(X)) : (X))

#define STRING_TOKEN_LONG               1
#define STRING_TOKEN_ULONG              2
#define STRING_TOKEN_ULONG_HEX          3
#define STRING_TOKEN_LONGLONG           4
#define STRING_TOKEN_ULONGLONG          5
#define STRING_TOKEN_ULONGLONG_HEX      6
#define STRING_TOKEN_PVOID              7
#define STRING_TOKEN_PCHAR              8
#define STRING_TOKEN_CHAR               9

CHAR
BlRtlConvertCharacterToUpperCase(
    CHAR C
    )

//++
//
//  Routine Description:
//
//    This function converts the specified character to upper case.
//
//  Arguments:
//
//    C   - Supplies the character to convert.
//
//  Return Value:
//
//    Upper case character matching the specified character.
//
//--

{
    if ((C >= 'a') && (C <= 'z')) {

        return C + 'A' - 'a';
    }

    return C;
}

BOOLEAN
BlRtlParsePositiveDecimal(
    PCSTR String,
    PUINT32 Number,
    PUINT32 CharactersConsumed
    )

//++
//
//  Routine Description:
//
//    This function parses a positive decimal value.
//
//  Arguments:
//
//    String              - Supplies a pointer to the string to parse.
//
//    Number              - Receives the number.
//
//    CharactersConsumed  - Receives the number of characters consumed.
//
//
//  Return Value:
//
//    TRUE, if parse was successful.
//    FALSE, otherwise.
//
//--

{
    UINT32 Digit;
    UINT32 Index;
    UINT32 Temp;

    if ((String[0] < '0') || (String[0] > '9')) {

        return FALSE;
    }

    Index = 0;
    Temp = 0;

    for (;;) {

        if ((String[Index] < '0') || (String[Index] > '9')) {

            *Number = Temp;
            *CharactersConsumed = Index;
            return TRUE;
        }

        Digit = String[Index] - '0';

        if (((Temp * 10) + Digit) < Temp) {

            return FALSE;
        }

        Temp = (Temp * 10) + Digit;
        Index += 1;
    }
}

BOOLEAN
BlRtlParseTypeSpecifier(
    PCSTR String,
    PINT32 Width,
    PCHAR PadCharacter,
    PUINT8 TokenType,
    PUINT32 CharactersConsumed
    )

//++
//
//  Routine Description:
//
//    This function parses a type specifier.
//
//  Arguments:
//
//    String              - Supplies a pointer to the string to parse.
//
//    Width               - Receives the width.
//
//    PadCharacter        - Receives the pad character.
//
//    TokenType           - Receives the token type.
//
//    CharactersConsumed  - Receives the number of characters consumed.
//
//
//  Return Value:
//
//    TRUE, if parse was successful.
//    FALSE, otherwise.
//
//--

{
    UINT32 Advance;
    BOOLEAN WidthPresent;
    UINT32 Index;
    BOOLEAN Minus;
    UINT32 WidthPositiveValue;
    BOOLEAN Zero;

    SATISFY_OVERZEALOUS_COMPILER(WidthPositiveValue = 0);

    //
    // Check if type specifier character is present.
    //

    if (String[0] != '%') {

        return FALSE;
    }

    Index = 1;

    //
    // Check for pad modifiers.
    //

    Minus = FALSE;
    Zero = FALSE;

    for (;;) {

        if (String[Index] == '-') {

            if (Minus != FALSE) {

                return FALSE;
            }

            Minus = TRUE;
            Index += 1;

        } else if (String[Index] == '0') {

            if (Zero != FALSE) {

                return FALSE;
            }

            Zero = TRUE;
            Index += 1;

        } else {

            break;
        }
    }

    //
    // - and 0 pad modifiers are mutually exclusive.
    //

    if ((Minus != FALSE) && (Zero != FALSE)) {

        return FALSE;
    }

    //
    // If there is a width value, then parse it.
    //

    WidthPresent = ((String[Index] >= '1') && (String[Index] <= '9'));

    if (WidthPresent != FALSE) {

        if (BlRtlParsePositiveDecimal(&String[Index],
                                      &WidthPositiveValue,
                                      &Advance) == FALSE) {

            return FALSE;
        }

        Index += Advance;
    }

    //
    // Pad modifiers require width value.
    //

    if (((Minus != FALSE) || (Zero != FALSE)) && (WidthPresent == FALSE)) {

        return FALSE;
    }

    //
    // Set pad character.
    //

    if (Zero != FALSE) {

        *PadCharacter = '0';

    } else {

        *PadCharacter = ' ';
    }

    //
    // Compute signed width value.
    //

    if (WidthPresent == FALSE) {

        *Width = 0;

    } else if (Minus == FALSE) {

        *Width = (INT32) WidthPositiveValue;

    } else {

        *Width = -((INT32) WidthPositiveValue);
    }

    //
    // Set type character.
    //

    if (BlRtlEqualStringN(&String[Index], "d", 1) != FALSE) {

        *TokenType = STRING_TOKEN_LONG;
        Index += 1;

    } else if (BlRtlEqualStringN(&String[Index], "u", 1) != FALSE) {

        *TokenType = STRING_TOKEN_ULONG;
        Index += 1;

    } else if (BlRtlEqualStringN(&String[Index], "x", 1) != FALSE) {

        *TokenType = STRING_TOKEN_ULONG_HEX;
        Index += 1;

    } else if (BlRtlEqualStringN(&String[Index], "I64d", 4) != FALSE) {

        *TokenType = STRING_TOKEN_LONGLONG;
        Index += 4;

    } else if (BlRtlEqualStringN(&String[Index], "I64u", 4) != FALSE) {

        *TokenType = STRING_TOKEN_ULONGLONG;
        Index += 4;

    } else if (BlRtlEqualStringN(&String[Index], "I64x", 4) != FALSE) {

        *TokenType = STRING_TOKEN_ULONGLONG_HEX;
        Index += 4;

    } else if (BlRtlEqualStringN(&String[Index], "p", 1) != FALSE) {

        *TokenType = STRING_TOKEN_PVOID;
        Index += 1;

    } else if (BlRtlEqualStringN(&String[Index], "s", 1) != FALSE) {

        *TokenType = STRING_TOKEN_PCHAR;
        Index += 1;

    } else if (BlRtlEqualStringN(&String[Index], "c", 1) != FALSE) {

        *TokenType = STRING_TOKEN_CHAR;
        Index += 1;

    } else {

        return FALSE;
    }

    //
    // Set number of characters consumed.
    //

    *CharactersConsumed = Index;

    return TRUE;
}

BOOLEAN
BlRtlFormatSignedDecimalLong(
    PCHAR Output,
    UINT32 OutputSize,
    INT32 Value,
    INT32 Width,
    PUINT32 CharactersConsumed
    )

//++
//
//  Routine Description:
//
//    This function formats a signed decimal long.
//
//  Arguments:
//
//    Output              - Supplies a pointer to the output buffer.
//
//    OutputSize          - Supplies the size of the output buffer.
//
//    Value               - Supplies the value to format.
//
//    Width               - Supplies the width.
//
//    CharactersConsumed  - Receives the number of characters consumed.
//
//
//  Return Value:
//
//    TRUE, if format was successful.
//    FALSE, otherwise.
//
//--

{
    UINT32 Index;
    UINT32 MinimumWidth;
    BOOLEAN Minus;
    UINT32 NumberWidth;
    UINT32 PadWidth;
    UINT32 Temp;

    //
    // Check if this is a negative value.
    //

    Minus = (BOOLEAN) (Value < 0);

    //
    // Compute the number of characters necessary.
    //

    Temp = ABS(Value);
    NumberWidth = 0;

    do {

        NumberWidth += 1;
        Temp = Temp / 10;

    } while (Temp > 0);

    if (Minus != FALSE) {

        NumberWidth += 1;
    }

    PadWidth = 0;
    MinimumWidth = ABS(Width);

    if (MinimumWidth > NumberWidth) {

        PadWidth = MinimumWidth - NumberWidth;
    }

    //
    // Check if there is sufficient space in the output buffer.
    //

    if ((NumberWidth + PadWidth) > OutputSize) {

        return FALSE;
    }

    Index = 0;

    //
    // If right alignment is specified, then insert any necessary pads before the number.
    //

    if (Width > 0) {

        while (PadWidth > 0) {

            Output[Index] = ' ';
            Index += 1;
            PadWidth -= 1;
        }
    }

    //
    // Insert absolute number starting with the least significant digit, going right to left.
    //

    Temp = ABS(Value);
    Index += NumberWidth;

    do {

        Index -= 1;
        Output[Index] = (CHAR) ('0' + (Temp % 10));
        Temp = Temp / 10;

    } while (Temp > 0);

    //
    // If the number is negative, then insert the negative sign.
    //

    if (Minus != FALSE) {

        Index -= 1;
        Output[Index] = '-';
    }

    //
    // If left alignment was specified, then insert any necessary pads after the number.
    //

    Index += NumberWidth;

    while (PadWidth > 0) {

        Output[Index] = ' ';
        Index += 1;
        PadWidth -= 1;
    }

    //
    // Set number of characters consumed in the buffer.
    //

    *CharactersConsumed = Index;

    return TRUE;
}

BOOLEAN
BlRtlFormatUnsignedLong(
    PCHAR Output,
    UINT32 OutputSize,
    UINT32 Value,
    UINT8 PadCharacter,
    INT32 Width,
    UINT32 Base,
    PUINT32 CharactersConsumed
    )

//++
//
//  Routine Description:
//
//    This function formats an unsigned long.
//
//  Arguments:
//
//    Output              - Supplies a pointer to the output buffer.
//
//    OutputSize          - Supplies the size of the output buffer.
//
//    Value               - Supplies the value to format.
//
//    PadCharacter        - Supplies the pad character.
//
//    Width               - Supplies the width.
//
//    Base                - Supplies the base.
//
//    CharactersConsumed  - Receives the number of characters consumed.
//
//
//  Return Value:
//
//    TRUE, if format was successful.
//    FALSE, otherwise.
//
//--

{
    UINT32 Index;
    UINT32 MinimumWidth;
    UINT32 NumberWidth;
    UINT32 PadWidth;
    UINT32 Temp;

    if (Base == 0) {

        return FALSE;
    }

    //
    // Compute the number of characters necessary.
    //

    Temp = Value;
    NumberWidth = 0;

    do {

        NumberWidth += 1;
        Temp = Temp / Base;

    } while (Temp > 0);

    PadWidth = 0;
    MinimumWidth = ABS(Width);

    if (MinimumWidth > NumberWidth) {

        PadWidth = MinimumWidth - NumberWidth;
    }

    //
    // Check if there is sufficient space in the output buffer.
    //

    if ((NumberWidth + PadWidth) > OutputSize) {

        return FALSE;
    }

    Index = 0;

    //
    // If right alignment is specified, then insert any necessary pads before the number.
    //

    if (Width > 0) {

        while (PadWidth > 0) {

            Output[Index] = PadCharacter;
            Index += 1;
            PadWidth -= 1;
        }
    }

    //
    // Insert absolute number starting with the least significant digit, going right to left.
    //

    Temp = Value;
    Index += NumberWidth;

    do {

        Index -= 1;

        switch (Base) {

            case 10: {

                Output[Index] = (CHAR) ('0' + (Temp % Base));
                break;
            }

            case 16: {

                if ((Temp % Base) < 10) {

                    Output[Index] = (CHAR) ('0' + (Temp % Base));

                } else {

                    Output[Index] = (CHAR) ('A' + (Temp % Base) - 10);
                }

                break;
            }

            default: {

                return FALSE;
            }
        }

        Temp = Temp / Base;

    } while (Temp > 0);

    //
    // If left alignment was specified, then insert any necessary pads after the number.
    //

    Index += NumberWidth;

    while (PadWidth > 0) {

        Output[Index] = PadCharacter;
        Index += 1;
        PadWidth -= 1;
    }

    //
    // Set number of characters consumed in the buffer.
    //

    *CharactersConsumed = Index;

    return TRUE;
}

BOOLEAN
BlRtlFormatUnsignedLongLong(
    PCHAR Output,
    UINT32 OutputSize,
    UINT64 Value,
    UINT8 PadCharacter,
    INT32 Width,
    UINT32 Base,
    PUINT32 CharactersConsumed
    )

//++
//
//  Routine Description:
//
//    This function formats an unsigned long long.
//
//  Arguments:
//
//    Output              - Supplies a pointer to the output buffer.
//
//    OutputSize          - Supplies the size of the output buffer.
//
//    Value               - Supplies the value to format.
//
//    PadCharacter        - Supplies the pad character.
//
//    Width               - Supplies the width.
//
//    Base                - Supplies the base.
//
//    CharactersConsumed  - Receives the number of characters consumed.
//
//
//  Return Value:
//
//    TRUE, if format was successful.
//    FALSE, otherwise.
//
//--

{
    UINT32 Index;
    UINT32 MinimumWidth;
    UINT32 NumberWidth;
    UINT32 PadWidth;
    UINT64 Temp;

    if (Base == 0) {

        return FALSE;
    }

    //
    // Compute the number of characters necessary.
    //

    Temp = Value;
    NumberWidth = 0;

    do {

        NumberWidth += 1;
        Temp = Temp / Base;

    } while (Temp > 0);

    PadWidth = 0;
    MinimumWidth = ABS(Width);

    if (MinimumWidth > NumberWidth) {

        PadWidth = MinimumWidth - NumberWidth;
    }

    //
    // Check if there is sufficient space in the output buffer.
    //

    if ((NumberWidth + PadWidth) > OutputSize) {

        return FALSE;
    }

    Index = 0;

    //
    // If right alignment is specified, then insert any necessary pads before the number.
    //

    if (Width > 0) {

        while (PadWidth > 0) {

            Output[Index] = PadCharacter;
            Index += 1;
            PadWidth -= 1;
        }
    }

    //
    // Insert absolute number starting with the least significant digit, going right to left.
    //

    Temp = Value;
    Index += NumberWidth;

    do {

        Index -= 1;

        switch (Base) {

            case 10: {

                Output[Index] = (CHAR) ('0' + (Temp % Base));
                break;
            }

            case 16: {

                if ((Temp % Base) < 10) {

                    Output[Index] = (CHAR) ('0' + (Temp % Base));

                } else {

                    Output[Index] = (CHAR) ('A' + (Temp % Base) - 10);
                }

                break;
            }

            default: {

                return FALSE;
            }
        }

        Temp = Temp / Base;

    } while (Temp > 0);

    //
    // If left alignment was specified, then insert any necessary pads after the number.
    //

    Index += NumberWidth;

    while (PadWidth > 0) {

        Output[Index] = PadCharacter;
        Index += 1;
        PadWidth -= 1;
    }

    //
    // Set number of characters consumed in the buffer.
    //

    *CharactersConsumed = Index;

    return TRUE;
}

UINT32
BlRtlStringLength(
    PCSTR String
    )

//++
//
//  Routine Description:
//
//    This function returns the length of the specified string.
//
//  Arguments:
//
//    String  - Supplies a pointer to the string.
//
//  Return Value:
//
//    Length of the string.
//
//--

{
    UINT32 Index;

    Index = 0;

    while (String[Index] != 0) {

        Index += 1;
    }

    return Index;
}

UINT32
BlRtlStringLengthW(
    PCWSTR String
    )

//++
//
//  Routine Description:
//
//    This function returns the length of the specified wide string.
//
//  Arguments:
//
//    String  - Supplies a pointer to the string.
//
//  Return Value:
//
//    Length of the string.
//
//--

{
    UINT32 Index;

    Index = 0;

    while (String[Index] != 0) {

        Index += 1;
    }

    return Index;
}

BOOLEAN
BlRtlFormatStringToken(
    PCHAR Output,
    UINT32 OutputSize,
    PCSTR String,
    INT32 Width,
    PUINT32 CharactersConsumed
    )

//++
//
//  Routine Description:
//
//    This function formats a string token.
//
//  Arguments:
//
//    Output              - Supplies a pointer to the output buffer.
//
//    OutputSize          - Supplies the size of the output buffer.
//
//    String              - Supplies the string token.
//
//    Width               - Supplies the width.
//
//    CharactersConsumed  - Receives the number of characters consumed.
//
//
//  Return Value:
//
//    TRUE, if format was successful.
//    FALSE, otherwise.
//
//--

{
    UINT32 Index;
    UINT32 MinimumWidth;
    UINT32 PadWidth;
    UINT32 StringIndex;
    UINT32 StringLength;

    //
    // Compute string length, minimum width, and pad width.
    //

    StringLength = BlRtlStringLength(String);

    MinimumWidth = ABS(Width);

    PadWidth = 0;

    if (MinimumWidth > StringLength) {

        PadWidth = MinimumWidth - StringLength;
    }

    //
    // Check if there is sufficient space in the output buffer.
    //

    if ((StringLength + PadWidth) > OutputSize) {

        return FALSE;
    }

    Index = 0;

    //
    // If right alignment is specified, then insert any necessary pads before the string.
    //

    if (Width > 0) {

        while (PadWidth > 0) {

            Output[Index] = ' ';
            Index += 1;
            PadWidth -= 1;
        }
    }

    //
    // Copy the string.
    //

    for (StringIndex = 0; StringIndex < StringLength; StringIndex += 1) {

        Output[Index] = String[StringIndex];
        Index += 1;
    }

    //
    // If left alignment was specified, then insert any necessary pads after the string.
    //

    while (PadWidth > 0) {

        Output[Index] = ' ';
        Index += 1;
        PadWidth -= 1;
    }

    //
    // Set number of characters consumed in the buffer.
    //

    *CharactersConsumed = Index;

    return TRUE;
}

BOOLEAN
BlRtlFormatChar(
    PCHAR Output,
    UINT32 OutputSize,
    CHAR Value,
    PUINT32 CharactersConsumed
    )

//++
//
//  Routine Description:
//
//    This function formats a character.
//
//  Arguments:
//
//    Output              - Supplies a pointer to the output buffer.
//
//    OutputSize          - Supplies the size of the output buffer.
//
//    Value               - Supplies the value to format.
//
//    CharactersConsumed  - Receives the number of characters consumed.
//
//
//  Return Value:
//
//    TRUE, if format was successful.
//    FALSE, otherwise.
//
//--

{
    //
    // Check if there is sufficient space in the output buffer.
    //

    if (1 > OutputSize) {

        return FALSE;
    }

    Output[0] = Value;

    //
    // Set number of characters consumed in the buffer.
    //

    *CharactersConsumed = 1;

    return TRUE;
}

BOOLEAN
BlRtlFormatString(
    PCHAR Output,
    UINT32 OutputSize,
    PCSTR Format,
    va_list ArgumentList
    )

//++
//
//  Routine Description:
//
//    This function formats a string.
//
//  Arguments:
//
//    Output          - Supplies a pointer to the output buffer.
//
//    OutputSize      - Supplies the size of the output buffer.
//
//    Format          - Supplies the format string.
//
//    ArgumentList    - Supplies the input parameters.
//
//  Return Value:
//
//    TRUE, if format was successful.
//    FALSE, otherwise.
//
//--

{
    UINT32 CharactersConsumed;
    UINT32 InputIndex;
    UINT32 OutputIndex;
    CHAR PadCharacter;
    UINT8 TokenType;
    INT32 Width;

    InputIndex = 0;
    OutputIndex = 0;

    for (;;) {

        if (OutputIndex == OutputSize) {

            return FALSE;
        }

        if (Format[InputIndex] == 0) {

            Output[OutputIndex] = 0;
            return TRUE;
        }

        if (Format[InputIndex] == '\\') {

            switch (Format[InputIndex + 1]) {

                case '\\': {

                    Output[OutputIndex] = '\\';
                    OutputIndex += 1;
                    break;
                }

                case 'r': {

                    Output[OutputIndex] = '\r';
                    OutputIndex += 1;
                    break;
                }

                case 'n': {

                    Output[OutputIndex] = '\r';
                    OutputIndex += 1;
                    break;
                }

                default: {

                    return FALSE;
                }
            }

            InputIndex += 2;
            continue;
        }

        if (BlRtlParseTypeSpecifier(&Format[InputIndex],
                                    &Width,
                                    &PadCharacter,
                                    &TokenType,
                                    &CharactersConsumed) != FALSE) {

            InputIndex += CharactersConsumed;

            switch (TokenType) {

                case STRING_TOKEN_LONG: {

                    if (BlRtlFormatSignedDecimalLong(&Output[OutputIndex],
                                                     OutputSize - OutputIndex,
                                                     va_arg(ArgumentList, INT32),
                                                     Width,
                                                     &CharactersConsumed) == FALSE) {

                        return FALSE;
                    }

                    OutputIndex += CharactersConsumed;
                    break;
                }

                case STRING_TOKEN_ULONG: {

                    if (BlRtlFormatUnsignedLong(&Output[OutputIndex],
                                                OutputSize - OutputIndex,
                                                va_arg(ArgumentList, UINT32),
                                                PadCharacter,
                                                Width,
                                                10,
                                                &CharactersConsumed) == FALSE) {

                        return FALSE;
                    }

                    OutputIndex += CharactersConsumed;
                    break;
                }

                case STRING_TOKEN_ULONG_HEX: {

                    if (BlRtlFormatUnsignedLong(&Output[OutputIndex],
                                                OutputSize - OutputIndex,
                                                va_arg(ArgumentList, UINT32),
                                                PadCharacter,
                                                Width,
                                                16,
                                                &CharactersConsumed) == FALSE) {

                        return FALSE;
                    }

                    OutputIndex += CharactersConsumed;
                    break;
                }

                case STRING_TOKEN_ULONGLONG: {

                    if (BlRtlFormatUnsignedLongLong(&Output[OutputIndex],
                                                    OutputSize - OutputIndex,
                                                    va_arg(ArgumentList, UINT64),
                                                    PadCharacter,
                                                    Width,
                                                    10,
                                                    &CharactersConsumed) == FALSE) {

                        return FALSE;
                    }

                    OutputIndex += CharactersConsumed;
                    break;
                }

                case STRING_TOKEN_ULONGLONG_HEX: {

                    if (BlRtlFormatUnsignedLongLong(&Output[OutputIndex],
                                                    OutputSize - OutputIndex,
                                                    va_arg(ArgumentList, UINT64),
                                                    PadCharacter,
                                                    Width,
                                                    16,
                                                    &CharactersConsumed) == FALSE) {

                        return FALSE;
                    }

                    OutputIndex += CharactersConsumed;
                    break;
                }

                case STRING_TOKEN_PVOID: {

#if defined(BOOT_X86)

                    if (BlRtlFormatUnsignedLong(&Output[OutputIndex],
                                                OutputSize - OutputIndex,
                                                va_arg(ArgumentList, UINT32),
                                                '0',
                                                8,
                                                16,
                                                &CharactersConsumed) == FALSE) {

                        return FALSE;
                    }

#elif defined(BOOT_X64)

                    if (BlRtlFormatUnsignedLongLong(&Output[OutputIndex],
                                                    OutputSize - OutputIndex,
                                                    va_arg(ArgumentList, UINT64),
                                                    '0',
                                                    16,
                                                    16,
                                                    &CharactersConsumed) == FALSE) {

                        return FALSE;
                    }

#endif

                    OutputIndex += CharactersConsumed;
                    break;
                }

                case STRING_TOKEN_PCHAR: {

                    if (BlRtlFormatStringToken(&Output[OutputIndex],
                                               OutputSize - OutputIndex,
                                               va_arg(ArgumentList, PCHAR),
                                               Width,
                                               &CharactersConsumed) == FALSE) {

                        return FALSE;
                    }

                    OutputIndex += CharactersConsumed;
                    break;
                }

                case STRING_TOKEN_CHAR: {

                    if (BlRtlFormatChar(&Output[OutputIndex],
                                        OutputSize - OutputIndex,
                                        va_arg(ArgumentList, CHAR),
                                        &CharactersConsumed) == FALSE) {

                        return FALSE;
                    }

                    OutputIndex += CharactersConsumed;
                    break;
                }
            }

            continue;
        }

        Output[OutputIndex] = Format[InputIndex];
        InputIndex += 1;
        OutputIndex += 1;
    }
}

BOOLEAN
BlRtlPrintf(
    PCSTR Format,
    ...
    )

//++
//
//  Routine Description:
//
//    This function implements C-style printf for the boot loader environment.
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

    if (BlRtlFormatString(Buffer, sizeof(Buffer), Format, ArgumentList) == FALSE) {

        return FALSE;
    }

    BlVideoPrintString(Buffer);

    BlKdPrintString(Buffer);

    return TRUE;
}

BOOLEAN
BlRtlEqualStringN(
    PCSTR String1,
    PCSTR String2,
    UINT32 Count
    )

//++
//
//  Routine Description:
//
//    This function compares two strings.
//
//  Arguments:
//
//    String1 - Supplies a pointer to the first string.
//
//    String2 - Supplies a pointer to the second string.
//
//    Count   - Number of characters to compare.
//
//  Return Value:
//
//    TRUE, if strings are equal.
//    FALSE, otherwise.
//
//--

{
    while (Count > 0) {

        if ((*String1 == 0) || (*String2 == 0)) {

            return FALSE;
        }

        if (*String1 != *String2) {

            return FALSE;
        }

        String1 += 1;
        String2 += 1;
        Count -= 1;
    }

    return TRUE;
}

BOOLEAN
BlRtlEqualStringI(
    PCSTR String1,
    PCSTR String2
    )

//++
//
//  Routine Description:
//
//    This function compares two strings ignoring case differences.
//
//  Arguments:
//
//    String1 - Supplies a pointer to the first string.
//
//    String2 - Supplies a pointer to the second string.
//
//  Return Value:
//
//    TRUE, if strings are equal.
//    FALSE, otherwise.
//
//--

{
    for (;;) {

        if (BlRtlConvertCharacterToUpperCase(*String1) != BlRtlConvertCharacterToUpperCase(*String2)) {

            return FALSE;
        }

        if (*String1 == 0) {

            return TRUE;
        }

        String1 += 1;
        String2 += 1;
    }
}

PCSTR
BlRtlFindSubstring(
    PCSTR String,
    PCSTR Substring
    )

//++
//
//  Routine Description:
//
//    This function searches for a substring.
//
//  Arguments:
//
//    String      - Supplies a pointer to the string to search in.
//
//    Substring   - Supplies a pointer to the substring to search for.
//
//  Return Value:
//
//    A pointer to the first instance of the substring, if search was successful.
//    NULL, otherwise.
//
//--

{
    UINT32 SubstringLength;

    SubstringLength = BlRtlStringLength(Substring);

    while (*String != 0) {

        if (BlRtlEqualStringN(String, Substring, SubstringLength) != FALSE) {

            return String;
        }

        String += 1;
    }

    return NULL;
}

