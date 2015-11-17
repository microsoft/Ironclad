//++
//
//  Copyright (c) Microsoft Corporation
//
//  Module Name:
//
//    blcom.cpp
//
//  Abstract:
//
//    This module implements COM port support for the boot loader.
//
//--

#include "bl.h"

#define COM1_ADDRESS                            0x3F8
#define COM2_ADDRESS                            0x2F8
#define COM3_ADDRESS                            0x3E8
#define COM4_ADDRESS                            0x2E8

const UINT16 BlComBasePort[COM_MAX_PORT + 1] = {
    0,
    COM1_ADDRESS,
    COM2_ADDRESS,
    COM3_ADDRESS,
    COM4_ADDRESS
};

#define COM_DATA_REGISTER                       0x0000
#define COM_INTERRUPT_ENABLE_REGISTER           0x0001
#define COM_INTERRUPT_IDENTIFICATION_REGISTER   0x0002
#define COM_FIFO_CONTROL_REGISTER               0x0002
#define COM_LINE_CONTROL_REGISTER               0x0003
#define COM_MODEM_CONTROL_REGISTER              0x0004
#define COM_LINE_STATUS_REGISTER                0x0005
#define COM_MODEM_STATUS_REGISTER               0x0006
#define COM_SCRATCH_REGISTER                    0x0007

#define COM_DIVISOR_LATCH_REGISTER_LOW          0x0000
#define COM_DIVISOR_LATCH_REGISTER_HIGH         0x0001

#define COM_CLOCK_RATE                          0x1C200

#define COM_LINE_CONTROL_8BITS_1STOP            0x03
#define COM_LINE_CONTROL_DIVISOR_ACCESS         0x80

#define COM_MODEM_CONTROL_DATA_TERMINAL_READY   0x01
#define COM_MODEM_CONTROL_REQUEST_TO_SEND       0x02

#define COM_LINE_STATUS_DATA_READY              0x01
#define COM_LINE_STATUS_OVERRUN_ERROR           0x02
#define COM_LINE_STATUS_PARITY_ERROR            0x04
#define COM_LINE_STATUS_FRAMING_ERROR           0x08
#define COM_LINE_STATUS_SEND_BUFFER_EMPTY       0x20

BOOLEAN
BlComInitialize(
    UINT8 PortNumber,
    UINT32 BaudRate
    )

//++
//
//  Routine Description:
//
//    This function initializes the specified COM port.
//
//  Arguments:
//
//    PortNumber  - Supplies the number of the port to initialize.
//
//    BaudRate    - Supplies the baud rate.
//
//  Return Value:
//
//    TRUE, if initialization was successful.
//    FALSE, otherwise.
//
//--

{
    UINT16 Base;
    UINT16 Divisor;
    UINT8 Index;
    UINT8 Status;

    BLASSERT((PortNumber >= 1) && (PortNumber <= COM_MAX_PORT));

    BLASSERT(BaudRate != 0);

    BLASSERT(BaudRate <= COM_CLOCK_RATE);

    BLASSERT((COM_CLOCK_RATE % BaudRate) == 0);

    BLASSERT((COM_CLOCK_RATE / BaudRate) <= 0x10000);

    Base = BlComBasePort[PortNumber];

    BlRtlWritePort8(Base + COM_LINE_CONTROL_REGISTER, 0);
    BlRtlWritePort8(Base + COM_INTERRUPT_ENABLE_REGISTER, 0);
    BlRtlWritePort8(Base + COM_MODEM_CONTROL_REGISTER, COM_MODEM_CONTROL_DATA_TERMINAL_READY | COM_MODEM_CONTROL_REQUEST_TO_SEND);

    Divisor = (UINT16) (COM_CLOCK_RATE / BaudRate);

    BlRtlWritePort8(Base + COM_LINE_CONTROL_REGISTER, COM_LINE_CONTROL_DIVISOR_ACCESS);
    BlRtlWritePort8(Base + COM_DIVISOR_LATCH_REGISTER_LOW, (UINT8) (Divisor & 0xFF));
    BlRtlWritePort8(Base + COM_DIVISOR_LATCH_REGISTER_HIGH, (UINT8) (Divisor >> 8));

    BlRtlWritePort8(Base + COM_LINE_CONTROL_REGISTER, COM_LINE_CONTROL_8BITS_1STOP);

    Index = 0;

    do {

        BlRtlWritePort8(Base + COM_SCRATCH_REGISTER, Index);

        if (BlRtlReadPort8(Base + COM_SCRATCH_REGISTER) != Index) {

            return FALSE;
        }

        Index += 1;

    } while (Index != 0);

    Status = BlRtlReadPort8(Base + COM_LINE_STATUS_REGISTER);

    if (Status == 0xFF) {

        return FALSE;
    }

#if COM_VERBOSE

    if ((Status & COM_LINE_STATUS_OVERRUN_ERROR) != 0) {

        BlVideoPrintf("COM%u: Overrun error!\n", PortNumber);
    }

    if ((Status & COM_LINE_STATUS_PARITY_ERROR) != 0) {

        BlVideoPrintf("COM%u: Parity error!\n", PortNumber);
    }

    if ((Status & COM_LINE_STATUS_FRAMING_ERROR) != 0) {

        BlVideoPrintf("COM%u: Framing error!\n", PortNumber);
    }

#endif

    return TRUE;
}

BOOLEAN
BlComSendByte(
    UINT8 PortNumber,
    UINT8 Byte
    )

//++
//
//  Routine Description:
//
//    This function sends a byte to the specified COM port.
//
//  Arguments:
//
//    PortNumber  - Supplies the number of the port to send to.
//
//    Byte        - Supplies the byte to send.
//
//  Return Value:
//
//    TRUE, if data was sent.
//    FALSE, otherwise.
//
//--

{
    UINT16 Base;
    UINT8 Status;

    BLASSERT((PortNumber >= 1) && (PortNumber <= COM_MAX_PORT));

    Base = BlComBasePort[PortNumber];

    do {

        Status = BlRtlReadPort8(Base + COM_LINE_STATUS_REGISTER);

#if COM_VERBOSE

        if ((Status & COM_LINE_STATUS_OVERRUN_ERROR) != 0) {

            BlVideoPrintf("COM%u: Overrun error!\n", PortNumber);
        }

        if ((Status & COM_LINE_STATUS_PARITY_ERROR) != 0) {

            BlVideoPrintf("COM%u: Parity error!\n", PortNumber);
        }

        if ((Status & COM_LINE_STATUS_FRAMING_ERROR) != 0) {

            BlVideoPrintf("COM%u: Framing error!\n", PortNumber);
        }

#endif

    } while ((Status & COM_LINE_STATUS_SEND_BUFFER_EMPTY) == 0);

    BlRtlWritePort8(Base + COM_DATA_REGISTER, Byte);

    Status = BlRtlReadPort8(Base + COM_LINE_STATUS_REGISTER);

#if COM_VERBOSE

    if ((Status & COM_LINE_STATUS_OVERRUN_ERROR) != 0) {

        BlVideoPrintf("COM%u: Overrun error!\n", PortNumber);
    }

    if ((Status & COM_LINE_STATUS_PARITY_ERROR) != 0) {

        BlVideoPrintf("COM%u: Parity error!\n", PortNumber);
    }

    if ((Status & COM_LINE_STATUS_FRAMING_ERROR) != 0) {

        BlVideoPrintf("COM%u: Framing error!\n", PortNumber);
    }

#endif

    return TRUE;
}

BOOLEAN
BlComDataAvailable(
    UINT8 PortNumber
    )

//++
//
//  Routine Description:
//
//    This function checks if data is available at the specified COM port.
//
//  Arguments:
//
//    PortNumber  - Supplies the number of the port to check.
//
//  Return Value:
//
//    TRUE, if data is available.
//    FALSE, otherwise.
//
//--

{
    UINT16 Base;
    UINT8 Status;

    BLASSERT((PortNumber >= 1) && (PortNumber <= COM_MAX_PORT));

    Base = BlComBasePort[PortNumber];

    Status = BlRtlReadPort8(Base + COM_LINE_STATUS_REGISTER);

#if COM_VERBOSE

    if ((Status & COM_LINE_STATUS_OVERRUN_ERROR) != 0) {

        BlVideoPrintf("COM%u: Overrun error!\n", PortNumber);
    }

    if ((Status & COM_LINE_STATUS_PARITY_ERROR) != 0) {

        BlVideoPrintf("COM%u: Parity error!\n", PortNumber);
    }

    if ((Status & COM_LINE_STATUS_FRAMING_ERROR) != 0) {

        BlVideoPrintf("COM%u: Framing error!\n", PortNumber);
    }

#endif

    return ((Status & COM_LINE_STATUS_DATA_READY) != 0);
}

UINT8
BlComReceiveByte(
    UINT8 PortNumber
    )

//++
//
//  Routine Description:
//
//    This function receives a byte from the specified COM port.
//
//  Arguments:
//
//    PortNumber  - Supplies the number of the port to receive from.
//
//  Return Value:
//
//    Byte received from the specified COM port.
//
//--

{
    UINT16 Base;
    UINT8 Byte;
    UINT8 Status;

    BLASSERT((PortNumber >= 1) && (PortNumber <= COM_MAX_PORT));

    Base = BlComBasePort[PortNumber];

    BlRtlReadPort8(Base + COM_MODEM_STATUS_REGISTER);

    do {

        Status = BlRtlReadPort8(Base + COM_LINE_STATUS_REGISTER);

#if COM_VERBOSE

        if ((Status & COM_LINE_STATUS_OVERRUN_ERROR) != 0) {

            BlVideoPrintf("COM%u: Overrun error!\n", PortNumber);
        }

        if ((Status & COM_LINE_STATUS_PARITY_ERROR) != 0) {

            BlVideoPrintf("COM%u: Parity error!\n", PortNumber);
        }

        if ((Status & COM_LINE_STATUS_FRAMING_ERROR) != 0) {

            BlVideoPrintf("COM%u: Framing error!\n", PortNumber);
        }

#endif

    } while ((Status & COM_LINE_STATUS_DATA_READY) == 0);

    Byte = BlRtlReadPort8(Base + COM_DATA_REGISTER);

    Status = BlRtlReadPort8(Base + COM_LINE_STATUS_REGISTER);

#if COM_VERBOSE

    if ((Status & COM_LINE_STATUS_OVERRUN_ERROR) != 0) {

        BlVideoPrintf("COM%u: Overrun error!\n", PortNumber);
    }

    if ((Status & COM_LINE_STATUS_PARITY_ERROR) != 0) {

        BlVideoPrintf("COM%u: Parity error!\n", PortNumber);
    }

    if ((Status & COM_LINE_STATUS_FRAMING_ERROR) != 0) {

        BlVideoPrintf("COM%u: Framing error!\n", PortNumber);
    }

#endif

    return Byte;
}
