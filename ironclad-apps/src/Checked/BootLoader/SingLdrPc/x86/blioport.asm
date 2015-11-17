;++
;
; Copyright (c) Microsoft Corporation
;
; Module Name:
;
;     blioport.asm
;
; Abstract:
;
;     This module implements IO port access routines for the boot loader.
;
; Environment:
;
;     Boot loader.
;
;--

include bl.inc

.686p
.model flat
.code

assume ds:flat
assume es:flat
assume ss:flat
assume fs:flat

;++
;
; UCHAR
; FASTCALL
; BlRtlReadPort8(
;     USHORT Port
;     )
;
; Routine Description:
;
;   This function reads from the specified 8-bit port.
;
; Arguments:
;
;   Port        - Supplies the port to read from.
;
; Return Value:
;
;   Value read from the port.
;
;--

?BlRtlReadPort8@@YIEG@Z proc

        mov     dx, cx
        in      al, dx
        ret

?BlRtlReadPort8@@YIEG@Z endp

;++
;
; ULONG
; FASTCALL
; BlRtlReadPort32(
;     USHORT Port
;     )
;
; Routine Description:
;
;   This function reads from the specified 32-bit port.
;
; Arguments:
;
;   Port        - Supplies the port to read from.
;
; Return Value:
;
;   Value read from the port.
;
;--

?BlRtlReadPort32@@YIKG@Z proc

        mov     dx, cx
        in      eax, dx
        ret

?BlRtlReadPort32@@YIKG@Z endp

;++
;
; VOID
; FASTCALL
; BlRtlWritePort8(
;     USHORT Port,
;     UCHAR Value
;     )
;
; Routine Description:
;
;   This function writes to the specified 8-bit port.
;
; Arguments:
;
;   Port        - Supplies the port to write to.
;
;   Value       - Supplies the value to write.
;
;--

?BlRtlWritePort8@@YIXGE@Z proc

        mov     al, dl
        mov     dx, cx
        out     dx, al
        ret

?BlRtlWritePort8@@YIXGE@Z endp

;++
;
; VOID
; FASTCALL
; BlRtlWritePort32(
;     USHORT Port,
;     ULONG Value
;     )
;
; Routine Description:
;
;   This function writes to the specified 32-bit port.
;
; Arguments:
;
;   Port        - Supplies the port to write to.
;
;   Value       - Supplies the value to write.
;
;--

?BlRtlWritePort32@@YIXGK@Z proc

        mov     eax, edx
        mov     dx, cx
        out     dx, eax
        ret

?BlRtlWritePort32@@YIXGK@Z endp

end
