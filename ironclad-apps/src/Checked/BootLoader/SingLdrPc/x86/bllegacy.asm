;++
;
; Copyright (c) Microsoft Corporation
;
; Module Name:
;
;     bllegacy.asm
;
; Abstract:
;
;     This module implements legacy call support.
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

.code

;
; Legacy call frame.
;

LegacyCallFrame         struct

        _eax            dq ?
        _ebx            dq ?
        _ecx            dq ?
        _edx            dq ?
        _ebp            dq ?
        _esi            dq ?
        _edi            dq ?
        _idtr           df ?

LegacyCallFrame         ends

BlLegacyReturnStackPointer      dd      0

;++
;
; VOID
; FASTCALL
; BlReturnToLegacyMode(
;     VOID
;     )
;
; Routine Description:
;
;   This function returns to legacy mode to process a legacy request.
;
;--

?BlReturnToLegacyMode@@YIXXZ proc

;
; Save all registers.
;

        sub     esp, (sizeof LegacyCallFrame)

        mov     dword ptr [esp].LegacyCallFrame._eax, eax
        mov     dword ptr [esp].LegacyCallFrame._ebx, ebx
        mov     dword ptr [esp].LegacyCallFrame._ecx, ecx
        mov     dword ptr [esp].LegacyCallFrame._edx, edx
        mov     dword ptr [esp].LegacyCallFrame._ebp, ebp
        mov     dword ptr [esp].LegacyCallFrame._esi, esi
        mov     dword ptr [esp].LegacyCallFrame._edi, edi

;
; Save IDTR
;
        sidt    fword ptr [esp].LegacyCallFrame._idtr

;
; Save stack pointer.
;

        mov     BlLegacyReturnStackPointer, esp

;
; Set return address in BEB.
;

        mov     eax, BEB_BASE
        lea     ecx, @f
        mov     dword ptr [eax].BEB.LegacyReturnAddress, ecx

;
; Get legacy call stub address from BEB.
;

        mov     ecx, dword ptr [eax].BEB.LegacyCallAddress

;
; Return to legacy mode.
;

        call    ecx

@@:

;
; Restore stack pointer.
;

        mov     esp, BlLegacyReturnStackPointer

;
; Restore all registers.
;

        mov     eax, dword ptr [esp].LegacyCallFrame._eax
        mov     ebx, dword ptr [esp].LegacyCallFrame._ebx
        mov     ecx, dword ptr [esp].LegacyCallFrame._ecx
        mov     edx, dword ptr [esp].LegacyCallFrame._edx
        mov     ebp, dword ptr [esp].LegacyCallFrame._ebp
        mov     esi, dword ptr [esp].LegacyCallFrame._esi
        mov     edi, dword ptr [esp].LegacyCallFrame._edi

;
; Restore IDT
;

        lidt    fword ptr [esp].LegacyCallFrame._idtr

        add     esp, (sizeof LegacyCallFrame)
        ret

?BlReturnToLegacyMode@@YIXXZ endp

public ?BlReturnToLegacyMode@@YIXXZ

end
