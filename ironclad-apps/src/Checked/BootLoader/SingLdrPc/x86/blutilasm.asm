;++
;
; Copyright (c) Microsoft Corporation
;
; Module Name:
;
;     blutilasm.asm
;
; Abstract:
;
;     This module implements utility functions for the boot loader.
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
; UINT
; DisablePaging(
;     UINT reg
;     )
;
; Routine Description:
;   This function takes one value as an argument and returns another
;   that have no meaning.  It was simpler to copy an existing function
;   than deduce the calling/name-mangling conventions for MS C++.
; Return Value:
;
;   None of interest
;
;--

?DisablePaging@@YIKK@Z proc

        ; Disable paging
        mov     eax, cr0
        and     eax, NOT CR0_PG
        mov     cr0, eax
        ; Make sure PAE is off, in case Verve turns paging back on
        mov     eax, cr4
        and     eax, NOT CR4_PAE 
        and     eax, NOT CR4_PSE
        mov     cr4, eax
        ; Make sure long mode (EFER.LME) and no-execute (EFER_NXE) is off
        mov     ecx, EFER_MSR_INDEX
        rdmsr
        and     eax, NOT (EFER_LME OR EFER_NXE)
        wrmsr
        ret

?DisablePaging@@YIKK@Z endp

;++
;
; ULONG_PTR
; FASTCALL
; BlMmGetCr3(
;     VOID
;     )
;
; Routine Description:
;
;   This function queries the CR3 register.
;
; Return Value:
;
;   Value of the CR3 register.
;
;--

?BlMmGetCr3@@YIKXZ proc

        mov     eax, cr3
        ret

?BlMmGetCr3@@YIKXZ endp

;++
;
; VOID
; FASTCALL
; BlMmSetCr3(
;     ULONG_PTR Value
;     )
;
; Routine Description:
;
;   This function sets the CR3 register.
;
; Arguments:
;
;   Value       - Supplies the value to write to the CR3 register.
;
;--

?BlMmSetCr3@@YIXK@Z proc

        mov     cr3, ecx
        ret

?BlMmSetCr3@@YIXK@Z endp

;++
;
; VOID
; FASTCALL
; BlFakeSKINIT(
;     ULONG_PTR Value
;     )
;
; Routine Description:
;
;   This function launches Verve as though we had invoked SKINIT 
;
; Arguments:
;
;   Value       - Supplies the base address of the Verve image
;
;--

?BlFakeSKINIT@@YIXK@Z proc

        mov     esp, ecx
        add     esp, 00010000h  ; esp == base + 64K
        mov     eax, ecx        ; eax == base
; Now calculate the actual entry point, based on the SL header
        mov     edx, [ecx]      ; edx contains the SL header
        and     edx, 0000FFFFh  ; edx contains the entry point offset
        add     ecx, edx        ; ecx contains the absolute entry point addr
        jmp     ecx

?BlFakeSKINIT@@YIXK@Z endp

;++
;
; VOID
; FASTCALL
; BlRealSKINIT(
;     ULONG_PTR Value
;     )
;
; Routine Description:
;
;   This function launches Verve as via a real SKINIT 
;
; Arguments:
;
;   Value       - Supplies the base address of the Verve image
;
;--

?BlRealSKINIT@@YIXK@Z proc

        mov     ebx, ecx        ; ebx == base

        ; Enable SVM
        mov     ecx, 0C0000080h  ; Specify EFER
        rdmsr                   ; Puts value in EAX (and EDX in 64-bit mode)
        or      eax, 000001000h  ; Bit 12, SVME, is now set
        wrmsr                   ; Enable SVME

        ; Do it!
        mov     eax, ebx        ; Move the base addr back into EAX
        ; Windows doesn't know that the SKINIT opcode is 0x0f01de
        db 00fh
        db 001h
        db 0deh
        ;__emit 00fh
        ;__emit 001h
        ;__emit 0deh

?BlRealSKINIT@@YIXK@Z endp


;++
;
; VOID
; FASTCALL
; BlMmGetGdtr(
;     PGDTR Gdtr
;     )
;
; Routine Description:
;
;   This function queries the GDTR register.
;
; Arguments:
;
;   Gdtr        - Receives the contents of the GDTR register.
;
;--

?BlMmGetGdtr@@YIXPAU_GDTR@@@Z proc

        sgdt    fword ptr [ecx]
        ret

?BlMmGetGdtr@@YIXPAU_GDTR@@@Z endp

;++
;
; VOID
; FASTCALL
; BlMmSetGdtr(
;     PGDTR Gdtr
;     )
;
; Routine Description:
;
;   This function sets the GDTR register.
;
; Arguments:
;
;   Gdtr        - Supplies the data to write to the GDTR register.
;
;--

?BlMmSetGdtr@@YIXPAU_GDTR@@@Z proc

        lgdt    fword ptr [ecx]
        ret

?BlMmSetGdtr@@YIXPAU_GDTR@@@Z endp

;++
;
; USHORT
; FASTCALL
; BlMmGetFs(
;     VOID
;     )
;
; Routine Description:
;
;   This function queries the FS register.
;
; Return Value:
;
;   Value of the FS register.
;
;--

@BlMmGetFs@0 proc

        mov     ax, fs
        ret

@BlMmGetFs@0 endp

;++
;
; VOID
; FASTCALL
; BlMmSetFs(
;     USHORT Value
;     )
;
; Routine Description:
;
;   This function sets the FS register.
;
; Arguments:
;
;   Value       - Supplies the value to write to the FS register.
;
;--

?BlMmSetFs@@YIXG@Z proc

        mov     fs, cx
        ret

?BlMmSetFs@@YIXG@Z endp

;++
;
; VOID
; FASTCALL
; BlMmSwitchStack(
;     PVOID Stack,
;     PVOID Function
;     )
;
; Routine Description:
;
;   This function switches the stack and calls the specified function.
;
; Arguments:
;
;   Stack       - Supplies the stack to switch to.
;
;   Function    - Supplies the function to call.
;
;--

?BlMmSwitchStack@@YIXPAX0@Z proc

        mov     esp, ecx
        call    edx

@@:
        jmp     @b

?BlMmSwitchStack@@YIXPAX0@Z endp

;++
;
; PVOID
; FASTCALL
; BlRtlGetEbp(
;     VOID
;     )
;
; Routine Description:
;
;   This function queries the value of the EBP register.
;
; Return Value:
;
;   Value of the EBP register.
;
;--

?BlRtlGetEbp@@YIPAXXZ proc

        mov     eax, ebp
        ret

?BlRtlGetEbp@@YIPAXXZ endp
        
;++
;
; UINT
; BlGetCpuidEax(
;     UINT reg
;     )
;
; Routine Description:
;
;   This function queries the CPUID.
;
; Return Value:
;
;   Value of the EAX register.
;
;--

?BlGetCpuidEax@@YIKK@Z proc

        mov     eax, ecx
        cpuid
        ret

?BlGetCpuidEax@@YIKK@Z endp

;++
;
; UINT
; BlGetCpuidEbx(
;     UINT reg
;     )
;
; Routine Description:
;
;   This function queries the CPUID.
;
; Return Value:
;
;   Value of the EBX register.
;
;--

?BlGetCpuidEbx@@YIKK@Z proc

        mov     eax, ecx
        cpuid
        mov     ebx, eax
        ret

?BlGetCpuidEbx@@YIKK@Z endp

;++
;
; UINT
; BlGetCpuidEcx(
;     UINT reg
;     )
;
; Routine Description:
;
;   This function queries the CPUID.
;
; Return Value:
;
;   Value of the ECX register.
;
;--

?BlGetCpuidEcx@@YIKK@Z proc

        mov     eax, ecx
        cpuid
        mov     eax, ecx
        ret
        
?BlGetCpuidEcx@@YIKK@Z endp

;++
;
; UINT
; BlGetCpuidEdx(
;     UINT reg
;     )
;
; Routine Description:
;
;   This function queries the CPUID.
;
; Return Value:
;
;   Value of the EDX register.
;
;--

?BlGetCpuidEdx@@YIKK@Z proc

        mov     eax, ecx
        cpuid
        mov     eax, edx
        ret

?BlGetCpuidEdx@@YIKK@Z endp

        
end
