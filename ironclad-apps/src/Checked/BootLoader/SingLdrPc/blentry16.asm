;++
;
; Copyright (c) Microsoft Corporation
;
; Module Name:
;
;     blentry16.asm (x64)
;
; Abstract:
;
;     This module implements the 16-bit entry point for the boot loader.
;
; Environment:
;
;     Boot loader.
;
;--


.model tiny, c

OPTION SCOPED

include bl.inc

REAL_MODE_BASE          equ     07b00h
VIDEO_BASE              equ     0b8000h
BLUE                    equ     01f00h
RED                     equ     02f00h        
GREEN                   equ     04f00h
        
.code
.686p

JMPF16 MACRO SEG:REQ,OFF:REQ
        db      0eah
        dw      OFF
        dw      SEG
ENDM        

JMPF32 MACRO SEG:REQ,OFF:REQ
        db      0eah
        dd      OFF
        dw      SEG
ENDM

_TEXT16 segment page public use16 'CODE'

        org     100h

;++
;
; VOID
; BlEntry16(
;     VOID
;     )
;
; Routine Description:
;
;   This function is the 16-bit entry point for the boot loader and it detects
;   the type of boot to perform and calls the appropriate function.
;
;--

BlEntry16       proc

;
; Disable interrupts.
;

        cli

        mov     bp, sp

        ;; Write a character to the screen.
        ;; Configure GS to point to the text-mode video console.
        mov     ax, 0b800h
        mov     gs, ax

        mov     ax, GREEN + 'A'
        mov     gs:[0], ax

        mov     ax, GREEN + '-'
        mov     gs:[2], ax
        
;
; If CS is 0x5000, then it indicates a CD or HD boot.
;

        mov     bx, PXE_BOOT
        mov     dx, 0
        mov     ax, cs
        cmp     ax, 05000h
        jne     boot_ready

;
; Check for CD signature on the stack.
;

        mov     dx, word ptr [bp + 8]
        mov     bx, CD_BOOT
        cmp     word ptr [bp + 4], 04344h
        je      boot_needs_fixup

;
; Check for FAT16 signature on the stack.
;

        mov     bx, FAT16_BOOT
        cmp     word ptr [bp + 4], 04806h
        je      boot_needs_fixup

;
; Check for FAT32 signature on the stack.
;

        mov     bx, FAT32_BOOT
        cmp     word ptr [bp + 4], 04803h
        je      boot_needs_fixup

;
; Unknown boot device
;

        mov     ax, GREEN + 'B'
        mov     gs:[2], ax
@@:
        jmp @b

;
; Copy 64K from 57C0:0000 to 07C0:0000.
;

boot_needs_fixup:
        mov     ax, GREEN + 'C'
        mov     gs:[4], ax
        
        mov     ax, 057C0h
        mov     ds, ax
        mov     si, 0
        mov     ax, 007C0h
        mov     es, ax
        mov     di, 0
        mov     cx, 04000h

        rep movsd

;
; Continue execution at the relocated block with known segment selector.
;

boot_ready:

        mov     ax, GREEN + 'D'
        mov     gs:[6], ax
  
;
; Jump to relocated code.
;
        
        JMPF16  07b0h, @f
@@:      

        ;     bx = BootType
        ;     dx = BootDriveNumber

;
; Initialize DS, ES, SS, and SP for real mode.
;

        mov     ax, cs
        mov     ds, ax
        mov     es, ax
        mov     ax, RM_INITIAL_SS
        mov     ss, ax
        mov     sp, RM_INITIAL_SP

        mov     ax, GREEN + 'E'
        mov     gs:[8], ax
        
;
; Initialize boot environment block (pass bx & dx).
;

        call    BlInitializeBeb

;
; Initialize video.
;

        call    BlInitializeVideo

;
; Load GDT.
;

        mov     ax, GREEN + 'F'
        mov     gs:[10], ax
        
        mov     di, OFFSET BlGDTS_Limit
        lgdt    fword ptr ds:[di]

        mov     ax, RM_VIDEO_SELECTOR
        mov     gs, ax

        mov     ax, GREEN + 'G'
        mov     gs:[12], ax
        
;
; Clear the real-mode segment registers.
;
        
        xor     ax, ax
        mov     ds, ax
        mov     es, ax
        mov     ss, ax
        mov     fs, ax
        mov     gs, ax
        
;
; Enable protected mode.
;

        mov     eax, cr0
        or      eax, CR0_PE OR CR0_NE
        mov     cr0, eax

;
; Jump far to 32-bit protected-mode code.
;

        JMPF16  PM_CODE_SELECTOR, LOWWORD ( REAL_MODE_BASE + OFFSET BlEntry32 )
        
BlEntry16       endp

;++
;
; VOID
; BlInitializeVideo(
;     VOID
;     )
;
; Routine Description:
;
;   This function initializes video support for the boot loader.
;
;--

BlInitializeVideo       proc

        mov     ax, 1202h       ; LINES_400_CONFIGURATION
        mov     bx, 0301h       ; SELECT_SCAN_LINE
        int     10h

        mov     ax, 3h          ; SET_80X25_16_COLOR_MODE
        mov     bx, 0h          ; PAGE0
        int     10h

        mov     ax, 1112h       ; LOAD_8X8_CHARACTER_SET
        mov     bx, 0h
        int     10h

        mov     ax, 1003h       ; Disable BLINK mode, enable background intensity.
        mov     bx, 0h
        int     10h

        mov     ax, 0200h       ; Set Cursor position to 0, 0
        mov     bx, 0h
        mov     dx, 0h
        int     10h

        ret

BlInitializeVideo       endp

;++
;
; VOID
; BlInitializeBeb(
;     bx = BootType
;     dx = BootDriveNumber
;     )
;
; Routine Description:
;
;   This function initializes the boot environment block.
;
;--

BlInitializeBeb proc

        push    es
        push    di

        mov     di, BEB_SEG16
        mov     es, di
        mov     di, BEB_OFF16

        xor     al, al
        mov     cx, 4096
        rep stosb

        mov     di, BEB_OFF16

        ;;  See if we are booting from Flash
        
        mov     si, BlFlashImage
        mov     eax, [si]
        cmp     eax, 0
        je      @f
        
        mov     dword ptr es:[di].BEB.FlashImage, eax
        mov     si, BlSmapAddr
        mov     eax, [si]
        mov     dword ptr es:[di].BEB.SmapAddr, eax
        mov     si, BlSmapSize
        mov     eax, [si]
        mov     dword ptr es:[di].BEB.SmapSize, eax
        mov     bx, FLASH_BOOT
@@:     
                
        mov     word ptr es:[di].BEB.BootType, bx
        mov     word ptr es:[di].BEB.BootDriveNumber, dx
ifdef BOOT_X64        
        mov     dword ptr es:[di].BEB.LegacyReturnCr3, LM_PML4T_ADDRESS
else
        mov     dword ptr es:[di].BEB.LegacyReturnCr3, PM_PDPT_ADDRESS
endif
        lea     ax, BlApEntry16
        mov     word ptr es:[di].BEB.ApEntry16, ax
        mov     ax, cs
        mov     word ptr es:[di].BEB.ApEntry16 + 2, ax

        lea     ax, BlApStartupLock
        mov     word ptr es:[di].BEB.ApStartupLock, ax
        mov     ax, cs
        mov     word ptr es:[di].BEB.ApStartupLock + 2, ax

        pop     di
        pop     es
        ret

BlInitializeBeb endp

;++
;
; Hardware Protection Configuration Data 
;
;--

;
; TSS.
;

ALIGN 16

BlTSS:

        db      066h dup (0)
        dw      068h

;
; Global Descriptor Table (GDT).
;

ALIGN 16

BlGDTStart:

        dq      00000000000000000h      ; 00: NULL segment              [NULL_SELECTOR].
        dq      00000930B8000FFFFh      ; 08: 000B8000[0000FFFF] Data   [PM_VIDEO_SELECTOR].
        dq      000009B007B00FFFFh      ; 10: 00007800[0000FFFF] COde   [RM_CODE_SELECTOR].
        dq      0000093007B00FFFFh      ; 18: 00007B00[0000FFFF] Data   [RM_DATA_SELECTOR].
        dq      000CF9B000000FFFFh      ; 20: PM code segment           [PM_CODE_SELECTOR].
        dq      000CF93000000FFFFh      ; 28: PM data segment           [PM_DATA_SELECTOR].
        dq      000209B0000000000h      ; 30: LM code segment           [LM_CODE_SELECTOR].
        dq      00000930000000000h      ; 38: LM data segment           [LM_DATA_SELECTOR].
        dq      00000000000000000h      ; 40: PM user code segment      [UM_CODE_SELECTOR].
        dq      00000000000000000h      ; 48: PM user data segment      [UM_DATA_SELECTOR].
        dq      00000000000000000h      ; 50: FS/GS segment             [PROCESSOR_SELECTOR].
        dq      00000000000000000h      ; 58:                           [UNUSED_SELECTOR]

;
; TSS segment.
;

        dw      00067h
        dw      REAL_MODE_BASE + OFFSET BlTSS
        db      000h
        db      089h
        dw      00000h
ifdef BOOT_X64        
        dq      00000000000000000h
endif        

BlGDTLimit:

;
; Global Descriptor Table Selector (GDTS).
;

ALIGN 16

;; Padding to align address (and limit to -2)
        dw      00000h
        dw      00000h
        dw      00000h
BlGDTS_Limit:
        dw      offset BlGDTLimit - offset BlGDTStart
BlGDTS_Address:
        dw      REAL_MODE_BASE + OFFSET BlGDTStart
        dw      0
        dd      0

;++
;
; VOID
; BlReturnToRealMode(
;     VOID
;     )
;
; Routine Description:
;
;   This function switches the processor back to real mode to execute a real
;   mode request.
;
;--

ALIGN 16
BlReturnToRealMode      proc

;
; Zero all registers.
;

        xor     ebx, ebx
        xor     ecx, ecx
        xor     edx, edx
        xor     esi, esi
        xor     edi, edi
        xor     esp, esp
        xor     ebp, ebp

        mov     ax, RM_DATA_SELECTOR
        mov     ds, ax
        mov     es, ax
        mov     ss, ax
        mov     fs, ax
        mov     gs, ax
;
; Disable protected mode.
;

        mov     eax, cr0
        and     eax, NOT (CR0_PE OR CR0_NE)
        mov     cr0, eax

;
; Return to real mode.
;
        JMPF16  07b0h, OFFSET BlProcessRealModeRequest

BlReturnToRealMode      endp

;++
;
; VOID
; BlLeaveLrbPmToBoot(
;     VOID
;     )
;
; Routine Description:
;
;   This function switches the processor back to real mode for boot.
;
;--

ALIGN 16
BlLeaveLrbPmToBoot      PROC

        mov     ax, RM_VIDEO_SELECTOR
        mov     gs, ax
        ;; Write to position 0.
        mov     ax, RED + 'T'
        mov     gs:[12], ax
        
; Zero all registers.
;

        xor     ebx, ebx
        xor     ecx, ecx
        xor     edx, edx
        xor     esi, esi
        xor     edi, edi
        xor     esp, esp
        xor     ebp, ebp

;
; Disable paging.
;

        mov     eax, cr0
        and     eax, NOT (CR0_PG)
        mov     cr0, eax
        
        xor     eax, eax
        mov     cr3, eax
        mov     cr4, eax

;
; Disable long mode and return to legacy protected-mode.
;

        mov     ecx, EFER_MSR_INDEX
        rdmsr
        and     eax, NOT (EFER_LME OR EFER_NXE)
        wrmsr

;
; Disable protected mode.
;

        mov     eax, cr0
        and     eax, NOT (CR0_PE OR CR0_NE)
        mov     cr0, eax
        
;
; Return to real mode.
;
        JMPF16  07b0h, OFFSET @f
@@:     
        mov     ax, 0b800h
        mov     gs, ax
        
        ;; Write to position 0.
        mov     ax, RED + 'U'
        mov     gs:[14], ax

        mov     ax, cs
        mov     ds, ax
        mov     es, ax
        mov     ax, RM_INITIAL_SS
        mov     ss, ax
        mov     sp, RM_INITIAL_SP
        
        ;; Write to position 0.
        mov     ax, RED + 'V'
        mov     gs:[16], ax

;
; Return to real mode boot entry.
;
        JMPF16  07b0h, OFFSET BlEntry16

BlLeaveLrbPmToBoot  endp

;++
;
; VOID
; BlProcessRealModeRequest(
;     VOID
;     )
;
; Routine Description:
;
;   This function performs the requested real mode operation and returns back to
;   protected mode as necessary.
;
;--

;
; Real-mode IDTR.
;

BlRealModeIdtr:

        dw      01000h
        dq      0

;
; Protected-mode IDTR.
;

BlProtModeIdtr:

        dw      01000h
        dq      0

BlProcessRealModeRequest        proc

;
; Set DS, ES, SS, SP, and SI for real-mode legacy call.
;

        xor     eax,eax
        mov     ax, cs
        mov     ds, ax
        mov     ax, BEB_SEG16
        mov     es, ax
        mov     ax, RM_INITIAL_SS
        mov     ss, ax
        mov     sp, RM_INITIAL_SP
        mov     si, BEB_OFF16

;
; Switch back to real-mode IDT.
;

        lea     eax, BlRealModeIdtr
        lidt    fword ptr ds:[eax]
                   
        cmp     word ptr es:[si].BEB.LegacyCall_OpCode, LC_INTXX
        jne     @f

        mov     cl, byte ptr es:[si].BEB.LegacyCall_Vector
        call    BlProcessIntXx
        jmp     BlProcessRealModeRequest_Exit

@@:

        cmp     word ptr es:[si].BEB.LegacyCall_OpCode, LC_FARCALL
        jne     @f

        call    BlProcessFarCall
        jmp     BlProcessRealModeRequest_Exit

@@:

BlProcessRealModeRequest_Exit:

;
; Restore DS, ES, SS, and SP to their initial real-mode values.
;

        mov     ax, cs
        mov     ds, ax
        mov     es, ax
        mov     ax, RM_INITIAL_SS
        mov     ss, ax
        mov     sp, RM_INITIAL_SP

;
; Load GDT.
;

        mov     di, OFFSET BlGDTS_Limit
        lgdt    fword ptr ds:[di]

;
; Clear the real-mode segment registers.
;
        
        xor     ax, ax
        mov     ds, ax
        mov     es, ax
        mov     ss, ax
        mov     fs, ax
        mov     gs, ax
        
;
; Enable protected mode.
;

        mov     eax, cr0
        or      eax, CR0_PE OR CR0_NE
        mov     cr0, eax

;
; Jump far to 32-bit protected-mode code.
;
        
        JMPF16  PM_CODE_SELECTOR, LOWWORD ( REAL_MODE_BASE + OFFSET BlEnter32AfterRealModeRequest )
        
BlProcessRealModeRequest        endp

;++
;
; Lock to protect shared access to real-mode boot stack.
;
;--
                
BlApStartupLock:

        dd      0

Bl16End db      0deh, 0adh, 0beh, 0efh

        
        org     500h

;++
;
; VOID
; BlApEntry16(
;     VOID
;     )
;
; Routine Description:
;
;   This function implements the entry point for application processors
;   on a multi-processor system.
;
;--

BlApEntry16     proc

;
; Disable interrupts.
;

        cli

;
; Set DS to access AP startup lock.
;

        mov     ax, 07b0h
        mov     ds, ax

;
; Acquire AP startup lock before touching any other memory or stack.
;

@@:
        cmp     word ptr ds:[BlApStartupLock], 0
        jne     @b

        mov     ax, 1
        xchg    word ptr ds:[BlApStartupLock], ax

        cmp     ax, 0
        jne     @b

;
; Set SS & SP and switch to 16-bit entry CS.
;

        mov     ax, RM_INITIAL_SS
        mov     ss, ax
        mov     sp, RM_INITIAL_SP

        JMPF16  07b0h, OFFSET @f
@@:

;
; Initialize DS, ES, SS, and SP for real mode.
;

        mov     ax, cs
        mov     ds, ax
        mov     es, ax
        mov     ax, RM_INITIAL_SS
        mov     ss, ax
        mov     sp, RM_INITIAL_SP

;
; Load GDT.
;

        mov     di, OFFSET BlGDTS_Limit
        lgdt    fword ptr ds:[di]

;
; Clear the real-mode segment registers.
;
        
        xor     ax, ax
        mov     ds, ax
        mov     es, ax
        mov     ss, ax
        mov     fs, ax
        mov     gs, ax
        
;
; Enable protected mode.
;

        mov     eax, cr0
        or      eax, CR0_PE OR CR0_NE
        mov     cr0, eax

;
; Jump far to 32-bit protected-mode code.
;
        
        JMPF16  PM_CODE_SELECTOR, LOWWORD ( REAL_MODE_BASE + OFFSET BlApEntry32 )
        
BlApEntry16     endp

;
;
;
              
SAVE_CONTEXT_TO_STACK           macro

        push    eax
        push    ebx
        push    ecx
        push    edx
        push    esi
        push    edi
        push    ds
        push    es
        pushfd

endm

RESTORE_CONTEXT_FROM_STACK      macro

        popfd
        pop     es
        pop     ds
        pop     edi
        pop     esi
        pop     edx
        pop     ecx
        pop     ebx
        pop     eax

endm

SAVE_CALL_CONTEXT_TO_STACK      macro

        mov     ax, BEB_SEG16
        mov     es, ax
        mov     si, BEB_OFF16

        push    dword ptr es:[si].BEB.LegacyCall_eax
        push    dword ptr es:[si].BEB.LegacyCall_ebx
        push    dword ptr es:[si].BEB.LegacyCall_ecx
        push    dword ptr es:[si].BEB.LegacyCall_edx
        push    dword ptr es:[si].BEB.LegacyCall_esi
        push    dword ptr es:[si].BEB.LegacyCall_edi
        push    word ptr es:[si].BEB.LegacyCall_ds
        push    word ptr es:[si].BEB.LegacyCall_es
        pushfd

endm

RESTORE_CALL_CONTEXT_FROM_STACK macro

        mov     ax, BEB_SEG16
        mov     es, ax
        mov     si, BEB_OFF16

        pop     dword ptr es:[si].BEB.LegacyCall_eflags
        pop     word ptr es:[si].BEB.LegacyCall_es
        pop     word ptr es:[si].BEB.LegacyCall_ds
        pop     dword ptr es:[si].BEB.LegacyCall_edi
        pop     dword ptr es:[si].BEB.LegacyCall_esi
        pop     dword ptr es:[si].BEB.LegacyCall_edx
        pop     dword ptr es:[si].BEB.LegacyCall_ecx
        pop     dword ptr es:[si].BEB.LegacyCall_ebx
        pop     dword ptr es:[si].BEB.LegacyCall_eax

endm

;++
;
; VOID
; BlProcessIntXx(
;     UCHAR InterruptVector
;     )
;
; Routine Description:
;
;   This function processes INT XX requests.
;
; Arguments:
;
;   InterruptVector (cl) - Supplies the interrupt vector to invoke.
;
;--

BlProcessIntXx  proc

        mov     byte ptr @f, cl

        SAVE_CONTEXT_TO_STACK

        SAVE_CALL_CONTEXT_TO_STACK

        RESTORE_CONTEXT_FROM_STACK

;
; INT XX instruction.
;

        db      0CDh

@@:

        db      000h

        SAVE_CONTEXT_TO_STACK

        RESTORE_CALL_CONTEXT_FROM_STACK

        RESTORE_CONTEXT_FROM_STACK

        ret

BlProcessIntXx  endp

;++
;
; VOID
; BlProcessFarCall(
;     UCHAR InterruptVector
;     )
;
; Routine Description:
;
;   This function processes far call requests.
;
;--

BlProcessFarCall        proc

        SAVE_CONTEXT_TO_STACK

        push    bp
        mov     bp, sp

;
; Copy the call frame to the stack.
;

        mov     ax, BEB_SEG16
        mov     es, ax
        mov     si, BEB_OFF16

        mov     ax, word ptr es:[si].BEB.LegacyCall_FramePtr + 2
        mov     ds, ax
        mov     bx, word ptr es:[si].BEB.LegacyCall_FramePtr

        mov     cx, word ptr es:[si].BEB.LegacyCall_FrameSize
        add     bx, cx
        mov     ax, cx

@@:

        cmp     ax, 0
        je      @f

        sub     bx, 2
        push    word ptr ds:[bx]

        sub     ax, 2
        jmp     @b

@@:

;
; Set return address.
;

        push    cs
        push    @f

;
; Set call address.
;

        push    dword ptr es:[si].BEB.LegacyCall_FuncPtr

;
; Set caller provided context.
;

        SAVE_CALL_CONTEXT_TO_STACK

        RESTORE_CONTEXT_FROM_STACK

;
; Call the specified function with a far return.
;

        retf

@@:

;
; Copy the output context to BEB.
;

        SAVE_CONTEXT_TO_STACK

        RESTORE_CALL_CONTEXT_FROM_STACK

        mov     sp, bp
        pop     bp

        RESTORE_CONTEXT_FROM_STACK

        ret

BlProcessFarCall        endp
        
_TEXT16 ends

_TEXT32 segment page public use32 'CODE'

;++
;
; VOID
; BlEntry32(
;     VOID
;     )
;
; Routine Description:
;
;   This function implements the 32-bit entry point for the boot loader.
;
;--

BlEntry32       proc

;
; Load the protected-mode segment registers.
;
        mov     ax, PM_DATA_SELECTOR
        mov     ds, ax
        mov     es, ax
        mov     ss, ax
        mov     esp, PM_INITIAL_ESP

        mov     ax, NULL_SELECTOR
        mov     fs, ax
        mov     gs, ax

        mov     esi, VIDEO_BASE + 14
        mov     [esi], ax
   
ifdef BOOT_X64             
;
; Check for long mode.
;

        call    BlCheckLongMode
        cmp     eax, 0
        jne     @f

;
; Long mode is not supported -- halt execution.
;

        call    BlHalt

@@:
endif
        
;
; Initialize boot environment block.
;

        call    BlRegisterExitAddress

;
; Prepare page tables.
;

        call    BlPreparePageTables

        mov     ax, GREEN + 'I'
        mov     esi, VIDEO_BASE + 14
        mov     [esi], ax
        
        
;
; Enable PSE, PAE, performance counters, and floating point support.
;

        mov     eax, cr4
        ;or      eax,                        CR4_PCE OR CR4_OSFXSR
        or      eax, CR4_PSE OR CR4_PAE OR CR4_PCE OR CR4_OSFXSR
        mov     cr4, eax

;
; Set root page table.
;

ifdef BOOT_X64
        mov     eax, LM_PML4T_ADDRESS
else
        mov     eax, PM_PDPT_ADDRESS
endif
        mov     cr3, eax

ifdef BOOT_X64        
;
; Enable long-mode and no-execute.
;

        mov     ecx, EFER_MSR_INDEX
        rdmsr
        or      eax, EFER_LME OR EFER_NXE
        wrmsr
endif        

;
; Enable paging.
;
         ;hlt
        mov     eax, cr0
        or      eax, CR0_PG
        mov     cr0, eax
;         mov  eax, cr0
;myInfLoop:         
;         and eax, 080000000h;
;         cmp eax, 0
;         jne myInfLoop


;
; Load PE image.
;

        call    BlLoadImage

        mov     bx, GREEN + 'J'
        mov     esi, VIDEO_BASE + 16
        mov     [esi], bx
        
ifdef BOOT_X64        
;
; Enter long mode.
;

        JMPF32  LM_CODE_SELECTOR, REAL_MODE_BASE + OFFSET @f
@@:

        mov     dx, LM_DATA_SELECTOR
        mov     ds, dx
        mov     es, dx
        mov     ss, dx

        mov     bx, GREEN + 'K'
        mov     esi, VIDEO_BASE + 18
        mov     [esi], bx
endif
                
;
; Switch to entry stack and call entry point.
;
        
        mov     esp, BL_ENTRY_SP
        call    eax

BlEntry32       endp

;++
;
; VOID
; BlEnter32AfterRealModeRequest(
;     VOID
;     )
;
; Routine Description:
;
;   This function returns to normal mode after a legacy mode request was handled.
;
;--

BlEnter32AfterRealModeRequest    proc

;
; Load the protected-mode segment registers.
;
        mov     ax, PM_DATA_SELECTOR
        mov     ds, ax
        mov     es, ax
        mov     ss, ax
        mov     esp, PM_INITIAL_ESP

        mov     ax, NULL_SELECTOR
        mov     fs, ax
        mov     gs, ax

;
; Enable PSE, PAE, performance counters, and floating point support.
;

        mov     eax, cr4
        ;or      eax,                        CR4_PCE OR CR4_OSFXSR
        or      eax, CR4_PSE OR CR4_PAE OR CR4_PCE OR CR4_OSFXSR
        mov     cr4, eax

;
; Set root page table.
;

        mov     eax, BEB_BASE
        mov     eax, dword ptr [eax].BEB.LegacyReturnCr3
        mov     cr3, eax

ifdef BOOT_X64
;
; Enable long-mode and no-execute.
;

        mov     ecx, EFER_MSR_INDEX
        rdmsr
        or      eax, EFER_LME OR EFER_NXE
        wrmsr
endif

;
; Restore the IDT
;

        mov     eax, OFFSET BlProtModeIdtr
        add     eax, REAL_MODE_BASE
        lidt    fword ptr ds:[eax]
        
;
; Enable paging.
;

        mov     eax, cr0
        or      eax, CR0_PG
        mov     cr0, eax

;
; Get return address from BEB.
;

        mov     eax, BEB_BASE
        mov     eax, dword ptr [eax].BEB.LegacyReturnAddress

ifdef BOOT_X64
;
; Enter long mode.
;

        JMPF32  LM_CODE_SELECTOR, REAL_MODE_BASE + OFFSET @f
@@:

        mov     edx, LM_DATA_SELECTOR
        mov     ds, edx
        mov     es, edx
        mov     ss, edx

endif
        
;
; Return to normal code.
;
        
        call    eax

BlEnter32AfterRealModeRequest    endp

;++
;
; VOID
; BlPreparePageTables(
;     VOID
;     )
;
; Routine Description:
;
;   This function prepares page tables for long mode execution.
;
;--

BlPreparePageTables     proc

ifdef BOOT_X64
;
; Clear all entries for 4th level table.
;

        xor     eax, eax
        mov     edi, LM_PML4T_ADDRESS
        mov     ecx, 0400h
        rep stosd

;
; Create a single 4th level entry.
;

        mov     eax, LM_PML4T_ADDRESS
        mov     dword ptr [eax], PM_PDPT_ADDRESS OR PTE_PRESENT OR PTE_WRITEABLE OR PTE_ACCESSED

endif
        
;
; Clear all entries for 2nd and 3rd level tables.
;

        xor     eax, eax
        mov     edi, PM_PDPT_ADDRESS
        mov     ecx, 0400h
        rep stosd

        xor     eax, eax
        mov     edi, PM_PDT_ADDRESS
        mov     ecx, 0400h
        rep stosd

;
; Create a single 3rd level entry.
;

        mov     eax, PM_PDPT_ADDRESS
ifdef BOOT_X64        
        mov     dword ptr [eax], PM_PDT_ADDRESS OR PTE_PRESENT OR PTE_WRITEABLE OR PTE_ACCESSED
else
;;; See if these can't be the same.
        mov     dword ptr [eax], PM_PDT_ADDRESS OR PTE_PRESENT
endif

;
; Create a single 2nd level entry to identity-map the first 2MB of memory.
;

        mov     eax, PM_PDT_ADDRESS
        mov     dword ptr [eax], 0 OR PTE_PRESENT OR PTE_WRITEABLE OR PTE_ACCESSED OR PTE_2MB

        ret

BlPreparePageTables     endp

ifdef BOOT_X64
                
;++
;
; VOID
; BlCheckLongMode(
;     VOID
;     )
;
; Routine Description:
;
;   This function checks if the processor supports long mode execution.
;
; Return Value:
;
;   TRUE, if long mode execution is supported.
;   FALSE, otherwise.
;
;--

BlCheckLongMode proc

;
; Get the largest extended function supported.
;

        mov     eax, 080000000h
        cpuid

;
; If 0x80000000 is the limit, then long mode is not supported.
;

        cmp     eax, 080000000h
        jbe     NoLongMode

;
; Execute extended function 1 and check for long mode bit.
;

        mov     eax, 080000001h
        cpuid

        bt      edx, 29
        jnc     NoLongMode

;
; Return 1 to indicate presence of long mode.
;

        mov     eax, 1
        ret

NoLongMode:

;
; Return 0 to indicate absense of long mode.
;

        mov     eax, 0
        ret

BlCheckLongMode endp

endif

;++
;
; VOID
; BlHalt(
;     VOID
;     )
;
; Routine Description:
;
;   This function halts execution.
;
;--

BlHalt  proc

@@:

        jmp     @b

BlHalt  endp

;++
;
; VOID
; BlLeaveProtectedMode(
;     VOID
;     )
;
; Routine Description:
;
;   This function leaves protected mode to perform a real mode operation.
;
;--

ALIGN 16        
BlLeaveProtectedMode    proc

;
; Disable paging, reset root page table, and flush TLB.
;

        mov     eax, cr0
        and     eax, NOT CR0_PG
        mov     cr0, eax

        xor     eax, eax
        mov     cr3, eax
        mov     cr4, eax

        jmp     @f
ALIGN 16
@@:

;
; Save the IDT.
;
             
        mov     eax, OFFSET BlProtModeIdtr
        add     eax, REAL_MODE_BASE
        sidt    fword ptr ds:[eax]
           
ifdef BOOT_X64        

;
; Disable long mode and return to legacy protected-mode.
;

        mov     ecx, EFER_MSR_INDEX
        rdmsr
        and     eax, NOT (EFER_LME OR EFER_NXE)
        wrmsr
endif
        
;
; Return to real-mode code.
;

        JMPF32  RM_CODE_SELECTOR, OFFSET BlReturnToRealMode

BlLeaveProtectedMode    endp

;++
;
; PVOID
; BlLoadImage(
;     VOID
;     )
;
; Routine Description:
;
;   This function loads the higher-level boot loader image.
;
; Return Value:
;
;   Entry point address for the loaded image.
;
;--

BlLoadImage     proc

        lea     ebp, OFFSET BlImageStart
        add     ebp, REAL_MODE_BASE

;
; Check DOS signature.
;

        cmp     word ptr [ebp], IMAGE_DOS_SIGNATURE
        jne     BlInvalidImage

;
; Calculate NT header address.
;

        mov     ebx, dword ptr [ebp + IDH_NT_HEADER_OFFSET]
        add     ebx, ebp

;
; Check NT signature.
;

        cmp     dword ptr [ebx + INH_SIGNATURE], IMAGE_NT_SIGNATURE
        jne     BlInvalidImage

;
; Check image base.
;

ifdef BOOT_X64        
        cmp     dword ptr [ebx + INH_OPTIONAL_HEADER + IOH64_IMAGE_BASE + 4], 0
        jne     BlInvalidImage

        cmp     dword ptr [ebx + INH_OPTIONAL_HEADER + IOH64_IMAGE_BASE], IMAGE_ADDRESS
else
        cmp     dword ptr [ebx + INH_OPTIONAL_HEADER + IOH32_IMAGE_BASE], IMAGE_ADDRESS
endif
        jne     BlInvalidImage

;
; Copy headers.
;

        mov     esi, ebp
        mov     edi, IMAGE_ADDRESS
        mov     ecx, dword ptr [ebx + INH_OPTIONAL_HEADER + IOH_SIZE_OF_HEADERS]
        rep movsb

;
; Calculate the address of first section header.
;
; SectionHeader = (PIMAGE_SECTION_HEADER) (((ULONG_PTR) &NtHeaders->OptionalHeader) + NtHeaders->FileHeader.SizeOfOptionalHeader)
;

        xor     esi, esi
        mov     si, word ptr [ebx + INH_FILE_HEADER + IFH_SIZE_OF_OPTIONAL_HEADER]
        add     esi, INH_OPTIONAL_HEADER
        add     esi, ebx

        xor     ecx, ecx
        mov     cx, word ptr [ebx + INH_FILE_HEADER + IFH_NUMBER_OF_SECTIONS]
        cmp     cx, 0
        jne     @f

        call    BlInvalidImage

;
; for (Index = 0; Index < NtHeaders->FileHeader.NumberOfSections; Index += 1) {
;
;     BlCopySection(DosHeader, &SectionHeader[Index]);
; }
;

@@:

        push    ecx

        mov     ecx, ebp
        mov     edx, esi

        call    BlCopySection

        pop     ecx

        add     esi, IMAGE_SECTION_HEADER_SIZE

        dec     ecx
        jnz     @b

        mov     eax, dword ptr [ebx + INH_OPTIONAL_HEADER + IOH_ADDRESS_OF_ENTRY_POINT]
        add     eax, IMAGE_ADDRESS
        ret

BlLoadImage     endp

;++
;
; VOID
; FASTCALL
; BlCopySection(
;     PIMAGE_DOS_HEADER DosHeader,
;     PIMAGE_SECTION_HEADER SectionHeader
;     )
;
; Routine Description:
;
;   This function copies the specified image section.
;
; Arguments:
;
;   DosHeader (ecx)     - Supplies a pointer to the source image to copy from.
;
;   SectionHeader (edx) - Supplies a pointer to the section header describing
;                         the section to copy.
;
;--

BlCopySection   proc

;
; Create call frame and save non-volatile registers that will be used.
;

        push    ebp
        mov     ebp, esp

        push    esi
        push    edi

;
; Calculate source and destination address for the copy operation.
;

        mov     esi, dword ptr [edx + ISH_POINTER_TO_RAW_DATA]
        add     esi, ecx

        mov     edi, dword ptr [edx + ISH_VIRTUAL_ADDRESS]
        add     edi, IMAGE_ADDRESS

;
; Save source and destination addresses -- rep stosb below will use them.
;

        push    esi
        push    edi

;
; Zero the entire target virtual range.
;

        mov     eax, 0
        mov     ecx, dword ptr [edx + ISH_VIRTUAL_SIZE]
        rep stosb

;
; Restore source and destination addresses.
;

        pop     edi
        pop     esi

;
; BytesToCopy = min(SectionHeader->VirtualSize, SectionHeader->SizeOfRawData)
;
        mov     ecx, dword ptr [edx + ISH_VIRTUAL_SIZE]
        cmp     ecx, dword ptr [edx + ISH_SIZE_OF_RAW_DATA]
        jl      @f

        mov     ecx, dword ptr [edx + ISH_SIZE_OF_RAW_DATA]

@@:

;
; Perform copy.
;

        rep movsb

;
; Restore used non-volatile registers, base pointer, and return.
;

        pop     edi
        pop     esi
        mov     esp, ebp
        pop     ebp
        ret

BlCopySection   endp

;++
;
; VOID
; BlInvalidImage(
;     VOID
;     )
;
; Routine Description:
;
;   This function is called to halt execution if the embedded image is corrupted.
;
;--

BlInvalidImage  proc

        call    BlHalt

BlInvalidImage  endp

;++
;
; VOID
; BlRegisterExitAddress(
;     VOID
;     )
;
; Routine Description:
;
;   This function registers the exit address in the boot environment block.
;
;--

BlRegisterExitAddress   proc

        mov     ecx, BEB_BASE

        lea     eax, BlLeaveProtectedMode
        add     eax, REAL_MODE_BASE

        mov     dword ptr [ecx].BEB.LegacyCallAddress, eax

        ret

BlRegisterExitAddress   endp

;++
;
; VOID
; BlApEntry32(
;     VOID
;     )
;
; Routine Description:
;
;   This function implements 32-bit entry point for application processors.
;
;--

BlApEntry32     proc

;
; Load the protected-mode segment registers.
;
        mov     ax, PM_DATA_SELECTOR
        mov     ds, ax
        mov     es, ax
        mov     ss, ax
        mov     esp, PM_INITIAL_ESP

        mov     ax, NULL_SELECTOR
        mov     fs, ax
        mov     gs, ax

;
; Enable PSE, PAE, performance counters, and floating point support.
;

        mov     eax, cr4
        or      eax, CR4_PSE OR CR4_PAE OR CR4_PCE OR CR4_OSFXSR
        mov     cr4, eax

;
; Set root page table.
;

        mov     eax, BEB_BASE
        mov     eax, dword ptr [eax].BEB.LegacyReturnCr3
        mov     cr3, eax

ifdef BOOT_X64        
;
; Enable long-mode and no-execute.
;

        mov     ecx, EFER_MSR_INDEX
        rdmsr
        or      eax, EFER_LME OR EFER_NXE
        wrmsr
endif
        
;
; Enable paging.
;

        mov     eax, cr0
        or      eax, CR0_PG
        mov     cr0, eax

;
; Get entry address from BEB.
;

        mov     eax, BEB_BASE
        mov     eax, dword ptr [eax].BEB.ApEntry

ifdef BOOT_X64
;
; Enter long mode.
;

        JMPF32  LM_CODE_SELECTOR, REAL_MODE_BASE + OFFSET @f
@@:

        mov     edx, LM_DATA_SELECTOR
        mov     ds, edx
        mov     es, edx
        mov     ss, edx
endif

;
; Switch to entry stack and call entry point.
;

        mov     esp, BL_ENTRY_SP
        call    eax

BlApEntry32     endp

        
;++
;
; VOID
; BlLeaveLrb64ToBoot(
;     VOID
;     )
;
; Routine Description:
;
;   This function leaves paging and protected mode to boot.
;
;--

ALIGN 16

        db      'S','I','N','G'
        db      'L','R','B',0
        db      0f8h, 0f9h, 0fah, 0fbh
        db      0fch, 0fdh, 0feh, 0ffh
BlFlashImage:         
        dd      0
BlSmapAddr:             
        dd      0
BlSmapSize:             
        dd      0
        dd      0
        
BlLeaveLrb64ToBoot    proc
        mov     eax, BLUE + 'P'
        mov     esi, VIDEO_BASE + 0
        mov     [esi], ax
        
        mov     eax, BLUE + 'O'
        mov     esi, VIDEO_BASE + 2
        mov     [esi], ax

        mov     eax, BLUE + 'N'
        mov     esi, VIDEO_BASE + 4
        mov     [esi], ax

        mov     eax, BLUE + 'M'
        mov     esi, VIDEO_BASE + 6
        mov     [esi], ax

        mov     eax, BLUE + 'L'
        mov     esi, VIDEO_BASE + 8
        mov     [esi], ax

;
; Prepare a known GDT.
;
        mov     eax, BLUE + 'K'
        mov     esi, VIDEO_BASE + 10
        mov     [esi], ax

        mov     eax, BLUE + 'J'
        mov     esi, VIDEO_BASE + 12
        mov     [esi], ax

;
; Load the known GDT.
;
        
        mov     edi, BlGDTS_Limit
        add     edi, REAL_MODE_BASE
        lgdt    fword ptr ds:[edi]
        
        mov     eax, RED + 'R'
        mov     esi, VIDEO_BASE + 8
        mov     [esi], ax

        mov     eax, RED + 'S'
        mov     esi, VIDEO_BASE + 10
        mov     [esi], ax

        mov     edi, REAL_MODE_BASE + offset target
        jmp     fword ptr [edi]
target: 
        dd      OFFSET BlLeaveLrbPmToBoot
        dw      RM_CODE_SELECTOR
        
BlLeaveLrb64ToBoot    endp

;
; Align to 16-bytes before PE image is concatenated.
;
        
ALIGN 16

BlImageStart:

_TEXT32 ends

end BlEntry16
