//++
//
//  Copyright (c) Microsoft Corporation
//
//  Module Name:
//
//    bltrap.cpp
//
//  Abstract:
//
//    This module implements trap capture.
//
//--


#include "bl.h"

IDTR    BlIdtr;
IDTE    BlIdt[32];

VOID
BlTrapEnable(
    VOID
    )

//++
//

{
    for (UINT32 i = 0; i < ARRAY_SIZE(BlIdt); i++) {

        UINT64 Enter = ((UINT64)BlTrapEnter) + i * 8;

        BlIdt[i].Offset0To15  =(UINT16)((Enter >>  0) & 0xffff);
        BlIdt[i].Offset16To31 = (UINT16)((Enter >> 16) & 0xffff);
#if defined(BOOT_X64)
        BlIdt[i].Selector = LM_CODE_SELECTOR;
#else
        BlIdt[i].Selector = PM_CODE_SELECTOR;
#endif
        BlIdt[i].Flags = 0;
        BlIdt[i].Access = 0x8e;

#if defined(BOOT_X64)
        BlIdt[i].Offset32To63 = (UINT32)((Enter >> 32) & 0xffffffff);
#endif

    }
    BlIdtr.Limit = 32 * 8;
    BlIdtr.Base = (UINT64)BlIdt;

    BlTrapSetIdtr(&BlIdtr);
}

VOID
BlTrapFatal(
    ULONG_PTR Trap,
    PBL_TRAP_CONTEXT Context
    )

//++
//
//  Routine Description:
//
//    This function returns the specified memory type string.
//
//  Arguments:
//
//    Type    - Supplies the memory type.
//
//--

{
    BlVideoPrintf("\n*** Fatal Trap: 0x%2x:%p [err=%p]\n",
                  Trap, Context, Context->Err);

#if defined(BOOT_X86)

    BlVideoPrintf("  eip=%p efl=%p cr2=%p cs=%2x num=%02x\n",
                  Context->Eip, Context->Efl, Context->Cr2,
                  (UINT32)Context->Cs0, (UINT32)Context->Num);
    BlVideoPrintf("  eax=%p ebx=%p ecx=%p edx=%p\n",
                  Context->Eax, Context->Ebx, Context->Ecx, Context->Edx);
    BlVideoPrintf("  esp=%p ebp=%p esi=%p edi=%p\n",
                  Context->Esp, Context->Ebp, Context->Esi, Context->Edi);

    ULONG_PTR * ebp = (ULONG_PTR *)Context->Ebp;
    BlVideoPrintf("\n");
    BlVideoPrintf("     Frame:     next   return     arg0     arg1     arg2     arg3\n");
    for (int i = 0; i < 10; i++) {
        if (ebp < (ULONG_PTR*)0x10000 || ebp > (ULONG_PTR*)0x7fffffff) {
            BlVideoPrintf("  %8x:\n", (ULONG_PTR)ebp);
            break;
        }
        ULONG_PTR *end = (ULONG_PTR *)ebp[0];
        if (end < ebp) {
            end = ebp + 6;
        }

        BlVideoPrintf("  %p: %p %p",
                      (ULONG_PTR)ebp, ebp[0], ebp[1]);
        for (int i = 2; i < 6 && ebp + i < end; i++) {
            BlVideoPrintf(" %p", ebp[i]);
        }
        BlVideoPrintf("\n");

        ebp = (ULONG_PTR *)ebp[0];
    }

    BlVideoPrintf("\n");
    ULONG_PTR * esp = (ULONG_PTR *)(Context->Esp);
    for (int i = 0; i < 6; i++) {
        BlVideoPrintf("  %p: %p %p %p %p\n", esp, esp[0], esp[1], esp[2], esp[3]);
        esp += 4;
    }
    BlVideoPrintf("\n");

    esp = (ULONG_PTR *)(Context);
    for (int i = 0; i < 6; i++) {
        BlVideoPrintf("  %p: %p %p %p\n", esp, esp[0], esp[1], esp[2], esp[3]);
        esp += 4;
    }

    BlVideoPrintf("\n");
    UINT8 * eip = (UINT8 *)Context->Eip;
    BlVideoPrintf("  %p:", eip);
    for (int i = 0; i < 12; i++) {
        BlVideoPrintf(" %02x", eip[i]);
    }

    BlVideoPrintf("\n");

#elif defined(BOOT_X64)

    BlVideoPrintf("  rip=%p rfl=%p cs=%2x num=%02x\n",
                  Context->Rip, Context->Rfl, (UINT32)Context->Cs0, (UINT32)Context->Num);
    BlVideoPrintf("  rsp=%p rbp=%p cr2=%p\n",
                  Context->Rsp, Context->Rbp, Context->Cr2);
    BlVideoPrintf("  rax=%p rbx=%p rcx=%p\n",
                  Context->Rax, Context->Rbx, Context->Rcx);
    BlVideoPrintf("  rdx=%p rsi=%p rdi=%p\n",
                  Context->Rdx, Context->Rsi, Context->Rdi);
    BlVideoPrintf("  r08=%p r09=%p r10=%p\n",
                  Context->R8, Context->R9, Context->R10);
    BlVideoPrintf("  r11=%p r12=%p r13=%p\n",
                  Context->R11, Context->R12, Context->R13);
    BlVideoPrintf("  r14=%p r15=%p\n",
                  Context->R14, Context->R15);

    ULONG_PTR * rbp = (ULONG_PTR *)Context->Rbp;
    BlVideoPrintf("\n");
    BlVideoPrintf("             Frame:             next           return             arg0\n");
    for (int i = 0; i < 10; i++) {
        if (rbp < (ULONG_PTR*)0x10000 || rbp > (ULONG_PTR*)0x7fffffff) {
            BlVideoPrintf("  %p:\n", (ULONG_PTR)rbp);
            break;
        }
        ULONG_PTR *end = (ULONG_PTR *)rbp[0];
        if (end < rbp) {
            end = rbp + 3;
        }

        BlVideoPrintf("  %p: %p %p",
                      (ULONG_PTR)rbp, rbp[0], rbp[1]);
        for (int i = 2; i < 3 && rbp + i < end; i++) {
            BlVideoPrintf(" %p", rbp[i]);
        }
        BlVideoPrintf("\n");

        rbp = (ULONG_PTR *)rbp[0];
    }

    BlVideoPrintf("\n");
    ULONG_PTR * rsp = (ULONG_PTR *)(Context->Rsp);
    for (int i = 0; i < 6; i++) {
        BlVideoPrintf("  %p: %p %p %p\n", rsp, rsp[0], rsp[1], rsp[2]);
        rsp += 3;
    }
    BlVideoPrintf("\n");

    rsp = (ULONG_PTR *)(Context);
    for (int i = 0; i < 6; i++) {
        BlVideoPrintf("  %p: %p %p %p\n", rsp, rsp[0], rsp[1], rsp[2]);
        rsp += 3;
    }

    BlVideoPrintf("\n");
    UINT8 * rip = (UINT8 *)Context->Rip;
    BlVideoPrintf("  %p:", rip);
    for (int i = 0; i < 12; i++) {
        BlVideoPrintf(" %02x", rip[i]);
    }

    BlVideoPrintf("\n");

#endif

    for (;;);
}

