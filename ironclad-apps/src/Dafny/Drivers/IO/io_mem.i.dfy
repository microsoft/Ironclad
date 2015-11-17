include "io_mem.s.dfy"

/******************************************************
 * Connection to Verve for interacting with IO memory *
 ******************************************************/

method {:decl} IoMemAddrRead(r_addr:int) returns (r_val:int)
    requires IoMemPerm.IoReadAddr?;
    requires IoMemPerm.r_addr == r_addr;
    modifies this`IoMemPerm;
    ensures  IoMemPerm.Null?;
    ensures  r_val == old(IoMemPerm).r_val;

method {:decl} IoMemAddrWrite(w_addr:int, w_val:int)
    requires IoMemPerm.IoWriteAddr?;
    requires IoMemPerm.w_addr == w_addr;
    requires IoMemPerm.w_val  == w_val;
    modifies this`IoMemPerm;
    ensures  IoMemPerm.Null?;
    
