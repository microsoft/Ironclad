
/***********************************************************
 * Spec for granting permission to interact with IO memory *
 ***********************************************************/

datatype {:imported} IoMemPerm_t = Null() | IoReadAddr(r_addr:int, r_val:int) | IoWriteAddr(w_addr:int, w_val:int);

ghost var {:imported} {:readonly} IoMemPerm:IoMemPerm_t;

