include "FatNatCommon.i.dfy"
include "../BigNum/BigNatX86Shim.i.dfy"

/*
method {:decl} Add32_unrolled_32(
    a:array<int>, ai:int,
    b:array<int>, bi:int,
    s:array<int>, si:int,
    c_in:int)
    returns (c_out:int, ghost carries:seq<int>)
    requires a!=null;
    requires IsWordSeq(a[..]);
    requires 0 <= ai;
    requires ai+32 <= a.Length;
    requires b!=null;
    requires IsWordSeq(b[..]);
    requires 0 <= bi;
    requires bi+32 <= b.Length;
    requires s!=null;
    requires 0 <= si;
    requires si+32 <= s.Length;
    requires 0<=c_in<=1;
    requires b!=s;
    requires a!=s;
    modifies s;
    ensures forall i :: 0<=i<s.Length && !(si<=i<si+32) ==> s[s.Length-1-i]==old(s[s.Length-1-i]);
    ensures 0<=c_out<=1;
    ensures |carries| == 33;
    ensures carries[0] == c_in;
    ensures carries[32] == c_out;
    //- This line will go through in 347s
    ensures forall i {:trigger a[FatNatAddIndex(a.Length, ai, i)]} :: 0<=i<32 ==> carries[i+1] == 
            if a[FatNatAddIndex(a.Length,ai,i)] +b[FatNatAddIndex(b.Length,bi,i)] + carries[i] >= 0x100000000 then 1 else 0;
    //- This line times out after 687s
    ensures forall i {:trigger s[FatNatAddIndex(s.Length, si, i)]} :: 0<=i<32 ==> s[FatNatAddIndex(s.Length, si, i)] ==  
        mod0x100000000(a[FatNatAddIndex(a.Length, ai,i)] +b[FatNatAddIndex(b.Length, bi, i)] + carries[i]);
*/
