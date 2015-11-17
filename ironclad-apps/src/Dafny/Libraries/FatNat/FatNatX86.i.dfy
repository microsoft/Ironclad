include "FatNatCommon.i.dfy"
include "../BigNum/BigNatX86Shim.i.dfy"
//-include "FatNatX86big.i.dfy"

method {:decl} Add32_unrolled_8(
    a:array<int>, ai:int,
    b:array<int>, bi:int,
    s:array<int>, si:int,
    c_in:int)
    returns (c_out:int, ghost carries:seq<int>)
    requires a!=null;
    requires IsWordSeq(a[..]);
    requires 0 <= ai;
    requires ai+8 <= a.Length;
    requires b!=null;
    requires IsWordSeq(b[..]);
    requires 0 <= bi;
    requires bi+8 <= b.Length;
    requires s!=null;
    requires 0 <= si;
    requires si+8 <= s.Length;
    requires 0<=c_in<=1;
    requires b!=s;
    requires a!=s;
    modifies s;
    ensures forall i :: 0<=i<s.Length && !(si<=i<si+8) ==> s[s.Length-1-i]==old(s[s.Length-1-i]);
    ensures 0<=c_out<=1;
    ensures |carries| == 9;
    ensures carries[0] == c_in;
    ensures carries[8] == c_out;
    ensures forall i :: 0<=i<8 ==> carries[i+1] == 
            if a[a.Length-1-(ai+i)] +b[b.Length-1-(bi+i)] + carries[i] >= 0x100000000 then 1 else 0;
    ensures forall i {:trigger s[FatNatAddIndex(s.Length, si, i)]} :: 0<=i<8 ==> s[FatNatAddIndex(s.Length, si, i)] ==  
        mod0x100000000(a[FatNatAddIndex(a.Length, ai,i)] +b[FatNatAddIndex(b.Length, bi, i)] + carries[i]);


method {:decl} Add32_unrolled_16(
    a:array<int>, ai:int,
    b:array<int>, bi:int,
    s:array<int>, si:int,
    c_in:int)
    returns (c_out:int, ghost carries:seq<int>)
    requires a!=null;
    requires IsWordSeq(a[..]);
    requires 0 <= ai;
    requires ai+16 <= a.Length;
    requires b!=null;
    requires IsWordSeq(b[..]);
    requires 0 <= bi;
    requires bi+16 <= b.Length;
    requires s!=null;
    requires 0 <= si;
    requires si+16 <= s.Length;
    requires 0<=c_in<=1;
    requires b!=s;
    requires a!=s;
    modifies s;
    ensures forall i :: 0<=i<s.Length && !(si<=i<si+16) ==> s[s.Length-1-i]==old(s[s.Length-1-i]);
    ensures 0<=c_out<=1;
    ensures |carries| == 17;
    ensures carries[0] == c_in;
    ensures carries[16] == c_out;

    ensures forall i {:trigger a[FatNatAddIndex(a.Length, ai, i)]} :: 0<=i<16 ==> carries[i+1] == 
            if a[FatNatAddIndex(a.Length,ai,i)] +b[FatNatAddIndex(b.Length,bi,i)] + carries[i] >= 0x100000000 then 1 else 0;
    ensures forall i {:trigger s[FatNatAddIndex(s.Length, si, i)]} :: 0<=i<16 ==> s[FatNatAddIndex(s.Length, si, i)] ==  
        mod0x100000000(a[FatNatAddIndex(a.Length, ai,i)] +b[FatNatAddIndex(b.Length, bi, i)] + carries[i]);
