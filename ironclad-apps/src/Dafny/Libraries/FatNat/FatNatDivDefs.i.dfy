include "FatNatCommon.i.dfy"
include "FatNatMul.i.dfy"
include "FatNatSub.i.dfy"
include "FatNatCompare.i.dfy"
include "../Util/seqs_canonical.i.dfy"

datatype FNDivData = FNDivData_c(
    n:array<int>, dv:array<int>, r:array<int>, q:array<int>);

datatype FNDivGhost = FNDivGhost_c(
    Ns:seq<int>,
    Ds:seq<int>,
    Rs:seq<int>,
    Qs:seq<int>,
    wks:seq<MulRow>,
    remainders:seq<int>);

predicate {:heap} FNDivision_invariant(d:FNDivData, g:FNDivGhost)
    reads d.n;
    reads d.dv;
    reads d.r;
    reads d.q;
{
       d.n != null
    && d.dv != null
    && d.r != null
    && d.n[..] == g.Ns
    && d.dv[..] == g.Ds
    && d.r[..] == g.Rs
    && d.q != null
    && d.q[..] == g.Qs
    && IsWordSeq(g.Ns)
    && IsWordSeq(g.Ds)

    && IsWordSeq(g.Rs)
//-    && IsCanonicalDigitSeq(power2(32), g.Rs)
//-    && |g.Ns| < power2(27)

    && BEWordSeqToInt(g.Rs) <= BEWordSeqToInt(g.Ns)
    && IsWordSeq(g.Qs)
    && 1 < BEWordSeqToInt(g.Ds)
    && FNMulProblemValid_partial(g.wks, BEWordSeqToInt(g.Ds), 0)
    && |g.wks| == |g.remainders|
    && g.remainders[|g.remainders|-1] == BEWordSeqToInt(g.Rs)
    && g.wks[|g.wks|-1].a_partial_sum == BEWordSeqToInt(g.Qs)
    && (forall i :: 0<=i<|g.wks| ==>
        g.wks[i].product + g.remainders[i] == BEWordSeqToInt(g.Ns))
//-    && (forall i :: 1<=i<|g.wks| ==>
//-        g.wks[i].product + g.remainders[i] == g.wks[i-1].product + g.remainders[i-1])
}
