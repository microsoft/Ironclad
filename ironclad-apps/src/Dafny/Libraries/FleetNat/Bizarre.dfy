include "../FatNat/FatNatCommon.i.dfy"
include "FleetNatCommon.i.dfy"

lemma lemma_asm_Sub_properties(x:int, y:int, z:int, c:int)
    requires word32(x);
    requires word32(y);
    requires word32(z);
    requires 0<=c<2;
    requires z == mod0x100000000(x - y);
    ensures z == (x - y) % 0x100000000;
    ensures x-y == z - 0x100000000*c;
{
    assume false;
}

lemma lemma_FleetNatSub_core(pv:int, oldcs:seq<int>, lastcs:seq<int>, bs:seq<int>, bdigits:int, cs:seq<int>, lastj:int, j:int, lastborrow:int, borrow:int)
    requires 1<=j<=bdigits<=|oldcs|==|lastcs|==|cs|;
    requires bdigits <= |bs|;
    requires lastj+1 == j;
    requires 0<=lastborrow<2;
    requires 0<=borrow<2;
    requires pv==power2(32)==0x100000000;
    requires IsDigitSeq(power2(32), oldcs);
    requires IsDigitSeq(power2(32), bs);
    requires IsDigitSeq(power2(32), cs);
    requires IsDigitSeq(power2(32), lastcs);
    requires BEWordSeqToInt(oldcs) - BEWordSeqToInt(bs) ==
            ( BEWordSeqToInt(SelectDigitRange(lastcs, |lastcs|, lastj))
              + lastborrow
              - BEWordSeqToInt(SelectDigitRange(bs, bdigits, lastj)) ) * power(pv,lastj)
            + BEWordSeqToInt(SelectDigitRange(lastcs, lastj, 0));
    ensures IsDigitSeq(power2(32), cs);
    ensures BEWordSeqToInt(oldcs) - BEWordSeqToInt(bs) ==
            ( BEWordSeqToInt(SelectDigitRange(cs, |cs|, j))
              + borrow
              - BEWordSeqToInt(SelectDigitRange(bs, bdigits, j)) ) * power(pv,j)
            + BEWordSeqToInt(SelectDigitRange(cs, j, 0));
{
    assume false;
}

lemma lemma_FleetNatSub_c_adequate_length(cs:seq<int>, bs:seq<int>, bdigits:int)
    requires IsWordSeq(cs);
    requires IsWordSeq(bs);
    requires BEWordSeqToInt(bs) <= BEWordSeqToInt(cs);
    requires (BEWordSeqToInt(bs)==0 && bdigits==0)
        || (0<bdigits && power(power2(32), bdigits-1) <= BEWordSeqToInt(bs));
    ensures bdigits<=|cs|;
{
    ghost var pv := power2(32); lemma_2toX();
    if (|cs| < bdigits)
    {
        calc {
        BEWordSeqToInt(cs);
        <   { lemma_BEDigitSeqToInt_bound(pv, cs); }
        power(pv, |cs|);
        <=  { lemma_power_increases(pv, |cs|, bdigits-1); }
        power(pv, bdigits-1);
        <=
        BEWordSeqToInt(bs);
        }   //- contradiction
    }
}

method FleetNatSub(c:array<int>, b:array<int>)
    //- always in-place because c always has enough room!
    requires b!=null;
    requires IsWordSeq(b[..]);
    requires c!=null;
    requires IsWordSeq(c[..]);
    requires c!=b;
    requires BEWordSeqToInt(b[..]) <= BEWordSeqToInt(c[..]);
    modifies c;
    ensures IsWordSeq(c[..]);
    ensures BEWordSeqToInt(old(c[..])) - BEWordSeqToInt(b[..]) == BEWordSeqToInt(c[..]);
{
    ghost var pv := power2(32); lemma_2toX();

    var bdigits := CountNonzeroDigits(b);

    lemma_FleetNatSub_c_adequate_length(c[..], b[..], bdigits);

    var borrow := 0;
    var blenm1 := b.Length - 1;
    var clenm1 := c.Length - 1;
    var j:=0;

    //- bridge from preconditions to subtract loop invariant
    calc {
        BEWordSeqToInt(old(c[..])) - BEWordSeqToInt(b[..]);
            { lemma_power_0(pv); }
        ( BEWordSeqToInt(c[..]) - BEWordSeqToInt(b[..]) ) * power(pv,j);
            {
                assert SelectDigitRange(c[..], c.Length, j) == c[..]; //- OBSERVE SEQ
            }
        ( BEWordSeqToInt(SelectDigitRange(c[..], c.Length, j))
          + borrow
          - BEWordSeqToInt(SelectDigitRange(b[..], bdigits, j)) ) * power(pv,j);
            {
                assert SelectDigitRange(c[..], j, 0)==[];   //- OBSERVE SEQ
                reveal_BEDigitSeqToInt_private();
            }
        ( BEWordSeqToInt(SelectDigitRange(c[..], c.Length, j))
          + borrow
          - BEWordSeqToInt(SelectDigitRange(b[..], bdigits, j)) ) * power(pv,j)
        + BEWordSeqToInt(SelectDigitRange(c[..], j, 0));
    }

    var C, B;
    assume C - B == borrow; 

    while (j<bdigits)
        invariant 0<=j<=bdigits;
        invariant IsWordSeq(b[..]);
        invariant IsWordSeq(c[..]);
        invariant IsWordSeq(SelectDigitRange(c[..], c.Length, j));
        invariant 0<=borrow<2;
        invariant C - B == borrow;
        invariant BEWordSeqToInt(old(c[..])) - BEWordSeqToInt(b[..]) ==
            ( BEWordSeqToInt(SelectDigitRange(c[..], c.Length, j))
              + borrow
              - BEWordSeqToInt(SelectDigitRange(b[..], bdigits, j)) ) * power(pv,j)
            + BEWordSeqToInt(SelectDigitRange(c[..], j, 0));
    {
        ghost var lastcs := c[..];
        ghost var lastborrow := borrow;
        ghost var lastj := j;

        var ci := clenm1 - j;
        var lastcj := c[ci];
        var borrow := 0;    // Could this shadowed variable be the problem? This should be an error!
        if (lastcj < borrow) { borrow := 1; }
        ghost var midborrow := borrow;
        lemma_word32(lastcj);
        lemma_word32(borrow);
        var midcj := asm_Sub(lastcj, borrow);

        var bj := b[blenm1 - j];
        lemma_word32(1);
        if (midcj < bj) {
//-            borrow := asm_Add(borrow, 1);
//-            borrow := borrow + 1;
            
            
            //-var dbg_lastborrow := borrow;
            
            var dbg_lastborrow := 7;
            borrow := dbg_lastborrow + 1;
        }
        lemma_word32(bj);
        var newcj := asm_Sub(midcj, bj);
        c[ci] := newcj;

        j := j+1;
        assume 0<=borrow<2;
        assume 0<=newcj<pv;

        lemma_FleetNatSub_core(pv, old(c[..]), lastcs, b[..], bdigits, c[..], lastj, j, lastborrow, borrow);

        assert BEWordSeqToInt(old(c[..])) - BEWordSeqToInt(b[..]) ==
            ( BEWordSeqToInt(SelectDigitRange(c[..], c.Length, j))
              + borrow
              - BEWordSeqToInt(SelectDigitRange(b[..], bdigits, j)) ) * power(pv,j)
            + BEWordSeqToInt(SelectDigitRange(c[..], j, 0));
    }

    //- bridge from subtract loop invariant to borrow loop invariant
    calc {
        BEWordSeqToInt(SelectDigitRange(b[..], bdigits, j));
            { assert SelectDigitRange(b[..], bdigits, j)==[]; /*OBSERVE SEQ*/ }
        BEWordSeqToInt([]);
            { reveal_BEDigitSeqToInt_private(); }
        0;
    }

    //- propagate borrow
    while (j<c.Length)
        invariant 0<=j<=c.Length;
        invariant IsWordSeq(c[..]);
        invariant BEWordSeqToInt(old(c[..])) - BEWordSeqToInt(b[..]) ==
            ( BEWordSeqToInt(SelectDigitRange(c[..], c.Length, j))
              + borrow) * power(pv,j)
            + BEWordSeqToInt(SelectDigitRange(c[..], j, 0));
    {
        assume false;
        j := j + 1;
    }

    //- bridge from borrow loop invariant to postcondition
    lemma_BEInterpretation_Select(pv, c[..], j);
//-    assert borrow==0;
//-    calc {
//-        BEWordSeqToInt(old(c[..])) - BEWordSeqToInt(b[..]);
//-        ( BEWordSeqToInt(SelectDigitRange(c[..], c.Length, j))
//-          + borrow) * power(pv,j)
//-            + BEWordSeqToInt(SelectDigitRange(c[..], j, 0));
//-        BEWordSeqToInt(SelectDigitRange(c[..], c.Length, j)) * power(pv,j)
//-            + BEWordSeqToInt(SelectDigitRange(c[..], j, 0));
//-            { lemma_BEInterpretation_Select(pv, c[..], j); }
//-        BEWordSeqToInt(c[..]);
//-    }
}

method foo()
{
    var borrow:int;
    var C,B;
    assume C - B == borrow;
    var digits;
    assume 0<=digits;
    var j:=0;
    while (j<digits)
        invariant C-B==borrow;
    {
        borrow := 6;
        j := j + 1;
    }
}
