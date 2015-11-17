include "../FatNat/FatNatCommon.i.dfy"
include "FleetNatCommon.i.dfy"
//-include "FleetNatSubOpt.i.dfy"

lemma lemma_asm_Sub_properties(x:int, y:int, z:int, c:int)
    requires word32(x);
    requires word32(y);
    requires word32(z);
    requires 0<=c<2;
    requires c==1 <==> x < y;
    requires z == mod0x100000000(x - y);
    ensures z == (x - y) % 0x100000000;
    ensures x-y == z - 0x100000000*c;
{
    var pv := 0x100000000;
    lemma_mod0x100000000(x-y);
    lemma_word32(x);
    lemma_word32(y);
    lemma_mod_properties();
    lemma_fundamental_div_mod(x-y, pv);
}

lemma lemma_FleetNatSub_local_math(pv:int, lastcj:int, newcj:int, midcj:int, bj:int, lastborrow:int, borrow1:int, borrow2:int, borrow:int)
    requires pv==power2(32)==0x100000000;
    requires 0<=lastcj<pv;
    requires 0<=newcj<pv;
    requires 0<=midcj<pv;
    requires 0<=bj<pv;
    requires 0<=lastborrow<2;
    requires 0<=borrow1<2;
    requires 0<=borrow2<2;
    requires borrow == (borrow1 + borrow2) % pv;
    requires lastcj-lastborrow == midcj - pv*borrow1;
    requires midcj-bj == newcj - pv*borrow2;
    ensures lastcj - lastborrow - bj == newcj - pv*borrow;
{
    calc {
        lastcj - lastborrow - bj;
        midcj - pv*borrow1 - bj;
        - pv*borrow1 + newcj - pv*borrow2;
        newcj - pv*borrow;
    }
}




lemma lemma_FleetNatSub_rearrangement_left(pv:int, lastcs:seq<int>, cs:seq<int>, lastj:int, j:int, lastborrow:int)
    requires 1<=j<=|lastcs|==|cs|;
    requires lastj+1 == j;
    requires 0<=lastborrow<2;
    requires pv==power2(32)==0x100000000;
    requires IsDigitSeq(power2(32), cs);
    requires IsDigitSeq(power2(32), lastcs);
    requires SelectDigitRange(lastcs, |lastcs|, j) == SelectDigitRange(cs, |cs|, j); //- stability
    requires SelectDigitRange(lastcs, lastj, 0) == SelectDigitRange(cs, lastj, 0); //- stability
    ensures
        BEWordSeqToInt(SelectDigitRange(lastcs, |lastcs|, lastj)) * power(pv,lastj)
          - lastborrow * power(pv,lastj)
          + BEWordSeqToInt(SelectDigitRange(lastcs, lastj, 0))
        == BEWordSeqToInt(SelectDigitRange(cs, |cs|, j)) * power(pv,j)
            + DigitAt(lastcs, lastj) * power(pv,lastj)
          - lastborrow * power(pv,lastj)
          + BEWordSeqToInt(SelectDigitRange(cs, lastj, 0));
{
    calc {
        BEWordSeqToInt(SelectDigitRange(lastcs, |lastcs|, lastj)) * power(pv,lastj)
          - lastborrow * power(pv,lastj)
          + BEWordSeqToInt(SelectDigitRange(lastcs, lastj, 0));
            { lemma_BEInterpretation_Select_general(pv, lastcs, |lastcs|, j, lastj); }
        ( BEWordSeqToInt(SelectDigitRange(lastcs, |lastcs|, j)) * power(pv,1)
            + BEWordSeqToInt(SelectDigitRange(lastcs, j, lastj)) ) * power(pv,lastj)
          - lastborrow * power(pv,lastj)
          + BEWordSeqToInt(SelectDigitRange(lastcs, lastj, 0));
            { lemma_mul_is_distributive_forall(); }
        BEWordSeqToInt(SelectDigitRange(lastcs, |lastcs|, j)) * power(pv,1) * power(pv,lastj)
            + BEWordSeqToInt(SelectDigitRange(lastcs, j, lastj)) * power(pv,lastj)
          - lastborrow * power(pv,lastj)
          + BEWordSeqToInt(SelectDigitRange(lastcs, lastj, 0));
            { lemma_mul_is_associative_forall(); lemma_power_adds(pv, 1, lastj); }
        BEWordSeqToInt(SelectDigitRange(lastcs, |lastcs|, j)) * power(pv,j)
            + BEWordSeqToInt(SelectDigitRange(lastcs, j, lastj)) * power(pv,lastj)
          - lastborrow * power(pv,lastj)
          + BEWordSeqToInt(SelectDigitRange(lastcs, lastj, 0));
            { lemma_SelectSingletonRange(lastcs, j, lastj);
              lemma_BEDigitSeqToInt_singleton(pv, DigitAt(lastcs,lastj)); }
        BEWordSeqToInt(SelectDigitRange(lastcs, |lastcs|, j)) * power(pv,j)
            + DigitAt(lastcs, lastj) * power(pv,lastj)
          - lastborrow * power(pv,lastj)
          + BEWordSeqToInt(SelectDigitRange(lastcs, lastj, 0));
            //- stability hypothesis
        BEWordSeqToInt(SelectDigitRange(cs, |cs|, j)) * power(pv,j)
            + DigitAt(lastcs, lastj) * power(pv,lastj)
          - lastborrow * power(pv,lastj)
          + BEWordSeqToInt(SelectDigitRange(cs, lastj, 0));
    }
}

lemma lemma_FleetNatSub_digit_rearrangement(pv:int, oldcs:seq<int>, lastcs:seq<int>, bs:seq<int>, bdigits:int, cs:seq<int>, lastj:int, j:int, lastborrow:int, borrow:int)
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
    requires SelectDigitRange(lastcs, |lastcs|, j) == SelectDigitRange(cs, |cs|, j); //- stability
    requires SelectDigitRange(lastcs, lastj, 0) == SelectDigitRange(cs, lastj, 0); //- stability
    requires BEWordSeqToInt(oldcs) - BEWordSeqToInt(bs) ==
            ( BEWordSeqToInt(SelectDigitRange(lastcs, |lastcs|, lastj))
              - lastborrow
              - BEWordSeqToInt(SelectDigitRange(bs, bdigits, lastj)) ) * power(pv,lastj)
            + BEWordSeqToInt(SelectDigitRange(lastcs, lastj, 0));
    requires DigitAt(lastcs, lastj) - lastborrow - DigitAt(bs, lastj)
        == DigitAt(cs, lastj) - pv*borrow; //- local math step
    ensures 0<=borrow<2;
    ensures IsDigitSeq(power2(32), cs);
    ensures BEWordSeqToInt(oldcs) - BEWordSeqToInt(bs) ==
            ( BEWordSeqToInt(SelectDigitRange(cs, |cs|, j))
              - borrow
              - BEWordSeqToInt(SelectDigitRange(bs, bdigits, j)) ) * power(pv,j)
            + BEWordSeqToInt(SelectDigitRange(cs, j, 0));
{
    //-ghost var pv := power2(32); lemma_2toX();
                                                  
    
    lemma_2toX();

    lemma_SelectSingletonRange(lastcs, j, lastj);
    lemma_BEDigitSeqToInt_singleton(pv, DigitAt(lastcs,lastj));
//-    assert BEWordSeqToInt(SelectDigitRange(lastcs, j, lastj)) == DigitAt(lastcs, lastj);

    lemma_SelectSingletonRange(cs, j, lastj);
    lemma_BEDigitSeqToInt_singleton(pv, DigitAt(cs,lastj));
//-    assert BEWordSeqToInt(SelectDigitRange(cs, j, lastj)) == DigitAt(cs, lastj);

    //- b-split
    calc {
        BEWordSeqToInt(SelectDigitRange(bs, bdigits, lastj)) * power(pv,lastj);
            { lemma_BEInterpretation_Select_general(pv, bs, bdigits, j, lastj); }
        ( BEWordSeqToInt(SelectDigitRange(bs, bdigits, j)) * power(pv,1)
            + BEWordSeqToInt(SelectDigitRange(bs, j, lastj)) )
            * power(pv,lastj);
            { lemma_mul_is_distributive_forall(); }
        BEWordSeqToInt(SelectDigitRange(bs, bdigits, j)) * power(pv,1) * power(pv, lastj)
            + BEWordSeqToInt(SelectDigitRange(bs, j, lastj)) * power(pv, lastj);
            { lemma_mul_is_associative_forall(); lemma_power_adds(pv, 1, lastj); }
        BEWordSeqToInt(SelectDigitRange(bs, bdigits, j)) * power(pv,j)
            + BEWordSeqToInt(SelectDigitRange(bs, j, lastj)) * power(pv, lastj);
            { lemma_SelectSingletonRange(bs, j, lastj);
              lemma_BEDigitSeqToInt_singleton(pv, DigitAt(bs,lastj)); }
        BEWordSeqToInt(SelectDigitRange(bs, bdigits, j)) * power(pv,j)
            + DigitAt(bs, lastj) * power(pv, lastj);
    }

    //- core
    calc {
        DigitAt(lastcs, lastj) * power(pv,lastj)
        - lastborrow * power(pv,lastj)
        - DigitAt(bs, lastj) * power(pv, lastj);
            { lemma_mul_is_distributive_forall(); }
        (DigitAt(lastcs, lastj) - lastborrow - DigitAt(bs, lastj)) * power(pv, lastj);
            //- requires "local math step"
        (DigitAt(cs, lastj) - borrow*pv) * power(pv, lastj);
            { lemma_mul_is_distributive_forall(); }
        DigitAt(cs, lastj)*power(pv,lastj)
          - borrow * pv * power(pv,lastj);
            { lemma_mul_is_associative_forall(); lemma_power_adds(pv, 1, lastj); lemma_power_1(pv); }
        DigitAt(cs, lastj)*power(pv,lastj)
          - borrow * power(pv,j);
    }

    calc {
        BEWordSeqToInt(oldcs) - BEWordSeqToInt(bs);
        ( BEWordSeqToInt(SelectDigitRange(lastcs, |lastcs|, lastj))
          - lastborrow
          - BEWordSeqToInt(SelectDigitRange(bs, bdigits, lastj)) ) * power(pv,lastj)
        + BEWordSeqToInt(SelectDigitRange(lastcs, lastj, 0));
            { lemma_mul_is_distributive_forall(); }
        BEWordSeqToInt(SelectDigitRange(lastcs, |lastcs|, lastj)) * power(pv,lastj)
          - lastborrow * power(pv,lastj)
          - BEWordSeqToInt(SelectDigitRange(bs, bdigits, lastj)) * power(pv,lastj)
          + BEWordSeqToInt(SelectDigitRange(lastcs, lastj, 0));
            { lemma_FleetNatSub_rearrangement_left(pv, lastcs, cs, lastj, j, lastborrow); }
        BEWordSeqToInt(SelectDigitRange(cs, |cs|, j)) * power(pv,j)
            + DigitAt(lastcs, lastj) * power(pv,lastj)
          - lastborrow * power(pv,lastj)
          + BEWordSeqToInt(SelectDigitRange(cs, lastj, 0))
          - BEWordSeqToInt(SelectDigitRange(bs, bdigits, lastj)) * power(pv,lastj);
            //- calc "b-split"
        BEWordSeqToInt(SelectDigitRange(cs, |cs|, j))*power(pv,j)
          + DigitAt(lastcs, lastj) * power(pv,lastj)
          - lastborrow * power(pv,lastj)
          - BEWordSeqToInt(SelectDigitRange(bs, bdigits, j)) * power(pv,j)
          - DigitAt(bs, lastj) * power(pv, lastj)
          + BEWordSeqToInt(SelectDigitRange(cs, lastj, 0));
            //- calc "core"
        BEWordSeqToInt(SelectDigitRange(cs, |cs|, j)) * power(pv,j)
          - borrow * power(pv,j)
          - BEWordSeqToInt(SelectDigitRange(bs, bdigits, j)) * power(pv,j)
          + DigitAt(cs, lastj)*power(pv,lastj)
          + BEWordSeqToInt(SelectDigitRange(cs, lastj, 0));
        BEWordSeqToInt(SelectDigitRange(cs, |cs|, j)) * power(pv,j)
          - borrow * power(pv,j)
          - BEWordSeqToInt(SelectDigitRange(bs, bdigits, j)) * power(pv,j)
          + BEWordSeqToInt(SelectDigitRange(cs, j, lastj))*power(pv,lastj)
          + BEWordSeqToInt(SelectDigitRange(cs, lastj, 0));
            { lemma_BEInterpretation_Select_general(pv, cs, j, lastj, 0); }
        BEWordSeqToInt(SelectDigitRange(cs, |cs|, j)) * power(pv,j)
          - borrow * power(pv,j)
          - BEWordSeqToInt(SelectDigitRange(bs, bdigits, j)) * power(pv,j)
          + BEWordSeqToInt(SelectDigitRange(cs, j, 0));
            { lemma_mul_is_distributive_forall(); }
        ( BEWordSeqToInt(SelectDigitRange(cs, |cs|, j))
          - borrow
          - BEWordSeqToInt(SelectDigitRange(bs, bdigits, j)) ) * power(pv,j)
        + BEWordSeqToInt(SelectDigitRange(cs, j, 0));
    }
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
        }   
    }
}

lemma lemma_FleetNatSub_borrow_propagation(pv:int, oldcs:seq<int>, lastcs:seq<int>, bs:seq<int>, cs:seq<int>, lastj:int, j:int, lastborrow:int, borrow:int)
    requires 1<=j<=|oldcs|==|lastcs|==|cs|;
    requires lastj+1 == j;
    requires 0<=lastborrow<2;
    requires 0<=borrow<2;
    requires pv==power2(32)==0x100000000;
    requires IsDigitSeq(power2(32), oldcs);
    requires IsDigitSeq(power2(32), bs);
    requires IsDigitSeq(power2(32), cs);
    requires IsDigitSeq(power2(32), lastcs);
    requires SelectDigitRange(lastcs, |lastcs|, j) == SelectDigitRange(cs, |cs|, j); //- stability
    requires SelectDigitRange(lastcs, lastj, 0) == SelectDigitRange(cs, lastj, 0); //- stability
    requires DigitAt(lastcs, lastj) - lastborrow == DigitAt(cs, lastj) - borrow * pv; //- core step
    requires BEWordSeqToInt(oldcs) - BEWordSeqToInt(bs) ==
        ( BEWordSeqToInt(SelectDigitRange(lastcs, |lastcs|, lastj))
          - lastborrow) * power(pv,lastj)
        + BEWordSeqToInt(SelectDigitRange(lastcs, lastj, 0));
    ensures BEWordSeqToInt(oldcs) - BEWordSeqToInt(bs) ==
        ( BEWordSeqToInt(SelectDigitRange(cs, |cs|, j))
          - borrow) * power(pv,j)
        + BEWordSeqToInt(SelectDigitRange(cs, j, 0));
{
    calc {
        DigitAt(lastcs, lastj) * power(pv,lastj) - lastborrow * power(pv,lastj);
            { lemma_mul_is_distributive_forall(); }
        (DigitAt(lastcs, lastj) - lastborrow) * power(pv,lastj);
            //- core step
        (DigitAt(cs, lastj) - borrow * pv) * power(pv,lastj);
            { lemma_mul_is_distributive_forall(); }
        DigitAt(cs, lastj) * power(pv, lastj) - borrow * pv * power(pv,lastj);
            { lemma_mul_is_associative_forall(); lemma_power_adds(pv, 1, lastj); lemma_power_1(pv); }
        DigitAt(cs, lastj) * power(pv, lastj) - borrow * power(pv,j);
    }
    calc {
        ( BEWordSeqToInt(SelectDigitRange(lastcs, |lastcs|, lastj))
          - lastborrow) * power(pv,lastj)
        + BEWordSeqToInt(SelectDigitRange(lastcs, lastj, 0));
            { lemma_mul_is_distributive_forall(); }
        BEWordSeqToInt(SelectDigitRange(lastcs, |lastcs|, lastj)) * power(pv,lastj)
          - lastborrow * power(pv,lastj)
          + BEWordSeqToInt(SelectDigitRange(lastcs, lastj, 0));
            { lemma_FleetNatSub_rearrangement_left(pv, lastcs, cs, lastj, j, lastborrow); }
        BEWordSeqToInt(SelectDigitRange(cs, |cs|, j)) * power(pv,j)
            + DigitAt(lastcs, lastj) * power(pv,lastj)
          - lastborrow * power(pv,lastj)
          + BEWordSeqToInt(SelectDigitRange(cs, lastj, 0));
            //- core calc
        BEWordSeqToInt(SelectDigitRange(cs, |cs|, j)) * power(pv,j)
          - borrow * power(pv,j)
          + DigitAt(cs, lastj) * power(pv, lastj)
          + BEWordSeqToInt(SelectDigitRange(cs, lastj, 0));
            { lemma_SelectSingletonRange(cs, j, lastj);
              lemma_BEDigitSeqToInt_singleton(pv, DigitAt(cs,lastj)); }
        BEWordSeqToInt(SelectDigitRange(cs, |cs|, j)) * power(pv,j)
          - borrow * power(pv,j)
          + BEWordSeqToInt(SelectDigitRange(cs, j, lastj)) * power(pv, lastj)
          + BEWordSeqToInt(SelectDigitRange(cs, lastj, 0));
            { lemma_BEInterpretation_Select_general(pv, cs, j, lastj, 0); }
        BEWordSeqToInt(SelectDigitRange(cs, |cs|, j)) * power(pv,j)
          - borrow * power(pv,j)
        + BEWordSeqToInt(SelectDigitRange(cs, j, 0));
            { lemma_mul_is_distributive_forall(); }
        ( BEWordSeqToInt(SelectDigitRange(cs, |cs|, j))
          - borrow) * power(pv,j)
        + BEWordSeqToInt(SelectDigitRange(cs, j, 0));
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

    //- subtract loop
    while (j<bdigits)
        invariant 0<=j<=bdigits;
        invariant IsWordSeq(b[..]);
        invariant IsWordSeq(c[..]);
        invariant IsWordSeq(SelectDigitRange(c[..], c.Length, j));
        invariant 0<=borrow<2;
        invariant BEWordSeqToInt(old(c[..])) - BEWordSeqToInt(b[..]) ==
            ( BEWordSeqToInt(SelectDigitRange(c[..], c.Length, j))
              - borrow
              - BEWordSeqToInt(SelectDigitRange(b[..], bdigits, j)) ) * power(pv,j)
            + BEWordSeqToInt(SelectDigitRange(c[..], j, 0));
    {
        ghost var lastcs := c[..];
        ghost var lastborrow := borrow;
        ghost var lastj := j;

        var ci := clenm1 - j;
        var bj := b[blenm1 - j];
        var lastcj := c[ci];

        var newcj;
//- #if opt
//-        newcj, borrow := FleetNatSub_local_math_core(lastcj, bj, borrow);
//- #endif opt
//- #if standard
        var borrow1 := 0;
        if (lastcj < borrow) { borrow1 := 1; }
        lemma_word32(lastcj);
        lemma_word32(borrow);
        var midcj := asm_Sub(lastcj, borrow);

        lemma_asm_Sub_properties(lastcj, borrow, midcj, borrow1);

        lemma_word32(1);
        var borrow2 := 0;
        if (midcj < bj) {
            borrow2 := 1;
        }
        lemma_word32(bj);
        newcj := asm_Sub(midcj, bj);

        lemma_asm_Sub_properties(midcj, bj, newcj, borrow2);
        lemma_word32(borrow1);
        borrow := asm_Add(borrow1, borrow2);
        lemma_mod0x100000000(borrow1+borrow2);
        lemma_FleetNatSub_local_math(pv, lastcj, newcj, midcj, bj, lastborrow, borrow1, borrow2, borrow);
//- #endif standard

        c[ci] := newcj;
        j := j+1;


        lemma_FleetNatSub_digit_rearrangement(pv, old(c[..]), lastcs, b[..], bdigits, c[..], lastj, j, lastborrow, borrow);
    }

    //- bridge from subtract loop invariant to borrow loop invariant
    calc {
        BEWordSeqToInt(SelectDigitRange(b[..], bdigits, j));
            { assert SelectDigitRange(b[..], bdigits, j)==[]; /*OBSERVE SEQ*/ }
        BEWordSeqToInt([]);
            { reveal_BEDigitSeqToInt_private(); }
        0;
    }

    //- propagate borrow loop
    while (j<c.Length)
        invariant 0<=j<=c.Length;
        invariant IsWordSeq(c[..]);
        invariant 0<=borrow<2;
        invariant BEWordSeqToInt(old(c[..])) - BEWordSeqToInt(b[..]) ==
            ( BEWordSeqToInt(SelectDigitRange(c[..], c.Length, j))
              - borrow) * power(pv,j)
            + BEWordSeqToInt(SelectDigitRange(c[..], j, 0));
    {
        ghost var lastj := j;
        ghost var lastcs := c[..];
        ghost var lastborrow := borrow;
        var ci := clenm1 - j;
        var newborrow := 0;
        var lastcj := c[ci];
        if (lastcj < borrow) {
            newborrow := 1;
        }
        lemma_word32(lastcj);
        lemma_word32(borrow);
        c[ci] := asm_Sub(lastcj, borrow);
        ghost var newcj := c[ci];

        lemma_asm_Sub_properties(lastcj, borrow, c[ci], newborrow);
        borrow := newborrow;

        j := j + 1;

//-        calc {
//-            DigitAt(lastcs, lastj) - lastborrow;
//-            lastcj - lastborrow;
//-            newcj - borrow * pv;
//-            DigitAt(c[..], lastj) - borrow * pv;
//-        }
        lemma_FleetNatSub_borrow_propagation(pv, old(c[..]), lastcs, b[..], c[..], lastj, j, lastborrow, borrow);
    }

    //- bridge from borrow loop invariant to postcondition
    lemma_BEInterpretation_Select(pv, c[..], j);
    if (borrow>0)
    {   //- borrow can't fall off the top, because we requires-ed that c>=b.
        calc {
            BEWordSeqToInt(old(c[..])) - BEWordSeqToInt(b[..]);
            ( BEWordSeqToInt(SelectDigitRange(c[..], c.Length, j)) - 1) * power(pv,j)
                + BEWordSeqToInt(SelectDigitRange(c[..], j, 0));
                { assert SelectDigitRange(c[..], c.Length, j)==[]; reveal_BEDigitSeqToInt_private(); }
            - 1 * power(pv,j) + BEWordSeqToInt(SelectDigitRange(c[..], j, 0));
            <   { lemma_BEDigitSeqToInt_bound(pv, SelectDigitRange(c[..], j, 0)); }
            0;
        } assert false;
    }
}

//- Caller assumes newly-allocated c.
method ICantBelieveItsNotFatNatSub(a:array<int>, b:array<int>) returns (c:array<int>)
    requires a!=null;
    requires b!=null;
    requires IsDigitSeq(power2(32), a[..]);
    requires IsDigitSeq(power2(32), b[..]);
    requires BEWordSeqToInt(b[..]) <= BEWordSeqToInt(a[..]);
    ensures c!=null;
    ensures fresh(c);
    ensures IsDigitSeq(power2(32), c[..]);
    ensures BEWordSeqToInt(a[..]) - BEWordSeqToInt(b[..]) == BEWordSeqToInt(c[..]);
{
    c := FleetAlloc(a.Length);  //- could just be c:=null, but DafnyCC doesn't allow it yet
    assert c!=null;    
    c := FleetCopy(c, a, 0);
    FleetNatSub(c, b);
}

