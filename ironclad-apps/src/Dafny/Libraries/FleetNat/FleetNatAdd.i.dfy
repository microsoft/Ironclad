include "../FatNat/FatNatCommon.i.dfy"
include "FleetNatCommon.i.dfy"

lemma lemma_FleetNatAddSimple_1(pv:int, bs:seq<int>, bdigits:int, lastcs:seq<int>, oldcs:seq<int>, newcs:seq<int>, j:int, oldj:int, lastcarry:int, prevcarry:int)
    requires pv==power2(32);
    requires 0 <= bdigits <= |bs|;
    requires bdigits <= |lastcs| == |oldcs| == |newcs|;
    requires 1<=j<=bdigits;
    requires oldj+1 == j;
    requires IsDigitSeq(pv, bs);
    requires IsDigitSeq(pv, SelectDigitRange(bs, j, oldj));
    requires IsDigitSeq(pv, SelectDigitRange(lastcs, oldj, 0));
    requires IsDigitSeq(pv, oldcs);
    requires IsDigitSeq(pv, SelectDigitRange(newcs, j, 0));
    requires IsDigitSeq(pv, SelectDigitRange(newcs, oldj, 0));
    requires IsDigitSeq(pv, SelectDigitRange(newcs, j, oldj));
    //- things right of oldj are stable
    requires SelectDigitRange(lastcs, oldj, 0) == SelectDigitRange(newcs, oldj, 0);
    //- local step math result
    requires BEWordSeqToInt(SelectDigitRange(bs, j, oldj)) + BEWordSeqToInt(SelectDigitRange(oldcs, j, oldj)) + prevcarry
        == BEWordSeqToInt(SelectDigitRange(newcs, j, oldj)) + pv * lastcarry;
    //- induction hypothesis loop invariant
    requires BEWordSeqToInt(SelectDigitRange(bs, oldj, 0)) + BEWordSeqToInt(SelectDigitRange(oldcs, oldj, 0))
            == BEWordSeqToInt(SelectDigitRange(lastcs, oldj, 0)) + prevcarry * power(pv, oldj);
    ensures BEWordSeqToInt(SelectDigitRange(bs, j, 0))
            + BEWordSeqToInt(SelectDigitRange(oldcs, j, 0))
        == BEWordSeqToInt(SelectDigitRange(newcs, j, 0)) + lastcarry * power(pv, j);
{
    lemma_2toX32();
    calc {
        BEWordSeqToInt(SelectDigitRange(bs, j, 0))
            + BEWordSeqToInt(SelectDigitRange(oldcs, j, 0));
            { lemma_BEInterpretation_Select_general(pv, bs, j, oldj, 0); }
        BEWordSeqToInt(SelectDigitRange(bs, j, oldj))*power(pv,oldj) + BEWordSeqToInt(SelectDigitRange(bs, oldj, 0))
            + BEWordSeqToInt(SelectDigitRange(oldcs, j, 0));
            { lemma_BEInterpretation_Select_general(pv, oldcs, j, oldj, 0); }
        BEWordSeqToInt(SelectDigitRange(bs, j, oldj))*power(pv,oldj) + BEWordSeqToInt(SelectDigitRange(bs, oldj, 0))
            + BEWordSeqToInt(SelectDigitRange(oldcs, j, oldj))*power(pv,oldj) + BEWordSeqToInt(SelectDigitRange(oldcs, oldj, 0));
            { lemma_mul_is_distributive_forall(); }
        (BEWordSeqToInt(SelectDigitRange(bs, j, oldj)) + BEWordSeqToInt(SelectDigitRange(oldcs, j, oldj)))
            *power(pv,oldj)
            + BEWordSeqToInt(SelectDigitRange(bs, oldj, 0)) + BEWordSeqToInt(SelectDigitRange(oldcs, oldj, 0));
            //- induction hypothesis loop invariant transforms last lines of expressions
        (BEWordSeqToInt(SelectDigitRange(bs, j, oldj)) + BEWordSeqToInt(SelectDigitRange(oldcs, j, oldj)))
            *power(pv,oldj)
            + BEWordSeqToInt(SelectDigitRange(bs, oldj, 0)) + BEWordSeqToInt(SelectDigitRange(oldcs, oldj, 0));
            { lemma_mul_is_distributive_forall(); }
        (BEWordSeqToInt(SelectDigitRange(bs, j, oldj)) + BEWordSeqToInt(SelectDigitRange(oldcs, j, oldj))
         +prevcarry)
            *power(pv,oldj)
            + BEWordSeqToInt(SelectDigitRange(lastcs, oldj, 0));
            //- by local math step
        (BEWordSeqToInt(SelectDigitRange(newcs, j, oldj)) + pv * lastcarry)*power(pv, oldj)
            + BEWordSeqToInt(SelectDigitRange(lastcs, oldj, 0));
        (BEWordSeqToInt(SelectDigitRange(newcs, j, oldj)) + pv * lastcarry)*power(pv, oldj)
            + BEWordSeqToInt(SelectDigitRange(newcs, oldj, 0));
            { lemma_mul_is_distributive_forall(); }
        BEWordSeqToInt(SelectDigitRange(newcs, j, oldj))*power(pv, oldj) + (pv * lastcarry)*power(pv, oldj)
           + BEWordSeqToInt(SelectDigitRange(newcs, oldj, 0));
            { lemma_mul_is_associative_forall(); }
        BEWordSeqToInt(SelectDigitRange(newcs, j, oldj))*power(pv, oldj) + lastcarry*(pv*power(pv, oldj))
            + BEWordSeqToInt(SelectDigitRange(newcs, oldj, 0));
            { lemma_power_1(pv); lemma_power_adds(pv,1,oldj); }
        BEWordSeqToInt(SelectDigitRange(newcs, j, oldj))*power(pv, oldj) + lastcarry*power(pv, j)
            + BEWordSeqToInt(SelectDigitRange(newcs, oldj, 0));
            { lemma_BEInterpretation_Select_general(pv, newcs, j, oldj, 0); }
        BEWordSeqToInt(SelectDigitRange(newcs, j, 0)) + lastcarry * power(pv, j);
    }
}

method FleetNatAddSimple(c:array<int>, b:array<int>, bdigits:int) returns (carry:int)
    requires c!=null;
    requires b!=null;
    requires c!=b;
    requires IsDigitSeq(power2(32), c[..]);
    requires IsDigitSeq(power2(32), b[..]);
    requires 0<=bdigits<=b.Length;
    requires bdigits <= c.Length;
    modifies c;
    ensures c!=null;
    ensures c==old(c);
    ensures IsDigitSeq(power2(32), c[..]);
//-    ensures BEWordSeqToInt(old(c[c.Length-bdigits..])) + BEWordSeqToInt(b[b.Length-bdigits..])
//-        == BEWordSeqToInt(c[c.Length-bdigits..]) + power(power2(32), bdigits)*carry;
    ensures 0<=carry<2;
    ensures BEWordSeqToInt(old(c[..])) + BEWordSeqToInt(b[b.Length-bdigits..])
        == BEWordSeqToInt(c[..]) + power(power2(32), bdigits)*carry;
{
    ghost var pv := power2(32);
    lemma_2toX32();
    ghost var bs := b[..];
    ghost var oldcs := c[..];
    ghost var clen := c.Length;

    var lastcarry:int := 0;
    var j:=0;

    calc {
        BEWordSeqToInt(SelectDigitRange(bs, j, 0)) + BEWordSeqToInt(SelectDigitRange(oldcs, j, 0));
            { reveal_BEDigitSeqToInt_private(); }
        BEWordSeqToInt(SelectDigitRange(c[..], j, 0)) + lastcarry * power(pv, j);
    }

    var clenm1 := c.Length - 1;
    var blenm1 := b.Length - 1;
    while (j<bdigits)
        invariant 0<=j<=bdigits;
        invariant SelectDigitRange(c[..], clen, j) == SelectDigitRange(oldcs, clen, j); //- haven't touched top limbs
        invariant IsDigitSeq(pv, SelectDigitRange(c[..], j, 0));    //- bottom limbs are correctly sized
        invariant 0<=lastcarry<2;
        invariant
            BEWordSeqToInt(SelectDigitRange(bs, j, 0)) + BEWordSeqToInt(SelectDigitRange(oldcs, j, 0))
            == BEWordSeqToInt(SelectDigitRange(c[..], j, 0)) + lastcarry * power(pv, j);
        decreases 32-j;
    {
        ghost var lastcs := c[..];
        ghost var lastj := j;
        ghost var prevcarry := lastcarry;
        ghost var ci := c.Length - 1 - j;
        ghost var bi := b.Length - 1 - j;
        ghost var lastci := ci;
        ghost var lastbi := bi;

        assert SelectDigitRange(oldcs, clen, lastj) == SelectDigitRange(lastcs, clen, lastj);

//-        assert SelectDigitRange(lastcs, lastj, 0) == SelectDigitRange(c[..], lastj, 0);

        //- mimicing bignum.c mpi_add_abs logic
        lemma_word32(c[ci]);
        assert c[ci] == SelectDigitRange(c[..], clen, j)[ci];   //- OBSERVE SEQ
        calc {
            oldcs[|oldcs|-clen..|oldcs|-j][ci];
            oldcs[|oldcs|-clen+ci];
            oldcs[ci];
        }
        assert oldcs[ci] == SelectDigitRange(oldcs, clen, j)[ci];   //- OBSERVE SEQ
        lemma_word32(lastcarry);
        var cidx := clenm1 - j;
        var ctmp := asm_Add(c[cidx], lastcarry);
        var intermediatecarry := 0;
        if (ctmp < lastcarry)
        {
            intermediatecarry := 1;
        }

        var btmp := b[blenm1 - j];
        lemma_word32(b[bi]);
        var ctmp2 := asm_Add(ctmp, btmp);
        ghost var secondcarry;
        if (ctmp2 < btmp)
        {
            lastcarry := 1;
            secondcarry := 1;
        }
        else
        {
            lastcarry := intermediatecarry;
            secondcarry := 0;
        }
        c[cidx] := ctmp2;

        j := j + 1;
        ci := c.Length - 1 - j;
        bi := b.Length - 1 - j;

        lemma_mod0x100000000(ctmp+btmp);
        lemma_mod_properties();
        //-assert 0<=ctmp2<pv;

        lemma_asm_Add_properties(oldcs[lastci], prevcarry, ctmp, intermediatecarry);
        lemma_asm_Add_properties(ctmp, bs[lastbi], ctmp2, secondcarry);
           
        calc {
            SelectDigitRange(c[..], j, 0);
            SelectDigitRange(c[..], j, lastj) + SelectDigitRange(c[..], lastj, 0);
                { lemma_SelectSingletonRange(c[..], j, lastj); }
            [DigitAt(c[..], lastj)] + SelectDigitRange(c[..], lastj, 0);
                { assert c[..][|c[..]|-1-lastj] == c[lastci]; }
            [c[lastci]] + SelectDigitRange(c[..], lastj, 0);
            [ctmp2] + SelectDigitRange(c[..], lastj, 0);
        }
        assert IsDigitSeq(pv, SelectDigitRange(c[..], j, 0));

        //- local math step
        calc {
            BEWordSeqToInt(SelectDigitRange(bs, j, lastj)) + BEWordSeqToInt(SelectDigitRange(oldcs, j, lastj)) + prevcarry;
                { lemma_SelectSingletonRange(bs, j, lastj);
                  lemma_SelectSingletonRange(oldcs, j, lastj); }
            BEWordSeqToInt([DigitAt(bs,lastj)]) + BEWordSeqToInt([DigitAt(oldcs,lastj)]) + prevcarry;
                { lemma_BEDigitSeqToInt_singleton(pv, DigitAt(bs, lastj));
                  lemma_BEDigitSeqToInt_singleton(pv, DigitAt(oldcs, lastj)); }
            DigitAt(bs,lastj) + DigitAt(oldcs,lastj) + prevcarry;
            ctmp2 + pv * lastcarry;
            DigitAt(c[..], lastj) + pv * lastcarry;
                { lemma_BEDigitSeqToInt_singleton(pv, DigitAt(c[..], lastj)); }
            BEWordSeqToInt([DigitAt(c[..], lastj)]) + pv * lastcarry;
                { lemma_SelectSingletonRange(c[..], j, lastj); }
            BEWordSeqToInt(SelectDigitRange(c[..], j, lastj)) + pv * lastcarry;
        }

        lemma_FleetNatAddSimple_1(pv, bs, bdigits, lastcs, oldcs, c[..], j, lastj, lastcarry, prevcarry);

        lemma_Select_subrange(oldcs, lastcs, clen, clen, j, lastj);
    }

    carry := lastcarry;

    //- all of c IsDigitSeq
    forall (i | 0<=i<c.Length)
        ensures 0 <= c[i] < pv;
    {
        if (i<c.Length-bdigits)
        {
            calc { //- OBSERVE SEQ
                c[i];
                SelectDigitRange(c[..], clen, bdigits)[i];
                SelectDigitRange(oldcs, clen, bdigits)[i];
                oldcs[i];
            }
        }
        else
        {
            assert c[i] == SelectDigitRange(c[..], bdigits, 0)[i-(c.Length-bdigits)]; //- OBSERVE SEQ
        }
    }

    assert j==bdigits;
    assert SelectDigitRange(c[..], bdigits, 0) == c[c.Length-bdigits..];    //- OBSERVE SEQ
    ghost var ctop
        := BEWordSeqToInt(SelectDigitRange(oldcs, |oldcs|, bdigits))*power(pv,bdigits);
    calc
    {
        BEWordSeqToInt(old(c[..]))
            + BEWordSeqToInt(b[b.Length-bdigits..]);
        BEWordSeqToInt(oldcs)
            + BEWordSeqToInt(b[b.Length-bdigits..]);
            { lemma_BEInterpretation_Select(pv, oldcs, bdigits); }
        ctop + BEWordSeqToInt(SelectDigitRange(oldcs, bdigits, 0))
            + BEWordSeqToInt(b[b.Length-bdigits..]);
        ctop + BEWordSeqToInt(SelectDigitRange(oldcs, j, 0))
            + BEWordSeqToInt(b[b.Length-bdigits..]);
            {
                assert b[b.Length-bdigits..] == SelectDigitRange(bs, j, 0); //- OBSERVE SEQ
            }
        ctop + BEWordSeqToInt(SelectDigitRange(bs, j, 0)) + BEWordSeqToInt(SelectDigitRange(oldcs, j, 0));
        ctop + BEWordSeqToInt(SelectDigitRange(c[..], j, 0)) + lastcarry * power(pv, j);
            {
                assert SelectDigitRange(c[..], j, 0) == c[c.Length-bdigits..]; //- OBSERVE SEQ
            }
        ctop + BEWordSeqToInt(c[c.Length-bdigits..]) + power(power2(32), bdigits)*carry;
            { lemma_BEInterpretation_Select(pv, c[..], bdigits); }
        BEWordSeqToInt(c[..]) + power(power2(32), bdigits)*carry;
    }
    assert IsDigitSeq(pv, SelectDigitRange(c[..], bdigits, 0));

}

method FleetNat_propagate_carry(c:array<int>, place:nat, carry:int) returns (c':array<int>)
    requires c!=null;
    requires IsDigitSeq(power2(32), c[..]);
    requires 0<=place<=c.Length;
    requires 0<=carry<power2(32);
    modifies c;
    ensures c'!=null;
    ensures c'==c || fresh(c');
    ensures IsDigitSeq(power2(32), c'[..]);
    ensures BEWordSeqToInt(old(c[..])) + power(power2(32), place)*carry == BEWordSeqToInt(c'[..]);
{
    lemma_2toX();
    ghost var pv := power2(32);
    var clenm1 := c.Length-1;
    var j := place;
    var curcarry := carry;
    while (j<c.Length)
        invariant place<=j<=c.Length;
        invariant 0<=curcarry<pv;
        invariant IsDigitSeq(pv, c[..]);
        invariant BEWordSeqToInt(old(c[..])) + power(pv, place)*carry
            == BEWordSeqToInt(c[..]) + power(pv, j)*curcarry;
    {
        var ci := clenm1-j;
        ghost var lastc := c[..];
        ghost var lastcci:=c[ci];
        ghost var lastcurcarry := curcarry;
        ghost var lastj := j;
        assert 0<=c[ci]<pv;
        lemma_word32(c[ci]);
        lemma_word32(curcarry);
        var newcj := asm_Add(c[ci], curcarry);
        if (newcj < curcarry)
        {
            curcarry := 1;
        }
        else
        {
            curcarry := 0;
        }
        c[ci] := newcj;
        j:=j+1;

        lemma_mod0x100000000(lastcci+lastcurcarry);
        lemma_mod_properties();
        calc {
            BEWordSeqToInt(old(c[..])) + power(pv, place)*carry;
            BEWordSeqToInt(lastc) + power(pv, lastj)*lastcurcarry;
                { lemma_BEInterpretation_Select(pv, lastc, lastj); }
            BEWordSeqToInt(SelectDigitRange(lastc, |lastc|, lastj))*power(pv,lastj)
                + BEWordSeqToInt(SelectDigitRange(lastc, lastj, 0))
                + power(pv, lastj)*lastcurcarry;
                {
                    var sbig := SelectDigitRange(lastc, |lastc|, lastj);
                    lemma_BEInterpretation_Select(pv, sbig, 1);
                    assert SelectDigitRange(sbig, |sbig|, 1)
                        == SelectDigitRange(lastc, |lastc|, j); //- OBSERVE SEQ
                    assert SelectDigitRange(sbig, 1, 0)
                        == SelectDigitRange(lastc, j, lastj); //- OBSERVE SEQ
                }
            (BEWordSeqToInt(SelectDigitRange(lastc, |lastc|, j))*power(pv,1)
                    + BEWordSeqToInt(SelectDigitRange(lastc, j, lastj)))*power(pv,lastj)
                + BEWordSeqToInt(SelectDigitRange(lastc, lastj, 0))
                + power(pv, lastj)*lastcurcarry;
                {
                    calc {
                        BEWordSeqToInt(SelectDigitRange(lastc, j, lastj));
                        { lemma_SelectSingletonRange(lastc, j, lastj); }
                        BEWordSeqToInt([DigitAt(lastc, lastj)]);
                        { lemma_BEDigitSeqToInt_singleton(pv, DigitAt(lastc, lastj)); }
                        DigitAt(lastc, lastj);
                        lastcci;
                    }
                }
            (BEWordSeqToInt(SelectDigitRange(lastc, |lastc|, j))*power(pv,1)
                    + lastcci)*power(pv,lastj)
                + BEWordSeqToInt(SelectDigitRange(lastc, lastj, 0))
                + power(pv, lastj)*lastcurcarry;
                { lemma_mul_is_distributive_forall(); }
            BEWordSeqToInt(SelectDigitRange(lastc, |lastc|, j))*power(pv,1)*power(pv,lastj)
                + lastcci*power(pv,lastj)
                + BEWordSeqToInt(SelectDigitRange(lastc, lastj, 0))
                + power(pv, lastj)*lastcurcarry;
                { lemma_mul_is_associative_forall(); }
            BEWordSeqToInt(SelectDigitRange(lastc, |lastc|, j))*(power(pv,1)*power(pv,lastj))
                + lastcci*power(pv,lastj)
                + BEWordSeqToInt(SelectDigitRange(lastc, lastj, 0))
                + power(pv, lastj)*lastcurcarry;
                { lemma_power_adds(pv, 1, lastj); }
            BEWordSeqToInt(SelectDigitRange(lastc, |lastc|, j))*power(pv,j)
                + BEWordSeqToInt(SelectDigitRange(lastc, lastj, 0))
                + lastcci*power(pv,lastj)
                + power(pv, lastj)*lastcurcarry;
            BEWordSeqToInt(SelectDigitRange(lastc, |lastc|, j))*power(pv,j)
                + BEWordSeqToInt(SelectDigitRange(lastc, lastj, 0))
                + lastcci*power(pv,lastj)
                + lastcurcarry*power(pv, lastj);
                { lemma_mul_is_distributive_forall(); }
            BEWordSeqToInt(SelectDigitRange(lastc, |lastc|, j))*power(pv,j)
                + BEWordSeqToInt(SelectDigitRange(lastc, lastj, 0))
                + (lastcci+lastcurcarry)*power(pv,lastj);
                { lemma_asm_Add_properties(lastcci, lastcurcarry, newcj, curcarry); }
            BEWordSeqToInt(SelectDigitRange(lastc, |lastc|, j))*power(pv,j)
                + BEWordSeqToInt(SelectDigitRange(lastc, lastj, 0))
                + (newcj + pv*curcarry)*power(pv,lastj);
                { lemma_mul_is_distributive_forall(); }
            BEWordSeqToInt(SelectDigitRange(lastc, |lastc|, j))*power(pv,j)
                + BEWordSeqToInt(SelectDigitRange(lastc, lastj, 0))
                + newcj*power(pv,lastj)
                + pv*curcarry*power(pv,lastj);
                { 
                    calc {
                        pv*curcarry*power(pv,lastj);
                        curcarry*pv*power(pv,lastj);
                        curcarry*(pv*power(pv,lastj));
                        { lemma_power_1(pv); }
                        curcarry*(power(pv,1)*power(pv,lastj));
                        { lemma_power_adds(pv, 1, lastj); }
                        curcarry*power(pv, j);
                    }
                }
            BEWordSeqToInt(SelectDigitRange(lastc, |lastc|, j))*power(pv,j)
                + BEWordSeqToInt(SelectDigitRange(lastc, lastj, 0))
                + newcj*power(pv,lastj)
                + curcarry*power(pv,j);
            {
                assert SelectDigitRange(lastc, |lastc|, j)==SelectDigitRange(c[..], |c[..]|, j);    //- OBSERVE SEQ
                assert SelectDigitRange(lastc, lastj, 0)==SelectDigitRange(c[..], lastj, 0);    //- OBSERVE SEQ
            }
            BEWordSeqToInt(SelectDigitRange(c[..], |c[..]|, j))*power(pv,j)
                + newcj*power(pv, lastj)
                + BEWordSeqToInt(SelectDigitRange(c[..], lastj, 0))
                + power(pv, j)*curcarry;
                {
                    calc {
                        BEWordSeqToInt(SelectDigitRange(c[..], j, lastj));
                        { lemma_SelectSingletonRange(c[..], j, lastj); }
                        BEWordSeqToInt([DigitAt(c[..], lastj)]);
                        { lemma_BEDigitSeqToInt_singleton(pv, DigitAt(c[..], lastj)); }
                        DigitAt(c[..], lastj);
                        newcj;
                    }
                }
            BEWordSeqToInt(SelectDigitRange(c[..], |c[..]|, j))*power(pv,j)
                + BEWordSeqToInt(SelectDigitRange(c[..], j, lastj))*power(pv, lastj)
                    + BEWordSeqToInt(SelectDigitRange(c[..], lastj, 0))
                + power(pv, j)*curcarry;
                {
                    var slarge := SelectDigitRange(c[..], j, 0);
                    lemma_BEInterpretation_Select(pv, slarge, lastj);
                    assert SelectDigitRange(slarge, |slarge|, lastj)
                        == SelectDigitRange(c[..], j, lastj);   //- OBSERVE SEQ
                    assert SelectDigitRange(slarge, lastj, 0)
                        == SelectDigitRange(c[..], lastj, 0);   //- OBSERVE SEQ
                }
            BEWordSeqToInt(SelectDigitRange(c[..], |c[..]|, j))*power(pv,j)
                + BEWordSeqToInt(SelectDigitRange(c[..], j, 0))
                + power(pv, j)*curcarry;
                { lemma_BEInterpretation_Select(pv, c[..], j); }
            BEWordSeqToInt(c[..]) + power(pv, j)*curcarry;
        }
    }

    if (curcarry==0)
    {
        c' := c;
        calc {
            BEWordSeqToInt(old(c[..])) + power(pv, place)*carry;
            BEWordSeqToInt(c[..]) + power(pv, j)*curcarry;
            BEWordSeqToInt(c[..]) + power(pv, j)*0;
            BEWordSeqToInt(c'[..]);
        }
    }
    else
    {
        c' := FleetGrow(c, c.Length+1);
        c'[0] := curcarry;
        ghost var oldclen := c.Length;
        calc {
            BEWordSeqToInt(old(c[..])) + power(pv, place)*carry;
                //- Loop invariant at termination.
            BEWordSeqToInt(c[..]) + power(pv, c.Length)*curcarry;
            {
                calc {
                    SelectDigitRange(c'[..], oldclen, 0);
                    c'[c'.Length-c.Length..c'.Length-0];
                    c'[1..];
                    c[..];
                }
            }
            curcarry*power(pv,oldclen)
                + BEWordSeqToInt(SelectDigitRange(c'[..], oldclen, 0));
            {
                calc {
                    BEWordSeqToInt(SelectDigitRange(c'[..], c'.Length, oldclen));
                    { lemma_SelectSingletonRange(c'[..], c'.Length, oldclen); }
                    BEWordSeqToInt([DigitAt(c'[..], oldclen)]);
                    { lemma_BEDigitSeqToInt_singleton(pv, DigitAt(c'[..], oldclen)); }
                    DigitAt(c'[..], oldclen);
                    curcarry;
                }
            }
            BEWordSeqToInt(SelectDigitRange(c'[..], c'.Length, oldclen))*power(pv,oldclen)
                + BEWordSeqToInt(SelectDigitRange(c'[..], oldclen, 0));
                { lemma_BEInterpretation_Select(pv, c'[..], oldclen); }
            BEWordSeqToInt(c'[..]);
        }
    }
}

lemma {:imported} RevealAbssValue()

method FleetNatAdd(c:array<int>, a:array<int>, b:array<int>) returns (c':array<int>)
    requires a!=null;
    requires IsDigitSeq(power2(32), a[..]);
    requires b!=null;
    requires IsDigitSeq(power2(32), b[..]);
    requires c!=null;
    requires IsDigitSeq(power2(32), c[..]);
    requires c!=b;
    requires c!=a;  
    modifies c;
    ensures c'!=null;
    ensures c'==c || fresh(c');
    ensures IsDigitSeq(power2(32), c'[..]);
    ensures BEWordSeqToInt(old(a[..])) + BEWordSeqToInt(b[..]) == BEWordSeqToInt(c'[..]);
{
    lemma_2toX();

    var bdigits := CountNonzeroDigits(b);

//-    RevealAbssValue();
//-    if (c!=a)
//-    {
//-        assert c!=a;
                        
        c' := FleetCopy(c, a, bdigits);
        assert BEWordSeqToInt(old(a[..])) == BEWordSeqToInt(c'[..]);
//-    }
//-    else if (c.Length<bdigits)  //- but c==a
//-    {
//-        c' := FleetGrow(c, bdigits);
//-        assert a==old(a);
//-        assert c==a;
                        
//-        assert BEWordSeqToInt(old(a[..])) == BEWordSeqToInt(c'[..]);
//-    }
//-    else
//-    {
//-        c' := c;
//-        assert a==old(a);
//-        assert c==a;
                        
//-        assert c'==c;
//-        assert BEWordSeqToInt(old(a[..])) == BEWordSeqToInt(c'[..]);
//-    }
//-    assert BEWordSeqToInt(old(a[..])) == BEWordSeqToInt(c'[..]);

    ghost var oldc's := c'[..];
    var carry := FleetNatAddSimple(c', b, bdigits);
    ghost var intc's := c'[..];
    c' := FleetNat_propagate_carry(c', bdigits, carry);
    calc {
        BEWordSeqToInt(old(a[..])) + BEWordSeqToInt(b[..]);
        BEWordSeqToInt(oldc's) + BEWordSeqToInt(b[..]);
            { lemma_LeadingZeros(power2(32), b[b.Length-bdigits..], b[..]); }
        BEWordSeqToInt(oldc's) + BEWordSeqToInt(b[b.Length-bdigits..]);
        BEWordSeqToInt(intc's) + power(power2(32), bdigits)*carry;
        BEWordSeqToInt(c'[..]);
    }
}

method ICantBelieveItsNotFatNatAdd(a:array<int>, b:array<int>) returns (c:array<int>)
    requires a!=null;
    requires b!=null;
    requires IsDigitSeq(power2(32), a[..]);
    requires IsDigitSeq(power2(32), b[..]);
    ensures c!=null;
    ensures IsDigitSeq(power2(32), c[..]);
    ensures BEWordSeqToInt(a[..]) + BEWordSeqToInt(b[..]) == BEWordSeqToInt(c[..]);
{
    c := FleetAlloc(a.Length);  //- could just be c:=null, but DafnyCC doesn't allow it yet
    
    assert c!=a;    
    c := FleetNatAdd(c, a, b);
}
