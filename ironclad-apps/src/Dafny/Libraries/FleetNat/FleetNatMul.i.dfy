include "FleetNatAdd.i.dfy"
include "FleetNatMulLoopOpt.i.dfy"

method FleetNatMul_one(c:array<int>, bi:nat, a:array<int>, adigits:int, bv:int)
    requires c!=null;
    requires IsDigitSeq(power2(32), c[..]);
    requires a!=c;
    requires a!=null;
    requires IsDigitSeq(power2(32), a[..]);
    requires 0<=adigits<=a.Length;
    requires adigits <= c.Length;
    //- c-adequate-length requirement:
    requires BEWordSeqToInt(c[..])
         + BEWordSeqToInt(SelectDigitRange(a[..], adigits, 0)) * bv * power(power2(32),bi)
        < power(power2(32), c.Length);
    requires adigits + bi <= c.Length;
    requires 0 <= bv < power2(32);
    modifies c;
    ensures IsDigitSeq(power2(32), c[..]);
    ensures BEWordSeqToInt(c[..])
        == BEWordSeqToInt(old(c[..]))
         + BEWordSeqToInt(SelectDigitRange(a[..], adigits, 0)) * bv * power(power2(32),bi);
{
    ghost var pv := power2(32);
    lemma_2toX();
    ghost var oldcs := c[..];

    var clenm1 := c.Length-1;

    var j := adigits;
    var carry;
    if (0 == adigits)
    {
        carry := 0;
        lemma_BEWordSeqToInt_SelectDigitRange_empty(a[..]);
    }
    else
    {
        carry := FleetNatMul_one_loop_opt(c, bi, a, adigits, bv);
    }

    //- propagate the carry out
    while (carry > 0)
        invariant adigits<=j<=c.Length;
        invariant 0<=carry<pv;
        invariant IsDigitSeq(pv, c[..]);
        invariant BEWordSeqToInt(c[..]) + carry*power(pv, j+bi)
            == BEWordSeqToInt(oldcs)
             + BEWordSeqToInt(SelectDigitRange(a[..], adigits, 0)) * bv * power(pv, bi);
        decreases c.Length - j;
    {
        ghost var lastcs := c[..];
        ghost var lastj := j;
        ghost var lastcarry := carry;

        if (j+bi >= c.Length)
        {
            calc {
                power(pv, c.Length);
                >  //- contradicts requirement c-adequate-length.
                BEWordSeqToInt(oldcs)
                 + BEWordSeqToInt(SelectDigitRange(a[..], adigits, 0)) * bv * power(pv, bi);
                BEWordSeqToInt(c[..]) + carry*power(pv, j+bi);
                >=  { lemma_BEWordSeqToInt_bound(c[..]); }
                carry*power(pv, j+bi);
                >=  { lemma_power_positive(pv,j+bi); lemma_mul_increases(carry, power(pv, j+bi)); }
                power(pv, j+bi);
                >=  { lemma_power_increases(pv, c.Length, j+bi); }
                power(pv, c.Length);
            }
        }
        var ci := clenm1 - (j+bi);
        var lastcj := c[ci];

        lemma_word32(carry);
        lemma_word32(lastcj);
        var newcj := asm_Add(carry, lastcj);
        lemma_mod0x100000000(carry+lastcj);
        c[ci] := newcj;
        carry := 0;
        if (newcj < lastcj) { carry := 1; }
        j := j + 1;
        

        calc {
            newcj * power(pv, lastj+bi) + carry*power(pv, j+bi);
            {
                lemma_mod0x100000000(lastcarry+lastcj);
                lemma_mod_properties();
                lemma_asm_Add_properties(lastcarry, lastcj, newcj, carry);
            }
            (lastcarry+lastcj-pv*carry) * power(pv, lastj+bi) + carry*power(pv, j+bi);
                { lemma_mul_is_distributive_forall(); }
            (lastcarry+lastcj) * power(pv, lastj+bi) - (pv*carry) * power(pv, lastj+bi) + carry*power(pv, j+bi);
                { lemma_mul_is_distributive_forall(); }
            lastcarry*power(pv, lastj+bi) + lastcj*power(pv, lastj+bi) - (pv*carry) * power(pv, lastj+bi) + carry*power(pv, j+bi);
            lastcj*power(pv,lastj+bi) + lastcarry*power(pv,lastj+bi)
                - (pv*carry)*power(pv,lastj+bi) + carry*power(pv, j+bi);
            {
                calc {
                    (pv * carry) * power(pv,lastj+bi);
                        { lemma_mul_is_associative_forall(); }
                    carry * (pv*power(pv,lastj+bi));
                        { lemma_power_1(pv); }
                    carry * (power(pv,1)*power(pv,lastj+bi));
                        { lemma_power_adds(pv,1,lastj+bi); }
                    carry * power(pv,j+bi);
                }
            }
            lastcj*power(pv, lastj+bi) + lastcarry * power(pv, lastj+bi);
        }
        ghost var leftjunk := BEWordSeqToInt(SelectDigitRange(c[..], c.Length, j+bi));
        assert SelectDigitRange(c[..], c.Length, j+bi) == SelectDigitRange(lastcs, |lastcs|, j+bi);   //- OBSERVE SEQ
        ghost var rightjunk := BEWordSeqToInt(SelectDigitRange(c[..], lastj+bi, 0));
        assert SelectDigitRange(c[..], lastj+bi, 0) == SelectDigitRange(lastcs, lastj+bi, 0); //- OBSERVE SEQ
        calc {
            BEWordSeqToInt(c[..]) + carry*power(pv, j+bi);
                { lemma_PluckDigit(c[..], lastj+bi); }
            BEWordSeqToInt(SelectDigitRange(c[..], c.Length, j+bi)) * power(pv, j+bi)
                + DigitAt(c[..], lastj+bi) * power(pv, lastj+bi)
                + BEWordSeqToInt(SelectDigitRange(c[..], lastj+bi, 0))
                + carry*power(pv, j+bi);
            leftjunk * power(pv, j+bi)
                + newcj * power(pv, lastj+bi)
                + rightjunk
                + carry*power(pv, j+bi);
            leftjunk * power(pv, j+bi)
                + lastcj * power(pv, lastj+bi)
                + rightjunk
                + lastcarry * power(pv, lastj+bi);
            BEWordSeqToInt(SelectDigitRange(lastcs, |lastcs|, j+bi)) * power(pv, j+bi)
                + DigitAt(lastcs, lastj+bi) * power(pv, lastj+bi)
                + BEWordSeqToInt(SelectDigitRange(lastcs, lastj+bi, 0))
                + lastcarry * power(pv, lastj+bi);
                { lemma_PluckDigit(lastcs, lastj+bi); }
            BEWordSeqToInt(lastcs) + lastcarry * power(pv, lastj+bi);
        }
    }
}

lemma {:timeLimitMultiplier 2} lemma_FleetNatMul_c_adequate_length(a:array<int>, b:array<int>, adigits:nat, bdigits:nat, bi:nat, bv:int)
    requires a!=null;
    requires IsDigitSeq(power2(32), a[..]);
    requires b!=null;
    requires IsDigitSeq(power2(32), b[..]);
    requires 0<=adigits<=a.Length;
    requires 0<=bi<bdigits<=b.Length;
    requires BEWordSeqToInt(a[..]) == BEWordSeqToInt(SelectDigitRange(a[..], adigits, 0));
    requires BEWordSeqToInt(a[..]) < power(power2(32), adigits);
    requires BEWordSeqToInt(b[..]) < power(power2(32), bdigits);
    requires bv == b[b.Length-1-bi];
    ensures BEWordSeqToInt(a[..]) * BEWordSeqToInt(SelectDigitRange(b[..], bi, 0))
             + BEWordSeqToInt(SelectDigitRange(a[..], adigits, 0)) * bv * power(power2(32),bi)
        < power(power2(32), adigits + bdigits);
{
    ghost var pv := power2(32); lemma_2toX();
    var aval := BEWordSeqToInt(a[..]);
    var bval := BEWordSeqToInt(b[..]);
    calc {
        BEWordSeqToInt(a[..]) * BEWordSeqToInt(SelectDigitRange(b[..], bi, 0))
         + BEWordSeqToInt(SelectDigitRange(a[..], adigits, 0)) * bv * power(power2(32),bi);
            //-{ lemma_LeadingZeros(pv, [], SelectDigitRange(a[..], adigits, 0)); }
        BEWordSeqToInt(a[..]) * BEWordSeqToInt(SelectDigitRange(b[..], bi, 0))
         + BEWordSeqToInt(a[..]) * bv * power(power2(32),bi);
            { lemma_mul_is_associative_forall(); lemma_mul_is_distributive_forall(); }
        BEWordSeqToInt(a[..]) * (
            BEWordSeqToInt(SelectDigitRange(b[..], bi, 0)) + bv * power(power2(32),bi));
            { lemma_BEDigitSeqToInt_singleton(pv, DigitAt(b[..], bi)); }
        BEWordSeqToInt(a[..]) *
            (BEDigitSeqToInt(pv, [DigitAt(b[..], bi)])*power(pv,bi)
                + BEDigitSeqToInt(pv, SelectDigitRange(b[..], bi, 0)));
            { lemma_SelectSingletonRange(b[..], bi+1, bi); }
        BEWordSeqToInt(a[..]) *
            (BEDigitSeqToInt(pv, SelectDigitRange(b[..], bi+1, bi))*power(pv,bi)
                + BEDigitSeqToInt(pv, SelectDigitRange(b[..], bi, 0)));
            { lemma_BEInterpretation_Select_general(pv, b[..], bi+1, bi, 0); }
        BEWordSeqToInt(a[..]) * BEWordSeqToInt(SelectDigitRange(b[..], bi+1, 0));
        <= {
            calc {
                BEWordSeqToInt(SelectDigitRange(b[..], bi+1, 0));
                <= {
                    lemma_BEWordSeqToInt_bound(SelectDigitRange(b[..], b.Length, bi+1));
                    lemma_power_positive(pv, bi+1);
                    lemma_mul_nonnegative(BEWordSeqToInt(SelectDigitRange(b[..], b.Length, bi+1)), power(pv, bi+1));
                }
                BEWordSeqToInt(SelectDigitRange(b[..], b.Length, bi+1))*power(pv, bi+1)
                    + BEWordSeqToInt(SelectDigitRange(b[..], bi+1, 0));
                { lemma_BEInterpretation_Select_general(pv, b[..], b.Length, bi+1, 0); }
                BEWordSeqToInt(SelectDigitRange(b[..], b.Length, 0));
                { assert b[..] == SelectDigitRange(b[..], b.Length, 0); /* OBSERVE SEQ */ }
                BEWordSeqToInt(b[..]);
            }
            lemma_BEWordSeqToInt_bound(a[..]);
            lemma_mul_inequality(
                BEWordSeqToInt(SelectDigitRange(b[..], bi+1, 0)),
                BEWordSeqToInt(b[..]),
                BEWordSeqToInt(a[..]));
          }
        BEWordSeqToInt(a[..]) * BEWordSeqToInt(b[..]);
        aval * bval;
        <=  {
            lemma_BEWordSeqToInt_bound(b[..]);
            lemma_mul_inequality(aval, power(pv,adigits), bval); }
        power(pv, adigits) * bval;
        <   {
            lemma_power_positive(pv, adigits);
            lemma_mul_strict_inequality(bval, power(pv, bdigits), power(pv,adigits)); }
        power(pv, adigits) * power(pv, bdigits);
            { lemma_power_adds(pv, adigits, bdigits); }
        power(pv, adigits + bdigits);
    }
}

method FleetNatMul(a:array<int>, b:array<int>) returns (c:array<int>)
    requires a!=null;
    requires IsDigitSeq(power2(32), a[..]);
    requires b!=null;
    requires IsDigitSeq(power2(32), b[..]);
    ensures c!=null;
    ensures fresh(c);
    ensures IsDigitSeq(power2(32), c[..]);
    ensures BEWordSeqToInt(c[..]) == BEWordSeqToInt(a[..]) * BEWordSeqToInt(b[..]);
{
    ghost var pv := power2(32); lemma_2toX();
    var adigits := CountNonzeroDigits(a);
    var bdigits := CountNonzeroDigits(b);
    var cdigits := adigits + bdigits;

    c := FleetAlloc(cdigits);

    var bi := 0;

    lemma_LeadingZeros(pv, [], SelectDigitRange(b[..], bi, 0));
    lemma_BEWordSeqToInt_SelectDigitRange_empty(b[..]);

    var blenm1 := b.Length - 1;
    while (bi < bdigits)
        invariant 0<=bi<=bdigits;
        invariant IsDigitSeq(power2(32), c[..]);
        invariant BEWordSeqToInt(c[..]) == BEWordSeqToInt(a[..]) * BEWordSeqToInt(SelectDigitRange(b[..], bi, 0));
    {
        ghost var lastc := c[..];
        ghost var lastbi := bi;
        var bv := b[blenm1 - bi];

        lemma_FleetNatMul_c_adequate_length(a, b, adigits, bdigits, bi, bv);
        FleetNatMul_one(c, bi, a, adigits, bv);
        bi := bi + 1;
        calc {
            BEWordSeqToInt(c[..]);
            BEWordSeqToInt(lastc)
                + BEWordSeqToInt(SelectDigitRange(a[..], adigits, 0)) * bv * power(pv,lastbi);
                
            BEWordSeqToInt(lastc)
               + BEWordSeqToInt(a[..]) * bv * power(pv,lastbi);
           
            BEWordSeqToInt(a[..]) * BEWordSeqToInt(SelectDigitRange(b[..], lastbi, 0))
               + BEWordSeqToInt(a[..]) * bv * power(pv,lastbi);
               { lemma_mul_is_associative(BEWordSeqToInt(a[..]), bv, power(pv,lastbi)); }
            BEWordSeqToInt(a[..]) * BEWordSeqToInt(SelectDigitRange(b[..], lastbi, 0))
                 + BEWordSeqToInt(a[..]) * (bv * power(pv,lastbi));               
                { lemma_mul_is_distributive(BEWordSeqToInt(a[..]),  BEWordSeqToInt(SelectDigitRange(b[..], lastbi, 0)), bv * power(pv,lastbi)); }
            BEWordSeqToInt(a[..]) * (
                BEWordSeqToInt(SelectDigitRange(b[..], lastbi, 0)) + bv * power(pv,lastbi));
                { lemma_SelectSingletonRange(b[..], bi, lastbi);
                  lemma_BEDigitSeqToInt_singleton(pv, DigitAt(b[..], lastbi)); }
            BEWordSeqToInt(a[..]) * (
                BEWordSeqToInt(SelectDigitRange(b[..], bi, lastbi)) * power(pv, lastbi)
                + BEWordSeqToInt(SelectDigitRange(b[..], lastbi, 0)));
                { lemma_BEInterpretation_Select_general(pv, b[..], bi, lastbi, 0); }
            BEWordSeqToInt(a[..]) * BEWordSeqToInt(SelectDigitRange(b[..], bi, 0));
        }
    }

    lemma_LeadingZeros(pv, SelectDigitRange(b[..], bi, 0), b[..]);
}
