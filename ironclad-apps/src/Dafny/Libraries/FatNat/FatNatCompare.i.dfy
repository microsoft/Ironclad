include "../Util/seqs_common.i.dfy"
include "FatNatCommon.i.dfy"
include "CanonicalArrays.i.dfy"

datatype Cmp = CmpLt | CmpEq | CmpGt;

predicate DefCmp(a:int, cmp:Cmp, b:int)
{
       (cmp==CmpLt <==> (a < b))
    && (cmp==CmpEq <==> (a == b))
    && (cmp==CmpGt <==> (a > b))
}

lemma lemma_FNCompare_inner_core_eq(pv:int, As:seq<int>, Bs:seq<int>, i:int, da:int, db:int)
    requires pv==power2(32);
    requires IsWordSeq(As);
    requires IsWordSeq(Bs);
    requires |As| == |Bs|;
    requires 0 < i <= |Bs|;
    requires DigitAt(As,i-1) == da;
    requires DigitAt(Bs,i-1) == db;
    requires BEDigitSeqToInt(pv, SelectDigitRange(As, |As|, i))
        == BEDigitSeqToInt(pv, SelectDigitRange(Bs, |Bs|, i));
    requires da==db;
    ensures BEDigitSeqToInt(pv, SelectDigitRange(As, |As|, i-1))
        == BEDigitSeqToInt(pv, SelectDigitRange(Bs, |Bs|, i-1));
{
    ghost var Ass := SelectDigitRange(As, |As|, i);
    ghost var Asl := SelectDigitRange(As, |As|, i-1);
    ghost var Bss := SelectDigitRange(Bs, |Bs|, i);
    ghost var Bsl := SelectDigitRange(Bs, |Bs|, i-1);

    calc {  
        Asl[|Asl|-1];
        DigitAt(As,i-1);
        DigitAt(Bs,i-1);
        Bsl[|Bsl|-1];
    }

    calc {
        BEDigitSeqToInt(pv, Asl);
            { reveal_BEDigitSeqToInt_private();
              assert Asl[0..|Asl|-1] == Asl[..|Asl|-1]; //- OBSERVE SEQ
              assert Asl[..|Asl|-1] == Ass;   //- OBSERVE SEQ
            }
        BEDigitSeqToInt(pv, Ass)*pv + Asl[|Asl|-1];
        BEDigitSeqToInt(pv, Bss)*pv + Bsl[|Bsl|-1];
            { reveal_BEDigitSeqToInt_private();
              assert Bsl[0..|Bsl|-1] == Bsl[..|Bsl|-1]; //- OBSERVE SEQ
              assert Bsl[..|Bsl|-1] == Bss;   //- OBSERVE SEQ
            }
        BEDigitSeqToInt(pv, Bsl);
    }
}

lemma lemma_FNCompare_inner_core_lt(pv:int, As:seq<int>, Bs:seq<int>, i:int, da:int, db:int)
    requires pv==power2(32);
    requires IsWordSeq(As);
    requires IsWordSeq(Bs);
    requires |As| == |Bs|;
    requires 0 < i <= |Bs|;
    requires DigitAt(As,i-1) == da;
    requires DigitAt(Bs,i-1) == db;
    requires BEDigitSeqToInt(pv, SelectDigitRange(As, |As|, i))
        == BEDigitSeqToInt(pv, SelectDigitRange(Bs, |Bs|, i));
    requires da<db;
    ensures BEDigitSeqToInt(pv, As) < BEDigitSeqToInt(pv, Bs);
{
    ghost var Asv := BEDigitSeqToInt(pv, As);
    ghost var Asl := SelectDigitRange(As, |As|, i);
    ghost var Aslv := BEDigitSeqToInt(pv, Asl);
    ghost var Asr := SelectDigitRange(As, i, 0);
    ghost var Asrv := BEDigitSeqToInt(pv, Asr);

    ghost var Bsv := BEDigitSeqToInt(pv, Bs);
    ghost var Bsl := SelectDigitRange(Bs, |Bs|, i);
    ghost var Bslv := BEDigitSeqToInt(pv, Bsl);
    ghost var Bsr := SelectDigitRange(Bs, i, 0);
    ghost var Bsrv := BEDigitSeqToInt(pv, Bsr);

    assert IsDigitSeq(pv, Asr);
    ghost var Asrl  := SelectDigitRange(Asr, |Asr|, i-1);
    ghost var Asrlv := BEDigitSeqToInt(pv, Asrl);
    ghost var Asrr := SelectDigitRange(Asr, i-1, 0);
    ghost var Asrrv := BEDigitSeqToInt(pv, Asrr);

    assert IsDigitSeq(pv, Bsr);
    ghost var Bsrl := SelectDigitRange(Bsr, |Bsr|, i-1);
    ghost var Bsrlv := BEDigitSeqToInt(pv, Bsrl);
    ghost var Bsrr := SelectDigitRange(Bsr, i-1, 0);
    ghost var Bsrrv := BEDigitSeqToInt(pv, Bsrr);

    lemma_SelectDigitNest(As, i, 0, i, i-1);
    lemma_SelectSingletonRange(As, i, i-1);
    assert Asrl == [da];

    lemma_SelectDigitNest(Bs, i, 0, i, i-1);
    lemma_SelectSingletonRange(Bs, i, i-1);
    assert Bsrl == [db];

    calc {
        Asv;
            { lemma_BEInterpretation_Select(pv, As, i); }
        Aslv * power(pv,i) + Asrv;
            { lemma_BEInterpretation_Select(pv, Asr, i-1); }
        Aslv * power(pv,i) + Asrlv * power(pv, i-1) + Asrrv;
            { lemma_BEDigitSeqToInt_singleton(pv, da); }
        Aslv * power(pv,i) + da * power(pv, i-1) + Asrrv;
            { lemma_power_adds(pv,1,i-1);
              lemma_mul_is_associative_forall(); }
        Aslv * power(pv,1) * power(pv,i-1) + da * power(pv, i-1) + Asrrv;
            { lemma_mul_is_distributive_forall(); }
        (Aslv * power(pv,1) + da) * power(pv,i-1) + Asrrv;
        <   { lemma_BEDigitSeqToInt_bound(pv, Asrr); }
        (Aslv * power(pv,1) + da) * power(pv,i-1) + power(pv, i-1);
            { lemma_mul_basics_forall(); }
        (Aslv * power(pv,1) + da) * power(pv,i-1) + mul(1,power(pv, i-1));
            { lemma_mul_is_distributive_forall(); }
        (Aslv * power(pv,1) + da + 1) * power(pv,i-1);
        <=  { lemma_power_positive(pv, i-1);
              lemma_mul_inequality(
                Aslv * power(pv,1) + da + 1,
                Bslv * power(pv,1) + db,
                power(pv,i-1)); }
        (Bslv * power(pv,1) + db) * power(pv,i-1);
        <=  { lemma_BEDigitSeqToInt_bound(pv, Bsrr); }
        (Bslv * power(pv,1) + db) * power(pv,i-1) + Bsrrv;
            { lemma_mul_is_distributive_forall(); }
        Bslv * power(pv,1) * power(pv,i-1) + db * power(pv, i-1) + Bsrrv;
            { lemma_power_adds(pv,1,i-1);
                lemma_mul_is_associative_forall(); }
        Bslv * power(pv,i) + db * power(pv, i-1) + Bsrrv;
            { lemma_BEDigitSeqToInt_singleton(pv, db); }
        Bslv * power(pv,i) + Bsrlv * power(pv, i-1) + Bsrrv;
            { lemma_BEInterpretation_Select(pv, Bsr, i-1); }
        Bslv * power(pv,i) + Bsrv;
            { lemma_BEInterpretation_Select(pv, Bs, i); }
        Bsv;
    }


}

method FNCompare_inner(a:array<int>, b:array<int>) returns (cmp:Cmp)
    requires a!=null;
    requires IsWordSeq(a[..]);
    requires b!=null;
    requires IsWordSeq(b[..]);
    requires a.Length<=b.Length;
    ensures (cmp==CmpLt) <==> (BEWordSeqToInt(a[..]) < BEWordSeqToInt(b[..]));
    ensures (cmp==CmpEq) <==> (BEWordSeqToInt(a[..]) == BEWordSeqToInt(b[..]));
    ensures (cmp==CmpGt) <==> (BEWordSeqToInt(a[..]) > BEWordSeqToInt(b[..]));
{
    lemma_2to32();
    ghost var pv := power2(32);
    ghost var Bs := b[..];
    ghost var As_short := a[..];
    ghost var As := RepeatDigit_premium(0,b.Length-a.Length) + As_short;
    lemma_LeadingZeros(pv, As_short, As);
    assert BEWordSeqToInt(As_short) == BEWordSeqToInt(As);
//-    assert |Bs|==b.Length;
//-    assert |As|==|Bs|;

    if (b.Length==0)
    {
        cmp := CmpEq;
        reveal_BEDigitSeqToInt_private();
        return;
    }
    assert 0<|Bs|;

    var i_plus_one := b.Length+1; //- DafnyCC ints can't go negative!
    ghost var i := |Bs|;

    assert As[..0] == [];   //- OBSERVE SEQ
    assert Bs[..0] == [];   //- OBSERVE SEQ
    //- i is the number of digits, starting from MSW, not yet known to be equal.
    //- If As==[x y z] and i==1, then As[0]==x==Bs[0],
    //- and da==As[1]==y and db==Bs[1]==y'.

    while (i_plus_one > 0+1)
        invariant 0+1 <= i_plus_one <= |Bs|+1;
        invariant i_plus_one == i+1;
        invariant 0 <= i <= |Bs|;
        invariant As_short == a[..];
        invariant Bs == b[..];
        invariant BEDigitSeqToInt(pv, SelectDigitRange(As, |As|, i))
            == BEDigitSeqToInt(pv, SelectDigitRange(Bs, |Bs|, i));
    {
        var da := ArrayDigitAt_cmp(a, i_plus_one-1-1);
        var db := ArrayDigitAt_cmp(b, i_plus_one-1-1);

        if (da < db) {
            cmp := CmpLt;
            lemma_FNCompare_inner_core_lt(pv, As, Bs, i, da, db);
            return;
        }
        if (db < da) {
            cmp := CmpGt;
            lemma_FNCompare_inner_core_lt(pv, Bs, As, i, db, da);
            return;
        }
        lemma_FNCompare_inner_core_eq(pv, Bs, As, i, db, da);
        i_plus_one := i_plus_one - 1;
        i := i - 1;
    }
    cmp := CmpEq;
    assert i==0;
    assert As==As[0..|As|];   //- OBSERVE SEQ
    assert Bs==Bs[0..|Bs|];   //- OBSERVE SEQ
    assert BEWordSeqToInt(a[..]) == BEWordSeqToInt(b[..]);
}

method FatNatCompare(a:array<int>, b:array<int>) returns (cmp:Cmp)
    requires a!=null;
    requires IsWordSeq(a[..]);
    requires b!=null;
    requires IsWordSeq(b[..]);
    ensures (cmp.CmpLt?) <==> (BEWordSeqToInt(a[..]) < BEWordSeqToInt(b[..]));
    ensures (cmp.CmpEq?) <==> (BEWordSeqToInt(a[..]) == BEWordSeqToInt(b[..]));
    ensures (cmp.CmpGt?) <==> (BEWordSeqToInt(a[..]) > BEWordSeqToInt(b[..]));
{
    if (a.Length > b.Length)
    {
        var neg_cmp := FNCompare_inner(b, a);
        match neg_cmp {
            case CmpEq =>
                cmp := CmpEq;
            case CmpLt =>
                cmp := CmpGt;
            case CmpGt =>
                cmp := CmpLt;
        }
    }
    else
    {
        cmp := FNCompare_inner(a, b);
    }
}

method FatNatLt(a:array<int>, b:array<int>) returns (rc:bool)
    requires WellformedFatNat(a);
    requires WellformedFatNat(b);
    ensures rc <==> (BEWordSeqToInt(a[..]) < BEWordSeqToInt(b[..]));
{
    var cv := FatNatCompare(a, b);
    rc := cv.CmpLt?;
}

method FatNatLe(a:array<int>, b:array<int>) returns (rc:bool)
    requires WellformedFatNat(a);
    requires WellformedFatNat(b);
    ensures rc <==> (BEWordSeqToInt(a[..]) <= BEWordSeqToInt(b[..]));
{
    var cv := FatNatCompare(a, b);
    rc := cv.CmpEq? || cv.CmpLt?;
}

method FatNatEq(a:array<int>, b:array<int>) returns (rc:bool)
    requires WellformedFatNat(a);
    requires WellformedFatNat(b);
    ensures rc <==> (BEWordSeqToInt(a[..]) == BEWordSeqToInt(b[..]));
{
    var cv := FatNatCompare(a, b);
    rc := cv.CmpEq?;
}

method FatNatGe(a:array<int>, b:array<int>) returns (rc:bool)
    requires WellformedFatNat(a);
    requires WellformedFatNat(b);
    ensures rc <==> (BEWordSeqToInt(a[..]) >= BEWordSeqToInt(b[..]));
{
    var cv := FatNatCompare(a, b);
    rc := cv.CmpEq? || cv.CmpGt?;
}

method FatNatGt(a:array<int>, b:array<int>) returns (rc:bool)
    requires WellformedFatNat(a);
    requires WellformedFatNat(b);
    ensures rc <==> (BEWordSeqToInt(a[..]) > BEWordSeqToInt(b[..]));
{
    var cv := FatNatCompare(a, b);
    rc := cv.CmpGt?;
}

method TestEqSmallLiteralFatNat(x:nat, X:array<int>) returns (rc:bool)
    requires IsWord(x);
    requires WellformedFatNat(X);
    ensures rc <==> J(X)==x;
{
    if (X.Length==0) {
        reveal_BEDigitSeqToInt_private();
        assert J(X)==0;
        rc := x==0;
    } else if (X.Length==1) {
        lemma_2toX();
        lemma_BEDigitSeqToInt_singleton(power2(32), X[0]);
        assert X[..] == [X[0]]; //- OBSERVE SEQ
        assert J(X)==X[0];
        rc := x==X[0];
    } else {
        
        var probe := MakeBELiteralArray(x);
        rc := FatNatEq(probe, X);
    }
}
