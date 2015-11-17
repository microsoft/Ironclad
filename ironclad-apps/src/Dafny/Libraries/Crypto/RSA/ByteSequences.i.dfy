include "RSASpec.s.dfy"
include "../../Math/power2.i.dfy"
include "../../Util/integer_sequences_premium.i.dfy"
include "../../BigNum/BigNumBEAdaptor.i.dfy"

static function BigEndianIntegerValue(os:seq<int>) : nat
    decreases |os|;
    requires IsByteSeq(os);
{
    if (os==[]) then
        0
    else
        BigEndianIntegerValue(os[0..|os|-1])*256 + os[|os|-1]
}

static lemma lemma_BigEndianIntegerValue_nonnegative(os:seq<int>)
    decreases |os|;
    requires IsByteSeq(os);
    ensures 0 <= BigEndianIntegerValue(os);
{
    if (os!=[])
    {
        calc {
            BigEndianIntegerValue(os);
            BigEndianIntegerValue(os[0..|os|-1])*256 + os[|os|-1];
            >=  { lemma_BigEndianIntegerValue_nonnegative(os[0..|os|-1]); }
            0*256 + os[|os|-1];
            os[|os|-1];
            >= 0;
        }
    }
}

static lemma lemma_BigEndianIntegerValue_strip_hi(os:seq<int>)
    decreases |os|;
    requires IsByteSeq(os);
    requires 0 < |os|;
    ensures BigEndianIntegerValue(os) == os[0]*power2(8*(|os|-1)) + BigEndianIntegerValue(os[1..]);
{
    if(|os|==1)
    {
        calc {
            BigEndianIntegerValue(os);
            BigEndianIntegerValue(os[0..|os|-1])*256 + os[|os|-1];
            BigEndianIntegerValue([])*256 + os[0];
            0*256 + os[0];
            os[0];
                { lemma_mul_basics_forall(); }
            mul(os[0],1);
                { lemma_power2_0_is_1(); }
            os[0]*power2(0);
            os[0]*power2(8*0);
            os[0]*power2(8*(|os|-1));
            os[0]*power2(8*(|os|-1)) + 0;
            os[0]*power2(8*(|os|-1)) + BigEndianIntegerValue(os[1..]);
        }
    } else {
        var sos := os[0..|os|-1];
        calc {
            BigEndianIntegerValue(os);
                //- defn BigEndianIntegerValue
            BigEndianIntegerValue(os[0..|os|-1])*256 + os[|os|-1];
                //- defn sos
            BigEndianIntegerValue(sos)*256 + os[|os|-1];
                { lemma_BigEndianIntegerValue_strip_hi(sos); }
            (sos[0]*power2(8*(|sos|-1)) + BigEndianIntegerValue(sos[1..]))*256 + os[|os|-1];
                //- distributitivity of boogie mul
            (sos[0]*power2(8*(|sos|-1)))*256 + BigEndianIntegerValue(sos[1..])*256 + os[|os|-1];
                {
                    assert |sos|-1 == |os|-2;
                    assert sos[1..] == os[1..|os|-1];
                }
            (os[0]*power2(8*(|os|-2)))*256 + BigEndianIntegerValue(os[1..|os|-1])*256 + os[|os|-1];
                { lemma_mul_is_mul_boogie(os[0]*power2(8*(|os|-2)),256); }
            mul(os[0]*power2(8*(|os|-2)),256) + BigEndianIntegerValue(os[1..|os|-1])*256 + os[|os|-1];
                { lemma_mul_is_associative_forall(); }
            os[0]*mul(power2(8*(|os|-2)),256) + BigEndianIntegerValue(os[1..|os|-1])*256 + os[|os|-1];
                {
                    lemma_2toX();
                    assert power2(8)==256;
                }
            os[0]*(power2(8*(|os|-2))*power2(8)) + BigEndianIntegerValue(os[1..|os|-1])*256 + os[|os|-1];
                { lemma_power2_adds(8*(|os|-2), 8); }
            os[0]*power2(8*(|os|-2)+8) + BigEndianIntegerValue(os[1..|os|-1])*256 + os[|os|-1];
                {
                    lemma_mul_is_mul_boogie(8, |os|-2);
                    lemma_mul_basics_forall();
                }
            os[0]*power2(mul(8,(|os|-2))+mul(8,1)) + BigEndianIntegerValue(os[1..|os|-1])*256 + os[|os|-1];
                { lemma_mul_is_distributive_forall(); }
            os[0]*power2(mul(8,(|os|-2)+1)) + BigEndianIntegerValue(os[1..|os|-1])*256 + os[|os|-1];
                //- boogie additive arithmetic
            os[0]*power2(mul(8,|os|-1)) + BigEndianIntegerValue(os[1..|os|-1])*256 + os[|os|-1];
                { lemma_mul_is_mul_boogie(8, |os|-1); }
            os[0]*power2(8*(|os|-1)) + BigEndianIntegerValue(os[1..|os|-1])*256 + os[|os|-1];
                {
                    assert os[1..|os|-1] == os[1..][0..|os[1..]|-1];
                    assert os[|os|-1] == os[1..][|os[1..]|-1];
                }
            os[0]*power2(8*(|os|-1)) + BigEndianIntegerValue(os[1..][0..|os[1..]|-1])*256 + os[1..][|os[1..]|-1];
                //- BigEndianIntegerValue ensures
            os[0]*power2(8*(|os|-1)) + BigEndianIntegerValue(os[1..]);
        }
    }
}

static lemma lemma_BigEndianIntegerValue_zero_prefix(s:seq<int>, s_suffix:seq<int>)
    requires IsByteSeq(s);
    requires IsByteSeq(s_suffix);
    requires ZeroPrefix(s, s_suffix);
    ensures BigEndianIntegerValue(s) == BigEndianIntegerValue(s_suffix);
{
    if (|s| == |s_suffix|)
    {
        assert s == s_suffix;
    }
    else
    {
        calc {
            BigEndianIntegerValue(s);
                { lemma_BigEndianIntegerValue_strip_hi(s); }
            s[0]*power2(8*(|s|-1)) + BigEndianIntegerValue(s[1..]);
            mul(0,power2(8*(|s|-1))) + BigEndianIntegerValue(s[1..]);
                { lemma_mul_basics_forall(); }
            BigEndianIntegerValue(s[1..]);
                { lemma_BigEndianIntegerValue_zero_prefix(s[1..], s_suffix); }
            BigEndianIntegerValue(s_suffix);
        }
    }
}

static lemma lemma_BigEndianIntegerValue_bound(s:seq<int>)
    decreases |s|;
    requires IsByteSeq(s);
    ensures |s|>0 ==> power2(8*(|s|-1))*s[0] <= BigEndianIntegerValue(s);
    ensures |s|>0 ==> BigEndianIntegerValue(s) < power2(8*(|s|-1))*(s[0]+1);
    ensures BigEndianIntegerValue(s) < power2(8*|s|);
{
    if (s==[])
    {
        calc {
            BigEndianIntegerValue(s);
            0;
            < 1;
                { lemma_power2_0_is_1(); }
            power2(0);
            power2(8*|s|);
        }
    }
    else
    {
        calc {
            BigEndianIntegerValue(s);
            BigEndianIntegerValue(s[0..|s|-1])*256 + s[|s|-1];
            <=  { lemma_BigEndianIntegerValue_bound(s[0..|s|-1]); }
            (power2(8*|s[0..|s|-1]|)-1)*256 + s[|s|-1];
                { assert |s[0..|s|-1]| == |s|-1; }
            (power2(8*(|s|-1))-1)*256 + s[|s|-1];
                {
                    lemma_mul_is_mul_boogie(power2(8*(|s|-1))-1,256);
                }
            mul(power2(8*(|s|-1))-1,256) + s[|s|-1];
                {
                    lemma_2toX();
                    assert power2(8)==256;
                }
            mul(power2(8*(|s|-1))-1,power2(8)) + s[|s|-1];
                { lemma_mul_is_distributive_forall(); }
            mul(power2(8*(|s|-1)),power2(8))-mul(1,power2(8)) + s[|s|-1];
                { lemma_power2_adds(8*(|s|-1), 8); }
            power2(8*(|s|-1)+8) - mul(1,power2(8)) + s[|s|-1];
                { lemma_mul_basics_forall(); }
            power2(8*(|s|-1)+8) - power2(8) + s[|s|-1];
                {
                    lemma_2toX();
                    assert power2(8)==256;
                }
            power2(8*(|s|-1)+8) - 256 + s[|s|-1];
            <   { lemma_2toX(); assert s[|s|-1] < 256; }
            power2(8*(|s|-1)+8);
            power2(8*|s|);
        }

        calc {
            BigEndianIntegerValue(s);
                { lemma_BigEndianIntegerValue_strip_hi(s); }
            s[0]*power2(8*(|s|-1)) + BigEndianIntegerValue(s[1..]);
            <    { lemma_BigEndianIntegerValue_bound(s[1..]); }
            s[0]*power2(8*(|s|-1)) + power2(8*|s[1..]|);
            s[0]*power2(8*(|s|-1)) + power2(8*(|s|-1));
                { lemma_mul_basics_forall(); }
            s[0]*power2(8*(|s|-1)) + mul(1,power2(8*(|s|-1)));
                { lemma_mul_is_distributive_forall(); }
            (s[0]+1)*power2(8*(|s|-1));
                { lemma_mul_is_commutative_forall(); }
            power2(8*(|s|-1))*(s[0]+1);
        }

        if (|s|==1)
        {
            calc {
                power2(8*(|s|-1))*s[0];
                power2(8*0)*s[0];
                power2(0)*s[0];
                    { lemma_power2_0_is_1(); }
                mul(1,s[0]);
                    { lemma_mul_is_mul_boogie(1,s[0]); }
                1*s[0];
                s[0];
                s[|s|-1];
                0*256 + s[|s|-1];
                BigEndianIntegerValue([])*256 + s[|s|-1];
                BigEndianIntegerValue(s[0..|s|-1])*256 + s[|s|-1];
                BigEndianIntegerValue(s);
            }
        }
        else
        {
            calc {
                power2(8*(|s|-1))*s[0];
                power2(8*(|s|-2+1))*s[0];
                power2(8*(|s|-2)+8)*s[0];
                    { lemma_power2_adds(8*(|s|-2), 8); }
                (power2(8*(|s|-2))*power2(8))*s[0];
                    { lemma_mul_is_associative_forall(); }
                power2(8*(|s|-2))*(power2(8)*s[0]);
                    { lemma_mul_is_commutative_forall(); }
                power2(8*(|s|-2))*(s[0]*power2(8));
                    { lemma_mul_is_associative_forall(); }
                (power2(8*(|s|-2))*s[0])*power2(8);
                    {
                        lemma_2toX();
                        assert power2(8)==256;
                    }
                mul(power2(8*(|s|-2))*s[0],256);
                    { lemma_mul_is_mul_boogie(power2(8*(|s|-2))*s[0],256); }
                (power2(8*(|s|-2))*s[0])*256;
                <= (power2(8*(|s|-2))*s[0])*256 + s[|s|-1];
                <=    {
                        lemma_BigEndianIntegerValue_bound(s[0..|s|-1]);
                        assert |s[0..|s|-1]|>0 ==> power2(8*(|s[0..|s|-1]|-1))*s[0..|s|-1][0] <= BigEndianIntegerValue(s[0..|s|-1]);
                        assert power2(8*(|s[0..|s|-1]|-1))*s[0..|s|-1][0] <= BigEndianIntegerValue(s[0..|s|-1]);
                        assert |s[0..|s|-1]|-1 == |s|-2;
                        assert s[0..|s|-1][0] == s[0];
                        assert power2(8*(|s|-2))*s[0] <= BigEndianIntegerValue(s[0..|s|-1]);
                        lemma_mul_inequality(power2(8*(|s|-2))*s[0], BigEndianIntegerValue(s[0..|s|-1]), 256);
                    }
                BigEndianIntegerValue(s[0..|s|-1])*256 + s[|s|-1];
                BigEndianIntegerValue(s);
            }
        }
    }
}

static lemma lemma_BigEndianIntegerValue_increases(prefix:seq<int>, common:seq<int>)
    requires IsByteSeq(prefix);
    requires IsByteSeq(common);
    ensures BigEndianIntegerValue(common) <= BigEndianIntegerValue(prefix+common);
{
    if (|prefix|==0)
    {
        assert common == prefix+common;
    }
    else
    {
        calc {
            BigEndianIntegerValue(common);
            <=  { lemma_BigEndianIntegerValue_increases(prefix[1..],common); }
            BigEndianIntegerValue(prefix[1..]+common);
                { assert prefix[1..]+common == (prefix+common)[1..]; }
            BigEndianIntegerValue((prefix+common)[1..]);
            <=  { lemma_mul_nonnegative((prefix+common)[0], power2(8*(|(prefix+common)|-1))); }
            (prefix+common)[0]*power2(8*(|(prefix+common)|-1)) + BigEndianIntegerValue((prefix+common)[1..]);
                { lemma_BigEndianIntegerValue_strip_hi(prefix+common); }
            BigEndianIntegerValue(prefix+common);
        }
    }
}



static lemma lemma_BigEndianIntegerValue_equal_prefix_increases(s0:seq<int>, s1:seq<int>, i:int)
    requires IsByteSeq(s0);
    requires IsByteSeq(s1);
    requires 0<=i<|s0|==|s1|;
    requires forall j :: 0<=j<i ==> s0[j] == s1[j];
    requires s0[i] < s1[i];
    ensures BigEndianIntegerValue(s0) < BigEndianIntegerValue(s1);
{
    if (i==0)
    {
        calc
        {
            BigEndianIntegerValue(s0);
            <   { lemma_BigEndianIntegerValue_bound(s0); }
            power2(8*(|s0|-1))*(s0[0]+1);
            power2(8*(|s1|-1))*(s0[0]+1);
            <=  { lemma_mul_left_inequality(power2(8*(|s1|-1)),s0[0]+1,s1[0]); }
            power2(8*(|s1|-1))*s1[0];
            <=  { lemma_BigEndianIntegerValue_bound(s1); }
            BigEndianIntegerValue(s1);
        }
    }
    else
    {
        calc
        {
            BigEndianIntegerValue(s0);
                { lemma_BigEndianIntegerValue_strip_hi(s0); }
            s0[0]*power2(8*(|s0|-1)) + BigEndianIntegerValue(s0[1..]);
            <   { lemma_BigEndianIntegerValue_equal_prefix_increases(s0[1..], s1[1..], i-1); }
            s0[0]*power2(8*(|s1|-1)) + BigEndianIntegerValue(s1[1..]);
            s1[0]*power2(8*(|s1|-1)) + BigEndianIntegerValue(s1[1..]);
                { lemma_BigEndianIntegerValue_strip_hi(s1); }
            BigEndianIntegerValue(s1);
        }
    }
}

static lemma lemma_BigEndianIntegerValue_equal_prefix_unequal(s0:seq<int>, s1:seq<int>, i:int)
    requires IsByteSeq(s0);
    requires IsByteSeq(s1);
    requires 0<=i<|s0|==|s1|;
    requires forall j :: 0<=j<i ==> s0[j] == s1[j];
    requires s0[i] != s1[i];
    ensures BigEndianIntegerValue(s0) != BigEndianIntegerValue(s1);
{
    if (s0[i]<s1[i])
    {
        lemma_BigEndianIntegerValue_equal_prefix_increases(s0, s1, i);
    }
    else
    {
        lemma_BigEndianIntegerValue_equal_prefix_increases(s1, s0, i);
    }
}

static lemma lemma_lemma_BigEndianIntegerValue_zero_prefix_converse_inner_helper(w0:int, w1:int, s0tail:seq<int>, s1:seq<int>) returns(w0':int)
    requires 0 <= w0 <= w1 < |s1| == |s0tail|;
    requires forall j :: 0 <= j < w0 ==> s0tail[j]==s1[j];
    requires s0tail[w1] != s1[w1];
    decreases w1 - w0;
    ensures 0 <= w0' <= w1 < |s1| == |s0tail|;
    ensures forall j :: 0 <= j < w0' ==> s0tail[j]==s1[j];
    ensures s0tail[w0'] != s1[w0'];
{
    w0' := w0;
    if (w0 <= w1 && s0tail[w0]==s1[w0])
    {
        w0' := lemma_lemma_BigEndianIntegerValue_zero_prefix_converse_inner_helper(w0 + 1, w1, s0tail, s1);
    }
}

static lemma lemma_BigEndianIntegerValue_zero_prefix_converse_inner(s0:seq<int>, s1:seq<int>)
    requires IsByteSeq(s0);
    requires IsByteSeq(s1);
    requires |s0| >= |s1|;
    requires BigEndianIntegerValue(s0) == BigEndianIntegerValue(s1);
    ensures ZeroPrefix(s0, s1);
{
    if !(forall i :: 0 <= i < |s0|-|s1| ==> s0[i] == 0)
    {
        //- a prefix byte isn't zero.
        var witness :| 0 <= witness < |s0|-|s1| && s0[witness] != 0;
        assert |s1| <= |s0|-witness-1;
        calc {
            BigEndianIntegerValue(s1);
            <   { lemma_BigEndianIntegerValue_bound(s1); }
            power2(8*|s1|);
            <=  { lemma_power2_increases(8*|s1|, 8*(|s0|-witness-1)); }
            power2(8*(|s0|-witness-1));
            <=  { lemma_mul_increases_forall(); }
            s0[witness]*power2(8*(|s0|-witness-1));
                { lemma_mul_is_commutative_forall(); }
            power2(8*(|s0|-witness-1))*s0[witness];
            power2(8*(|s0[witness..]|-1))*s0[witness..][0];
            <=  { lemma_BigEndianIntegerValue_bound(s0[witness..]); }
            BigEndianIntegerValue(s0[witness..]);
            <=  { lemma_BigEndianIntegerValue_increases(s0[..witness], s0[witness..]); }
            BigEndianIntegerValue(s0[..witness]+s0[witness..]);
                { assert s0[..witness]+s0[witness..] == s0; }
            BigEndianIntegerValue(s0);
        }
        assert false;
    }
    else if (s0[ |s0|-|s1| .. ] != s1)
    {
        //- don't agree on suffix
        var s0tail := s0[ |s0|-|s1| .. ];

        var w1 :| 0 <= w1 < |s1| && (s0tail[w1] != s1[w1]);
        assert w1 < |s1|;

        //- convince Dafny there's a LEAST such element.
        var w0 := lemma_lemma_BigEndianIntegerValue_zero_prefix_converse_inner_helper(0, w1, s0tail, s1);
/* dafnycc TODO: ghost while loops
        var w0 := 0;
        while (w0 <= w1
            && s0tail[w0]==s1[w0])
            invariant w0 <= w1 < |s1| == |s0tail|;
            invariant forall j :: 0 <= j < w0 ==> s0tail[j]==s1[j];
        {
            w0 := w0 + 1;
        }
*/

        if (w0 > w1)
        {
            assert s0tail[w1]!=s1[w1];
            assert forall j :: 0 <= j < w1 ==> s0tail[j]==s1[j];
        }
        else
        {
            w1 := w0;
            assert s0tail[w1]!=s1[w1];
            assert forall j :: 0 <= j < w1 ==> s0tail[j]==s1[j];
        }

        lemma_BigEndianIntegerValue_zero_prefix(s0, s0tail);
        assert BigEndianIntegerValue(s0) == BigEndianIntegerValue(s0tail);
        lemma_BigEndianIntegerValue_equal_prefix_unequal(s0tail, s1, w1);
        assert BigEndianIntegerValue(s0tail) != BigEndianIntegerValue(s1);
        assert false;
    }
    else
    {
        assert ZeroPrefix(s0, s1);
    }
}

static lemma lemma_BigEndianIntegerValue_zero_prefix_converse(s0:seq<int>, s1:seq<int>)
    requires IsByteSeq(s0);
    requires IsByteSeq(s1);
    requires BigEndianIntegerValue(s0) == BigEndianIntegerValue(s1);
    ensures ZeroPrefix(s0, s1) || ZeroPrefix(s1, s0);
{
    if (|s0| >= |s1|)
    {
        lemma_BigEndianIntegerValue_zero_prefix_converse_inner(s0, s1);
    }
    else
    {
        lemma_BigEndianIntegerValue_zero_prefix_converse_inner(s1, s0);
    }
}

static lemma lemma_SingleZeroPrefixedBigEndianIntegerValuesEqual(s0:seq<int>, s1:seq<int>)
    requires IsByteSeq(s0);
    requires IsByteSeq(s1);
    requires BigEndianIntegerValue(s0) == BigEndianIntegerValue(s1);
    requires |s0|>0;
    requires |s1|>0;
//-    requires |s0|>0 ==> s0[0] == 0;
//-    requires |s1|>0 ==> s1[0] == 0;
    requires s0[0] == 0;
    requires s1[0] == 0;
    requires |s0|>1 ==> s0[1] != 0;
    requires |s1|>1 ==> s1[1] != 0;
    ensures s0 == s1;
{
    lemma_BigEndianIntegerValue_zero_prefix_converse(s0, s1);
}

static function LittleEndianIntegerValue(os:seq<int>) : nat
    requires IsByteSeq(os);
{
    if (os==[]) then
        0
    else
        LittleEndianIntegerValue(os[1..])*256 + os[0]
}

static method ReverseOctetString(os:seq<int>) returns (rs:seq<int>)
    ensures rs == Reverse(os);
    ensures IsByteSeq(os) ==> IsByteSeq(rs);
    ensures |os| == |rs|;
    ensures forall i :: 0<=i<|os| ==> os[i] == rs[|rs|-1-i];
{
    reveal_Reverse();
    rs := [];
    var ptr:int := 0;

    while (ptr < |os|)
        invariant 0 <= ptr <= |os|;
        invariant rs == Reverse(os[0..ptr]);
    {
        ghost var old_rs := rs;

        rs := [os[ptr]] + rs;

        ghost var os1 := os[0..ptr+1];
        calc {
            rs;
            [os[ptr]] + old_rs;
            [os[ptr]] + Reverse(os[0..ptr]);
            [os1[|os1|-1]] + Reverse(os[0..ptr]);
                {
                    calc {
                        os[0..ptr];
                        {
                            assert forall i :: 0<=i<ptr ==>
                                os[0..ptr][i] == os1[0..ptr][i];
                        }
                        os1[0..ptr];
                        os1[0..|os1|-1];
                    }
                }
            [os1[|os1|-1]] + Reverse(os1[0..|os1|-1]);
            Reverse(os1);
        }

        ptr := ptr + 1;
    }

    assert os[0..ptr] == os;
    lemma_Reverse(os, rs);
    if (IsByteSeq(os))
    {
        forall (i | 0<=i<|rs|)
            ensures 0<=rs[i]<power2(8);
        {
            assert rs[i] == os[|os|-1-i];
        }
    }
}

static lemma lemma_endian_reversal(bes:seq<int>)
    decreases |bes|;
    requires IsByteSeq(bes);
    ensures IsByteSeq(Reverse(bes));
    ensures LittleEndianIntegerValue(Reverse(bes)) == BigEndianIntegerValue(bes);
{
    reveal_Reverse();
    lemma_Reverse(bes, Reverse(bes));

    if (bes==[])
    {
    }
    else
    {
        lemma_endian_reversal(bes[0..|bes|-1]);
/*
        var les := Reverse(bes);
        assert les == [bes[|bes|-1]] + Reverse(bes[0..|bes|-1]);

        calc {
            LittleEndianIntegerValue(Reverse(bes));
            LittleEndianIntegerValue(les);
            LittleEndianIntegerValue(les[1..])*256 + les[0];
            LittleEndianIntegerValue( Reverse(bes[0..|bes|-1]) )*256 + bes[|bes|-1];
                { lemma_endian_reversal(bes[0..|bes|-1]); }
            BigEndianIntegerValue(bes[0..|bes|-1])*256 + bes[|bes|-1];
            BigEndianIntegerValue(bes);
        }
*/
    }
}

static lemma lemma_BigEndianIntegerValue_equals_BEByteSeqToInt(bs:seq<int>)
    decreases |bs|;
    requires IsByteSeq(bs);
    ensures BigEndianIntegerValue(bs) == BEByteSeqToInt(bs);
{
    lemma_2toX();
    if (bs==[])
    {
        calc {
            BigEndianIntegerValue(bs);
            0;
                { reveal_BEDigitSeqToInt_private(); }
            BEDigitSeqToInt_private(power2(8), bs);
            BEDigitSeqToInt(power2(8), bs);
            BEByteSeqToInt(bs);
        }
    }
    else
    {
        lemma_BigEndianIntegerValue_equals_BEByteSeqToInt(bs[0..|bs|-1]);
        calc {
            BigEndianIntegerValue(bs);
            BigEndianIntegerValue(bs[0..|bs|-1])*256 + bs[|bs|-1];
                { lemma_BigEndianIntegerValue_equals_BEByteSeqToInt(bs[0..|bs|-1]); }
            BEByteSeqToInt(bs[0..|bs|-1])*256 + bs[|bs|-1];
            BEDigitSeqToInt_private(256, bs[0..|bs|-1])*256 + bs[|bs|-1];
                { lemma_mul_is_mul_boogie(BEDigitSeqToInt_private(256, bs[0..|bs|-1]), 256); }
            mul(BEDigitSeqToInt_private(256, bs[0..|bs|-1]),256) + bs[|bs|-1];
                { reveal_BEDigitSeqToInt_private(); }
            BEDigitSeqToInt_private(256, bs);
            BEDigitSeqToInt(256, bs);
                { lemma_2toX(); }
            BEDigitSeqToInt(power2(8), bs);
            BEByteSeqToInt(bs);
        }
    }
}
