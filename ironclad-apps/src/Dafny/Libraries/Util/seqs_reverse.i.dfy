include "integer_sequences.s.dfy"

//-////////////////////////////////////////////////////////////////////////////
//- This file relates Big Endian (BE) seqs to LE seqs via the reverse operation.


//-////////////////////////////////////////////////////////////////////////////
//- Little-endian
//-////////////////////////////////////////////////////////////////////////////

static function {:opaque} LEDigitSeqToInt_private(place_value:int, digits:seq<int>) : int
    decreases |digits|;
{
    if (digits==[]) then
        0
    else
        LEDigitSeqToInt_private(place_value, digits[1..])*place_value + digits[0]
}

static function LEDigitSeqToInt(place_value:int, digits:seq<int>) : int
    requires IsDigitSeq(place_value, digits);
{
    LEDigitSeqToInt_private(place_value, digits)
}


//-////////////////////////////////////////////////////////////////////////////
//- Reverse
//-////////////////////////////////////////////////////////////////////////////

static lemma{:dafnycc_conservative_seq_triggers} lemma_Reverse(os:seq<int>, rs:seq<int>)
    requires rs == Reverse(os);
    ensures |os| == |rs|;
    ensures forall i :: 0<=i<|os| ==> os[i] == rs[|rs|-1-i];
    decreases |os|;
{
    reveal_Reverse();
    if (os==[])
    {
    }
    else
    {
        var sos := os[0..|os|-1];
        lemma_Reverse(sos, Reverse(sos));
        forall (i | 0<=i<|os|)
            ensures os[i] == rs[|rs|-1-i];
        {
            if (i==|os|-1)
            {
            }
            else
            {
                calc {
                    os[i];
                    sos[i];
                    Reverse(sos)[|Reverse(sos)|-1-i];
                    rs[|rs|-1-i];
                }
            }
        }
    }
}

static lemma lemma_Reverse_symmetry(os:seq<int>, rs:seq<int>)
    requires os == Reverse(rs);
    ensures rs == Reverse(os);
{
    lemma_Reverse(os, Reverse(os));
    assert |os| == |Reverse(os)|;
    assert forall i :: 0<=i<|os| ==> os[i] == Reverse(os)[|Reverse(os)|-1-i];

    lemma_Reverse(rs, Reverse(rs));
    assert |rs| == |Reverse(rs)|;
    assert forall i :: 0<=i<|rs| ==> rs[i] == Reverse(rs)[|Reverse(rs)|-1-i];

    assert |Reverse(os)| == |os| == |Reverse(rs)| == |rs|;
    forall (i | 0<=i<|rs|)
        ensures Reverse(os)[i] == rs[i];
    {
    }
}

static method{:dafnycc_conservative_seq_triggers} ReverseDigitSeq(ghost pv:int, ds:seq<int>) returns (rs:seq<int>)
    requires 1<pv;
    requires IsDigitSeq(pv, ds);
    ensures rs == Reverse(ds);
    ensures |ds| == |rs|;
    ensures IsDigitSeq(pv, rs);
{
    reveal_Reverse();
    rs := [];
    var ptr:int := 0;

    while (ptr < |ds|)
        invariant 0 <= ptr <= |ds|;
        invariant rs == Reverse(ds[0..ptr]);
    {
        ghost var old_rs := rs;

        rs := [ds[ptr]] + rs;    // This is probably n^2. :v)

        ghost var os1 := ds[0..ptr+1];
        calc {
            rs;
            [ds[ptr]] + old_rs;
            [ds[ptr]] + Reverse(ds[0..ptr]);
            [os1[|os1|-1]] + Reverse(ds[0..ptr]);
                {
                    calc {
                        ds[0..ptr];
                        {
                            assert forall i :: 0<=i<ptr ==>
                                ds[0..ptr][i] == os1[0..ptr][i];
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

    assert ds[0..ptr] == ds;
    lemma_Reverse(ds, rs);
    lemma_ReverseDigitSeq_helper(pv, ds, ptr, rs);
}

static lemma lemma_ReverseDigitSeq_helper(pv:int, ds:seq<int>, ptr:int, rs:seq<int>)
    requires 0<= ptr <= |ds|;
    requires ds[0..ptr] == ds;
     requires 1<pv;
    requires IsDigitSeq(pv, ds);
    requires rs == Reverse(ds[0..ptr]);
    ensures forall i ::  0<=i<|rs| ==> 0<=rs[i]<pv;
{
    lemma_Reverse(ds, rs);
    forall (i | 0<=i<|rs|)
        ensures 0<=rs[i]<pv;
    {
        assert rs[i] == ds[|ds|-1-i];
        assert 0<=rs[i]<pv;
    }
}

static lemma lemma_Reverse_preserves_IsDigitSeq(pv:int, ds:seq<int>, rs:seq<int>)
    requires 1<pv;
    requires rs == Reverse(ds);
    ensures IsDigitSeq(pv, ds) == IsDigitSeq(pv, rs);
{
    lemma_Reverse(ds, rs);
    if (IsDigitSeq(pv, ds))
    {
        forall (i | 0<=i<|rs|)
            ensures 0 <= rs[i] < pv;
        {
            assert ds[|ds|-1-i] == rs[i];
        }
    }
}

static lemma lemma_Reverse_converts_endianness_inner(pv:int, ds:seq<int>, rs:seq<int>)
    requires 1<pv;
    requires IsDigitSeq(pv, ds);
    requires IsDigitSeq(pv, rs);
    requires |ds|==|rs|;
    requires forall i :: 0<=i<|ds| ==> ds[i] == rs[|rs|-1-i];
    decreases |ds|;
    ensures BEDigitSeqToInt(pv, ds) == LEDigitSeqToInt(pv, rs);
{
    reveal_BEDigitSeqToInt_private();
    reveal_LEDigitSeqToInt_private();
    if (|ds|!=0)
    {
        lemma_Reverse_converts_endianness_inner(pv, ds[0..|ds|-1], rs[1..]);
    }
}

static lemma lemma_Reverse_converts_endianness(pv:int, ds:seq<int>, rs:seq<int>)
    requires 1<pv;
    requires IsDigitSeq(pv, ds);
    requires IsDigitSeq(pv, rs);
    requires rs == Reverse(ds);
    ensures BEDigitSeqToInt(pv, ds) == LEDigitSeqToInt(pv, rs);
{
    lemma_Reverse(ds, rs);
    lemma_Reverse_converts_endianness_inner(pv, ds, rs);
}


