include "../../BigNum/BigNumBEAdaptor.i.dfy"

lemma lemma_keybits_implies_length(N:BigNat, w:nat)
    requires WellformedBigNat(N);
    requires 0<w;
    requires I(N) < power2(32*(w-1));
    ensures |N.words| < w;
{
    if (|N.words|==0) {
        lemma_power2_0_is_1();
        lemma_power2_increases(0,w);
    } else {
        
        
        ghost var pv:=power2(32);
        lemma_2toX();
        var fn := Reverse(N.words);
        lemma_Reverse(N.words, fn);
        lemma_Reverse_preserves_IsDigitSeq(pv, N.words, fn);
        lemma_Reverse_converts_endianness_inner(Width(), fn, N.words);
        assert fn[0] == N.words[|N.words|-1];   //- OBSERVE SEQ
        assert 1 <= fn[0];

        if (w <= |N.words|)
        {
            calc {
                power2(32*(w-1));
                    { lemma_power2_unfolding(32, w-1);
                      lemma_mul_is_mul_boogie(32, w-1); }
                power(pv, w-1);
                <=  { lemma_power_increases(pv, w-1, |N.words|-1); }
                power(pv, |N.words|-1);
                power(pv, |fn|-1);
                    { lemma_mul_basics_forall(); }
                mul(1, power(pv, |fn|-1));
                <=  { lemma_power_positive(pv, |fn|-1);
                      lemma_mul_inequality(1, fn[0], power(pv, |fn|-1)); }
                fn[0] * power(pv, |fn|-1);
                <=  { lemma_BEDigitSeqToInt_bound(power2(32), fn); }
                BEDigitSeqToInt(Width(), fn);
                LEDigitSeqToInt(Width(), N.words);
                    { lemma_BigNatIIsLEDigitSeqToInt(N); }
                I(N);
                <
                power2(32*(w-1));   //- contradiction
            }
        }
    }
}

lemma lemma_keybits_implies_length25(N:BigNat)
    requires WellformedBigNat(N);
    requires I(N) < power2(power2(29));
    ensures |N.words| < power2(25);
{
    calc {
        power2(power2(29));
        <   { lemma_2toX32();
              lemma_power2_strictly_increases(power2(29), 32*(power2(25)-1)); }
        power2(32*(power2(25)-1));
    }
    lemma_keybits_implies_length(N, power2(25));
}

