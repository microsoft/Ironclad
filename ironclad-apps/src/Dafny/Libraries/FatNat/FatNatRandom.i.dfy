include "FatNatCompare.i.dfy"
include "Bitwise.i.dfy"
include "../Crypto/RandomNumberGen.s.dfy"
include "../../Drivers/TPM/tpm-wrapper.i.dfy"
//-include "../Math/round.i.dfy"
//-include "../Math/BitwiseOperations.i.dfy"
//-include "../../Drivers/TPM/tpm-wrapper.i.dfy"
//-include "../../Drivers/CPU/assembly_premium.i.dfy"

method BEWordSeqToFatNat(s:seq<int>) returns (F:array<int>)
    requires IsWordSeq(s);
    ensures fresh(F);
    ensures WellformedFatNat(F);
    ensures F[..] == s;
    ensures J(F) == BEWordSeqToInt(s);
{
    F := new int[|s|];

    var i:int := 0;
    while i < |s|
        invariant 0 <= i <= |s|;
        invariant IsWordSeq(F[..i]);
        invariant F[..i] == s[..i];
    {
        F[i] := s[i];
        assert F[..i+1] == F[..i] + [F[i]];
        assert s[..i+1] == s[..i] + [s[i]];
        i := i + 1;
    }

    calc {
        F[..];
        F[..i];
        s[..i];
        s;
    }
}

method MakeTopBitsZero(x:int, bits:int) returns (y:int)
    requires 0 <= bits < 32;
    requires Word32(x);
    ensures y == x % power2(32-bits);
    ensures Word32(y);
{
    if bits == 0 {
        y := x;
        lemma_small_mod(x, power2(32));
    }
    else {
        var two_to_bits := ComputePower2(32-bits);
        y := Asm_Mod(x, two_to_bits);
        lemma_mod_is_mod_boogie(x, power2(32-bits));
    }
}

lemma Lemma_ModMultiplies(a:int, b:int, m:int)
    requires a >= 0;
    requires b > 0;
    requires m > 0;
    ensures m * b != 0;
    ensures (a % m) * b == (a * b) % (m * b);
{
    calc {
        m * b;
        > { lemma_mul_strict_inequality(0, m, b); lemma_mul_is_mul_boogie(0, b); }
          0 * b;
        0;
    }

    calc {
        a * b;
        { lemma_mul_is_commutative(a, b); }
        b * a;
        { lemma_fundamental_div_mod(a, m); }
        b * (m * (a / m) + (a % m));
        { lemma_mul_is_distributive_add(b, m * (a / m), a % m); }
        b * (m * (a / m)) + b * (a % m);
        { lemma_mul_is_associative(b, m, a/m); }
        (b * m) * (a / m) + b * (a % m);
        { lemma_mul_is_commutative(a/m, b*m); }
        (a / m) * (b * m) + b * (a % m);
        { lemma_mul_is_commutative(b, m); }
        (a / m) * (m * b) + b * (a % m);
    }
    calc {
        b * (a % m);
        { lemma_mul_is_commutative(b, a % m); }
        (a % m) * b;
        <= { lemma_mod_pos_bound(a, m); lemma_mul_inequality(a % m, m-1, b); }
           (m - 1) * b;
        { lemma_mul_is_commutative(b, m-1); }
        b * (m - 1);
        { lemma_mul_is_distributive_sub(b, m, 1); lemma_mul_is_mul_boogie(b, 1); }
        b * m - b * 1;
        { lemma_mul_is_commutative(m, b); }
        m * b - b * 1;
        < m * b;
    }
    calc {
        (a * b) % (m * b);
        { lemma_mul_nonnegative(m, b);
          lemma_mod_pos_bound(a, m);
          lemma_mul_nonnegative(b, a % m);
          lemma_fundamental_div_mod_converse(a * b, m * b, a / m, b * (a % m)); }
        b * (a % m);
    }
    lemma_mul_is_commutative(b, a % m);
}

lemma Lemma_ExpressWordSeqInTermsOfTopWord(y:seq<int>)
    requires IsWordSeq(y);
    requires |y| > 0;
    ensures BEWordSeqToInt(y) == y[0] * power2(32*(|y|-1)) + BEWordSeqToInt(y[1..]);
{
    reveal_BEDigitSeqToInt_private();
    calc {
        BEWordSeqToInt([y[0]]);
        BEWordSeqToInt([y[0]][0..|[y[0]]|-1])*power2(32) + [y[0]][|[y[0]]|-1];
        BEWordSeqToInt([])*power2(32) + [y[0]][|[y[0]]|-1];
        BEWordSeqToInt([])*power2(32) + y[0];
        { lemma_mul_is_mul_boogie(0, power2(32)); }
        0*power2(32) + y[0];
        y[0];
    }
    calc {
        BEWordSeqToInt(y);
        { lemma_2to32(); lemma_BEInterpretation(power2(32), y, |y|-1); }
        BEWordSeqToInt(y[..1]) * power(power2(32), |y|-1) + BEWordSeqToInt(y[1..]);
        { assert y[..1] == [y[0]]; }
        BEWordSeqToInt([y[0]]) * power(power2(32), |y|-1) + BEWordSeqToInt(y[1..]);
        { assert BEWordSeqToInt([y[0]]) == y[0]; }
        y[0] * power(power2(32), |y|-1) + BEWordSeqToInt(y[1..]);
        { lemma_power2_unfolding(32, |y|-1); lemma_mul_is_mul_boogie(32, |y|-1); }
        y[0] * power2(32*(|y|-1)) + BEWordSeqToInt(y[1..]);
    }
}

lemma Lemma_MakingTopBitsZeroAffectsEntireSequence(x:seq<int>, y:seq<int>, bits:int)
    requires 0 <= bits < 32;
    requires |x| == |y|;
    requires |x| > 0;
    requires IsWordSeq(x);
    requires IsWordSeq(y);
    requires y[0] == x[0] % power2(32-bits);
    requires forall i :: 0 < i < |x| ==> y[i] == x[i];
    ensures BEWordSeqToInt(y) == BEWordSeqToInt(x) % power2(|x|*32-bits);
    decreases |x|;
{
    reveal_BEDigitSeqToInt_private();
    calc {
        BEWordSeqToInt(y);
        { Lemma_ExpressWordSeqInTermsOfTopWord(y); }
        y[0] * power2(32*(|y|-1)) + BEWordSeqToInt(y[1..]);
        { assert y[1..] == x[1..]; }
        y[0] * power2(32*(|x|-1)) + BEWordSeqToInt(x[1..]);
        (x[0] % power2(32-bits)) * power2(32*(|x|-1)) + BEWordSeqToInt(x[1..]);
    }
    calc {
        BEWordSeqToInt(x[1..]);
        < { lemma_BEDigitSeqToInt_bound(power2(32), x[1..]); }
          power(power2(32), |x|-1);
        { lemma_power2_unfolding(32, |x|-1); lemma_mul_is_mul_boogie(32, |x|-1); }
        power2(32 * (|x|-1));
    }
    calc {
        (x[0] % power2(32-bits)) * power2(32*(|x|-1)) + BEWordSeqToInt(x[1..]);
        < (x[0] % power2(32-bits)) * power2(32*(|x|-1)) + power2(32*(|x|-1));
        { lemma_mul_is_commutative(x[0] % power2(32-bits), power2(32*(|x|-1))); }
        power2(32*(|x|-1)) * (x[0] % power2(32-bits)) + power2(32*(|x|-1));
        power2(32*(|x|-1)) * (x[0] % power2(32-bits)) + power2(32*(|x|-1)) * 1;
        { lemma_mul_is_distributive_add(power2(32*(|x|-1)), x[0] % power2(32-bits), 1); lemma_mul_is_mul_boogie(power2(32*(|x|-1)), 1); }
        power2(32*(|x|-1)) * (x[0] % power2(32-bits) + 1);
        { lemma_mul_is_commutative(power2(32*(|x|-1)), x[0] % power2(32-bits) + 1); }
        (x[0] % power2(32-bits) + 1) * power2(32*(|x|-1));
        <= { lemma_mod_properties(); lemma_mul_inequality(x[0] % power2(32-bits) + 1, power2(32-bits), power2(32*(|x|-1))); }
        power2(32-bits) * power2(32*(|x|-1));
        { lemma_power2_adds(32-bits, 32*(|x|-1)); }
        power2(32 - bits + 32*(|x|-1));
        { lemma_mul_is_mul_boogie(32, |x|-1); lemma_mul_is_distributive_sub(32, |x|, 1); lemma_mul_is_mul_boogie(32, 1); }
        power2(32 - bits + 32*|x| - 32*1);
        power2(32*|x| - bits);
    }
    calc {
        (x[0] % power2(32-bits)) * power2(32*(|x|-1)) + BEWordSeqToInt(x[1..]);
        { Lemma_ModMultiplies(x[0], power2(32*(|x|-1)), power2(32-bits)); }
        (x[0] * power2(32*(|x|-1))) % (power2(32-bits)*power2(32*(|x|-1))) + BEWordSeqToInt(x[1..]);
        { lemma_power2_adds(32-bits, 32*(|x|-1)); }
        (x[0] * power2(32*(|x|-1))) % power2(32-bits + 32*(|x|-1)) + BEWordSeqToInt(x[1..]);
        { lemma_mul_is_mul_boogie(32, |x|-1); lemma_mul_is_distributive_sub(32, |x|, 1); lemma_mul_is_mul_boogie(32, 1); }
        (x[0] * power2(32*(|x|-1))) % power2(32-bits + 32*|x|-32*1) + BEWordSeqToInt(x[1..]);
        (x[0] * power2(32*(|x|-1))) % power2(32*|x|-bits) + BEWordSeqToInt(x[1..]);
        calc {
            BEWordSeqToInt(x[1..]);
            < { lemma_BEDigitSeqToInt_bound(power2(32), x[1..]); }
              power(power2(32), |x|-1);
            { lemma_power2_unfolding(32, |x|-1); lemma_mul_is_mul_boogie(32, |x|-1); }
            power2(32 * (|x|-1));
            { lemma_mul_is_distributive_sub(32, |x|, 1); lemma_mul_is_mul_boogie(32, |x|-1); lemma_mul_is_mul_boogie(32, |x|); lemma_mul_is_mul_boogie(32, 1); }
            power2(32 * |x| - 32 * 1);
            power2(32 * |x| - 32);
            <= { lemma_power2_increases(32 * |x| - 32, 32 * |x| - bits); } power2(32 * |x| - bits);
        }
        { lemma_small_mod(BEWordSeqToInt_premium(x[1..]), power2(32 * |x| - bits)); }
        (x[0] * power2(32*(|x|-1))) % power2(32*|x|-bits) + BEWordSeqToInt(x[1..]) % power2(32*|x|-bits);
    }
    calc {
        (x[0] * power2(32*(|x|-1))) % power2(32*|x|-bits) + BEWordSeqToInt(x[1..]) % power2(32*|x|-bits);
        { assert (x[0] * power2(32*(|x|-1))) % power2(32*|x|-bits) + BEWordSeqToInt(x[1..]) % power2(32*|x|-bits) == BEWordSeqToInt_premium(y); }
        { lemma_small_mod((x[0] * power2(32*(|x|-1))) % power2(32*|x|-bits) + BEWordSeqToInt(x[1..]) % power2(32*|x|-bits), power2(32*|x|-bits)); }
        ((x[0] * power2(32*(|x|-1))) % power2(32*|x|-bits) + BEWordSeqToInt(x[1..]) % power2(32*|x|-bits)) % power2(32*|x|-bits);
        { lemma_add_mod_noop(x[0] * power2(32*(|x|-1)), BEWordSeqToInt(x[1..]), power2(32*|x|-bits)); }
        (x[0] * power2(32*(|x|-1)) + BEWordSeqToInt(x[1..])) % power2(32*|x|-bits);
        { Lemma_ExpressWordSeqInTermsOfTopWord(x); }
        BEWordSeqToInt(x) % power2(32*|x|-bits);
    }
}

method FatNatRandomPower2(c:nat) returns (R:array<int>, ghost randoms:seq<int>)
    requires TPM_ready();
    ensures fresh(R);
    ensures R != null;
    ensures WellformedFatNat(R);
    ensures IsByteSeqOfLen(randoms, DivideRoundingUp(c, 8));
    ensures J(R) == BEByteSeqToInt(randoms) % power2(c);
    ensures J(R) < power2(c);
    ensures TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures TPMs_match_except_for_randoms(old(TPM), TPM);
    ensures old(TPM).random_index <= TPM.random_index;
    ensures randoms == TPM_random_bytes_premium(old(TPM).random_index, TPM.random_index);
{
    lemma_2to32();
    var byte_count := DivideRoundingUp_premium(c, 8);

    var byte_seq := get_random(byte_count);
    randoms := byte_seq;
    assert |randoms| == byte_count == DivideRoundingUp(c, 8);
    var word_seq,padding := BEByteSeqToWordSeq_impl(byte_seq);
    assert |word_seq| == (|byte_seq|+3)/4;
//-    var trim_seq := TrimLeadingZeros(4294967296, word_seq);

    R := BEWordSeqToFatNat(word_seq);
    assert WellformedFatNat(R);
    assert J(R) == BEWordSeqToInt(word_seq) == BEByteSeqToInt(randoms);

    calc {
        byte_count*8;
        >= { lemma_mul_is_mul_boogie(byte_count, 8); } c;
    }

    if byte_count > 0 {
        calc {
            |word_seq| * 32 - c;
            (byte_count+3)/4 * 32 - c;
            (DivideRoundingUp_premium(c, 8)+3)/4 * 32 - c;
            ((c + 7)/8 +3)/4 * 32 - c;
            ((c + 7)/8 + 24 / 8)/4 * 32 - c;
            ((c + 31)/8)/4 * 32 - c;
            (c + 31)/32 * 32 - c;
            DivideRoundingUp_premium(c, 32) * 32 - c;
            < { lemma_mul_is_commutative(DivideRoundingUp_premium(c, 32), 32); }
              c + 32 - c;
            32;
        }
        R[0] := MakeTopBitsZero(R[0], |word_seq| * 32 - c);
        Lemma_MakingTopBitsZeroAffectsEntireSequence(word_seq, R[..], |word_seq| * 32 - c);
        calc {
            J(R);
            BEWordSeqToInt(word_seq) % power2(|word_seq|*32-(|word_seq|*32-c));
            BEWordSeqToInt(word_seq) % power2(c);
        }
        assert J(R) == BEByteSeqToInt(randoms) % power2(c);
    }
    else {
        calc {
            J(R);
            BEWordSeqToInt([]);
            { reveal_BEDigitSeqToInt_private(); }
            0;
        }
        calc {
            BEByteSeqToInt(randoms) % power2(c);
            < { lemma_mod_properties(); } power2(c);
            { reveal_power2(); }
            1;
        }
    }

    lemma_mod_properties();
    assert J(R) < power2(c);
}
//-
static predicate CandidateSeedWorksheetValid_incremental(req:SelectRandomRequest, worksheet:CandidateSeedWorksheet, last_succeeds:bool)
{
    (forall i :: 0<=i<|worksheet.rows| ==> CandidateSeedWorksheetRowValid(req, worksheet.rows[i]))
    //- all but last row fail
    && (forall i:int :: 0<=i<|worksheet.rows|-1 ==> !worksheet.rows[i].accepted)
    //- last as specified
    && (|worksheet.rows|>0 ==> worksheet.rows[|worksheet.rows|-1].accepted == last_succeeds)
    //- randoms properly accounted for
    && CandidateSeedWorksheetConsumesRandoms(worksheet.rows) == worksheet.randoms
}

method FatNatRandomFromInclusiveRange(L:array<int>, H:array<int>, ghost req:SelectRandomRequest) returns (R:array<int>, ghost worksheet:CandidateSeedWorksheet)
    requires WellformedFatNat(L);
    requires WellformedFatNat(H);
    requires J(L) <= J(H);
    requires req.l == J(L);
    requires req.h == J(H);
    requires SelectRandomRequestValid(req);
    requires TPM_ready();
    ensures TPM_ready();
    ensures WellformedFatNat(R);
    ensures J(L) <= J(R) <= J(H);
    ensures CandidateSeedWorksheetValid(req, worksheet);
    ensures J(R) == CandidateSeedWorksheetOutput(worksheet);
    modifies this`TPM;   
    modifies this`IoMemPerm;
    ensures TPMs_match_except_for_randoms(old(TPM), TPM);
    ensures old(TPM).random_index <= TPM.random_index;
    ensures worksheet.randoms == TPM_random_bytes_premium(old(TPM).random_index, TPM.random_index);
{
    var c:nat := FatNatCountBits(H);

    lemma_bit_count_is_unique(J(H), c, req.h_bits);

    var lobound:bool := false;
    var hibound:bool := false;

    ghost var randoms;
    worksheet := CandidateSeedWorksheet_c([], []);

    ghost var started := false;
    R := new int[0]; //- dafnycc requires us to initialize this variable, and doesn't support initializing it to null.
    var accepted := false;
    while (!accepted)
        decreases *;    //- Possibly doesn't terminate.
        invariant started ==> WellformedFatNat(R);
        invariant started ==> lobound == (J(L)<=J(R));
        invariant started ==> hibound == (J(R)<=J(H));
        invariant started ==> 0<|worksheet.rows|;
        invariant accepted ==> started;
        invariant CandidateSeedWorksheetValid_incremental(req, worksheet, accepted);
        invariant accepted ==> CandidateSeedWorksheetOutput(worksheet) == J(R);
        invariant TPM_ready();
        invariant TPMs_match_except_for_randoms(old(TPM), TPM);
        invariant old(TPM).random_index <= TPM.random_index;
        invariant worksheet.randoms == TPM_random_bytes_premium(old(TPM).random_index, TPM.random_index);
        invariant TPM.random_index - old(TPM).random_index == |worksheet.randoms|;
    {
        R, randoms := FatNatRandomPower2(c);
        lobound := FatNatLe(L, R);
        hibound := FatNatLe(R, H);
        started := true;
        accepted := lobound && hibound;

        ghost var row := CandidateSeedWorksheetRow_c(J(R), accepted, randoms);
        ghost var worksheet' := CandidateSeedWorksheet_c(
            worksheet.rows + [row],
            worksheet.randoms + randoms);
        lemma_random_comprehension(old(TPM).random_index, worksheet.randoms, randoms);

        worksheet := worksheet';
    }
}
