include "OAEP.s.dfy"
include "../../Math/power.i.dfy"
include "../../Math/power2.i.dfy"
include "../../Math/round.i.dfy"
include "../../Math/bit_vector_lemmas_premium.i.dfy"
include "../../Util/integer_sequences_premium.i.dfy"

static function SHA256_BytesToBytes_premium(M:seq<int>) : seq<int>
    requires IsByteSeq(M);
    requires |M| < power2(61) || |BEByteSeqToBitSeq(M)| < power2(64);

    ensures IsBitSeq(BEByteSeqToBitSeq(M));
    ensures |BEByteSeqToBitSeq(M)| < power2(64);

    ensures SHA256_BytesToBytes_premium(M) == SHA256_BytesToBytes(M);
    ensures IsByteSeqOfLen(SHA256_BytesToBytes(M), hLen());
{
    calc {
        |M| < power2(61);
        ==> 8*|M| < 8*power2(61);
        ==> { lemma_2toX(); lemma_power2_add8(56); } 8*|M| < power2(64);
        ==> |BEByteSeqToBitSeq_premium(M)| < power2(64);
    }
    BEWordSeqToByteSeq_premium(SHA256(BEByteSeqToBitSeq_premium(M)))
}

static function ByteSeqXor_premium(X:seq<int>, Y:seq<int>) : seq<int>
    requires IsByteSeq(X);
    requires IsByteSeq(Y);
    requires |X| == |Y|;

    ensures |ByteSeqXor_premium(X, Y)| == |X|;
    ensures IsByteSeq(ByteSeqXor_premium(X, Y));
    ensures ByteSeqXor_premium(X, Y) == ByteSeqXor(X, Y);
{
    if X == [] || Y == [] then
        []
    else
        lemma_power2_strictly_increases(8, 32);
        lemma_2toX();
        lemma_xor_bytes_premium(X[0], Y[0]);
        [BitwiseXor(X[0], Y[0])] + ByteSeqXor_premium(X[1..], Y[1..])
}

static function I2OSP_premium(x:int, xLen:int) : seq<int>
    requires 0 <= xLen;
    requires 0 <= x < power(power2(8), xLen);

    ensures IsByteSeq(I2OSP_premium(x, xLen));
    ensures I2OSP_premium(x, xLen) == I2OSP(x, xLen);
    ensures |I2OSP_premium(x, xLen)| == xLen;
{
    lemma_2toX();
    BEIntToDigitSeq_premium(power2(8), xLen, x)
}

static function OS2IP_premium(X:seq<int>) : int
    requires IsByteSeq(X);

    ensures OS2IP_premium(X) == OS2IP(X);
    ensures 0 <= OS2IP_premium(X) < power(power2(8), |X|);
{
    lemma_2toX();
    BEDigitSeqToInt_premium(power2(8), X)
}

static predicate MGF1_step_requirements_simplified(seed:seq<int>, counter:nat)
    ensures MGF1_step_requirements_simplified(seed, counter) ==> MGF1_step_requirements(seed, counter);
{
    if Word32(counter) && IsByteSeq(seed) && |seed| < power2(60) then
        Lemma_MGF1_step_requirements_simplified_imply_MGF1_step_requirements(seed, counter);
        true
    else
        false
}

static lemma Lemma_MGF1_step_requirements_simplified_imply_MGF1_step_requirements(seed:seq<int>, counter:nat)
    requires IsByteSeq(seed);
    requires |seed| < power2(60);
    requires Word32(counter);
    ensures MGF1_step_requirements(seed, counter);
{
    calc {
        counter;
        < { lemma_power2_unfolding(8, 4); lemma_mul_is_mul_boogie(8, 4); } power(power2(8), 4);
    }
    assert IsByteSeq(I2OSP_premium(counter, 4));
    assert IsBitSeq(BEByteSeqToBitSeq_premium(seed + I2OSP_premium(counter, 4)));

    calc {
        |BEByteSeqToBitSeq_premium(seed + I2OSP_premium(counter, 4))|;
        |seed + I2OSP_premium(counter, 4)| * 8;
        == |seed| * 8 + |I2OSP_premium(counter, 4)| * 8;
        <= |seed| * 8 + 4 * 8;
        <= |seed| * 8 + 32;
        < power2(60) * 8 + 32;
        < { lemma_2toX(); } power2(64);
    }

    assert |BEByteSeqToBitSeq(seed + I2OSP_premium(counter, 4))| < power2(64);
}

static function MGF1_step_premium(seed:seq<int>, counter:nat) : seq<int>
    requires IsByteSeq(seed);
    requires |seed| < power2(60);
    requires Word32(counter);
    ensures MGF1_step_requirements(seed, counter);
    ensures MGF1_step_premium(seed, counter) == MGF1_step(seed, counter);
    ensures IsByteSeqOfLen(MGF1_step_premium(seed, counter), hLen());
{
    assert MGF1_step_requirements_simplified(seed, counter);
    var C := I2OSP_premium(counter, 4);
    SHA256_BytesToBytes_premium(seed + C)
}

static function MGF1_prefix_premium(seed:seq<int>, counter:nat) : seq<int>
    requires IsByteSeq(seed);
    requires |seed| < power2(60);
    requires Word32(counter);

    ensures forall j :: 0 <= j < counter ==> MGF1_step_requirements(seed, j);
    ensures MGF1_prefix_premium(seed, counter) == MGF1_prefix(seed, counter);
    ensures IsByteSeq(MGF1_prefix_premium(seed, counter));
    ensures |MGF1_prefix_premium(seed, counter)| == hLen() * counter;

    decreases counter;
{
    assert forall j :: 0 <= j < counter ==> MGF1_step_requirements_simplified(seed, j);
    if counter == 0 then
        calc {
            |[]|;
            32 * 0;
            { lemma_mul_is_mul_boogie(32, 0); }
            hLen() * counter;
        }
        []
    else
        calc {
            |MGF1_prefix_premium(seed, counter-1) + MGF1_step_premium(seed, counter-1)|;
            |MGF1_prefix_premium(seed, counter-1)| + |MGF1_step_premium(seed, counter-1)|;
            hLen() * (counter-1) + hLen();
            hLen() * (counter-1) + hLen() * 1;
            { lemma_mul_is_distributive_add(hLen(), counter-1, 1); lemma_mul_is_mul_boogie(hLen(), 1); }
            hLen() * (counter-1+1);
            hLen() * counter;
        }
        MGF1_prefix_premium(seed, counter-1) + MGF1_step_premium(seed, counter-1)
}

static function MGF1_premium(seed:seq<int>, maskLen:int) : seq<int>
    requires IsByteSeq(seed);
    requires |seed| < power2(60);
    requires Word32(maskLen);

    ensures 0 <= maskLen <= power2(32) * hLen();
    ensures var counter := DivideRoundingUp(maskLen, hLen());
            counter >= 0 &&
            (forall j :: 0 <= j < counter ==> MGF1_step_requirements(seed, j)) &&
            |MGF1_prefix(seed, counter)| >= maskLen;

    ensures MGF1_premium(seed, maskLen) == MGF1(seed, maskLen);
    ensures IsByteSeqOfLen(MGF1_premium(seed, maskLen), maskLen);
{
    calc {
        maskLen;
        < power2(32);
        == { lemma_2toX(); } 0x100000000;
        < 0x100000000 * 32;
        == { lemma_2toX(); } power2(32) * 32;
        == { lemma_mul_is_mul_boogie(power2(32), hLen()); } power2(32) * hLen();
    }

    var counter := DivideRoundingUp_premium(maskLen, hLen());
    lemma_mul_is_commutative(hLen(), counter);
    MGF1_prefix_premium(seed, counter)[..maskLen]
}

static function RSAEP_premium(pubkey:RSAPubKeySpec, m:int) : int
    requires WellformedRSAPubKeySpec(pubkey);
    requires 0 <= m < pubkey.n;

    ensures 0 <= RSAEP_premium(pubkey, m) < pubkey.n;
{
    lemma_mod_properties();
    power(m, pubkey.e) % pubkey.n
}

static function RSAES_OAEP_ENCRYPT_premium(pubkey:RSAPubKeySpec, M:seq<int>, L:seq<int>, seed:seq<int>) : seq<int>
    requires WellformedRSAPubKeySpec(pubkey);
    requires IsByteSeq(M);
    requires IsByteSeq(L);
    requires IsByteSeq(seed);
    requires |M| <= pubkey.size - 2 * hLen() - 2;
    requires |seed| == hLen();
    requires Word32(pubkey.size);

    requires Word32(pubkey.size);
    requires |L| < power2(61);

    ensures IsBitSeq(BEByteSeqToBitSeq(L)) &&
            |BEByteSeqToBitSeq(L)| < power2(64) &&
            var lHash := SHA256_BytesToBytes(L);
            var k := pubkey.size;
            var PS := RepeatDigit(0, k - |M| - 2*hLen() - 2);
            var DB := lHash + PS + [0x01] + M;
            IsByteSeq(DB) &&
            var maskLen := pubkey.size - hLen() - 1;
            var counter := DivideRoundingUp(maskLen, hLen());
            0 <= maskLen <= power2(32) * hLen() &&
            counter >= 0 &&
            (forall j :: 0 <= j < counter ==> MGF1_step_requirements(seed, j)) &&
            |MGF1_prefix(seed, counter)| >= maskLen &&
            var dbMask := MGF1(seed, k - hLen() - 1);
            IsByteSeq(DB) &&
            IsByteSeq(dbMask) &&
            var maskedDB := ByteSeqXor(DB, dbMask);
            var maskLen2 := hLen();
            var counter2 := DivideRoundingUp(maskLen2, hLen());
            0 <= maskLen2 <= power2(32) * hLen() &&
            counter2 >= 0 &&
            (forall j :: 0 <= j < counter2 ==> MGF1_step_requirements(maskedDB, j)) &&
            |MGF1_prefix(maskedDB, counter2)| >= maskLen2 &&
            var seedMask := MGF1(maskedDB, hLen());
            IsByteSeq(seedMask) &&
            var maskedSeed := ByteSeqXor(seed, seedMask);
            var EM := [0x00] + maskedSeed + maskedDB;
            IsByteSeq(EM) &&
            var m := OS2IP(EM);
            0 <= m < pubkey.n &&
            var c := RSAEP(pubkey, m);
            0 <= c < power(power2(8), pubkey.size);

    ensures RSAES_OAEP_ENCRYPT_premium(pubkey, M, L, seed) == RSAES_OAEP_ENCRYPT(pubkey, M, L, seed);
{
    calc {
        |BEByteSeqToBitSeq_premium(L)|;
        8*|L|;
        <   8*power2(61);
            { lemma_2toX(); lemma_power2_add8(56); }
        power2(64);
    }
    var lHash := SHA256_BytesToBytes_premium(L);
    var k := pubkey.size;
    var PS := RepeatDigit_premium(0, k - |M| - 2*hLen() - 2);
    var DB := lHash + PS + [0x01] + M;
    calc {
        0x01;
        < { lemma_2toX(); } power2(8);
    }
    assert IsByteSeq(DB);
    var maskLen := pubkey.size - hLen() - 1;
    var counter := DivideRoundingUp_premium(maskLen, hLen());
    calc {
        maskLen;
        < power2(32) - hLen() - 1;
        == power2(32) - 33;
        == { lemma_2toX(); } 0x100000000 - 33;
        < 0x100000000 * 32;
        == { lemma_2toX(); } power2(32) * 32;
        == { lemma_mul_is_mul_boogie(power2(32), hLen()); } power2(32) * hLen();
    }
    calc {
        |seed|;
        hLen();
        < { lemma_2toX(); } power2(60);
    }
    var dbMask := MGF1_premium(seed, k - hLen() - 1);
    assert IsByteSeq(DB);
    assert IsByteSeq(dbMask);
    var maskedDB := ByteSeqXor_premium(DB, dbMask);
    calc {
        |maskedDB|;
        k - hLen() - 1;
        < power2(32);
        < { lemma_power2_strictly_increases(32, 60); } power2(60);
    }
    var seedMask := MGF1_premium(maskedDB, hLen());
    assert IsByteSeq(seedMask);
    var maskedSeed := ByteSeqXor_premium(seed, seedMask);
    var EM := [0x00] + maskedSeed + maskedDB;
    assert IsByteSeq(EM);
    var m := OS2IP_premium(EM);
    calc {
        m;
        == { lemma_LeadingZeros(power2(8), EM[1..], EM); }
           OS2IP_premium(EM[1..]);
        < power(power2(8), |EM|-1);
        == power(power2(8), k-1);
        == { lemma_power2_unfolding(8, k-1); lemma_mul_is_mul_boogie(8, k-1); } power2(8*(k-1));
        <= pubkey.n;
    }
    var c := RSAEP_premium(pubkey, m);
    calc {
        c;
        < pubkey.n;
        <= power2(8*k);
        == { lemma_power2_unfolding(8, k); lemma_mul_is_mul_boogie(8, k); } power(power2(8), k);
    }

    RSAES_OAEP_ENCRYPT(pubkey, M, L, seed)
}
