//-<NuBuild BasmEnableSymdiff true />
//- <NuBuild AddDafnyFlag /z3opt:NL_ARITH=true/>
//- <NuBuild AddDafnyFlag /z3opt:ARITH_RANDOM_SEED=1 />
include "Noise.s.dfy"
include "../../Libraries/BigNum/BigRat.i.dfy"
include "../../Libraries/Math/round.i.dfy"
include "../../Libraries/Util/arrays_and_seqs.i.dfy"
include "../../Libraries/Util/seqs_and_ints.i.dfy"
include "../../Libraries/BigNum/BigNumBEAdaptor.i.dfy"
include "ErrorCodes.i.dfy"

datatype DiffPrivParametersImpl = DiffPrivParametersImpl_ctor(alpha:BigRat, beta:BigRat, delta:int, B:int);

static function WellformedDiffPrivParameters (p:DiffPrivParametersImpl) : bool
{
    WellformedBigRat(p.alpha) && WellformedBigRat(p.beta) && Word32(p.delta) && Word32(p.B)
}

static function DiffPrivParametersImplToSpec (p:DiffPrivParametersImpl) : DiffPrivParameters
    requires WellformedDiffPrivParameters(p);
{
    DiffPrivParameters_ctor(RV(p.alpha), RV(p.beta), p.delta, p.B)
}

method BigRatPower(x:BigRat, e:int) returns (r:BigRat)
    requires WellformedBigRat(x);
    requires e >= 0;
    ensures WellformedBigRat(r);
    ensures RV(r) == RealPower(RV(x), e);
{
    r := MakeSmallLiteralBigRat(1);

    var k := 0;
    while k < e
        invariant 0 <= k <= e;
        invariant WellformedBigRat(r);
        invariant RV(r) == RealPower(RV(x), k);
    {
        r := BigRatMul(r, x);
        k := k + 1;
    }
}

method BigRatMin (a:BigRat, b:BigRat) returns (r:BigRat)
    requires WellformedBigRat(a);
    requires WellformedBigRat(b);
    ensures WellformedBigRat(r);
    ensures RV(r) == RealMin(RV(a), RV(b));
{
    var a_less_than_b:bool := BigRatLt(a, b);
    if (a_less_than_b) {
        r := a;
    }
    else {
        r := b;
    }
}

method {:timeLimitMultiplier 2} FindHigherPowerOfTwo (y:BigRat) returns (success:bool, x:nat)
    requires WellformedBigRat(y);
    ensures Word32(x);
    ensures success ==> real(power2(x)) >= RV(y);

    requires public(RV(y));
    ensures public(success);
    ensures public(x);
{
    lemma_2toX();
    reveal_power2();

    x := 0;
    var two_to_x:BigNat := MakeSmallLiteralBigNat(1);
    var two:BigNat := MakeSmallLiteralBigNat(2);

    while x < 0xFFFFFFFF
        invariant Word32(x);
        invariant WellformedBigNat(two_to_x);
        invariant I(two_to_x) == power2(x);
        invariant public(RV(y));
        invariant public(x);
        invariant public(I(two_to_x));
        invariant public(I(two));
    {
        var done:bool := BigRatGe(BigNatToBigRat(two_to_x), y);
        if (done) {
            success := true;
            return;
        }
        ghost var old_two_to_x := two_to_x;
        two_to_x := BigNatMul(two, two_to_x);
        calc {
            I(two_to_x);
            I(two) * I(old_two_to_x);
            I(two) * power2(x);
            { lemma_mul_is_mul_boogie(I(two), power2(x)); }
            2 * power2(x);
            power2(x+1);
        }
        x := x + 1;
    }

    //- At the end of the loop, handle the case of x == 0xFFFFFFFF.

    success := BigRatGe(BigNatToBigRat(two_to_x), y);
}

method DetermineIfDiffPrivParametersValid (p:DiffPrivParametersImpl) returns (error_code:int)
    requires WellformedDiffPrivParameters(p);
    requires p.delta >= 0;
    ensures Word32(error_code);
    ensures error_code == 0 <==> DiffPrivParametersValid(DiffPrivParametersImplToSpec(p));

    requires public(p);
    ensures public(error_code);
{
    lemma_2toX();

    if p.B <= 0 {
        error_code := ErrorAnswerRangeNotPositive();
        return;
    }

    var One := MakeSmallLiteralBigRat(1);
    var AlphaLeOne:bool := BigRatLe(p.alpha, One);
    if (AlphaLeOne) {
        error_code := ErrorAlphaNotGreaterThanOne();
        return;
    }

    var AlphaToDelta := BigRatPower(p.alpha, p.delta);
    var BetaLeAlphaToDelta := BigRatLe(p.beta, AlphaToDelta);
    if (BetaLeAlphaToDelta) {
        error_code := ErrorBetaNotGreaterThanAlphaToPowerOfSensitivity();
        return;
    }

    Lemma_RealPowerPreservesGeOne(RV(p.alpha), p.delta);
    error_code := 0;
}

method {:timeLimitMultiplier 6} ComputeRequiredNoiseEntropyPart1 (p:DiffPrivParametersImpl) returns (entropy:BigRat)
    requires WellformedDiffPrivParameters(p);
    requires DiffPrivParametersValid(DiffPrivParametersImplToSpec(p));
    ensures WellformedBigRat(entropy);
    ensures RV(entropy) == RequiredNoiseEntropyPart1(DiffPrivParametersImplToSpec(p));
    ensures RV(entropy) > 0.0;
{
    lemma_2toX();
    var One := MakeSmallLiteralBigRat(1);
    var Two := MakeSmallLiteralBigRat(2);
    var AlphaPlusOne := BigRatAdd(p.alpha, One);
    var BetaPlusOne := BigRatAdd(p.beta, One);
    var AlphaToDelta := BigRatPower(p.alpha, p.delta);
    var BetaMinusAlphaToDelta := BigRatSub(p.beta, AlphaToDelta);
    var Numerator := BigRatMul(AlphaPlusOne, BetaPlusOne);
    var AlphaMinusOne := BigRatSub(p.alpha, One);
    var MinAlphaMinusOneAndTwo := BigRatMin(AlphaMinusOne, Two);
    var Denominator := BigRatMul(BetaMinusAlphaToDelta, MinAlphaMinusOneAndTwo);
    entropy := BigRatDiv(Numerator, Denominator);

    Lemma_RequiredNoiseEntropyPart1Correct(DiffPrivParametersImplToSpec(p), RV(AlphaPlusOne), RV(BetaPlusOne),
                                           RV(One), RV(Two), RV(AlphaToDelta), RV(BetaMinusAlphaToDelta),
                                           RV(Numerator), RV(AlphaMinusOne), RV(MinAlphaMinusOneAndTwo), RV(Denominator), RV(entropy));
}

method ComputeBytesForNoiseGeneration (p:DiffPrivParametersImpl) returns (error_code:int, bytes:nat)
    requires WellformedDiffPrivParameters(p);
    requires DiffPrivParametersValid(DiffPrivParametersImplToSpec(p));
    ensures Word32(error_code);
    ensures error_code == 0 ==> Word32((bytes-1)*8+1);
    ensures error_code == 0 ==> SufficientBytesForNoiseGeneration(DiffPrivParametersImplToSpec(p), bytes);
    ensures error_code != 0 ==> bytes == 0;

    requires public(p);
    ensures public(error_code);
    ensures public(bytes);
{
    lemma_2toX();
    reveal_power2();

    var entropy_part_1 := ComputeRequiredNoiseEntropyPart1(p);
    var success, r1 := FindHigherPowerOfTwo(entropy_part_1);
    if !success || r1 >= 0xFFFFFFE0 {
        error_code := ErrorRequiresTooManyBitsOfRandomness();
        bytes := 0;
        return;
   }

    var log_alpha:nat;
    success, log_alpha := FindHigherPowerOfTwo(p.alpha);
    if !success || log_alpha > 0xFFFFFFFF / p.B {
        error_code := ErrorRequiresTooManyBitsOfRandomness();
        bytes := 0;
        return;
    }
    lemma_mul_nonnegative(log_alpha, p.B-1);
    var r2:nat := log_alpha * (p.B-1);
    Lemma_SufficientR2(RV(p.alpha), p.B, log_alpha, r2);

    if r2 >= 0xFFFFFFC8 - r1 {
        error_code := ErrorRequiresTooManyBitsOfRandomness();
        bytes := 0;
        return;
    }

    error_code := 0;
    var min_r := r1 + r2 + 7;      //- need 7 extra bits so we can use an entire byte for the sign bit
    bytes := TurnSufficientBitsIntoSufficientBytes(min_r);
    Lemma_RealPowerPreservesPositivity(RV(p.alpha), p.B-1);
    Lemma_BreakdownOfSufficientBytesForNoiseGeneration(DiffPrivParametersImplToSpec(p), r1, r2, bytes);
}

static method TurnSufficientBitsIntoSufficientBytes (min_r:nat) returns (bytes:int)
    requires min_r < 0xFFFFFFD0;
    ensures Word32((bytes-1)*8+1);
    ensures bytes >= 1;
    ensures ModuloFour(bytes) == 1;
    ensures bytes * 8 >= min_r;

    requires public(min_r);
    ensures public(bytes);
{
    reveal_ModuloFour();

    var r:int := RoundUpToMultiple(min_r, 8);
    assert r == RoundUpToMultiple_premium(min_r, 8);
    lemma_mod_is_mod_boogie(r, 8);
    var bytes1:int := r / 8;
    var bytes2:int := RoundUpToMultiple(bytes1, 4);
    assert bytes2 == RoundUpToMultiple_premium(bytes1, 4);
    lemma_mod_is_mod_boogie(bytes2, 4);
    bytes := bytes2 + 1;
    lemma_mod_is_mod_boogie(bytes2, 4);

    calc {
        (bytes-1)*8 + 1;
        bytes2 * 8 + 1;
        < (bytes1 + 4) * 8 + 1;
        bytes1 * 8 + 33;
        (r / 8) * 8 + 33;
        <= ((min_r + 8) / 8) * 8 + 33;
        < ((0xFFFFFFD0 + 8) / 8) * 8 + 33;
        < 0xFFFFFFFF;
        < { lemma_2toX(); reveal_power2(); }
          power2(32);
    }
}

method BigNatPower2 (e:nat) returns (r:BigNat)
    requires Word32(e+1);
    ensures WellformedBigNat(r);
    ensures I(r) == power2(e);
{
    lemma_2toX();
    reveal_power2();
    var One := MakeSmallLiteralBigNat(1);
    ghost var rc:nat;
    r, rc := BigNatBitShift_(One, 1, e);
    lemma_mul_is_mul_boogie(power2(e), I(One));
}

method FindHighestPowerLeThreshold (alpha:BigRat, threshold:BigRat, max_power:nat, ghost u:BigRat) returns (e:nat)
    requires WellformedBigRat(alpha);
    requires WellformedBigRat(threshold);
    requires Word32(max_power);
    requires WellformedBigRat(u);
    requires RV(u) > 0.0;
    requires RV(alpha) > 1.0;
    requires RV(threshold) >= 1.0;
    requires RV(threshold) == NoiseThreshold(RV(alpha), RV(u));
    ensures RealPower(RV(alpha), e) <= RV(threshold);
    ensures e == max_power || RealPower(RV(alpha), e+1) > RV(threshold);
    ensures Word32(e);
    ensures RV(threshold) == NoiseThreshold(RV(alpha), RV(u));
{
    var alpha_to_e := MakeSmallLiteralBigRat(1);
    e := 0;

    while e < max_power
        invariant 0 <= e <= max_power;
        invariant WellformedBigRat(alpha_to_e);
        invariant RV(alpha_to_e) == RealPower(RV(alpha), e);
        invariant RV(alpha_to_e) <= RV(threshold);
    {
        alpha_to_e := BigRatMul(alpha, alpha_to_e);
        var done := BigRatGt(alpha_to_e, threshold);
        if (done) {
            assert RealPower(RV(alpha), e+1) == RV(alpha_to_e) > RV(threshold);
            return;
        }
        e := e + 1;
    }
}

method {:timeLimitMultiplier 6} DeriveRandomValues (randoms:seq<int>) returns (negate_noise:bool, u:BigRat)
    requires |randoms| > 0;
    requires Word32((|randoms|-1) * 8 + 1);
    requires IsByteSeq(randoms);
    ensures WellformedBigRat(u);
    ensures negate_noise == ShouldNegateNoise(randoms[0]);
    ensures RV(u) == GetUniformBetweenZeroAndOne(randoms[1..]);
    ensures 0.0 < RV(u) <= 1.0;
{
    reveal_ShouldNegateNoise();

    negate_noise := (randoms[0] % 2 == 1);

    lemma_2toX();
    var U:BigNat := BEByteSeqToBigNat(randoms[1..]);
    assert I(U) == BEByteSeqToInt(randoms[1..]);
    var OneHalf:BigRat := BigRat_ctor(MakeSmallLiteralBigNum(1), MakeSmallLiteralBigNat(2));
    var Numerator:BigRat := BigRatAdd(BigNatToBigRat(U), OneHalf);
    var Denominator:BigNat := BigNatPower2((|randoms|-1)*8);
    u := BigRatDiv(Numerator, BigNatToBigRat(Denominator));
    assert WellformedBigRat(u);

    Lemma_RandomDerivationsCorrect(randoms, RV(u), negate_noise, I(U), RV(OneHalf), RV(Numerator), I(Denominator));
}

method ComputeNoiseThreshold (alpha:BigRat, u:BigRat) returns (Threshold:BigRat)
    requires WellformedBigRat(alpha);
    requires WellformedBigRat(u);
    requires RV(alpha) > 1.0;
    requires 0.0 < RV(u) <= 1.0;
    ensures WellformedBigRat(Threshold);
    ensures RV(Threshold) == NoiseThreshold(RV(alpha), RV(u));
    ensures RV(Threshold) >= 1.0;
{
    lemma_2toX();

    var ThresholdNumerator := BigRatMul(MakeSmallLiteralBigRat(2), alpha);
    var AlphaPlusOne := BigRatAdd(alpha, MakeSmallLiteralBigRat(1));
    var ThresholdDenominator := BigRatMul(u, AlphaPlusOne);

    Threshold := BigRatDiv(ThresholdNumerator, ThresholdDenominator);
    Lemma_ThresholdCorrect(RV(alpha), RV(u), RV(ThresholdNumerator), RV(AlphaPlusOne), RV(ThresholdDenominator), RV(Threshold));
    Lemma_ThresholdGeOne(RV(alpha), RV(u), RV(Threshold));
}

method {:timeLimitMultiplier 6} ComputeNoise (p:DiffPrivParametersImpl, randoms:seq<int>)
                                                    returns (negate_noise:bool, absolute_noise:int, ghost noise:int)
    requires WellformedDiffPrivParameters(p);
    requires IsByteSeq(randoms);
    requires DiffPrivParametersValid(DiffPrivParametersImplToSpec(p));
    requires |randoms| > 0;
    requires Word32((|randoms|-1)*8+1);
    requires SufficientBytesForNoiseGeneration(DiffPrivParametersImplToSpec(p), |randoms|);
    ensures Word32(absolute_noise);
    ensures noise == if negate_noise then -absolute_noise else absolute_noise;
    ensures NoiseComputedCorrectly(DiffPrivParametersImplToSpec(p), randoms, noise);
{
    var u:BigRat;
    negate_noise, u := DeriveRandomValues(randoms);
    assert RV(u) == GetUniformBetweenZeroAndOne(randoms[1..]);
    var Threshold := ComputeNoiseThreshold(p.alpha, u);
    absolute_noise := FindHighestPowerLeThreshold(p.alpha, Threshold, p.B, u);
    assert RV(Threshold) == NoiseThreshold(RV(p.alpha), RV(u));
    noise := if negate_noise then -absolute_noise else absolute_noise;

    Lemma_NoiseComputedCorrectlyFromRandomValues(DiffPrivParametersImplToSpec(p), randoms, RV(u), negate_noise, absolute_noise, noise);
}

static lemma {:timeLimitMultiplier 3}
             Lemma_RequiredNoiseEntropyPart1Correct (p:DiffPrivParameters, AlphaPlusOne:real, BetaPlusOne:real,
                                                     One:real, Two:real, AlphaToDelta:real, BetaMinusAlphaToDelta:real,
                                                     Numerator:real, AlphaMinusOne:real, MinAlphaMinusOneAndTwo:real, Denominator:real,
                                                     entropy:real)
    requires Word32(p.delta);
    requires Word32(p.B);
    requires DiffPrivParametersValid(p);
    requires One == 1.0;
    requires Two == 2.0;
    requires AlphaPlusOne == p.alpha + One;
    requires BetaPlusOne == p.beta + One;
    requires AlphaToDelta == RealPower(p.alpha, p.delta);
    requires BetaMinusAlphaToDelta == p.beta - AlphaToDelta;
    requires Numerator == AlphaPlusOne * BetaPlusOne;
    requires AlphaMinusOne == p.alpha - One;
    requires MinAlphaMinusOneAndTwo == RealMin(AlphaMinusOne, Two);
    requires Denominator == BetaMinusAlphaToDelta * MinAlphaMinusOneAndTwo;
    requires Denominator != 0.0;
    requires entropy == Numerator / Denominator;
    ensures entropy == RequiredNoiseEntropyPart1(p);
{
    calc {
        entropy;
        Numerator / Denominator;
        (AlphaPlusOne * BetaPlusOne) / Denominator;
        ((p.alpha + One) * BetaPlusOne) / Denominator;
        ((p.alpha + One) * (p.beta + One)) / Denominator;
        ((p.alpha + One) * (p.beta + One)) / (BetaMinusAlphaToDelta * MinAlphaMinusOneAndTwo);
        ((p.alpha + One) * (p.beta + One)) / ((p.beta - AlphaToDelta) * MinAlphaMinusOneAndTwo);
        ((p.alpha + One) * (p.beta + One)) / ((p.beta - RealPower(p.alpha, p.delta)) * MinAlphaMinusOneAndTwo);
        ((p.alpha + One) * (p.beta + One)) / ((p.beta - RealPower(p.alpha, p.delta)) * RealMin(AlphaMinusOne, Two));
        ((p.alpha + One) * (p.beta + One)) / ((p.beta - RealPower(p.alpha, p.delta)) * RealMin(p.alpha - One, Two));
    }
}

static lemma Lemma_RealPowerPreservesGeOne (x:real, e:nat)
    requires x >= 1.0;
    ensures RealPower(x, e) >= 1.0;
    decreases e;
{
    if e != 0 {
        Lemma_RealPowerPreservesGeOne(x, e-1);
    }
}

static lemma Lemma_DividingByPositiveMaintainsInequality(smaller:real, larger:real, denominator:real)
    requires denominator > 0.0;
    requires smaller <= larger;
    ensures smaller / denominator <= larger / denominator;
{
}

static lemma Lemma_RandomDerivationsCorrect (randoms:seq<int>, u:real, negate_noise:bool, U:nat, OneHalf:real, Numerator:real, Denominator:nat)
    requires |randoms| > 0;
    requires IsByteSeq(randoms);
    requires negate_noise == (randoms[0] % 2 == 1);
    requires U == BEByteSeqToInt(randoms[1..]);
    requires OneHalf == 0.5;
    requires Numerator == real(U) + OneHalf;
    requires Denominator == power2((|randoms|-1)*8);
    requires u == Numerator / real(Denominator);
    ensures u == GetUniformBetweenZeroAndOne(randoms[1..]);
    ensures 0.0 < u <= 1.0;
    decreases U;
{
    calc {
        Denominator;
        power2((|randoms|-1)*8);
        >= { lemma_power2_increases(0, (|randoms|-1)*8); } power2(0);
        == { reveal_power2(); } 1;
    }
    calc {
        real(Denominator);
        >= real(1);
        > 0.0;
    }
    calc ==> {
        true;
        { lemma_BEByteSeqToInt_bound(randoms[1..]); }
        U <= power2((|randoms|-1)*8) - 1;
        real(U) <= real(power2((|randoms|-1)*8) - 1);
        real(U) + OneHalf <= real(power2((|randoms|-1)*8) - 1) + OneHalf;
        { Lemma_DividingByPositiveMaintainsInequality(real(U) + OneHalf, real(power2((|randoms|-1)*8) - 1) + OneHalf, real(Denominator)); }
        (real(U) + OneHalf) / real(Denominator) <= (real(power2((|randoms|-1)*8) - 1) + OneHalf) / real(Denominator);
    }
    calc {
        u;
        Numerator / real(Denominator);
        (real(U) + OneHalf) / real(Denominator);
        <=
        (real(power2((|randoms|-1)*8) - 1) + OneHalf) / real(Denominator);
        (real(power2((|randoms|-1)*8) - 1) + 0.5) / real(Denominator);
        (real(power2((|randoms|-1)*8) - 1) + 0.5) / real(power2((|randoms|-1)*8));
        < real(power2((|randoms|-1)*8)) / real(power2((|randoms|-1)*8));
        1.0;
    }
}

static lemma Lemma_ThresholdCorrect (alpha:real, u:real, ThresholdNumerator:real, AlphaPlusOne:real, ThresholdDenominator:real, Threshold:real)
    requires u > 0.0;
    requires alpha > 1.0;
    requires ThresholdNumerator == 2.0 * alpha;
    requires AlphaPlusOne == alpha + 1.0;
    requires ThresholdDenominator == u * AlphaPlusOne;
    requires Threshold == ThresholdNumerator / ThresholdDenominator;
    ensures Threshold == NoiseThreshold(alpha, u);
{
}

static lemma Lemma_NoiseComputedCorrectlyFromRandomValues (p:DiffPrivParameters, randoms:seq<int>,
                                                    u:real, negate_noise:bool, absolute_noise:nat, ghost noise:int)
    requires DiffPrivParametersValid(p);
    requires p.alpha > 1.0;
    requires u > 0.0;
    requires IsByteSeq(randoms);
    requires |randoms| > 0;
    requires SufficientBytesForNoiseGeneration(p, |randoms|);
    requires negate_noise == ShouldNegateNoise(randoms[0]);
    requires u == GetUniformBetweenZeroAndOne(randoms[1..]);
    requires RealPower(p.alpha, absolute_noise) <= NoiseThreshold(p.alpha, u);
    requires (absolute_noise == p.B || RealPower(p.alpha, absolute_noise + 1) > NoiseThreshold(p.alpha, u));
    requires noise == if negate_noise then -absolute_noise else absolute_noise;
    ensures NoiseComputedCorrectly(p, randoms, noise);
{
    assert AbsoluteNoiseComputedCorrectlyTrigger(absolute_noise);
    assert NoiseOK(p, negate_noise, u, absolute_noise, noise);
}

static lemma Lemma_ThresholdGeOne (alpha:real, u:real, threshold:real)
    requires 1.0 >= u > 0.0;
    requires alpha > 1.0;
    requires threshold == NoiseThreshold(alpha, u);
    ensures threshold >= 1.0;
{
    calc {
        threshold;
        (2.0 * alpha) / (u * (alpha + 1.0));
        (alpha + alpha) / (u * (alpha + 1.0));
        (alpha + alpha) / (u * (alpha + 1.0));
        (alpha + alpha) / (alpha + 1.0) / u;
        >= 1.0 / u;
        >= 1.0;
    }
}

static function RequiredNoiseEntropyPart1 (p:DiffPrivParameters) : real
    requires DiffPrivParametersValid(p);
    ensures RequiredNoiseEntropyPart1(p) > 0.0;
{
    assert p.beta - RealPower(p.alpha, p.delta) > 0.0;
    assert RealMin(p.alpha - 1.0, 2.0) > 0.0;
    (p.alpha + 1.0) * (p.beta + 1.0) / ((p.beta - RealPower(p.alpha, p.delta)) * RealMin(p.alpha - 1.0, 2.0))
}

static lemma Lemma_SufficientR2 (alpha:real, B:int, log_alpha:nat, r2:nat)
    requires B > 0;
    requires alpha > 1.0;
    requires real(power2(log_alpha)) >= alpha;
    requires r2 >= log_alpha * (B-1);
    ensures real(power2(r2)) >= RealPower(alpha, B-1);
    decreases B;
{
    if B > 1 {
        calc {
            r2 - log_alpha;
            >= log_alpha * (B-1) - log_alpha;
            log_alpha * (B-1) - log_alpha * 1;
            { lemma_mul_is_distributive_sub(log_alpha, B-1, 1); lemma_mul_is_mul_boogie(log_alpha, 1); }
            log_alpha * (B-1 - 1);
            log_alpha * (B-2);
        }
        lemma_mul_nonnegative(log_alpha, B-2);
        assert r2 - log_alpha >= log_alpha * (B-2) >= 0;
        Lemma_SufficientR2(alpha, B-1, log_alpha, r2 - log_alpha);
        assert real(power2(r2 - log_alpha)) >= RealPower(alpha, B-2);
        calc {
            real(power2(r2));
            { lemma_power2_adds(log_alpha, r2-log_alpha); }
            real(power2(log_alpha) * power2(r2-log_alpha));
            { Lemma_RealOfMultiplyIsMultiply(power2(log_alpha), power2(r2-log_alpha)); }
            real(power2(log_alpha)) * real(power2(r2-log_alpha));
            >= alpha * real(power2(r2-log_alpha));
            >= alpha * RealPower(alpha, B-2);
            RealPower(alpha, B-1);
        }
    }
}

static lemma Lemma_MultiplyDivideOrderIrrelevant (x:real, y:real, z:real)
    requires y != 0.0;
    ensures (x/y)*z == (x*z)/y;
{
}

static lemma Lemma_BreakdownOfSufficientBytesForNoiseGeneration (p:DiffPrivParameters, r1:nat, r2:nat, bytes:nat)
    requires DiffPrivParametersValid(p);
    requires real(power2(r1)) >= RequiredNoiseEntropyPart1(p) > 0.0;
    requires real(power2(r2)) >= RealPower(p.alpha, p.B - 1) > 0.0;
    requires bytes >= 1;
    requires ModuloFour(bytes) == 1;
    requires bytes * 8 - 7 >= r1 + r2;
    ensures SufficientBytesForNoiseGeneration(p, bytes);
    decreases r1;
{
//-    assert (p.beta - RealPower(p.alpha, p.delta)) > 0.0;
//-    assert RealMin(p.alpha - 1.0, 2.0) > 0.0;
//-    assert (p.beta - RealPower(p.alpha, p.delta)) * RealMin(p.alpha - 1.0, 2.0) > 0.0;

//-    assert real(power2(r2)) >= RealPower(p.alpha, p.B - 1);
    calc ==> {
        true;
        {
            calc {
                real(power2(bytes * 8 - 7));
                >= { lemma_power2_increases(r1 + r2, bytes * 8 - 7); }
                real(power2(r1 + r2));
                { lemma_power2_adds(r1, r2); }
                real(power2(r1) * power2(r2));
                { Lemma_RealOfMultiplyIsMultiply(power2(r1), power2(r2)); }
                real(power2(r1)) * real(power2(r2));
                >= RequiredNoiseEntropyPart1(p) * real(power2(r2));
            }
        }
        real(power2(bytes * 8 - 7)) >= RequiredNoiseEntropyPart1(p) * real(power2(r2));
        {
            calc {
                RequiredNoiseEntropyPart1(p) * real(power2(r2));
                >= { assert real(power2(r2)) >= RealPower(p.alpha, p.B - 1); }
                RequiredNoiseEntropyPart1(p) * RealPower(p.alpha, p.B - 1);
                == { assert p.beta - RealPower(p.alpha, p.delta) > 0.0; assert RealMin(p.alpha - 1.0, 2.0) > 0.0; }
                ((p.alpha + 1.0) * (p.beta + 1.0) / ((p.beta - RealPower(p.alpha, p.delta)) * RealMin(p.alpha - 1.0, 2.0))) * RealPower(p.alpha, p.B - 1);
                == { Lemma_MultiplyDivideOrderIrrelevant((p.alpha + 1.0) * (p.beta + 1.0), (p.beta - RealPower(p.alpha, p.delta)) * RealMin(p.alpha - 1.0, 2.0), RealPower(p.alpha, p.B - 1)); }
                (p.alpha + 1.0) * (p.beta + 1.0) * RealPower(p.alpha, p.B - 1) / ((p.beta - RealPower(p.alpha, p.delta)) * RealMin(p.alpha - 1.0, 2.0));
                RequiredNoiseEntropy(p);
            }
        }
        real(power2(bytes * 8 - 7)) >= RequiredNoiseEntropy(p);
    }

//-    calc { ModuloFour(bytes); { reveal_ModuloFour(); } 1; }
    calc {
        true;
        { reveal_SufficientBytesForNoiseGeneration(); }
//-        { assert bytes >= 1; }
//-        { assert ModuloFour(bytes) == 1; }
//-        { assert real(power2(bytes * 8 - 7)) >= RequiredNoiseEntropy(p); }
        SufficientBytesForNoiseGeneration(p, bytes);
    }
}

static lemma Lemma_RealPowerPreservesPositivity (x:real, e:nat)
    requires x > 0.0;
    ensures RealPower(x, e) > 0.0;
    decreases e;
{
    if e > 0 {
        Lemma_RealPowerPreservesPositivity(x, e-1);
    }
}
