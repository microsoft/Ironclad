//- <NuBuild AddDafnyFlag /z3opt:NL_ARITH=true/>
include "../../Libraries/Util/be_sequences.s.dfy"

static function RealPower(x:real, e:nat) : real
    decreases e;
{
    if e == 0 then 1.0 else x * RealPower(x, e-1)
}

static function RealMin(a:real, b:real) : real
{
    if a < b then a else b
}

datatype DiffPrivParameters = DiffPrivParameters_ctor(alpha:real, beta:real, delta:int, B:int);

static function DiffPrivParametersValid (p:DiffPrivParameters) : bool
{
    p.delta >= 0 &&
    p.alpha > 1.0 &&
    p.beta > RealPower(p.alpha, p.delta) &&
    p.B > 0 &&
    p.beta >= 1.0
}

static function RequiredNoiseEntropy (p:DiffPrivParameters) : real
    requires DiffPrivParametersValid(p);
{
    (p.alpha + 1.0) * (p.beta + 1.0) * RealPower(p.alpha, p.B - 1) / ((p.beta - RealPower(p.alpha, p.delta)) * RealMin(p.alpha - 1.0, 2.0))
}

static function {:opaque} ModuloFour (x:int) : int
{
    x % 4
}

static function {:opaque} SufficientBytesForNoiseGeneration (p:DiffPrivParameters, bytes:nat) : bool
    requires DiffPrivParametersValid(p);
{
    bytes >= 1 &&
    ModuloFour(bytes) == 1 &&
    real(power2(bytes * 8 - 7)) >= RequiredNoiseEntropy(p) //- We need 7 extra bits because we use an entire byte for the sign bit.
}

static function NoiseThreshold (alpha:real, u:real) : real
    requires u > 0.0;
    requires alpha > 1.0;
{
    (2.0 * alpha) / (u * (alpha + 1.0))
}

static predicate {:opaque} ShouldNegateNoise (r:int)
{
    (r % 2 == 1)
}

static function GetUniformBetweenZeroAndOne (randoms:seq<int>) : real
    requires IsByteSeq(randoms);
{
    (real(BEByteSeqToInt(randoms)) + 0.5) / real(power2(|randoms|*8))
}

static function NoiseOK (p:DiffPrivParameters, negate_noise:bool, u:real, absolute_noise:nat, noise:int) : bool
    requires DiffPrivParametersValid(p);
{
    u > 0.0 &&
    RealPower(p.alpha, absolute_noise) <= NoiseThreshold(p.alpha, u) &&
    (absolute_noise == p.B || RealPower(p.alpha, absolute_noise + 1) > NoiseThreshold(p.alpha, u)) &&
    noise == (if negate_noise then -absolute_noise else absolute_noise)
}

static function AbsoluteNoiseComputedCorrectlyTrigger (absolute_noise:nat) : bool
{
    true
}

static function NoiseComputedCorrectly (p:DiffPrivParameters, randoms:seq<int>, noise:int) : bool
    requires DiffPrivParametersValid(p);
{
    |randoms| > 0 &&
    IsByteSeq(randoms) &&
    SufficientBytesForNoiseGeneration(p, |randoms|) &&
    exists absolute_noise:nat {:trigger AbsoluteNoiseComputedCorrectlyTrigger(absolute_noise)} ::
        NoiseOK(p, ShouldNegateNoise(randoms[0]), GetUniformBetweenZeroAndOne(randoms[1..]), absolute_noise, noise)
}
