include "../../FatNat/FatNatCompare.i.dfy"
include "../../FatNat/FatNatRandom.i.dfy"
include "../../FatNat/FatNatMod.i.dfy"
include "../../Math/evenodd.i.dfy"
include "../../Math/power.i.dfy"
include "../../../Drivers/TPM/tpm-wrapper.i.dfy"
include "MillerRabin.s.dfy"
include "division.i.dfy"
include "../../FatNat/FatNatCommon.i.dfy"

static function method{:CompiledSpec} CompiledSpec_Configure_MillerRabinStrength() : int

static function IsPrime(n:nat) : bool
{
    forall cf:nat :: 2 <= cf < n ==> !divides(cf, n)
}

predicate IsEvenFatNat_inner(N:array<int>)
    reads N;
    requires WellformedFatNat(N);
{
    N.Length==0 || IsEven(ArrayDigitAt(N,0))
}

lemma lemma_bignat_even(N:array<int>)
    requires WellformedFatNat(N);
    ensures IsEven(BEWordSeqToInt(N[..])) == IsEvenFatNat_inner(N);
{
    var Ns := N[..];
    var Nv := BEWordSeqToInt(Ns);
    if (N.Length == 0)
    {
        calc {
            IsEven(BEWordSeqToInt(N[..]));
            IsEven(Nv);
                { lemma_even_mod_0_pos(Nv); }
            mod(Nv, 2) == 0;
                { reveal_BEDigitSeqToInt_private(); }
            mod(0, 2) == 0;
                { lemma_small_mod(0,2); }
            true;
            IsEvenFatNat_inner(N);
        }
    }
    else
    {
        lemma_2toX();
        var pv := power2(32);
        var Hv := BEDigitSeqToInt(pv, SelectDigitRange(Ns, |Ns|, 1));
        var Lv := DigitAt(Ns,0);

        if (|Ns|==1)
        {
            assert Ns == [Lv];  //- OBSERVE SEQ
            calc {
                Nv;
                BEDigitSeqToInt(pv, [Lv]);
                    { lemma_BEDigitSeqToInt_singleton(pv, Lv); }
                Lv;
                ArrayDigitAt(N,0);
            }
        }
        else
        {
            var L2 := 2;
            calc {
                Nv;
                    { lemma_BEInterpretation_Select(pv, Ns, 1); }
                Hv * power(pv,1) + BEDigitSeqToInt(pv, SelectDigitRange(Ns, 1, 0));
                    { lemma_SelectSingletonRange(Ns, 1, 0); }
                Hv * power(pv,1) + BEDigitSeqToInt(pv, [DigitAt(Ns,0)]);
                    { lemma_BEDigitSeqToInt_singleton(pv, Lv); }
                Hv * power(pv,1) + Lv;
                    { lemma_power2_unfolding(32, 1);
                      lemma_mul_is_mul_boogie(32, 1); }
                Hv * power2(32*1) + Lv;
                    { lemma_power2_adds(32*1-1,1); }
                Hv * (power2(32*1-1) * power2(1)) + Lv;
                    { lemma_mul_is_associative_forall(); }
                (Hv*power2(32*1-1)) * power2(1) + Lv;
                    { lemma_fundamental_div_mod(Lv,L2); }
                (Hv*power2(32*1-1)) * power2(1) + L2*(Lv/L2) + Lv%L2;
                    { lemma_power2_1_is_2();
                      lemma_mul_is_commutative_forall(); }
                L2*(Hv*power2(32*1-1)) + L2*(Lv/L2) + Lv%L2;
                    { lemma_mul_is_distributive_forall(); }
                L2*(Hv*power2(32*1-1) + Lv/L2) + Lv%L2;
            }
            var ugly := Hv*power2(32*1-1) + Lv/L2;
            calc {
                Nv % L2;
                (L2*ugly + Lv%L2) % L2;
                    { lemma_mod_multiples_vanish(ugly, Lv%L2, L2); }
                (Lv%L2) % L2;
                    { lemma_mod_properties();
                      lemma_small_mod(Lv%L2, L2); }
                Lv%L2;
                ArrayDigitAt(N,0) % L2;
            }
        }
        calc {
            IsEven(BEWordSeqToInt(N[..]));
                { lemma_even_mod_0_pos(Nv); }
            mod(Nv, 2) == 0;
            mod(ArrayDigitAt(N,0), 2) == 0;
                { lemma_even_mod_0_pos(ArrayDigitAt(N,0)); }
            IsEvenFatNat_inner(N);
        }
    }

//-    var w31 := power2(31);
//-    reveal_power2();
//-    assert w31*2 == Width();
//-    { lemma_mul_is_mul_boogie(w31,2); }
//-    assert mul(w31,2) == Width();

//-    if (IsEven(lo(N)))
//-    {
//-        var y0:int :| mul(y0, 2) == lo(N);
//-        lemma_mul_is_mul_boogie(y0, 2);
//-        var y := w31 * J(hi(N)) + y0;
//-
//-        calc {
//-            mul(y, 2);
//-                { lemma_mul_is_mul_boogie(y, 2); }
//-            y * 2;
//-            (w31*J(hi(N)) + y0) * 2;
//-                { lemma_mul_is_distributive_add_forall(); }
//-            (w31*J(hi(N)))*2 + y0*2;
//-                { lemma_mul_is_mul_boogie((w31*J(hi(N))),2); }
//-            mul(w31*J(hi(N)),2) + y0*2;
//-                { lemma_mul_is_commutative_forall(); }
//-            mul(2,w31*J(hi(N))) + y0*2;
//-                { lemma_mul_is_associative_forall(); }
//-            mul(mul(2,w31),J(hi(N))) + y0*2;
//-                { lemma_mul_is_commutative_forall(); }
//-            mul(mul(w31,2),J(hi(N))) + y0*2;
//-            mul(Width(),J(hi(N))) + y0*2;
//-            Width()*J(hi(N)) + y0*2;
//-            Width()*J(hi(N)) + lo(N);
//-                {
//-                    lemma_hilo(N);
//-                    lemma_mul_is_commutative_forall();
//-                }
//-            J(N);
//-        }
//-        assert IsEven(J(N));
//-    }
//-    if (IsEven(J(N)))
//-    {
//-        var y :| mul(y, 2) == J(N);
//-        lemma_mul_is_mul_boogie(y, 2);
//-        calc ==> {
//-            true;
//-                {
//-                    lemma_hilo(N);
//-                    lemma_mul_is_commutative_forall();
//-                }
//-            y*2 == Width()*J(hi(N)) + lo(N);
//-            y*2 == mul(w31,2)*J(hi(N)) + lo(N);
//-            y*2 - mul(w31,2)*J(hi(N)) == lo(N);
//-                {
//-                    lemma_mul_is_commutative_forall();
//-                    lemma_mul_is_associative_forall();
//-                }
//-            y*2 - mul(mul(w31,J(hi(N))),2) == lo(N);
//-                { lemma_mul_is_mul_boogie(y,2); }
//-            mul(y,2) - mul(mul(w31,J(hi(N))),2) == lo(N);
//-                { lemma_mul_is_commutative_forall(); }
//-            mul(2,y) - mul(2,mul(w31,J(hi(N)))) == lo(N);
//-                { lemma_mul_is_distributive_sub(2, y, mul(w31,J(hi(N)))); }
//-            mul(2, y - mul(w31,J(hi(N)))) == lo(N);
//-            mul(2, y - w31*J(hi(N))) == lo(N);
//-                { lemma_mul_is_commutative_forall(); }
//-            mul(y - w31*J(hi(N)), 2) == lo(N);
//-                { lemma_mul_is_mul_boogie(y - w31*J(hi(N)),2); }
//-            IsEven(lo(N));
//-        }
//-    }
}

static function method WordIsEven_def(x:nat) : bool
    requires Word32(x);
{
    
    x%2 == 0
}

static lemma lemma_WordIsEven(x:nat)
    requires Word32(x);
    ensures WordIsEven_def(x) == IsEven(x);
{
    lemma_even_mod_0_pos(x);
    lemma_mod_is_mod_boogie(x, 2);
}

static function method WordIsEven(x:nat) : bool
    requires Word32(x);
    ensures IsEven(x) == WordIsEven(x);
{
    lemma_WordIsEven(x);
    WordIsEven_def(x)
    
}


function method IsEvenFatNat_def(N:array<int>) : bool
    reads N;
    requires WellformedFatNat(N);
{
    if (N.Length==0) then
        true
    else
        WordIsEven(ArrayDigitAt(N,0))
}

lemma lemma_IsEvenFatNat(N:array<int>)
    requires WellformedFatNat(N);
    ensures IsEvenFatNat_def(N) == IsEven(J(N));
{
    if (N.Length==0) {
        calc {
            IsEvenFatNat_def(N);
            true;
                { lemma_mul_is_mul_boogie(0, 2); }
                { assert mul(0, 2) == 0; }
            IsEven(0);
                { reveal_BEDigitSeqToInt_private(); }
            IsEven(J(N));
        }
    }
    else
    {
        calc {
            IsEvenFatNat_def(N);
            WordIsEven(ArrayDigitAt(N,0));
            IsEven(ArrayDigitAt(N,0));
                { lemma_bignat_even(N); }
            IsEven(J(N));
        }
    }
}

function method IsEvenFatNat(N:array<int>) : bool
    reads N;
    requires WellformedFatNat(N);
    ensures IsEvenFatNat(N) == IsEven(J(N));
{
    lemma_IsEvenFatNat(N);
    IsEvenFatNat_def(N)
}

static lemma lemma_dividing_by_two(n:nat, q:nat, r:nat)
    requires 0 < n;
    requires mul(q,2)+r==n;
    requires r<2;
    requires IsEven(n);
    ensures 0 < q;
    ensures q < n;
    ensures r == 0;
{
    if (r!=0)
    {
        var y:int :| mul(y, 2) == n;
        assert r==1;
        calc ==> {
            mul(q,2)+1==n;
            mul(q,2)+1==mul(y,2);
            1==mul(y,2) - mul(q,2);
                { lemma_mul_is_commutative_forall(); }
            1==mul(2,y) - mul(2,q);
                { lemma_mul_is_distributive_sub(2,y,q); }
            1==mul(2,y-q);
                { lemma_mul_is_mul_boogie(2,y-q); }
            1==2*(y-q);
                { lemma_no_half(y-q); }
            false;
        }
    }
    assert r==0;

    calc ==> {
        0 < mul(q,2);
            { lemma_mul_basics(2); }
        mul(0,2) < mul(q,2);
            { lemma_mul_strict_inequality_converse(0,q,2); }
        0 < q;
    }

    calc ==> {
        true;
            { lemma_mul_strictly_increases(2,q); }
        q < mul(2,q);
            { lemma_mul_is_commutative_forall(); }
        q < mul(q,2);
        q < n;
    }
}

method MR_find_s_D(N:array<int>, two:array<int>) returns (s:nat, D:array<int>)
    decreases J(N);
//-    requires ModestBigNatWords(N);
    requires WellformedFatNat(N);
    requires 0 < J(N);
    requires WellformedFatNat(two);
    requires J(two) == 2;
//-    requires ModestBigNatWords(two);
    ensures  WellformedFatNat(D);
    ensures  0 < J(D);
    ensures  power2(s)*J(D) == J(N);
    ensures  J(D) <= J(N);
    ensures  !IsEven(J(D));
    
    
    
{
    D := N;
    s := 0;

    calc {
        power2(s)*J(D);
        power2(0)*J(D);
            { lemma_power2_0_is_1(); }
        mul(1,J(D));
            { lemma_mul_basics_forall(); }
        J(D);
        J(N);
    }

    while (IsEvenFatNat(D))
        invariant WellformedFatNat(D);
        invariant 0 < J(D);
        invariant power2(s)*J(D) == J(N);
        invariant J(D) <= J(N);
        decreases J(D);
    {
        lemma_2to32();
        assert 2 < Width();

//-        assert ModestBigNatWords(D);
        var Nover2_nc:array<int>,zero:array<int> := FatNatDiv(D, two);
        var Nover2 := CanonicalizeArray(Nover2_nc);

        calc {
            mul(J(Nover2),2)+J(zero);
                { lemma_mul_is_commutative_forall(); }
            J(D);
        }
        lemma_dividing_by_two(J(D), J(Nover2), J(zero));
        assert 0 < J(Nover2);
        assert J(Nover2) < J(D);
        assert J(zero)==0;    //- else !WordIsEven()

//-        calc ==> {
//-            J(Nover2) <= J(D);
//-                { lemma_modesty_word_value_equivalence(D); }
//-            J(Nover2) < KindaBigNat();
//-                { lemma_modesty_word_value_equivalence(Nover2); }
//-            ModestBigNatWords(Nover2);
//-        }

        calc {
            power2(s+1) * J(Nover2);
                { lemma_power2_adds(s,1); }
            (power2(s) * power2(1)) * J(Nover2);
                { lemma_mul_is_associative_forall(); }
            power2(s) * (power2(1) * J(Nover2));
                { lemma_power2_1_is_2(); }
            power2(s) * mul(2, J(Nover2));
                { lemma_mul_is_commutative_forall(); }
            power2(s) * mul(J(Nover2), 2);
            power2(s) * (J(D));
            J(N);
        }
        D := Nover2;
        s := s + 1;
    }
}

static lemma lemma_even_divisble_by_2(x:int)
    requires 0 <= x;
    requires IsEven(x);
    ensures  divides(2,x);
{
    lemma_even_mod_0_pos(x);
    assert mod(x, 2) == 0;
    assert divides(2,x);
}

method ProbeLoop(N:array<int>, Nminus1:array<int>, Xinit:array<int>, s:int, ghost problem:MRProblem, ghost probe_init:MRProbe)
    returns (isProbablyPrime:bool, ghost probe:MRProbe)

    requires WellformedFatNat(N);
    requires MRProblemNeedsProbes(problem);
    requires WellformedFatNat(Nminus1);
    requires J(Nminus1) == J(N) - 1;
    requires WellformedFatNat(Xinit);
    requires MRProblemValid(problem);
    requires probe_init.squares == [J(Xinit)];
    requires J(Xinit) != 1;
    requires J(Xinit) != problem.n-1;
    requires MRProbeInit(problem, probe_init);
    requires problem.n == J(N);
    requires problem.s == s;
    ensures probe.a == probe_init.a;
    ensures isProbablyPrime ==> MRProbeSucceeds(problem, probe);
    ensures !isProbablyPrime ==> MRProbeFails(problem, probe);
{
//-    lemma_frumpy_is_modest(N);

    isProbablyPrime := true;
    probe := probe_init;

    var si:int := 1;
    var probing := true;
    var X:array<int> := Xinit;
    while (si <= s-1)
//-        invariant FrumpyBigNat(X);
        invariant MRProblemValid(problem);
        invariant 0 < |probe.squares|;
        invariant 0<s ==> |probe.squares| <= s;
        invariant MRProbeInit(problem, probe);
        invariant si==|probe.squares|;
        invariant probe.a == probe_init.a;
        invariant WellformedFatNat(X);
        invariant probe.squares[si-1] == J(X);
        invariant isProbablyPrime ==>
            (forall i :: 0<i<si ==>
                MRProbeChain(problem, probe, i));
        invariant !isProbablyPrime || probing || MRProbeSucceeds(problem, probe);
        invariant !isProbablyPrime ==> MRProbeFails(problem, probe);
        invariant isProbablyPrime && !probing ==> probe.squares[|probe.squares|-1]==problem.n-1;
        invariant MRProbeValid(problem, probe);
        invariant forall i :: 0<i<|probe.squares| ==> probe.squares[i] != 1;
        invariant si <= MRProbeLimit(problem);
        invariant forall i :: 0<=i<|probe.squares| ==> probe.squares[i] != problem.n-1;
    {
        var Xsquared:array<int> := FatNatMul(X,X);
        lemma_mul_nonnegative(J(X),J(X));
//-        lemma_frumpy_squared_is_modest(X,Xsquared);
        assert 0 <= J(Xsquared);
        assert 0 < J(N);
        var oldX := X;
        var X_nc := FatNatModulo(Xsquared, N);
        X := CanonicalizeArray(X_nc);

        ghost var old_probe := probe;
        assert |old_probe.squares|==si;
        assert forall i :: 0<i<|old_probe.squares| ==>
            MRProbeChain(problem, old_probe, i);
        assert forall i :: 0<i<|old_probe.squares| ==>
            old_probe.squares[i] != 1;
        probe := MRProbe_c(probe.a, probe.squares + [J(X)]);

        lemma_mod_pos_bound(J(Xsquared),J(N));
        assert J(X) < J(N);
//-        assert FrumpyBigNat(X);
        lemma_2to32();

        calc {
            probe.squares[si];
            J(X);
            J(Xsquared) % J(N);
            (J(oldX)*J(oldX)) % J(N);
                { lemma_square_is_power_2(J(oldX)); }
            power(J(oldX),2) % J(N);
                { assert probe.squares[si-1] == J(oldX); }
            power(probe.squares[si-1],2) % J(N);
            power(probe.squares[si-1],2) % problem.n;
        }

        var is_one:bool := TestEqSmallLiteralFatNat(1, X);
        if (is_one)
        {
            //- n divides (a^{d2^{r-1}}-1)(a^{d2^{r-1}}+1);
            //- hence n could be factored.
            
            
            isProbablyPrime := false;
            probing := false;
            assert probing ==> s <= si;
            forall (i:int | 0<i<|probe.squares|)
                ensures MRProbeChain(problem, probe, i);
            {
                if (i < |probe.squares|-1)
                {
                    assert MRProbeChain(problem, old_probe, i);
                    assert MRProbeChain(problem, probe, i);
                }
                else
                {
                    assert MRProbeChain(problem, probe, i);
                }
            }
            forall (i:int | 0<i<|probe.squares|-1)
                ensures probe.squares[i]!=1;
            {
                if (i < |probe.squares|-1-1)
                {
                    assert (0<i<|probe.squares|-1 ==> probe.squares[i]!=1);
                }
                else
                {
                    assert (0<i<|probe.squares|-1 ==> probe.squares[i]!=1);
                }
            }

            assert 0 < |probe.squares| <= problem.s;
            assert MRProblemValid(problem);
            assert MRProbeInit(problem,probe);
            assert forall i:int ::
                (0<i<|probe.squares| ==> MRProbeChain(problem, probe, i));
            assert forall i:int ::
                (0<i<|probe.squares|-1 ==> probe.squares[i]!=1);
            
            assert MRProbeValid(problem, probe);
            assert probing ==> forall i :: 0<=i<|probe.squares| ==> probe.squares[i] != problem.n-1;
            break;
        }
        assert |probe.squares| == si+1;
        assert probe.squares[si] == power(probe.squares[si-1], 2) % problem.n;
        assert MRProbeChain(problem, probe, si);

        var is_nminus1:bool := FatNatEq(X, Nminus1);

        if (is_nminus1)
        {
            //- "do next WitnessLoop" -- this one is successful
            probing := false;
            calc {
                |probe.squares|;
                si+1;
                <= s;
            }
            calc {
                probe.squares[|probe.squares|-1];
                J(X);
                J(Nminus1);
                J(N)-1;
                problem.n-1;
            }
            forall (i | 0<i<|probe.squares|)
                ensures MRProbeChain(problem, probe, i);
            {
                if (i<|old_probe.squares|)
                {
                    assert i < |old_probe.squares|;    
                    assert MRProbeChain(problem, old_probe, i);
                    assert MRProbeChain(problem, probe, i);
                }
                else
                {
                    assert i==|probe.squares|-1==si;
                    assert MRProbeChain(problem, probe, i);
                }
            }

            assert MRProbeSucceeds(problem, probe);
            assert probing ==> s <= si;
            assert MRProbeValid(problem, probe);
            assert probing ==> forall i :: 0<=i<|probe.squares| ==> probe.squares[i] != problem.n-1;
            break;
        }

        ghost var old_si:int := si;
        assert forall i :: 0<i<old_si ==>
            MRProbeChain(problem, old_probe, i);
        forall (i | 0<i<old_si)
            ensures MRProbeChain(problem, probe, i);
        {
            assert MRProbeChain(problem, old_probe, i);
            assert probe.squares[i]==old_probe.squares[i];
        }
        si := si + 1;
        assert MRProbeChain(problem, probe, si-1);
        forall (i | 0<i<si)
            ensures MRProbeChain(problem, probe, i);
        {
        }
        assert forall i :: 0<i<si ==>
                MRProbeChain(problem, probe, i);
    }

    if (probing)
    {
        //- Unsatisfactory initial X, and never
        //- found the x-1 we needed in s-1 additional steps.
        isProbablyPrime := false;
    }
    assert isProbablyPrime ==> MRProbeSucceeds(problem, probe);

    if (!isProbablyPrime)
    {
        assert MRProbeValid(problem, probe);
        assert (|probe.squares| == MRProbeLimit(problem)
            || (0 < |probe.squares|
                && probe.squares[|probe.squares|-1] == 1));
        assert probe.squares!=[1];
        assert probe.squares!=[problem.n-1];
        assert probe.squares[|probe.squares|-1]!=problem.n-1;
    }
    
    assert !isProbablyPrime ==> MRProbeFails(problem, probe);
}

static predicate MillerRabinSpecSucceeding_incremental(problem:MRProblem, probes:seq<MRProbe>)
    //- all probes succeed
    //- probed exactly as many times as problem strength requires
{
    MRProblemNeedsProbes(problem)
    && problem.n%2==1
    && problem.n>3
    && forall i :: 0 <= i < |probes|-1 ==> MRProbeSucceeds(problem, probes[i])
}

static predicate MillerRabinWorksheetValid_incremental(n:int, worksheet:MillerRabinWorksheet)
{
    |worksheet.probes|==|worksheet.probe_candidates|
    && |worksheet.probes|==|worksheet.probe_seed_reqs|
    && (forall i :: 0<=i<|worksheet.probes| ==> MillerRabinProbeConsistency(n, worksheet.probe_candidates[i], worksheet.probe_seed_reqs[i], worksheet.probes[i]))
    && worksheet.problem.n == n
    && worksheet.problem.strength == Configure_MillerRabinStrength()
    && MillerRabinSpecSucceeding_incremental(worksheet.problem, worksheet.probes)
    && MillerRabinWorksheetConsumesRandoms(worksheet.probe_candidates) == worksheet.randoms
}




method GhostFatNatCountBits(x:array<int>) returns (ghost e:nat)
    requires x!=null && IsWordSeq(x[..]);
    ensures FatNatBitCount(x[..], e);
{
    var real_e := FatNatCountBits(x);
    e := real_e;
}

method {:timeLimitMultiplier 3} WitnessLoop(N:array<int>, Nminus1:array<int>, Nminus2:array<int>, D:array<int>, s:int, two:array<int>, strength:nat, ghost problem:MRProblem)
    returns (isProbablyPrime:bool, ghost worksheet:MillerRabinWorksheet)

    requires WellformedFatNat(N);
//-    requires FrumpyBigNat(N);
    requires MRProblemNeedsProbes(problem);
    requires WellformedFatNat(Nminus1);
    requires J(Nminus1) == J(N) - 1;
    requires WellformedFatNat(Nminus2);
//-    requires ModestBigNatWords(Nminus2);
    requires J(Nminus2) == J(N) - 2;
    requires WellformedFatNat(D);
//-    requires FrumpyBigNat(D);
    requires WellformedFatNat(two);
//-    requires ModestBigNatWords(two);
    requires J(two) == 2;
    requires strength == Configure_MillerRabinStrength();
    requires MRProblemValid(problem);
    requires problem.n == J(N);
    requires problem.strength == strength;
    requires problem.s == s;
    requires problem.d == J(D);
    ensures MillerRabinWorksheetValid(problem.n, worksheet);
    ensures MillerRabinSpecValid(problem, worksheet.probes, worksheet.is_probably_prime);
    ensures worksheet.is_probably_prime == isProbablyPrime;
    requires TPM_ready();
    ensures TPM_ready();
    modifies this`TPM;   
    modifies this`IoMemPerm;
    ensures TPMs_match_except_for_randoms(old(TPM), TPM);
    ensures old(TPM).random_index <= TPM.random_index;
    ensures worksheet.randoms == TPM_random_bytes_premium(old(TPM).random_index, TPM.random_index);
{
    ghost var probes := [];

    worksheet := MillerRabinWorksheet_c(
        problem,
        [],
        [],
        [],
        true,
        []);
    assert MillerRabinWorksheetValid_incremental(J(N), worksheet);

    var ki:int :=0;
    isProbablyPrime := true;
    while (ki < strength && isProbablyPrime)
        decreases strength - ki;
        invariant (forall i :: 0<=i<|probes|-1
                ==> MRProbeSucceeds(problem, probes[i]));
        invariant !isProbablyPrime ==>
            0<|probes| && MRProbeFails(problem, probes[|probes|-1]);
        invariant (forall probe :: 0 <= probe < |probes|
                ==> MRProbeValid(problem, probes[probe]));
        invariant isProbablyPrime ==>
            (forall probe :: 0 <= probe < |probes|
                ==> MRProbeSucceeds(problem, probes[probe]));
        invariant MRProblemValid(problem);
        invariant |probes|==ki;
        invariant ki <= strength;
        invariant worksheet.problem == problem;
        invariant worksheet.probes == probes;
        invariant MillerRabinWorksheetValid_incremental(J(N), worksheet);
        invariant worksheet.is_probably_prime == isProbablyPrime;
        invariant TPM_ready();
        invariant TPMs_match_except_for_randoms(old(TPM), TPM);
        invariant old(TPM).random_index <= TPM.random_index;
        invariant worksheet.randoms == TPM_random_bytes_premium(old(TPM).random_index, TPM.random_index);
    {
        ghost var loop_TPM_index := TPM.random_index;
        ghost var Nminus2fatbits := GhostFatNatCountBits(Nminus2);
        ghost var req := SelectRandomRequest_c(2, J(Nminus2), Nminus2fatbits);
        lemma_power2_0_is_1();
        var A:array<int>,candidate_worksheet := FatNatRandomFromInclusiveRange(two, Nminus2, req);
        assert TPM_random_bytes_premium(loop_TPM_index, TPM.random_index) == candidate_worksheet.randoms;

        var X:array<int> := FatNatModExp(A, D, N);
//-        assert FrumpyBigNat(X);

        ghost var probe:MRProbe := MRProbe_c(J(A), [J(X)]);
        calc {
            probe.squares[0];
            J(X);
            power(J(A),J(D)) % J(N);
            power(probe.a, problem.d) % problem.n;
        }
        assert MRProbeInit(problem, probe);

        assert MRProbeValid(problem, probe);
        lemma_2toX();
        var is_one:bool := TestEqSmallLiteralFatNat(1, X);
        if (is_one)
        {    //- "continue"
            assert probe.squares==[J(X)]==[1];
            assert MRProbeSucceeds(problem, probe);
        }
        else
        {
            var is_nminus1:bool := FatNatEq(X, Nminus1);
            if (is_nminus1)
            {    //- "continue"
                calc {
                    probe.squares;
                    [J(X)];
                    [J(Nminus1)];
                    [J(N)-1];
                    [problem.n - 1];
                }
                assert MRProbeSucceeds(problem, probe);
            }
            else
            {
                isProbablyPrime,probe := ProbeLoop(N, Nminus1, X, s, problem, probe);
            } //- "continue"
        } //- "continue"

        probes := probes + [probe];

        ki := ki + 1;

        ghost var worksheet' := MillerRabinWorksheet_c(
            problem,
            worksheet.probe_candidates + [candidate_worksheet],
            worksheet.probe_seed_reqs + [req],
            worksheet.probes + [probe],
            isProbablyPrime,
            worksheet.randoms + candidate_worksheet.randoms);

//-        assert MillerRabinWorksheetConsumesRandoms(worksheet'.probe_candidates) == worksheet'.randoms;
        assert MillerRabinWorksheetValid_incremental(J(N), worksheet');

        assert old(TPM).random_index + |worksheet.randoms| == loop_TPM_index;
        assert TPM_random_bytes_premium(
            old(TPM).random_index,
            old(TPM).random_index + |worksheet.randoms|)
            == worksheet.randoms;   // loop invariant
        assert TPM_random_bytes_premium(loop_TPM_index, TPM.random_index) == candidate_worksheet.randoms;    // FatNatRandomFromInclusiveRange
        assert loop_TPM_index == old(TPM).random_index + |worksheet.randoms|;
        assert TPM.random_index == loop_TPM_index + |candidate_worksheet.randoms|;
        assert TPM_random_bytes_premium(
            old(TPM).random_index + |worksheet.randoms|,
            old(TPM).random_index + |worksheet.randoms| + |candidate_worksheet.randoms|)
            == candidate_worksheet.randoms;
        lemma_random_comprehension(old(TPM).random_index, worksheet.randoms, candidate_worksheet.randoms);

        worksheet := worksheet';
        assert (forall probe :: 0 <= probe < |probes|
                ==> MRProbeValid(problem, probes[probe]));
    }
    if (isProbablyPrime)
    {
        assert strength <= ki;
        assert forall probe :: 0 <= probe < |probes|
            ==> MRProbeSucceeds(problem, probes[probe]);
        calc {
            problem.strength;
            strength;
            <= ki;
            |probes|;
        }
        assert MillerRabinSpecSucceeds(problem, probes);
    }
    else
    {
        assert MRProbeValid(problem, probes[|probes|-1]);
        assert MillerRabinSpecFails(problem, probes);
    }
}

method {:timeLimitMultiplier 3} MillerRabinTest(N:array<int>, strength:nat) returns (isProbablyPrime:bool, ghost worksheet:MillerRabinWorksheet)
//-    requires FrumpyBigNat(N);
    requires WellformedFatNat(N);
    requires J(N) > 3;
    requires strength == Configure_MillerRabinStrength();
    ensures isProbablyPrime ==> IsProbablyPrime(J(N), strength);
    ensures MillerRabinWorksheetValid(J(N), worksheet);
    ensures worksheet.is_probably_prime == isProbablyPrime;
    requires TPM_ready();
    ensures TPM_ready();
    modifies this`TPM;   
    modifies this`IoMemPerm;
    ensures TPMs_match_except_for_randoms(old(TPM), TPM);
    ensures old(TPM).random_index <= TPM.random_index;
    ensures worksheet.randoms == TPM_random_bytes_premium(old(TPM).random_index, TPM.random_index);
{
    ProfileTally(Tally_MillerRabinTest(), 1);
//-    debug_print(0x90, 0x88778877);
//-    lemma_frumpy_is_modest(N);
    lemma_2toX();

    var early_reject:bool := false;
    var three := MakeBELiteralArray(3);
    var too_small := FatNatLe(N, three);
    if (too_small)
    {
        early_reject := true;
        assert J(N)<=3;
    }
    else if (IsEvenFatNat(N))
    {
        early_reject := true;
        lemma_even_divisble_by_2(J(N));
        lemma_mod_is_mod_boogie(J(N), 2);
        assert J(N) % 2 == 0;
//-        assert divides(2, J(N));
//-        assert !IsPrime(J(N));
    }
    assert early_reject ==> (J(N) <= 3 || J(N)%2==0);

    if (early_reject)
    {
        isProbablyPrime := false;

        //- even N? s & d irrelevant.
        ghost var problem := MRProblem_c(J(N), strength, 0, 0);
        worksheet := MillerRabinWorksheet_c(
            problem,
            //- No probes in this case.
            [],
            [],
            [],
            false,
            []);
        assert MillerRabinSpecFails(problem, []);
    }
    else
    {
        var one:array<int> := MakeBELiteralArray(1);
        lemma_2toX32();
        assert 2 < Width();
        var two:array<int> := MakeBELiteralArray(2);
        var Nminus1:array<int> := FatNatSub(N,one);

//-        lemma_modesty_word_value_equivalence(N);
//-        lemma_modesty_word_value_equivalence(Nminus1);
//-        assert ModestBigNatWords(Nminus1);

        var Nminus2:array<int> := FatNatSub(N,two);
//-        lemma_modesty_word_value_equivalence(Nminus2);

        lemma_power2_increases(power2(1), power2(31));
//-        lemma_modesty_word_value_equivalence(two);

        var s:int,D:array<int> := MR_find_s_D(Nminus1, two);
//-        assert FrumpyBigNat(D);

        ghost var problem:MRProblem := MRProblem_c(J(N), strength, s, J(D));
        assert s==problem.s;

        lemma_x_odd(J(N));
        lemma_x_odd(J(D));
        calc {
            power(2,problem.s)*problem.d;
            power(2,s)*J(D);
                { lemma_power2_is_power_2(s); }
            power2(s)*J(D);
            J(N)-1;
        }
        assert MRProblemValid(problem);

        isProbablyPrime,worksheet := WitnessLoop(N, Nminus1, Nminus2, D, s, two, strength, problem);
        if (isProbablyPrime)
        {
            MillerRabinSpec(problem, worksheet.probes);
        }
    }
}
