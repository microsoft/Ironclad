include "RSASpec.s.dfy"
include "../Hash/Digest.i.dfy"
include "../../BigNum/BigNum.i.dfy"
include "../../BigNum/BigNatDiv.i.dfy"
include "../../BigNum/BigNatMod.i.dfy"
include "Extended_GCD.i.dfy"
include "KeyGen.i.dfy"
include "BlockEncoding.i.dfy"
include "KeyImpl.i.dfy"
include "../../FatNat/BigNatToFatNatAdaptor.i.dfy"
include "../../FatNat/FatNatMod.i.dfy"
include "../../FatNat/Transforms.i.dfy"
include "../../FatNat/FatNatReciprocal.i.dfy"
include "KeybitsLength.i.dfy"
include "MultiplicativeInverse.i.dfy"

method ComputeKeySize(N:array<int>) returns (k:nat)
    requires WellformedFatNat(N);
    requires 0<J(N);
    ensures 0<k;
    ensures KeyModulusMatchesSizeInBytes(J(N), k);
{
    //- Can't compute this from |N.words|, since that's only
    //- word-level precision; need byte-level. So we'll start from bits.
//-    lemma_frumpy_is_modest(N);
    var bit_count := FatNatCountBits(N);
    assert 0 < bit_count;
    k := (bit_count-1) / 8 + 1;
    
    calc {
        bit_count-1;
        { lemma_fundamental_div_mod(bit_count-1,8); }
        mul(8,div(bit_count-1,8)) + mod(bit_count-1,8);
        { lemma_mul_is_mul_boogie(8,div(bit_count-1,8)); }
        8*div(bit_count-1,8) + mod(bit_count-1,8);
        8*((bit_count-1)/8) + mod(bit_count-1,8);
            8*((bit_count-1)/8) + 8 - 8 + mod(bit_count-1,8);
            8*((bit_count-1)/8+1) - 8 + mod(bit_count-1,8);
            8*k - 8 + mod(bit_count-1,8);
    }

    if (k>0)
    {
        calc {
            power2(8*(k-1));
                power2(8*k-8);
                <=    {
                    lemma_mod_remainder();
                        assert 0 <= mod(bit_count-1,8);
                        assert 8*k-8 <= 8*k - 8 + mod(bit_count-1,8);
                        lemma_power2_increases(8*k-8, 8*k - 8 + mod(bit_count-1,8));
                }
            power2(8*k - 8 + mod(bit_count-1,8));
                power2(bit_count-1);
                <= J(N);
        }
    }

    calc {
        J(N);
            < power2(bit_count);
            power2(bit_count-1+1);
            power2(8*k - 8 + mod(bit_count-1,8) + 1);
            power2(8*k - 7 + mod(bit_count-1,8));
            <=    {
                lemma_mod_remainder();
                    assert mod(bit_count-1,8) < 8;
                    lemma_power2_increases(8*k - 7 + mod(bit_count-1,8), 8*k);
            }
        power2(8*k);
    }
}

static predicate RSAKeyGenerationWorksheetValid_premium(keybits:int, worksheet:RSAKeyGenerationWorksheet)
    requires forall i :: 0 <= i < |worksheet.rows|
        ==> 0 < |worksheet.rows[i].P.rows|
         && 0 < |worksheet.rows[i].Q.rows|
         ;
//-         && 0 < |worksheet.rows[i].P.rows[|worksheet.rows[i].P.rows|-1].candidate.rows|
//-         && 0 < |worksheet.rows[i].Q.rows[|worksheet.rows[i].Q.rows|-1].candidate.rows|;
{
    RSAKeyGenerationWorksheetValid(keybits, worksheet)
}

static predicate RSAKeyConsistentWithWorksheet_precondition(worksheet:RSAKeyGenerationWorksheet)
{
    (forall i :: 0 <= i < |worksheet.rows|
        ==> PrimeGenerationWorksheetValid_precondition(worksheet.rows[i].P)
         && PrimeGenerationWorksheetValid_precondition(worksheet.rows[i].Q))
}

static predicate RSAKeyConsistentWithWorksheet_premium(requested_keybits:int, key:RSAKeyPairSpec, worksheet:RSAKeyGenerationWorksheet)
    requires RSAKeyConsistentWithWorksheet_precondition(worksheet);
{
    RSAKeyConsistentWithWorksheet(requested_keybits, key, worksheet)
}

static predicate RSAKeyGenerationWorksheetSummaryValid_Impl(worksheet:RSAKeyGenerationWorksheet, last_accepted:bool)
    requires 0 < |worksheet.rows|;
    requires 0 < |worksheet.rows[|worksheet.rows|-1].P.rows|;
    requires 0 < |worksheet.rows[|worksheet.rows|-1].Q.rows|;
{
    var final := worksheet.rows[|worksheet.rows|-1];
    worksheet.rows[|worksheet.rows|-1].accepted == last_accepted
    && 0 < |final.P.rows|
    && worksheet.p == PrimeGenerationOutput(final.P)
    && 0 < |final.Q.rows|
    && worksheet.q == PrimeGenerationOutput(final.Q)
    && worksheet.phi == (worksheet.p-1)*(worksheet.q-1)
    && worksheet.phi != 0
    && worksheet.n == worksheet.p*worksheet.q
}

static predicate RSAKeyGenerationWorksheetValid_Impl(keybits:int, worksheet:RSAKeyGenerationWorksheet, last_accepted:bool)
    requires RSAKeyConsistentWithWorksheet_precondition(worksheet);
{
    (forall i :: 0 <= i < |worksheet.rows| ==> RSAKeyGenerationWorksheetRowValid(worksheet.keybits, worksheet.rows[i]))
    && (forall i :: 0 <= i < |worksheet.rows|-1 ==> !worksheet.rows[i].accepted)
    && (0<|worksheet.rows| ==> worksheet.rows[|worksheet.rows|-1].accepted == last_accepted)
    && (RSAKeyGenerationWorksheetConsumesRandoms(worksheet.rows) == worksheet.randoms)
    && (0<|worksheet.rows| ==> RSAKeyGenerationWorksheetSummaryValid_Impl(worksheet, last_accepted))
}

static function RSAKeyGenerationWorksheetAppend(worksheet:RSAKeyGenerationWorksheet, worksheet_row:RSAKeyGenerationWorksheetRow, last_accepted:bool) : RSAKeyGenerationWorksheet
    requires 0 < |worksheet_row.P.rows|;
    requires 0 < |worksheet_row.Q.rows|;
    requires RSAKeyConsistentWithWorksheet_precondition(worksheet);
    requires RSAKeyGenerationWorksheetValid_Impl(worksheet.keybits, worksheet, false);
{
    RSAKeyGenerationWorksheet_c(
        worksheet.keybits,
        worksheet.rows + [worksheet_row],
        worksheet.randoms + worksheet_row.randoms,
        PrimeGenerationOutput(worksheet_row.P),
        PrimeGenerationOutput(worksheet_row.Q),
        (PrimeGenerationOutput(worksheet_row.P)-1)*(PrimeGenerationOutput(worksheet_row.Q)-1),
        PrimeGenerationOutput(worksheet_row.P)*PrimeGenerationOutput(worksheet_row.Q))
}

static lemma WorksheetAppend_lemma(worksheet:RSAKeyGenerationWorksheet, worksheet_row:RSAKeyGenerationWorksheetRow, last_accepted:bool, worksheet':RSAKeyGenerationWorksheet)
    requires RSAKeyConsistentWithWorksheet_precondition(worksheet);
    requires RSAKeyGenerationWorksheetValid_Impl(worksheet.keybits, worksheet, false);
    requires 0 < |worksheet_row.P.rows|;
    requires 0 < |worksheet_row.Q.rows|;
    requires worksheet' == RSAKeyGenerationWorksheetAppend(worksheet, worksheet_row, last_accepted);
    requires PrimeGenerationWorksheetValid_precondition(worksheet_row.P);
    requires PrimeGenerationWorksheetValid_precondition(worksheet_row.Q);
    requires RSAKeyGenerationWorksheetRowValid(worksheet'.keybits, worksheet_row);
    requires worksheet'.rows[|worksheet'.rows|-1].accepted == last_accepted;
    requires worksheet'.p == PrimeGenerationOutput(worksheet'.rows[|worksheet'.rows|-1].P);
    requires worksheet'.q == PrimeGenerationOutput(worksheet'.rows[|worksheet'.rows|-1].Q);
    requires worksheet'.phi == (worksheet'.p-1)*(worksheet'.q-1);
    requires worksheet'.phi != 0;
    requires worksheet'.n == worksheet'.p*worksheet'.q;
    ensures RSAKeyConsistentWithWorksheet_precondition(worksheet');
    ensures last_accepted ==> RSAKeyGenerationWorksheetValid_Impl(worksheet'.keybits, worksheet', last_accepted);
    ensures RSAKeyGenerationWorksheetConsumesRandoms(worksheet'.rows) == worksheet'.randoms;
    ensures 0 < |worksheet'.rows|;
{
}

method RSAKeyGenSetup(keybits:nat) returns (e:array<int>, halfbits:nat)
    requires 20<keybits;
//-    requires keybits<power2(29);
    ensures WellformedFatNat(e);
    ensures J(e) == 65537;
//-   ensures power2(halfbits) <= power2(power2(29));
    ensures 3 < halfbits;
//-    ensures halfbits < power2(30);
    ensures keybits <= 2*(halfbits-1);
    ensures halfbits == keybits/2+2;
{
    lemma_2to32();
    e := MakeBELiteralArray(65537);
    
//-    calc {
//-        I(e);
//-            < 131072;
//-            { lemma_2toX(); reveal_power2(); }
//-        power2(17);
//-            <    { lemma_power2_strictly_increases(17,1073741824); }
//-            power2(1073741824);
//-            { lemma_2toX(); reveal_power2(); }
//-        power2(power2(30));
//-            Frump();
//-    }

    halfbits := keybits/2 + 2;
    
    lemma_div_is_ordered(20, keybits, 2);
    assert 20/2 <= keybits/2;
    assert 10 <= keybits/2;
    assert 10 <= halfbits;
    
//-    calc {
//-        halfbits;
//-            keybits/2 + 2;
//-            <=    { lemma_div_is_ordered(keybits, power2(29), 2); }
//-            power2(29)/2 + 2;
//-            {
//-                calc {
//-                    power2(29)/2;
//-                    { reveal_power2(); }
//-                    (2*power2(28))/2;
//-                        (power2(28)*2)/2;
//-                        { lemma_mul_is_mul_boogie(power2(28), 2); }
//-                    mul(power2(28),2)/2;
//-                    { lemma_div_by_multiple(power2(28), 2); }
//-                    power2(28);
//-                }
//-            }
//-        power2(28) + 2;
//-            <=    {
//-                calc {
//-                    2;
//-                    { lemma_power2_1_is_2(); }
//-                    power2(1);
//-                        <    { lemma_power2_strictly_increases(1,28); }
//-                        power2(28);
//-                }
//-            }
//-        power2(28) + power2(28);
//-            2*power2(28);
//-            { reveal_power2(); }
//-        power2(29);
//-    }
//-    lemma_power2_strictly_increases(29,30);
//-    
//-    calc {
//-        power2(halfbits);
//-            <=    { lemma_power2_increases(halfbits, power2(29)); }
//-            power2(power2(29));
//-    }
}

lemma lemma_RSAKeyGen_1(keybits:nat, halfbits:nat, p:array<int>, q:array<int>, n:int)
    requires keybits <= 2*halfbits-2;
    requires WellformedFatNat(p);
    requires WellformedFatNat(q);
    requires n == J(p)*J(q);
    requires power2(halfbits-1) <= J(p);
    requires power2(halfbits-1) <= J(q);
    ensures power2(keybits) <= n;
{
    calc {
        power2(keybits);
            <= { lemma_power2_increases(keybits, halfbits-1 + halfbits-1); }
            power2(halfbits-1 + halfbits-1);
            { lemma_power2_adds(halfbits-1, halfbits-1); }
        power2(halfbits-1) * power2(halfbits-1);
            <=    { lemma_mul_inequality(power2(halfbits-1), J(p), power2(halfbits-1)); }
            J(p) * power2(halfbits-1);
            <=    { lemma_mul_left_inequality(J(p), power2(halfbits-1), J(q)); }
            J(p) * J(q);
            n;
    }
}

lemma lemma_RSAKeyGen_2(keybits:nat, halfbits:nat, p:array<int>, q:array<int>, n:int, e:array<int>, pMinus1:array<int>, qMinus1:array<int>, phi_n:array<int>)
    requires keybits <= 2*halfbits-2;
//-    requires 3 < halfbits < power2(30);
    requires 3 < halfbits < power2(32);
    requires 20<keybits;
    requires keybits <= 2*(halfbits-1);
    requires WellformedFatNat(p);
    requires WellformedFatNat(q);
    requires WellformedFatNat(e);
    requires WellformedFatNat(pMinus1);
    requires WellformedFatNat(qMinus1);
    requires WellformedFatNat(phi_n);
//-    requires J(p) < power2(power2(29));
//-    requires J(q) < power2(power2(29));
    requires n == J(p)*J(q);
    requires power2(halfbits-1) <= J(p);
    requires power2(halfbits-1) <= J(q);
    requires J(e) == 65537;
    requires J(pMinus1) == J(p)-1;
    requires J(qMinus1) == J(q)-1;
    requires J(phi_n) == J(pMinus1)*J(qMinus1);
    ensures 1 < power2(halfbits-1)-1;
    ensures power2(halfbits-2) < power2(halfbits-1) - 1;
    ensures power2(halfbits-1) - 1 <= J(pMinus1);
    ensures power2(halfbits-1) - 1 <= J(qMinus1);
    ensures J(e) < J(phi_n);
//-    ensures J(p)*J(q) < Frump();
//-    ensures J(phi_n) < Frump();
    ensures 1 < J(phi_n);
{
    calc {
        1;
            { lemma_power2_0_is_1(); }
        power2(0);
        <    { lemma_power2_strictly_increases(0,halfbits-2); }
        power2(halfbits-2);
        power2(halfbits-2) + power2(halfbits-2) - power2(halfbits-2);
        2*power2(halfbits-2) - power2(halfbits-2);
        //-  { lemma_mul_is_mul_boogie(2, power2(halfbits-2)); }
        //-            mul(2,power2(halfbits-2)) - power2(halfbits-2);
            { reveal_power2(); }
        power2(halfbits-1) - power2(halfbits-2);
        <=    { lemma_power2_strictly_increases(0,halfbits-2); }
        power2(halfbits-1) - power2(0);
            { lemma_power2_0_is_1(); }
        power2(halfbits-1) - 1;
    }

    calc {
        power2(halfbits-2);
        power2(halfbits-2) + power2(halfbits-2) - power2(halfbits-2);
        <    {
            lemma_power2_0_is_1();
                lemma_power2_strictly_increases(0,halfbits-2);
        }
        power2(halfbits-2) + power2(halfbits-2) - 1;
            2*power2(halfbits-2) - 1;
            { reveal_power2(); }
        power2(halfbits-1) - 1;
    }

    calc {
        power2(halfbits-1) - 1;
            <=    //- GenRandomPrime ensures ensures
            J(p) - 1;
            J(pMinus1);
    }

    assert power2(halfbits-1) - 1 <= J(pMinus1);
    calc {
        power2(halfbits-1) - 1;
            <=    //- GenRandomPrime ensures ensures
            J(q) - 1;
            J(qMinus1);
    }
    assert power2(halfbits-1) - 1 <= J(qMinus1);
    assert 1 < power2(halfbits-1) - 1;
        
    calc {
        J(e);
        < 131072;
            { lemma_2toX(); reveal_power2(); }
        power2(17);
        <    { lemma_power2_strictly_increases(17,2*halfbits-4); }
        power2(2*halfbits-4);
        power2(halfbits-2 + halfbits-2);
            { lemma_power2_adds(halfbits-2, halfbits-2); }
        power2(halfbits-2) * power2(halfbits-2);
        <=    { lemma_mul_inequality(power2(halfbits-2), J(pMinus1), power2(halfbits-2)); }
        J(pMinus1) * power2(halfbits-2);
        <=    {
                assert power2(halfbits-2) <= J(qMinus1);
                    lemma_mul_left_inequality(J(pMinus1), power2(halfbits-2), J(qMinus1));
            }
        J(pMinus1) * J(qMinus1);
        J(phi_n);
    }

//-    calc {
//-        J(p) * J(q);
//-        <    { lemma_mul_strict_inequality(
//-                J(p), power2(power2(29)), J(q)); }
//-        power2(power2(29)) * J(q);
//-        <    { lemma_mul_left_inequality(
//-                power2(power2(29)), J(q), power2(power2(29))); }
//-        power2(power2(29)) * power2(power2(29));
//-            { lemma_power2_adds(power2(29), power2(29)); }
//-        power2(power2(29) + power2(29));
//-        power2(2*power2(29));
//-            { reveal_power2(); }
//-        power2(power2(30));
//-        Frump();
//-    }
//-
//-    calc {
//-        J(phi_n);
//-        J(pMinus1) * J(qMinus1);
//-        <    { lemma_mul_strict_inequality(
//-                J(pMinus1), power2(power2(29)), J(qMinus1)); }
//-        power2(power2(29)) * J(qMinus1);
//-        <    { lemma_mul_left_inequality(
//-                power2(power2(29)), J(qMinus1), power2(power2(29))); }
//-        power2(power2(29)) * power2(power2(29));
//-            { lemma_power2_adds(power2(29), power2(29)); }
//-        power2(power2(29) + power2(29));
//-        power2(2*power2(29));
//-            { reveal_power2(); }
//-        power2(power2(30));
//-        Frump();
//-    }

    calc {
        1;
            < J(qMinus1);
            <    {
                assert 1 < J(pMinus1);
                    assert 0 < J(qMinus1);
                    lemma_mul_strictly_increases(J(pMinus1), J(qMinus1));
                    assert J(qMinus1) < J(pMinus1)*J(qMinus1);
            }
        J(pMinus1) * J(qMinus1);
            J(phi_n);
    }
}

static lemma lemma_RSAKeyGen_3(worksheet:RSAKeyGenerationWorksheet, worksheet_row:RSAKeyGenerationWorksheetRow, worksheet':RSAKeyGenerationWorksheet, success:bool)
    requires RSAKeyConsistentWithWorksheet_precondition(worksheet);
    requires RSAKeyGenerationWorksheetValid_Impl(worksheet.keybits, worksheet, false);
    requires RSAKeyGenerationWorksheetRowValid(worksheet.keybits, worksheet_row);
    requires 0 < |worksheet_row.P.rows|;
    requires 0 < |worksheet_row.Q.rows|;
    requires worksheet_row.accepted == success;
    requires RSAKeyConsistentWithWorksheet_precondition(worksheet);
    requires worksheet' == RSAKeyGenerationWorksheetAppend(worksheet, worksheet_row, success);
    requires 1<worksheet'.p;
    requires 1<worksheet'.q;
    ensures RSAKeyConsistentWithWorksheet_precondition(worksheet');
    ensures RSAKeyGenerationWorksheetValid_Impl(worksheet'.keybits, worksheet', success);
{
    lemma_mul_strictly_positive(worksheet'.p-1, worksheet'.q-1);
}

predicate {:heap} RSAKeyGenLoop_requires(keybits:nat, e:array<int>, halfbits:nat, one:array<int>)
    reads one;
    reads e;
    reads this`TPM;
    reads this`IoMemPerm;
{
    true
    && (20<keybits)
    && (WellformedFatNat(one))
    && (J(one) == 1)
    && (WellformedFatNat(e))
    && (J(e) == 65537)
    && (3 < halfbits)
    && (halfbits < power2(32))
    && (keybits <= 2*(halfbits-1))
    && (halfbits == keybits/2+2)
    && (TPM_ready())
}

predicate {:heap} RSAKeyGenLoop_success_properties(
    keybits:nat,
    e:array<int>,
    started:bool,
    p:array<int>,
    q:array<int>,
    d:array<int>,
    n:int,
    worksheet:RSAKeyGenerationWorksheet)
    requires WellformedFatNat(e);
    reads e;
    reads p;
    reads d;
    reads q;
{
    true
    && (WellformedFatNat(p))
    && (WellformedFatNat(q))
    && (WellformedFatNat(d))
    && (n == J(p)*J(q))
    && (n != 0)
    && (power2(keybits) <= n)
    && (((J(p)-1)*(J(q)-1)) != 0)
    && (mul(J(d), J(e)) % ((J(p)-1)*(J(q)-1)) == 1)
    && (started)
    && (worksheet.p == J(p))
    && (worksheet.q == J(q))
}

predicate RSAKeyGenLoop_invariant(
    keybits:nat,
    e:array<int>,
    started:bool,
    success:bool,
    p:array<int>,
    q:array<int>,
    d:array<int>,
    n:int,
    worksheet:RSAKeyGenerationWorksheet,
    oldTPM:TPM_struct,
    curTPM:TPM_struct)
    requires WellformedFatNat(e);
    reads e;
    reads p;
    reads q;
    reads d;
{
    true
    && (success ==> RSAKeyGenLoop_success_properties(keybits, e, started, p, q, d, n, worksheet))
    && (started ==> 0 < |worksheet.rows|)
    && (RSAKeyConsistentWithWorksheet_precondition(worksheet))
    && (RSAKeyGenerationWorksheetValid_Impl(keybits, worksheet, success))
    && (worksheet.keybits == keybits)
    && (RSAKeyGenerationWorksheetConsumesRandoms(worksheet.rows) == worksheet.randoms)
    && (TPMs_match_except_for_randoms(oldTPM, curTPM))
    && (oldTPM.random_index <= curTPM.random_index)
    && (curTPM.random_index == oldTPM.random_index + |worksheet.randoms|)
    && (worksheet.randoms == TPM_random_bytes_premium(oldTPM.random_index, curTPM.random_index))
}

method {:timeLimitMultiplier 2} RSAKeyGenLoop_step(
        keybits:nat,
        e:array<int>,
        halfbits:nat,
        one:array<int>,
        ghost started:bool,
        p:array<int>,
        q:array<int>,
        d:array<int>,
        ghost n:int,
        ghost worksheet:RSAKeyGenerationWorksheet,
        ghost origTPM:TPM_struct)
    returns (
        success':bool,
        p':array<int>,
        q':array<int>,
        d':array<int>,
        ghost n':int,
        ghost worksheet':RSAKeyGenerationWorksheet)
    requires RSAKeyGenLoop_requires(keybits, e, halfbits, one);
    requires RSAKeyGenLoop_invariant(keybits, e, started, false, p, q, d, n, worksheet, origTPM, TPM);
    requires TPM_ready();   
    ensures RSAKeyGenLoop_invariant(keybits, e, true, success', p', q', d', n', worksheet', origTPM, TPM);
    ensures TPM_ready();

    modifies this`TPM;   
    modifies this`IoMemPerm;
{
    ghost var loop_TPM_index := TPM.random_index;
    ghost var p_worksheet, q_worksheet;
    assert TPM_ready();
    p', p_worksheet := GenRandomPrime(halfbits);
    ghost var mid_TPM_index := TPM.random_index;
    q', q_worksheet := GenRandomPrime(halfbits);
//-        assert J(p') < power2(power2(29));
//-        assert J(q') < power2(power2(29));

    assert J(p')!=0;
    assert J(q')!=0;
    n' := J(p')*J(q');
    lemma_mul_nonzero(J(p'), J(q'));
    assert n'!=0;
    
    lemma_RSAKeyGen_1(keybits, halfbits, p', q', n');

    var pMinus1:array<int> := FatNatSub(p',one);
    var qMinus1:array<int> := FatNatSub(q',one);
//-        assert J(pMinus1) < power2(power2(29));
//-        assert J(qMinus1) < power2(power2(29));
    
    var phi_n:array<int> := FatNatMul(pMinus1,qMinus1);

    lemma_RSAKeyGen_2(keybits, halfbits, p', q', n', e, pMinus1, qMinus1, phi_n);

//-        assert J(phi_n) < power2(power2(30)) == Frump();
//-        assert FrumpyBigNat(phi_n);
    
//-        assert J(e) < J(phi_n);
//-        assert FrumpyBigNat(e);
    
    success',d' := MultiplicativeInverse(phi_n, e);
    
    ghost var worksheet_row := RSAKeyGenerationWorksheetRow_c(
        p_worksheet, q_worksheet, success', p_worksheet.randoms + q_worksheet.randoms);

    
    
    /**/ assert TPM.random_index == mid_TPM_index + |q_worksheet.randoms|;
    /**/ assert mid_TPM_index == loop_TPM_index + |p_worksheet.randoms|;
    lemma_random_comprehension(loop_TPM_index, p_worksheet.randoms, q_worksheet.randoms);
    /**/ assert TPM.random_index == loop_TPM_index + |p_worksheet.randoms| + |q_worksheet.randoms|;
    
    worksheet' := RSAKeyGenerationWorksheetAppend(worksheet, worksheet_row, success');
    /**/ assert worksheet.randoms == TPM_random_bytes_premium(origTPM.random_index, loop_TPM_index);
    /**/ assert worksheet.randoms == TPM_random_bytes(origTPM.random_index, origTPM.random_index + |worksheet.randoms|);
    /**/ assert loop_TPM_index + |worksheet_row.randoms| == TPM.random_index;
    /**/ assert TPM_random_bytes(loop_TPM_index, TPM.random_index) == worksheet_row.randoms;
    lemma_random_comprehension(origTPM.random_index, worksheet.randoms, worksheet_row.randoms);
    /**/ assert TPM.random_index == origTPM.random_index + |worksheet'.randoms|;

    ghost var randoms' := worksheet.randoms + worksheet_row.randoms;

    WorksheetAppend_lemma(worksheet, worksheet_row, success', worksheet');
    assert worksheet'.randoms == randoms';

    lemma_RSAKeyGen_3(worksheet, worksheet_row, worksheet', success');

    calc {
        n';
        J(p')*J(q');
    }
}

method RSAKeyGenLoop(keybits:nat, e:array<int>, halfbits:nat, one:array<int>)
    returns (p:array<int>, q:array<int>, d:array<int>, ghost worksheet:RSAKeyGenerationWorksheet, ghost n:int)
    requires RSAKeyGenLoop_requires(keybits, e, halfbits, one);
    
    modifies this`TPM;   
    modifies this`IoMemPerm;

    ensures RSAKeyConsistentWithWorksheet_precondition(worksheet);
    ensures RSAKeyGenerationWorksheetValid_Impl(keybits, worksheet, true);
    ensures worksheet.keybits == keybits;
    ensures RSAKeyGenerationWorksheetConsumesRandoms(worksheet.rows) == worksheet.randoms;
    ensures TPM_ready();
    ensures TPMs_match_except_for_randoms(old(TPM), TPM);
    ensures old(TPM).random_index <= TPM.random_index;
    ensures TPM.random_index == old(TPM).random_index + |worksheet.randoms|;
    ensures worksheet.randoms == TPM_random_bytes_premium(old(TPM).random_index, TPM.random_index);
    ensures 0 < |worksheet.rows|;

    ensures WellformedFatNat(p);
    ensures WellformedFatNat(q);
    ensures WellformedFatNat(d);
    ensures n == J(p)*J(q);
    ensures n != 0;
    ensures power2(keybits) <= n;
    ensures ((J(p)-1)*(J(q)-1)) != 0;
    ensures mul(J(d), J(e)) % ((J(p)-1)*(J(q)-1)) == 1;
    ensures worksheet.p == J(p);
    ensures worksheet.q == J(q);
{
    worksheet := RSAKeyGenerationWorksheet_c(keybits, [], [], 0, 0, 0, 0);
    p := one; //- dafnycc: initialize variable
    q := one; //- dafnycc: initialize variable
    d := one; //- dafnycc: initialize variable

    ghost var started := false;
    var success:bool := false;
    while (!success)
        decreases *;
        invariant RSAKeyGenLoop_invariant(keybits, e, started, success, p, q, d, n, worksheet, old(TPM), TPM);
        invariant TPM_ready();
    {
        success,p,q,d,n,worksheet := RSAKeyGenLoop_step(keybits, e, halfbits, one, started, p, q, d, n, worksheet, old(TPM));
        started := true;
    }
}

lemma lemma_prime_bound(halfbits:nat, wks:CandidatePrimeWorksheet)
    requires 0<halfbits;
    requires CandidatePrimeWorksheetValid(halfbits, wks);
    ensures wks.candidate < power2(halfbits);
{
    calc {
        wks.candidate;
        <=
        wks.raw + power2(halfbits-1);
        <   { lemma_mod_properties(); }
        2*power2(halfbits-1);
            { lemma_power2_1_is_2();
              lemma_mul_is_mul_boogie(2,power2(halfbits-1)); }
        power2(1)*power2(halfbits-1);
            { lemma_power2_adds(1, halfbits-1); }
        power2(halfbits);
    }
}

lemma lemma_key_modulus_bound(keybits:nat, row:RSAKeyGenerationWorksheetRow)
    requires RSAKeyGenerationWorksheetRowValid(keybits, row);
    ensures PrimeGenerationOutput(row.P)*PrimeGenerationOutput(row.Q) < power2(keybits+5);
{
    var halfbits := keybits/2+2;
    var p := PrimeGenerationOutput(row.P);
    var q := PrimeGenerationOutput(row.Q);
    var last_p_row := row.P.rows[|row.P.rows|-1];
    var last_q_row := row.Q.rows[|row.Q.rows|-1];
    calc {
        p * q;
        <   { lemma_prime_bound(halfbits, last_q_row.candidate);
              lemma_mul_strict_inequality_forall();
              lemma_mul_is_commutative_forall(); }
        p * power2(halfbits);
        <   { lemma_prime_bound(halfbits, last_p_row.candidate);
              lemma_mul_strict_inequality_forall(); }
        power2(halfbits) * power2(halfbits);
        power2(keybits/2+2)*power2(keybits/2+2);
            { lemma_power2_adds(keybits/2+2,keybits/2+2); }
        power2(2*(keybits/2)+4);
        <=  { assert 2*(keybits/2) <= keybits;
              lemma_power2_increases(2*(keybits/2)+4, keybits+1+4); }
        power2(keybits+1+4);
    }
}

//-lemma lemma_modulus_length_acceptable(keybits:nat, N:array<int>, wks:RSAKeyGenerationWorksheet)
//-    requires keybits<power2(28);
//-    requires WellformedFatNat(N);
//-    requires J(N) == wks.p * wks.q;
//-    requires RSAKeyGenerationWorksheetValid(keybits, wks);
//-    ensures |N.words| < power2(25);
//-{
//-    var row := wks.rows[|wks.rows|-1];
//-    lemma_key_modulus_bound(keybits, row);
//-    lemma_2toX32();
//-    calc {
//-        power2(29);
//-        32*power2(24);
//-        < 32*(power2(25)-1);
//-    }
//-    calc {
//-        I(N);
//-        wks.p * wks.q;
//-        PrimeGenerationOutput(row.P)*PrimeGenerationOutput(row.Q);
//-        <
//-        power2(keybits+5);
//-        <=  { lemma_2toX32();
//-              lemma_power2_increases(keybits+5, power2(29)); }
//-        power2(power2(29));
//-    }
//-    lemma_keybits_implies_length25(N);
//-}

method RSAKeyGen_internal(keybits:nat) returns (key:RSAKeyPairImpl_internal)
    requires 20<keybits;
    requires keybits<power2(28);

    requires TPM_ready();
    ensures TPM_ready();
    modifies this`TPM;   
    modifies this`IoMemPerm;
    ensures TPMs_match_except_for_randoms(old(TPM), TPM);
    ensures old(TPM).random_index <= TPM.random_index;

    //    ensures ValidKeyLength(key);    
    ensures WellformedRSAKeyPairImpl_internal(key);
    ensures J(key.pub.n) >= power2(keybits);
    ensures key.pub.size >= keybits / 8;
    ensures RSAKeyGenerationValid(keybits, KeyPairImplToSpec_internal(key), TPM_random_bytes_premium(old(TPM).random_index, TPM.random_index));
{
    lemma_2to32();
    var one := MakeBELiteralArray(1);
    var e, halfbits;
    lemma_power2_increases(28, 29);
    e,halfbits := RSAKeyGenSetup(keybits);

    var p:array<int>, q:array<int>, d:array<int>;
    ghost var worksheet:RSAKeyGenerationWorksheet;
    ghost var n:int;
    lemma_power2_increases(28, 32);
    p, q, d, worksheet, n := RSAKeyGenLoop(keybits, e, halfbits, one);

    var N:array<int> := FatNatMul(p, q);
    assert J(N)==n;
//-    assert FrumpyBigNat(N);
    assert J(N)!=0;
    
    var size := ComputeKeySize(N);
    var nReciprocal := FatNatComputeReciprocal(N);
    var recip_ref := if nReciprocal.FNDivKnownReciprocal? then nReciprocal.TwoTo32wDividedByD else p; //- do something real to nReciprocal.TwoTo32wDividedByD
    key := RSAKeyPairImpl_c_internal(RSAPubKeyImpl_c_internal(N, size, e, nReciprocal), d);

    if (key.pub.size < keybits/8)
    {
        calc {
            power2(keybits);
                <= J(key.pub.n);
                < power2(8 * key.pub.size);
                < { lemma_power2_strictly_increases(8 * key.pub.size, 8 * (keybits / 8)); }
                power2(8 * (keybits / 8));
                <= { lemma_power2_increases(8 * (keybits / 8), keybits); }
                power2(keybits);
        }
        assert false;
    }

//-    lemma_modulus_length_acceptable(keybits, N, worksheet);
    assert WellformedFatNat(key.d);
    assert WellformedRSAKeyPairImpl_internal(key);
    assert RSAKeyGenerationWorksheetConsumesRandoms(worksheet.rows) == worksheet.randoms;
    assert RSAKeyGenerationWorksheetValid(keybits, worksheet);
    assert RSAKeyConsistentWithWorksheet(keybits, KeyPairImplToSpec_internal(key), worksheet);
    assert RSAKeyGenerationValid(keybits, KeyPairImplToSpec_internal(key), worksheet.randoms);
}

method GenDummyKey_internal() returns (key_pair:RSAKeyPairImpl_internal)
    //- used when dafnycc requires that we initialize a variable
{
    var zilch := MakeBELiteralArray(0);
    key_pair := RSAKeyPairImpl_c_internal(RSAPubKeyImpl_c_internal(zilch, 0, zilch, FNDivUnknownReciprocal()), zilch);
}

method MakeNullKey(bits:nat) returns (key:RSAKeyPairImpl_internal)
requires Word32(bits);
{
    var n := FatPower2(bits);
    lemma_2to32();
    var one := MakeBELiteralArray(1);
    key := RSAKeyPairImpl_c_internal(RSAPubKeyImpl_c_internal(n, 1, one, FNDivUnknownReciprocal()), one);
}
