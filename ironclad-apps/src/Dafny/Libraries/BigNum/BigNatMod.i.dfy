include "BigNatDiv.i.dfy"
include "BigNatBitCount.i.dfy"
include "../Math/power.i.dfy"

method BigNatModulo(N:BigNat, M:BigNat) returns (R:BigNat)
    requires ModestBigNatWords(N);
    requires ModestBigNatWords(M);
    requires 0 <= I(N);
    requires 0 < I(M);
    ensures WellformedBigNat(R);
    ensures I(N) % I(M) == I(R);
    ensures I(R) < I(M);
    ensures ModestBigNatWords(R);
{
    var Q:BigNat;
    Q,R := BigNatDiv(N,M);

    lemma_fundamental_div_mod_converse(I(N), I(M), I(Q), I(R));

    assert I(R)<I(M);
    lemma_modesty_word_value_equivalence(M);
    lemma_modesty_word_value_equivalence(R);
    assert ModestBigNatWords(R);
}

method BigNatModExp(B:BigNat, E:BigNat, M:BigNat) returns (R:BigNat)
    requires FrumpyBigNat(B);
    requires FrumpyBigNat(E);
    requires FrumpyBigNat(M);
    requires !zero(B);
    requires !zero(M);
    requires 1 < I(M);
    ensures WellformedBigNat(R);
    ensures power(I(B),I(E)) % I(M) == I(R);
    ensures I(R) < I(M);
{
    //-ProfileTally(Tally_BigNatModExpCalls(), 1);

    lemma_2toX32();
    lemma_mul_basics_forall();
    lemma_frumpy_is_modest(B);
    lemma_frumpy_is_modest(E);
    lemma_frumpy_is_modest(M);

    var one:BigNat := MakeSmallLiteralBigNat(1);
    assert BitCount(one, 1);

    var ec:nat := BigNatCountBits(E);
    var bp2:nat := ec;
    var E1:BigNat := E;
    R := one;
    lemma_1_power(power2(bp2));

    while (bp2 != 0)
        decreases bp2;
        invariant 0 <= bp2 <= ec;
        invariant FrumpyBigNat(E1);
        invariant FrumpyBigNat(R);
        invariant I(E1) < power2(bp2);
        invariant I(R) < I(M);
        invariant (power(I(B),I(E1)) * power(I(R),power2(bp2))) % I(M) == power(I(B),I(E)) % I(M);
    {
        //-ProfileTally(Tally_BigNatModExpWhileLoops(), 1);
        
        lemma_power_positive(I(B),power2(ec-bp2));
        bp2 := bp2 - 1;

        var R_squared:BigNat := BigNatMul(R, R);
        lemma_frumpy_squared_is_modest(R, R_squared);
        R_squared := BigNatModulo(R_squared, M);

        var E2:BigNat,oc:nat := BigNatBitShift_(one, 1, bp2);
        calc {
            I(E2);
            power2(bp2) * I(one);
            power2(bp2) * 1;
                { lemma_mul_basics_forall(); }
            power2(bp2);
        }

        var E_sub:BigNat;
        var use_this_product:bool := BigNatGe(E1, E2);
        if (use_this_product)
        {
            E_sub := BigNatSub(E1, E2);

            assert I(E_sub) <= I(E1);
            assert FrumpyBigNat(E_sub);

            calc {
                I(E_sub);
                I(E1) - I(E2);
                I(E1) - power2(bp2);
                <
                power2(bp2+1) - power2(bp2);
                    { reveal_power2(); }
                2*power2(bp2) - power2(bp2);
                power2(bp2);
            }

            var R_big:BigNat := BigNatMul(R_squared, B);
            lemma_frumpy_product_is_modest(R_squared, B, R_big);
            lemma_mod_properties();
            calc {
                (power(I(B),I(E_sub)) * power(I(R_big) % I(M),power2(bp2))) % I(M);
                (power(I(B),I(E1)-power2(bp2)) * (power((I(R)*I(R) % I(M))*I(B) % I(M),power2(bp2)))) % I(M);
                    { lemma_mul_mod_noop_general(power(I(B),I(E1)-power2(bp2)), power((I(R)*I(R) % I(M))*I(B) % I(M),power2(bp2)), I(M)); }
                (power(I(B),I(E1)-power2(bp2)) * (power((I(R)*I(R) % I(M))*I(B) % I(M),power2(bp2)) % I(M))) % I(M);
                calc {
                    power(I(R_big) % I(M),power2(bp2)) % I(M);
                    power((I(R)*I(R) % I(M))*I(B) % I(M),power2(bp2)) % I(M);
                        { lemma_mul_mod_noop_general(I(R)*I(R), I(B), I(M)); }
                    power(I(R)*I(R)*I(B) % I(M),power2(bp2)) % I(M);
                        { lemma_power_mod_noop(I(R)*I(R)*I(B), power2(bp2), I(M)); }
                    power(I(R)*I(R)*I(B),power2(bp2)) % I(M);
                        { lemma_power_distributes(I(R)*I(R), I(B), power2(bp2)); }
                    power(I(R)*I(R),power2(bp2)) * power(I(B),power2(bp2)) % I(M);
                        { lemma_square_is_power_2(I(R)); }
                    power(power(I(R),2),power2(bp2)) * power(I(B),power2(bp2)) % I(M);
                        { lemma_power_multiplies(I(R), 2, power2(bp2)); }
                    power(I(R),2*power2(bp2)) * power(I(B),power2(bp2)) % I(M);
                        { reveal_power2(); }
                    power(I(R),power2(bp2+1)) * power(I(B),power2(bp2)) % I(M);
                }
                { assert (power((I(R)*I(R) % I(M))*I(B) % I(M),power2(bp2)) % I(M)) == (power(I(R),power2(bp2+1)) * power(I(B),power2(bp2)) % I(M)); }
                (power(I(B),I(E1)-power2(bp2)) * ((power(I(R),power2(bp2+1)) * power(I(B),power2(bp2))) % I(M))) % I(M);
                    { lemma_mul_mod_noop_general(power(I(B),I(E1)-power2(bp2)), power(I(R),power2(bp2+1)) * power(I(B),power2(bp2)), I(M)); }
                (power(I(B),I(E1)-power2(bp2)) * (power(I(R),power2(bp2+1)) * power(I(B),power2(bp2)))) % I(M);
                    { lemma_mul_is_associative_forall(); lemma_mul_is_commutative_forall(); }
                (power(I(B),I(E1)-power2(bp2)) * power(I(B),power2(bp2)) * power(I(R),power2(bp2+1))) % I(M);
                    { lemma_power_adds(I(B), I(E1)-power2(bp2), power2(bp2)); }
                (power(I(B),I(E1)) * power(I(R),power2(bp2+1))) % I(M);
                power(I(B),I(E)) % I(M);
            }
            R := BigNatModulo(R_big, M);
        }
        else
        {
            E_sub := E1;
            calc {
                I(E_sub);
                I(E1);
                < I(E2);
                power2(bp2);
            }
            calc {
                (power(I(B),I(E1)) * power(I(R_squared),power2(bp2))) % I(M);
                    { lemma_mul_mod_noop_general(power(I(B),I(E1)), power(I(R_squared),power2(bp2)), I(M)); }
                (power(I(B),I(E1)) * (power(I(R_squared),power2(bp2)) % I(M))) % I(M);
                calc {
                    power(I(R_squared),power2(bp2)) % I(M);
                    power(I(R)*I(R) % I(M),power2(bp2)) % I(M);
                        { lemma_power_mod_noop(I(R)*I(R), power2(bp2), I(M)); }
                    power(I(R)*I(R),power2(bp2)) % I(M);
                        { lemma_square_is_power_2(I(R)); }
                    power(power(I(R),2),power2(bp2)) % I(M);
                        { lemma_power_multiplies(I(R), 2, power2(bp2)); }
                    power(I(R),2*power2(bp2)) % I(M);
                        { reveal_power2(); }
                    power(I(R),power2(bp2+1)) % I(M);
                }
                { assert (power(I(R_squared),power2(bp2)) % I(M)) == (power(I(R),power2(bp2+1)) % I(M)); }
                (power(I(B),I(E1)) * (power(I(R),power2(bp2+1)) % I(M))) % I(M);
                    { lemma_mul_mod_noop_general(power(I(B),I(E1)), power(I(R),power2(bp2+1)), I(M)); }
                (power(I(B),I(E1)) * power(I(R),power2(bp2+1))) % I(M);
                power(I(B),I(E)) % I(M);
            }
            R := R_squared;
        }
        E1 := E_sub;
    }

    calc {
        power(I(B),I(E)) % I(M);
        //- loop invariant
        (power(I(B),I(E1)) * power(I(R),power2(bp2))) % I(M);
        //- loop termination
        (power(I(B),0) * power(I(R),power2(0))) % I(M);
        { lemma_power_0(I(B)); lemma_power_1(I(R)); }
        (1 * I(R)) % I(M);
        I(R) % I(M);
        { lemma_small_mod(I(R), I(M)); }
        I(R);
    }
}
