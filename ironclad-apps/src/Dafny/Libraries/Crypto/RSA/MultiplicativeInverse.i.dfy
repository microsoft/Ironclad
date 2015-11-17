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


static function K(x:seq<int>) : int
    requires IsWordSeq(x);
{
    BEWordSeqToInt(x)
}


lemma lemma_MultiplicativeInverse(phi:seq<int>, e:seq<int>, d:seq<int>, k_num:int, d_num:int, gcd:int)
    requires IsWordSeq(phi);
    requires IsWordSeq(e);
    requires IsWordSeq(d);
    requires gcd == K(phi)*k_num + K(e)*d_num;
    requires 1 == gcd;
    requires 0 <= K(e);
    requires 0 <= 1 < K(phi);
    requires d_num <= K(phi);
    requires is_gcd(K(phi), K(e), gcd);
    requires K(d) == if d_num < 0 then d_num + K(phi) else d_num;
    
    ensures K(d) <= K(phi);
    ensures mul(K(d), K(e)) % K(phi) == 1;
    ensures is_gcd(K(phi),K(e),1);
{
    calc {
        1;
            
        gcd;
        K(phi)*k_num + K(e)*d_num + 0*K(phi);
            { lemma_mul_is_mul_boogie(0, K(phi)); }
        K(phi) * k_num + K(e) * d_num + mul(0, K(phi));
    }
    
    lemma_mul_basics_forall();
    assert K(phi) * k_num + K(e) * d_num == mul(0, K(phi)) + 1;
    lemma_fundamental_div_mod_converse(
            K(phi) * k_num + K(e) * d_num,
            K(phi),
            0,
            1);
    assert (K(phi) * k_num + K(e) * d_num) % K(phi) == 1;
    
    calc ==> {
        true;
        (K(phi) * k_num + K(e) * d_num) % K(phi) == 1;
        { lemma_mod_multiples_vanish(k_num, K(e) * d_num, K(phi)); }
        (K(e) * d_num) % K(phi) == 1;
        { lemma_mul_is_commutative_forall(); }
        (d_num * K(e)) % K(phi) == 1;
    }


    if (0 <= d_num)
    {
        calc {
            K(d);
            d_num;
            <= K(phi);
        }
    }
    else
    {
        
        calc {
            1;
            (d_num*K(e)) % K(phi);
                { lemma_mod_multiples_vanish(K(e), d_num*K(e), K(phi)); }
            (K(phi)*K(e) + d_num*K(e)) % K(phi);
                { lemma_mul_is_commutative_forall(); }
            (d_num*K(e) + K(e) * K(phi)) % K(phi);
                { lemma_mul_is_commutative_forall(); }
            (d_num*K(e) + K(phi) * K(e)) % K(phi);
                { lemma_mul_is_distributive_forall(); }
            ((d_num + K(phi)) * K(e)) % K(phi);
//-            (FIV(d_prime)*K(e)) % K(phi);
            (K(d)*K(e)) % K(phi);
        }
    
//-        assert WellformedFatInt(d_prime);
        
        calc {
            K(d);
//-                FIV(d_prime);
            d_num+K(phi);
            <= K(phi);
        }
    }
}

method {:timeLimitMultiplier 3} MultiplicativeInverse(phi:array<int>, e:array<int>) returns (success:bool, d:array<int>)
    requires WellformedFatNat(phi);
    requires 1<J(phi);
    requires WellformedFatNat(e);
    requires J(e) < J(phi);
    requires 0<J(phi);
    ensures success ==> WellformedFatNat(d);
    ensures success ==> J(d) <= J(phi);
    ensures success ==> mul(J(d), J(e)) % J(phi) == 1;
    ensures success <==> is_gcd(J(phi),J(e),1);
{
//-    lemma_frumpy_is_modest(phi);
//-    lemma_frumpy_is_modest(e);
    ghost var phi_seq := phi[..];
    ghost var phi_v := K(phi_seq);
    ghost var e_seq := e[..];
    ghost var e_v := K(e_seq);
    assert IsWordSeq(e_seq);
    var k_num:FatInt,d_num:FatInt := Extended_gcd(phi,e);
    var k_ref := k_num.value; //- do something real to k_num.value so dafnycc realizes it's allocated
    var d_ref := d_num.value; //- do something real to d_num.value so dafnycc realizes it's allocated

    ghost var k_num_v := FIV(k_num);
    ghost var d_num_v := FIV(d_num);
//-    ghost var k_num_s := k_num.value[..];

    assert WellformedFatInt(k_num);
    assert WellformedFatInt(d_num);
    
    var phik:FatInt := FatIntMul(FatInt_ctor(false, phi),k_num);
    var phik_ref := phik.value; //- do something real to phik.value so dafnycc realizes it's allocated
    ghost var phik_v := FIV(phik);
    assert phi_seq==phi[..];    //- OBSERVE array
    var ed:FatInt := FatIntMul(FatInt_ctor(false, e),d_num);
    var ed_ref := ed.value; //- do something real to ed.value so dafnycc realizes it's allocated
    assert phi_seq==phi[..];    //- OBSERVE array
    ghost var ed_v := FIV(ed);
    var gcd:FatInt := FatIntAdd(phik,ed);
    var gcd_ref := gcd.value; //- do something real to gcd.value so dafnycc realizes it's allocated
    assert phi_seq==phi[..];    //- OBSERVE array
    ghost var gcd_v := FIV(gcd);
    calc {
        gcd_v;
        phik_v+ed_v;
        phi_v*k_num_v + e_v*d_num_v;
    }
    assert WellformedFatInt(k_num);
    
    lemma_2toX();
    var one := MakeSmallLiteralFatInt(1);
    var one_ref := one.value; //- do something real to one.value so dafnycc realizes it's allocated
    var sane_gcd:bool := FatIntEq(gcd, one);
    assert WellformedFatInt(k_num);
    if (sane_gcd)
    {
        success := true;
    }
    else
    {
        success := false;
    }

    if (success)
    {
        if (!d_num.negate)
        {
            d := d_num.value;
            assert WellformedFatNat(d);
//-            assert phi_seq==phi[..];    //- OBSERVE array
        }
        else
        {
            var d_prime:FatInt := FatIntAdd(d_num, FatInt_ctor(false, phi));
            var dprime_ref := d_prime.value; //- do something real to d_prime.value so dafnycc realizes it's allocated
//-            assert phi_seq==phi[..];    //- OBSERVE array
            assert 0<=FIV(d_prime);
            d := d_prime.value;
            assert FIV(d_prime) == J(d);
            assert WellformedFatNat(d);
        }

        assert FIV(gcd)==gcd_v==phi_v*k_num_v + e_v*d_num_v;
        assert phi_seq==phi[..];    //- OBSERVE array
        assert phi_v==K(phi_seq);
        assert e_v==K(e[..]);
        assert k_num_v==FIV(k_num);
        assert d_num_v==FIV(d_num);
        assert e_seq==e[..];
        lemma_MultiplicativeInverse(phi[..], e[..], d[..], FIV(k_num), FIV(d_num), FIV(gcd));
        calc {
            mul(J(d), J(e)) % J(phi);
            mul(K(d[..]), K(e[..])) % K(phi[..]);
            1;
        }
        calc ==> {
            true;
            is_gcd(K(phi[..]),K(e[..]),1);
            is_gcd(J(phi),J(e),1);
        }
    }
    else
    {
        //- dafnycc: initialize variables
        d := e;
        assert WellformedFatNat(d);
    }
}
