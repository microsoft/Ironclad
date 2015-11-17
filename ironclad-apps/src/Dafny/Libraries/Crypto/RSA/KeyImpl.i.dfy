include "RSASpec.s.dfy"
include "../../FatNat/FatNatCommon.i.dfy"
include "../../FatNat/FatNatReciprocal.i.dfy"

datatype RSAPubKeyImpl_internal = RSAPubKeyImpl_c_internal(
    n:array<int>,    //- modulus
    size:nat,
    e:array<int>,     //- public key exponent
    nReciprocal:FNDivReciprocal
    );

predicate {:heap} WellformedRSAPubKeyImpl_internal(pub:RSAPubKeyImpl_internal)
    reads pub.n;
    reads pub.e;
    reads if pub.nReciprocal.FNDivKnownReciprocal? then pub.nReciprocal.TwoTo32wDividedByD else pub.n;
{
//-    FrumpyBigNat(pub.n)
    true
    && WellformedFatNat(pub.n)
    && WellformedFatNat(pub.e)
//-    && pub.n.Length < power2(25)    //- transitional, while converting to FatNats
    && 0<J(pub.n)
//-    && FrumpyBigNat(pub.e)
    && KeyModulusMatchesSizeInBytes(J(pub.n), pub.size)
    && FNDivReciprocalValid(pub.nReciprocal, pub.n)
}

datatype RSAKeyPairImpl_internal = RSAKeyPairImpl_c_internal(
    pub:RSAPubKeyImpl_internal,
    d:array<int>     //- private key exponent
    );

predicate {:heap} WellformedRSAKeyPairImpl_internal(p:RSAKeyPairImpl_internal)
    reads p.pub.n;
    reads p.pub.e;
    reads p.d;
    reads if p.pub.nReciprocal.FNDivKnownReciprocal? then p.pub.nReciprocal.TwoTo32wDividedByD else p.pub.n;
{
    WellformedRSAPubKeyImpl_internal(p.pub)
    && WellformedFatNat(p.d)
//-    && FrumpyBigNat(p.d)
}

function {:heap} PubKeyImplToSpec_internal(pubkey:RSAPubKeyImpl_internal) : RSAPubKeySpec
    requires WellformedRSAPubKeyImpl_internal(pubkey);
    reads pubkey.n;
    reads pubkey.e;
    reads if pubkey.nReciprocal.FNDivKnownReciprocal? then pubkey.nReciprocal.TwoTo32wDividedByD else pubkey.n;
{
    RSAPublicKeySpec_c(J(pubkey.n), pubkey.size, J(pubkey.e))
}

function {:heap} KeyPairImplToSpec_internal(key:RSAKeyPairImpl_internal) : RSAKeyPairSpec
    requires WellformedRSAKeyPairImpl_internal(key);
    reads key.d;
    reads key.pub.n;
    reads key.pub.e;
    reads if key.pub.nReciprocal.FNDivKnownReciprocal? then key.pub.nReciprocal.TwoTo32wDividedByD else key.pub.n;
{
    RSAKeyPairSpec_c(PubKeyImplToSpec_internal(key.pub), J(key.d))
}

lemma {:heap} lemma_WellformedPubKeyImplImpliesWellformedPubKeySpec (pubkey:RSAPubKeyImpl_internal)
    requires WellformedRSAPubKeyImpl_internal(pubkey);
    ensures WellformedRSAPubKeySpec(PubKeyImplToSpec_internal(pubkey));
{
}
