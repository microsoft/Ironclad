include "../../Services/SHT/AppInterface.i.dfy"

module SHT__Keys_i {
import opened AppInterface_i`All

predicate method KeyLe(ka:Key, kb:Key) {
    ka == kb || KeyLt(ka, kb)
}

lemma KeyAntisymmetry(ka:Key, kb:Key)
    ensures KeyLt(ka,kb) ==> !KeyLe(kb,ka);
    ensures !KeyLt(ka,kb) ==> KeyLe(kb,ka);
    ensures KeyLe(ka,kb) ==> !KeyLt(kb,ka);
    ensures !KeyLe(ka,kb) ==> KeyLt(kb,ka);
{
    lemma_KeyOrdering();
}

lemma KeyEq(ka:Key, kb:Key)
    requires ka==kb;
    ensures KeyLe(ka, kb);
    ensures KeyLe(kb, ka);
{
}

lemma KeyReflexivity(ka:Key, kb:Key)
    requires KeyLe(ka, kb);
    requires KeyLe(kb, ka);
    ensures ka==kb;
{
    lemma_KeyOrdering();
}

lemma KeyTransitivityLe(ka:Key, kb:Key, kc:Key)
    requires KeyLe(ka,kb) && KeyLe(kb,kc);
    ensures KeyLe(ka,kc);
{
    lemma_KeyOrdering();
}

lemma KeyTransitivity(ka:Key, kb:Key, kc:Key)
    ensures KeyLt(ka,kb) && KeyLe(kb,kc) ==> KeyLt(ka,kc);
    ensures KeyLe(ka,kb) && KeyLt(kb,kc) ==> KeyLt(ka,kc);
    ensures KeyLt(ka,kb) && KeyLt(kb,kc) ==> KeyLt(ka,kc);
    ensures KeyLe(ka,kb) && KeyLe(kb,kc) ==> KeyLe(ka,kc);
{
    lemma_KeyOrdering();
}

//////////////////////////////////////////////////////////////////////////////
// KeyPlus creates lower and upper bounds for keys
    
datatype KeyPlus = KeyZero() | KeyPlus(k:Key) | KeyInf()

predicate method KeyPlusLt(kp:KeyPlus, kp':KeyPlus) {
    kp != kp' &&
    match kp {
        case KeyZero => true
        case KeyInf  => false 
        case KeyPlus(k) => 
            match kp' {
                case KeyZero => false
                case KeyInf  => true
                case KeyPlus(k') => KeyLt(k, k')
            }
    }
}

predicate method KeyPlusLe(kp:KeyPlus, kp':KeyPlus) {
    kp == kp' || KeyPlusLt(kp, kp')
}

lemma KeyPlusAntisymmetry(ka:KeyPlus, kb:KeyPlus)
    ensures KeyPlusLt(ka,kb) ==> !KeyPlusLe(kb,ka);
    ensures !KeyPlusLt(ka,kb) ==> KeyPlusLe(kb,ka);
    ensures KeyPlusLe(ka,kb) ==> !KeyPlusLt(kb,ka);
    ensures !KeyPlusLe(ka,kb) ==> KeyPlusLt(kb,ka);
{
    if ka.KeyPlus? && kb.KeyPlus? {
        KeyAntisymmetry(ka.k, kb.k);
    }
}


lemma KeyPlusTransitivity(ka:KeyPlus, kb:KeyPlus, kc:KeyPlus)
    ensures KeyPlusLt(ka,kb) && KeyPlusLe(kb,kc) ==> KeyPlusLt(ka,kc);
    ensures KeyPlusLe(ka,kb) && KeyPlusLt(kb,kc) ==> KeyPlusLt(ka,kc);
    ensures KeyPlusLt(ka,kb) && KeyPlusLt(kb,kc) ==> KeyPlusLt(ka,kc);
    ensures KeyPlusLe(ka,kb) && KeyPlusLe(kb,kc) ==> KeyPlusLe(ka,kc);
{
    lemma_KeyOrdering();
}

//////////////////////////////////////////////////////////////////////////////
// KeyRanges
    
datatype KeyRange = KeyRange(klo:KeyPlus, khi:KeyPlus)
    // range includes all keys klo <= k < khi

predicate method KeyRangeContains(range:KeyRange, kp:KeyPlus) {
    KeyPlusLe(range.klo, kp) && KeyPlusLt(kp, range.khi)
}

predicate RangesOverlap(kra:KeyRange, krb:KeyRange) {
       KeyRangeContains(kra, krb.klo)
    || KeyRangeContains(kra, krb.khi)
    || KeyRangeContains(krb, kra.klo)
    || KeyRangeContains(krb, kra.khi)   // Redundant, but adds symmetry
}

function CompleteRange() : KeyRange
{
    KeyRange(KeyZero(), KeyInf())
}

predicate method EmptyKeyRange(kr:KeyRange)
{
    KeyPlusLe(kr.khi, kr.klo)
}

lemma lemma_EmptyKeyRange(kr:KeyRange)
    ensures EmptyKeyRange(kr) <==> !KeyPlusLt(kr.klo, kr.khi);
{
    KeyPlusAntisymmetry(kr.klo, kr.khi);
}

} 
