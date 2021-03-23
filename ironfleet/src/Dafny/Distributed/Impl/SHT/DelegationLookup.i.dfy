include "Delegations.i.dfy"

module DelegationLookup_i {
import opened Native__NativeTypes_s
import opened Native__Io_s
import opened Impl__Delegations_i
import opened SHT__Keys_i
import opened Common__NodeIdentity_i
import opened AppInterface_i`Spec
import opened SHT__Delegations_i

function min(x:int, y:int) : int { if x < y then x else y }

predicate InBounds(i:int, low:int, high:int, len:int)
{
    low <= i < min(high, len)
}

lemma lemma_CDM_NoLowsAreInfinite(m:CDelegationMap)
    requires CDelegationMapIsValid(m);
    ensures  forall i :: 0 <= i < |m.lows| ==> !m.lows[i].klo.KeyInf?;
{
    forall i | 0 <= i < |m.lows|
        ensures !m.lows[i].klo.KeyInf?;
    {
        if m.lows[i].klo.KeyInf? {
            CDelegationMapIsSortedExtension(m);
            var last := |m.lows| - 1;
            if i == last {
                assert KeyPlusLt(m.lows[i].klo, KeyInf());
            } else {
                assert KeyPlusLt(m.lows[i].klo, m.lows[last].klo);
                KeyPlusTransitivity(m.lows[i].klo, m.lows[last].klo, KeyInf());
            }
            KeyPlusAntisymmetry(m.lows[i].klo, KeyInf());
            assert false;
        }
    }
}

lemma CDM_IndexForKey_Ordering_specific(m:CDelegationMap, k1:KeyPlus, k2:KeyPlus)
    requires CDelegationMapIsValid(m);
    requires KeyPlusLe(k1, k2);
    ensures  CDM_IndexForKey(m, k1) <= CDM_IndexForKey(m, k2);
{
    CDM_IndexForKey_Ordering(m);
}


method DelegateForKeyRangeIsHostImpl(m:CDelegationMap, kr:KeyRange, id:EndPoint) returns (b:bool)
    requires CDelegationMapIsValid(m);
    requires EndPointIsAbstractable(id);
    ensures  b == DelegateForKeyRangeIsHost(AbstractifyCDelegationMapToDelegationMap(m), kr, AbstractifyEndPointToNodeIdentity(id));
{
    if EmptyKeyRange(kr) {
        b := true;
        forall k | KeyRangeContains(kr, KeyPlus(k))
            ensures false;
        {
            assert KeyPlusLe(kr.klo, KeyPlus(k));
            assert KeyPlusLt(KeyPlus(k), kr.khi);
            assert KeyPlusLe(kr.khi, kr.klo);
            KeyPlusTransitivity(kr.klo, KeyPlus(k), kr.khi);
            assert KeyPlusLt(kr.klo, kr.khi);
            KeyPlusAntisymmetry(kr.klo, kr.khi);
        }
        return;
    } 

    var k_min := KeyMin();
    if kr.klo.KeyZero? && kr.khi == KeyPlus(k_min) {
        forall k | KeyRangeContains(kr, KeyPlus(k))
            ensures false;
        {
            assert KeyPlusLe(kr.khi, KeyPlus(k));
            KeyPlusAntisymmetry(kr.khi, KeyPlus(k));
        }
       return true;
    }

    var m' := CDM_Defragment(m);

    var lo_index := CDM_IndexForKey(m', kr.klo);
    var hi_index := CDM_IndexForKey(m', kr.khi);

    forall () ensures lo_index <= hi_index;
    {
        KeyPlusAntisymmetry(kr.klo, kr.khi);
        CDM_IndexForKey_Ordering_specific(m', kr.klo, kr.khi);
    }

    var index := lo_index;
    ghost var witness_key := kr.klo;
    assert KeyPlusLe(kr.klo, witness_key);
    KeyPlusAntisymmetry(kr.klo, kr.khi);    // ==>
    assert KeyPlusLt(witness_key, kr.khi);
    while index <= hi_index 
        invariant lo_index <= index <= hi_index + 1;
        invariant forall i {:trigger InBounds(i, lo_index as int, index as int, |m'.lows|)} :: 
                    InBounds(i, lo_index as int, index as int, |m'.lows|) ==> m'.lows[i].id == id;
        invariant !witness_key.KeyInf?;
        invariant KeyRangeContains(kr, witness_key);
        invariant index <= hi_index ==> CDM_IndexForKey(m', witness_key) == index;
    {
        if m'.lows[index].id != id {
            b := false;

            forall () ensures AbstractifyEndPointToNodeIdentity(m'.lows[index].id) != AbstractifyEndPointToNodeIdentity(id) 
            {
                if AbstractifyEndPointToNodeIdentity(m'.lows[index].id) == AbstractifyEndPointToNodeIdentity(id) {
                   lemma_AbstractifyEndPointToNodeIdentity_injective(m'.lows[index].id, id);
                   assert false;
                }
            }
            if !witness_key.KeyZero? {
                assert !DelegateForKeyRangeIsHost(AbstractifyCDelegationMapToDelegationMap(m'), kr, AbstractifyEndPointToNodeIdentity(id));
            } else {
                assert kr.klo.KeyZero?;
                assert !kr.khi.KeyZero? && kr.khi != KeyPlus(k_min);
                forall () ensures index == 0;
                {
                    assert KeyRangeContains(CDM_IndexToKeyRange(m', 0), witness_key);
                    CDM_Partitioned(m', witness_key, 0);
                    if index != 0 {
                        assert CDM_IndexForKey(m', witness_key) != 0;
                        assert KeyRangeContains(CDM_IndexToKeyRange(m', index as int), witness_key);
                        assert false;
                    }
                    assert index == 0;  // Because witness_key is 0, it can only be contained from below by the 0th mapping
                }
                if |m'.lows| == 1 {
                    assert KeyRangeContains(kr, KeyPlus(k_min));
                    assert AbstractifyCDelegationMapToDelegationMap(m')[k_min] != AbstractifyEndPointToNodeIdentity(id);
                } else {
                    assert m'.lows[1].klo != KeyPlus(k_min);
                    assert KeyPlusLt(KeyPlus(k_min), m'.lows[1].klo);
                    assert KeyRangeContains(kr, KeyPlus(k_min));
                    assert KeyRangeContains(CDM_IndexToKeyRange(m', 0), KeyPlus(k_min));
                    calc ==> {
                        true;
                            { CDM_Partitioned(m', KeyPlus(k_min), 0); }
                        CDM_IndexForKey(m', KeyPlus(k_min)) == 0; 
                    }
                    assert AbstractifyCDelegationMapToDelegationMap(m')[k_min] != AbstractifyEndPointToNodeIdentity(id);
                }
                assert b == DelegateForKeyRangeIsHost(AbstractifyCDelegationMapToDelegationMap(m'), kr, AbstractifyEndPointToNodeIdentity(id));
            }
            return;
        }
        ghost var old_index := index;
        index := index + 1;
        if index <= hi_index {
            ghost var old_witness := witness_key;
            witness_key := m'.lows[index].klo;
            lemma_CDM_NoLowsAreInfinite(m');
            //CDM_IndexForKey_Ordering_specific(m');

            assert KeyPlusLe(kr.klo, old_witness);
            assert CDM_IndexForKey(m', old_witness) == old_index;
            assert KeyPlusLt(old_witness, m'.lows[old_index + 1].klo);
            assert KeyPlusLe(m'.lows[old_index+1].klo, witness_key);
            KeyPlusTransitivity(kr.klo, old_witness, m'.lows[old_index + 1].klo);
            KeyPlusTransitivity(kr.klo, m'.lows[old_index + 1].klo, witness_key);
            assert KeyPlusLe(kr.klo, witness_key);

            if index < hi_index {
                assert KeyPlusLt(witness_key, CDM_IndexToKeyRange(m', index as int).khi);
                CDM_KeyRangesAreOrdered(m', index as int, hi_index as int);
                KeyPlusTransitivity(witness_key, CDM_IndexToKeyRange(m', index as int).khi, m'.lows[hi_index].klo);
                assert KeyPlusLt(witness_key, m'.lows[hi_index].klo);
                assert KeyPlusLe(m'.lows[hi_index].klo, kr.khi);
                KeyPlusTransitivity(witness_key, m'.lows[hi_index].klo, kr.khi);
                assert KeyPlusLt(witness_key, kr.khi);
                assert KeyRangeContains(kr, witness_key);
            } else {
                if kr.khi != m'.lows[index].klo {
                    assert KeyRangeContains(kr, witness_key);
                } else {
                    forall k | KeyRangeContains(kr, KeyPlus(k))
                        ensures AbstractifyCDelegationMapToDelegationMap(m')[k] == AbstractifyEndPointToNodeIdentity(id);
                    {
                        assert KeyPlusLe(kr.klo, KeyPlus(k));
                        assert KeyPlusLt(KeyPlus(k), kr.khi);
                        assert KeyPlusLe(KeyPlus(k), kr.khi);
                        ghost var k_index := CDM_IndexForKey(m', KeyPlus(k));
                        CDM_IndexForKey_Ordering_specific(m', kr.klo, KeyPlus(k));
                        CDM_IndexForKey_Ordering_specific(m', KeyPlus(k), kr.khi);
                        assert lo_index as int <= k_index as int <= hi_index as int < |m'.lows|;
                        if k_index == hi_index {
                            assert KeyPlusLe(kr.khi, KeyPlus(k));
                            KeyPlusAntisymmetry(kr.khi, KeyPlus(k));
                            assert false;
                        }
                        assert InBounds(k_index as int, lo_index as int, hi_index as int, |m'.lows|);
                        if k_index < old_index {
                            assert InBounds(k_index as int, lo_index as int, old_index as int, |m'.lows|);
                            assert m'.lows[k_index].id == id;
                        } else {
                            assert m'.lows[k_index].id == id;
                        }
                    }

                    return true;
                }
            }

            assert KeyRangeContains(CDM_IndexToKeyRange(m', index as int), witness_key);
            CDM_Partitioned(m', witness_key, index as int);
            assert CDM_IndexForKey(m', witness_key) == index;
        }
        forall i {:trigger InBounds(i, lo_index as int, index as int, |m'.lows|)} | 
                 InBounds(i, lo_index as int, index as int, |m'.lows|)
            ensures m'.lows[i].id == id;
        {
            if i < old_index as int {
                assert InBounds(i, lo_index as int, old_index as int, |m'.lows|) ==> m'.lows[i].id == id;
            } else {
            }
        }

    }

    forall k | KeyRangeContains(kr, KeyPlus(k))
        ensures AbstractifyCDelegationMapToDelegationMap(m')[k] == AbstractifyEndPointToNodeIdentity(id);
    {
        assert KeyPlusLe(kr.klo, KeyPlus(k));
        assert KeyPlusLt(KeyPlus(k), kr.khi);
        assert KeyPlusLe(KeyPlus(k), kr.khi);
        ghost var k_index := CDM_IndexForKey(m', KeyPlus(k));
        CDM_IndexForKey_Ordering_specific(m', kr.klo, KeyPlus(k));
        CDM_IndexForKey_Ordering_specific(m', KeyPlus(k), kr.khi);
        assert lo_index as int <= k_index as int <= hi_index as int < |m'.lows|;
        assert InBounds(k_index as int, lo_index as int, index as int, |m'.lows|);
        assert m'.lows[k_index].id == id;
    }

    b := true;
    return;
}

lemma lemma_CDM_Defragment_equivalence(m:CDelegationMap, m':CDelegationMap)
    requires CDelegationMapIsValid(m);
    requires  CDelegationMapIsValid(m');
    requires forall k:Key :: true ==> m.lows[CDM_IndexForKey(m,KeyPlus(k))].id == m'.lows[CDM_IndexForKey(m',KeyPlus(k))].id;
    ensures  AbstractifyCDelegationMapToDelegationMap(m) == AbstractifyCDelegationMapToDelegationMap(m');
{
}

// TODO: Call this from update, not lookup (and add the last ensures to IsValid)
// TODO: Defragment more aggressively
method CDM_Defragment(m:CDelegationMap) returns (m':CDelegationMap)
    requires CDelegationMapIsValid(m);
    ensures  CDelegationMapIsValid(m');
    ensures  AbstractifyCDelegationMapToDelegationMap(m) == AbstractifyCDelegationMapToDelegationMap(m');
    ensures  |m'.lows| >= 2 && m'.lows[1].klo.KeyPlus? ==> m'.lows[1].klo.k != KeyMin();
{
    if |m.lows| as uint64 < 2 || m.lows[1].klo != KeyPlus(KeyMin()) {
        return m;
    }

    if |m.lows| >= 3 {
        CDelegationMapIsSortedExtension_recursive(m, 1, 2);
        KeyPlusAntisymmetry(m.lows[1].klo, m.lows[2].klo);
        assert m.lows[2].klo != KeyPlus(KeyMin());
    }

    var new_lows := [Mapping(KeyZero(), m.lows[1].id)] + m.lows[2..];
    m' := CDelegationMap(new_lows);

    // Prove the third ensures
    lemma_CDM_NoLowsAreInfinite(m);

    // Prove sorted to prove IsValid
    assert CDelegationMapBoundedSize(m');
    forall i | 0 <= i < |m'.lows| - 1
        ensures KeyPlusLt(m'.lows[i].klo, m'.lows[i+1].klo);
    {
        if i == 0 {
            assert KeyPlusLt(m.lows[0].klo, m.lows[1].klo);
        } else {
            assert m'.lows[i]   == m.lows[2..][i-1] == m.lows[1+i];
            assert m'.lows[i+1] == m.lows[2..][i]   == m.lows[2+i];
            CDelegationMapIsSortedExtension_recursive(m, 1+i, 2+i);
            assert KeyPlusLt(m.lows[1+i].klo, m.lows[2+i].klo);
        }
    }
    assert KeyPlusLt(m'.lows[|m'.lows|-1].klo, KeyInf());
    assert CDelegationMapIsSorted(m');
    
    // Prove equivalent refinements
    forall k:Key 
        ensures m.lows[CDM_IndexForKey(m,KeyPlus(k))].id == m'.lows[CDM_IndexForKey(m',KeyPlus(k))].id;
    {
        ghost var kp := KeyPlus(k);
        ghost var k_index  := CDM_IndexForKey(m,  kp) as int;
        ghost var k_index' := CDM_IndexForKey(m', kp) as int;
        if KeyRangeContains(CDM_IndexToKeyRange(m, 0), kp) {
            assert KeyPlusLt(kp, m.lows[1].klo);
            assert KeyPlusLt(kp, KeyPlus(KeyMin()));
            KeyPlusAntisymmetry(kp, KeyPlus(KeyMin()));
            assert false;
        }
        assert k_index >= 1;
    
        if k_index' == 0 {
            if k_index == 1 {
                assert m'.lows[0].id == m.lows[1].id;
            } else {
                assert KeyPlusLt(kp, m'.lows[1].klo);
                assert KeyPlusLt(kp, m.lows[2].klo);
                if 2 < k_index {
                    CDelegationMapIsSortedExtension_recursive(m, 2, k_index);
                }
                assert KeyPlusLe(m.lows[2].klo, m.lows[k_index].klo);
                KeyPlusTransitivity(kp, m.lows[2].klo, m.lows[k_index].klo);    // ==> kp < m.lows[k_index]
                // But we also know:
                assert KeyPlusLe(m.lows[k_index].klo, kp);
                KeyPlusAntisymmetry(m.lows[k_index].klo, kp);   // Contradiction!
                assert false;
            }
        } else {
            if k_index == k_index' + 1 {
                assert m'.lows[k_index'] == m.lows[k_index];
            } else {
                assert m'.lows[k_index'] == m.lows[k_index' + 1];
                assert KeyRangeContains(CDM_IndexToKeyRange(m, k_index), kp);
                assert KeyRangeContains(CDM_IndexToKeyRange(m, k_index' + 1), kp);
                CDM_Partitioned(m, kp, k_index);
                assert false;
            }
        } 
    }
    lemma_CDM_Defragment_equivalence(m, m');
}
}
