include "Io.s.dfy"

module Native__IoLemmas_i {

import opened Native__NativeTypes_s
import opened Native__Io_s

lemma lemma_KVTupleSeqToMapCantIncreaseNumKeys<K, V>(kvs: seq<(K, V)>)
  ensures |KVTupleSeqToMap(kvs)| <= |kvs|
{
  if |kvs| == 0 {
    return;
  }

  var kvs_prefix := kvs[..|kvs|-1];
  lemma_KVTupleSeqToMapCantIncreaseNumKeys(kvs_prefix);
}

lemma lemma_SetOfSequenceElementsNoBiggerThanSeq<T>(s: seq<T>)
  ensures |(set x | x in s)| <= |s|
{
  if |s| == 0 {
    return;
  }

  lemma_SetOfSequenceElementsNoBiggerThanSeq(s[1..]);
  assert (set x | x in s) == {s[0]} + (set x | x in s[1..]);
}

lemma lemma_AsKVTuplesEnsuresKeysDistinct<K, V>(m: map<K, V>, kvs: seq<(K, V)>)
  requires |kvs| == |m.Keys|
  requires forall k :: k in m ==> (k, m[k]) in kvs
  requires forall k, v :: (k, v) in kvs ==> k in m && m[k] == v
  requires |kvs| > 0
  ensures  kvs[|kvs|-1] !in kvs[..|kvs|-1]
{
  forall kv | kv in kvs
    ensures kv in m.Items
  {
    var (k, v) := kv;
    assert k in m && m[k] == v;
    assert kv in m.Items;
  }

  forall kv | kv in m.Items
    ensures kv in kvs
  {
    var (k, v) := kv;
    assert k in m && m[k] == v;
    assert (k, m[k]) in kvs;
  }

  var kv_last := kvs[|kvs|-1];
  var kvs_prefix := kvs[..|kvs|-1];
  if kv_last in kvs_prefix {
    var s'' := set kv | kv in kvs_prefix;
    assert s'' == m.Items;
    lemma_SetOfSequenceElementsNoBiggerThanSeq(kvs_prefix);
    assert |s''| <= |kvs_prefix| < |kvs|;
    assert false;
  }
}

lemma lemma_AsKVTuplesThenKVTupleSeqToMapIsIdentity<K, V>(m: map<K, V>, kvs: seq<(K, V)>)
  requires |kvs| == |m.Keys|
  requires forall k :: k in m ==> (k, m[k]) in kvs
  requires forall k, v :: (k, v) in kvs ==> k in m && m[k] == v
  ensures  KVTupleSeqToMap(kvs) == m
{
  if |kvs| == 0 {
    return;
  }

  var kvs_prefix := kvs[..|kvs|-1];
  var kv_last := kvs[|kvs|-1];
  var m_prefix := m - {kv_last.0};
  assert kv_last !in kvs_prefix by { lemma_AsKVTuplesEnsuresKeysDistinct(m, kvs); }
  lemma_AsKVTuplesThenKVTupleSeqToMapIsIdentity(m_prefix, kvs_prefix);
}

}
