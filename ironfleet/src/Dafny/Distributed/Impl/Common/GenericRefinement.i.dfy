include "../../Common/Native/NativeTypes.s.dfy"
include "../../Common/Collections/Maps.i.dfy"
include "../../Common/Collections/Sets.i.dfy"

module GenericRefinement_i {
import opened Native__NativeTypes_s
import opened Collections__Maps_i
import opened Collections__Sets_i

// Useful to give this cast a name, so it can be used as a higher-order function
function uint64_to_int(u:uint64) : int { u as int }

//////////////////////////////////////////////////////////////////////////////
//  Generic seq-to-seq refinement
function {:opaque} MapSeqToSeq<T(!new),U>(s:seq<T>, refine_func:T~>U) : seq<U>
  reads refine_func.reads
  requires forall i :: refine_func.reads(i) == {}
  requires forall i :: 0 <= i < |s| ==> refine_func.requires(s[i])
  ensures |MapSeqToSeq(s, refine_func)| == |s|
  ensures forall i :: 0 <= i < |s| ==> refine_func(s[i]) == MapSeqToSeq(s,refine_func)[i]
{
  if |s| == 0 then []
  else [refine_func(s[0])] + MapSeqToSeq(s[1..], refine_func)
}

/////////////////////////////////////////////////////////
//  Generic map refinement from concrete to abstract 
/////////////////////////////////////////////////////////
predicate MapIsAbstractable<KT,VT,CKT,CVT>(m:map<CKT,CVT>, RefineKey:CKT~>KT, RefineValue:CVT~>VT, ReverseKey:KT~>CKT) 
  reads RefineKey.reads, RefineValue.reads, ReverseKey.reads
{
  && (forall ck :: ck in m ==> RefineKey.requires(ck) && RefineValue.requires(m[ck]))
  && (forall ck :: ck in m ==> ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck)
}

function {:opaque} AbstractifyMap<CKT,CVT,KT,VT>(m:map<CKT,CVT>, RefineKey:CKT~>KT, RefineValue:CVT~>VT, ReverseKey:KT~>CKT) : map<KT,VT>
  reads RefineKey.reads, RefineValue.reads, ReverseKey.reads
  requires forall ck :: ck in m ==> RefineKey.requires(ck) && RefineValue.requires(m[ck])
  requires forall ck :: ck in m ==> ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck
  ensures  var rm  := AbstractifyMap(m,RefineKey,RefineValue,ReverseKey);
           forall k :: k in rm ==> (exists ck :: ck in m && RefineKey(ck) == k)
{
  // var new_domain := set ck | ck in m :: RefineKey(ck);
  // map k | k in new_domain :: RefineValue(m[ReverseKey(k)])
  map k | k in (set ck | ck in m :: RefineKey(ck)) :: RefineValue(m[ReverseKey(k)])
}

lemma Lemma_AbstractifyMap_basic_properties<CKT,CVT,KT,VT>(m:map<CKT,CVT>, RefineKey:CKT~>KT, RefineValue:CVT~>VT, ReverseKey:KT~>CKT)
  requires MapIsAbstractable(m, RefineKey, RefineValue, ReverseKey)
  // Injectivity
  requires forall ck1, ck2 :: RefineKey.requires(ck1) && RefineKey.requires(ck2) && RefineKey(ck1) == RefineKey(ck2) ==> ck1 == ck2
  ensures  m == map [] ==> AbstractifyMap(m, RefineKey, RefineValue, ReverseKey) == map []
  ensures  forall ck :: ck in m <==> RefineKey.requires(ck) && RefineKey(ck) in AbstractifyMap(m, RefineKey, RefineValue, ReverseKey)
  ensures  forall ck :: ck in m ==> AbstractifyMap(m, RefineKey, RefineValue, ReverseKey)[RefineKey(ck)] == RefineValue(m[ck])
{
  reveal AbstractifyMap();
}

lemma Lemma_AbstractifyMap_preimage<KT,VT,CKT,CVT>(cm:map<CKT,CVT>, RefineKey:CKT~>KT, RefineValue:CVT~>VT, ReverseKey:KT~>CKT)
  requires MapIsAbstractable(cm, RefineKey, RefineValue, ReverseKey)
  // Injectivity
  requires forall ck1, ck2 :: RefineKey.requires(ck1) && RefineKey.requires(ck2) && RefineKey(ck1) == RefineKey(ck2) ==> ck1 == ck2
  ensures  var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
           forall k :: k in rm ==> (exists ck :: ck in cm && RefineKey(ck) == k)
{
  var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
  Lemma_AbstractifyMap_basic_properties(cm, RefineKey, RefineValue, ReverseKey);
  forall k | k in rm 
    ensures (exists ck :: ck in cm && RefineKey(ck) == k)
  {
    reveal AbstractifyMap();
  }
}

lemma Lemma_AbstractifyMap_append<KT,VT,CKT,CVT>(cm:map<CKT,CVT>, RefineKey:CKT~>KT, RefineValue:CVT~>VT, ReverseKey:KT~>CKT,
                                                 ck:CKT, cval:CVT)
  requires MapIsAbstractable(cm, RefineKey, RefineValue, ReverseKey)
  // Injectivity
  requires forall ck1, ck2 :: RefineKey.requires(ck1) && RefineKey.requires(ck2) && RefineKey(ck1) == RefineKey(ck2) ==> ck1 == ck2
  requires RefineKey.requires(ck)
  requires RefineValue.requires(cval)
  requires ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck
  ensures  var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
           var rm' := AbstractifyMap(cm[ck := cval], RefineKey, RefineValue, ReverseKey);
           rm' == AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey)[RefineKey(ck) := RefineValue(cval)]
{
  var rm := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
  var cm' := cm[ck := cval];
  var rm' := AbstractifyMap(cm', RefineKey, RefineValue, ReverseKey);
  var r_cm' := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey)[RefineKey(ck) := RefineValue(cval)];

  forall rk | rk in rm'
    ensures rk in r_cm'
    ensures r_cm'[rk] == rm'[rk]
  {
    Lemma_AbstractifyMap_basic_properties(cm', RefineKey, RefineValue, ReverseKey);
    Lemma_AbstractifyMap_preimage(cm', RefineKey, RefineValue, ReverseKey);
    if (exists p :: p in cm' && RefineKey(p) == rk){
      var preimage :| preimage in cm' && RefineKey(preimage) == rk;
      if preimage in cm {
        Lemma_AbstractifyMap_basic_properties(cm, RefineKey, RefineValue, ReverseKey);
        calc ==> {
          true;
            { Lemma_AbstractifyMap_preimage(cm, RefineKey, RefineValue, ReverseKey); }
          RefineKey(preimage) in rm;
          RefineKey(preimage) in rm';
          rk in r_cm';
        }
      } else {
        assert preimage == ck;
        assert RefineKey(preimage) in r_cm';
      }
    }
    reveal AbstractifyMap();
  }

  forall rk | rk in r_cm'
    ensures rk in rm'
  {
    Lemma_AbstractifyMap_basic_properties(cm, RefineKey, RefineValue, ReverseKey);
    Lemma_AbstractifyMap_preimage(cm, RefineKey, RefineValue, ReverseKey);
    Lemma_AbstractifyMap_basic_properties(cm', RefineKey, RefineValue, ReverseKey);
    if rk in rm {
      if(exists p :: p in cm && RefineKey(p) == rk){
        var preimage :| preimage in cm && RefineKey(preimage) == rk;
        assert rk in rm';
      }
    } else {
      assert rk == RefineKey(ck);
    }
    reveal AbstractifyMap();
  }

  assert r_cm' == rm';
}

lemma Lemma_AbstractifyMap_remove<KT(!new),VT(!new),CKT(!new),CVT(!new)>(
  cm:map<CKT,CVT>, RefineKey:CKT~>KT, RefineValue:CVT~>VT, ReverseKey:KT~>CKT, ck:CKT)
  requires MapIsAbstractable(cm, RefineKey, RefineValue, ReverseKey)
  // Injectivity
  requires forall ck1, ck2 :: RefineKey.requires(ck1) && RefineKey.requires(ck2) && RefineKey(ck1) == RefineKey(ck2) ==> ck1 == ck2
  requires RefineKey.requires(ck)
  requires ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck
  requires ck in cm
  ensures  var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
           var rm' := AbstractifyMap(RemoveElt(cm, ck), RefineKey, RefineValue, ReverseKey);
           RefineKey(ck) in rm &&
           rm' == RemoveElt(rm, RefineKey(ck))
{
  Lemma_AbstractifyMap_basic_properties(cm, RefineKey, RefineValue, ReverseKey);

  var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
  var smaller_cm := RemoveElt(cm, ck);
  var rm' := AbstractifyMap(smaller_cm, RefineKey, RefineValue, ReverseKey);
  var smaller_rm := RemoveElt(rm, RefineKey(ck));

  Lemma_AbstractifyMap_basic_properties(smaller_cm, RefineKey, RefineValue, ReverseKey);

  forall o | o in rm'
    ensures o in smaller_rm && rm'[o] == smaller_rm[o];
  {
    if (exists c :: c in smaller_cm && RefineKey(c) == o){
      var co :| co in smaller_cm && RefineKey(co) == o;
      assert co != ck;
      assert RefineKey(co) != RefineKey(ck);
    }
    reveal AbstractifyMap();
  }

  forall o | o in smaller_rm
    ensures o in rm' && rm'[o] == smaller_rm[o]
  {
    Lemma_AbstractifyMap_preimage(cm, RefineKey, RefineValue, ReverseKey);
    // var co :| co in cm && co != ck && RefineKey(co) == o;
    reveal AbstractifyMap();
  }

  assert forall o :: (o in rm' <==> o in smaller_rm) && (o in rm' ==> rm'[o] == smaller_rm[o]);
  assert rm' == smaller_rm;
}

lemma lemma_AbstractifyMap_properties<CKT(!new),CVT(!new),KT(!new),VT(!new)>(
  cm:map<CKT,CVT>, RefineKey:CKT~>KT, RefineValue:CVT~>VT, ReverseKey:KT~>CKT)
  requires MapIsAbstractable(cm, RefineKey, RefineValue, ReverseKey)
  // Injectivity
  requires forall ck1, ck2 :: RefineKey.requires(ck1) && RefineKey.requires(ck2) && RefineKey(ck1) == RefineKey(ck2) ==> ck1 == ck2
  ensures  cm == map [] ==> AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey) == map []
  ensures  forall ck :: ck in cm <==> RefineKey.requires(ck) && RefineKey(ck) in AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey)
  ensures  forall ck :: ck in cm ==> AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey)[RefineKey(ck)] == RefineValue(cm[ck])
  ensures  forall ck :: ck !in cm && RefineKey.requires(ck) ==> RefineKey(ck) !in AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey)
  ensures  var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
           forall k :: k in rm ==> (exists ck :: ck in cm && RefineKey(ck) == k)
  ensures forall ck, cval {:trigger cm[ck := cval]} {:trigger RefineKey(ck), RefineValue(cval)} ::
            (RefineKey.requires(ck) && RefineValue.requires(cval) 
            && ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck) ==>
            var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
            var rm' := AbstractifyMap(cm[ck := cval], RefineKey, RefineValue, ReverseKey);
            rm' == AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey)[RefineKey(ck) := RefineValue(cval)]
  ensures forall ck {:trigger RemoveElt(AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey), RefineKey(ck)) } :: 
            (RefineKey.requires(ck) && ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck && ck in cm) ==>
            var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
            var rm' := AbstractifyMap(RemoveElt(cm, ck), RefineKey, RefineValue, ReverseKey);
            rm' == RemoveElt(rm, RefineKey(ck))
{
  Lemma_AbstractifyMap_basic_properties(cm, RefineKey, RefineValue, ReverseKey);
  Lemma_AbstractifyMap_preimage(cm, RefineKey, RefineValue, ReverseKey);

  forall ck, cval | RefineKey.requires(ck) && RefineValue.requires(cval)
                    && ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck
    ensures var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
            var rm' := AbstractifyMap(cm[ck := cval], RefineKey, RefineValue, ReverseKey);
            rm' == AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey)[RefineKey(ck) := RefineValue(cval)]
  {
    Lemma_AbstractifyMap_append(cm, RefineKey, RefineValue, ReverseKey, ck, cval);
  }

  forall ck | RefineKey.requires(ck) && ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck && ck in cm
    ensures var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
            var rm' := AbstractifyMap(RemoveElt(cm, ck), RefineKey, RefineValue, ReverseKey);
            rm' == RemoveElt(rm, RefineKey(ck))
  {
    Lemma_AbstractifyMap_remove(cm, RefineKey, RefineValue, ReverseKey, ck);
  }
}

} 
