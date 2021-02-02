include "Maps2.s.dfy"
// TODO eliminate redundancy between these two libraries we've accreted.

module Collections__Maps2_i {
import opened Collections__Maps2_s

function maprange<KT,VT>(m:map<KT,VT>) : set<VT>
{
    set k | k in m :: m[k]
}

type imap2<K1, K2, V> = imap<K1, imap<K2, V>>

predicate imap2total<K1(!new), K2, V>(m:imap2<K1, K2, V>)
{
    imaptotal(m) && forall k1 :: imaptotal(m[k1])
}

predicate imaptotal_(f:imap<int, int>) { imaptotal(f) } // TODO: remove hack when opaque/generic bug is fixed

predicate monotonic(f:imap<int, int>)
{
    forall i1, i2 :: i1 in f && i2 in f && i1 <= i2 ==> f[i1] <= f[i2]
}

predicate monotonic_from(start:int, f:imap<int, int>)
{
    forall i1, i2 :: i1 in f && i2 in f && start <= i1 <= i2 ==> f[i1] <= f[i2]
}

predicate behaviorMonotonic<S>(b:imap<int, S>, f:imap<S, int>)
    requires imaptotal(b);
    requires imaptotal(f);
{
    forall i1, i2 :: i1 <= i2 ==> f[b[i1]] <= f[b[i2]]
}

// TODO_MODULE: module Collections__Maps2_i {
// TODO_MODULE: import opened Collections__Maps2_s

lemma Lemma_EqualityConditionForMapsWithSameDomain<S, T>(m1:map<S, T>, m2:map<S, T>)
    requires mapdomain(m1) == mapdomain(m2);
    requires forall s :: s in m1 && s in m2 ==> m1[s] == m2[s];
    ensures  m1 == m2;
{
    forall s | s in m1
        ensures s in m2;
    {
        assert s in mapdomain(m1);
        assert s in mapdomain(m2);
    }

    forall s | s in m2
        ensures s in m1;
    {
        assert s in mapdomain(m2);
        assert s in mapdomain(m1);
    }
}

lemma Lemma_imap2equiv<K1, K2, V>(f:imap2<K1, K2, V>, g:imap2<K1, K2, V>)
    requires forall k1 :: k1 in f <==> k1 in g;
    requires forall k1 :: k1 in f ==> f[k1] == g[k1];
    ensures  f == g;
{
}

predicate TLe(i:int, j:int) { i <= j }

lemma Lemma_imapInductionRange(start:int, end:int, f:imap<int, bool>)
    requires TLe(start, end);
    requires forall i :: TLe(start, i) && TLe(i, end) ==> i in f;
    requires forall i :: TLe(start, i) && TLe(i + 1, end) && f[i] ==> f[i + 1];
    requires f[start];
    ensures  f[end];
    decreases end - start;
{
    if (start != end) {
        assert TLe(start, start) && TLe(start + 1, end);
        forall i | TLe(start + 1, i) && TLe(i + 1, end)
            ensures f[i] ==> f[i+1];
        {
            assert TLe(start, i) && TLe(i + 1, end);
        }
        Lemma_imapInductionRange(start + 1, end, f);
    }
}


// TODO_MODULE: } import opened Collections__Maps2_i_ = Collections__Maps2_i

} 
