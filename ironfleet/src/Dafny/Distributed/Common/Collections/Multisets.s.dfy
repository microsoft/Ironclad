
module Collections__Multisets_s {
function RestrictMultiset<S>(m:multiset<S>, f:S->bool):multiset<S>
    reads f.reads;
    requires forall x :: f.requires(x);
    ensures RestrictMultiset(m, f) <= m;
    ensures forall x :: RestrictMultiset(m, f)[x] == if f(x) then m[x] else 0
{
    if |m| == 0 then
        multiset{}
    else
        var x :| x in m;
        var m_without_x := m[x := 0];
        if f(x) then
            RestrictMultiset(m_without_x, f)[x := m[x]]
        else
            RestrictMultiset(m_without_x, f)
}

} 
