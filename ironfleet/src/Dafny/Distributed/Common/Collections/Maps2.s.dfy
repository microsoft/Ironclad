// TODO eliminate redundancy between these two libraries we've accreted.

module Collections__Maps2_s {

function mapdomain<KT,VT>(m:map<KT,VT>) : set<KT>
{
    set k | k in m :: k
}

function mapremove<KT,VT>(m:map<KT,VT>, k:KT) : map<KT,VT>
{
    map ki | ki in m && ki != k :: m[ki]
}

predicate imaptotal<KT,VT>(m:imap<KT,VT>)
{
    forall k {:trigger m[k]}{:trigger k in m} :: k in m
}
} 
