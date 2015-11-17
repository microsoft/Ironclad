static predicate is_prefix(prefix:seq<int>, super:seq<int>)
{
    |super| >= |prefix|
    && super[..|prefix|] == prefix
}

static predicate is_suffix(suffix:seq<int>, super:seq<int>)
{
    |super| >= |suffix|
    && super[|suffix|..] == suffix
}
