//- <NuBuild AddDafnyFlag /z3opt:NL_ARITH=true/>
//- WARNING: In general, you shouldn't need to call these directly.  Try
//- to use the ones in mul.i.dfy instead.  They're more full-featured anyway.







static lemma lemma_mul_strictly_positive(x:int, y:int)
    ensures (0 < x && 0 < y) ==> (0 < x*y);
{}

static lemma lemma_mul_nonzero(x:int, y:int)
    ensures x*y != 0 <==> x != 0 && y != 0;
{}

static lemma lemma_mul_is_associative(x:int, y:int, z:int)
    ensures x * (y * z) == (x * y) * z;
{}

static lemma lemma_mul_is_distributive_add(x:int, y:int, z:int)
    ensures x*(y + z) == x*y + x*z;
{}

static lemma lemma_mul_ordering(x:int, y:int, b:int)
    requires 0 < x;
    requires 0 < y;
    requires 0 <= x*y < b;
    ensures x < b && y < b;
{ }

static lemma lemma_mul_strict_inequality(x:int, y:int, z:int)
    requires x < y;
    requires z > 0;
    ensures  x*z < y*z;
{}
