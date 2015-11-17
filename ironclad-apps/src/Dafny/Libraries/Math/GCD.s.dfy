static function divides(d:nat, n:int) : bool
    requires d != 0;
{
    (n % d) == 0
}

static predicate is_gcd(a:nat, b:nat, gcd:nat)
{
    gcd != 0
    && divides(gcd,a)
    && divides(gcd,b)
    && forall x:int :: gcd<x ==> !(divides(x,a) && divides(x,b))
}

