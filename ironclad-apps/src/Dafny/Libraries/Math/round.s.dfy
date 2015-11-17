static function method RoundUpToMultiple (x:int, m:int) : int
    requires m > 0;
    requires x >= 0;
{
    ((x + m - 1) / m) * m
}

static function method DivideRoundingUp (x:int, m:int) : int
    requires x >= 0;
    requires m > 0;
{
    (x/m) + (if x % m == 0 then 0 else 1)
}
