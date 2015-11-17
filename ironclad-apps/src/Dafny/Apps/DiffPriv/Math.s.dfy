include "../../Libraries/Math/round.s.dfy"

static function method Clip (value:int, min:int, max:int):int
    requires min <= max;
    ensures min <= Clip(value, min, max) <= max;
{
    if value < min then min else if value > max then max else value
}

static function method Scale (value:int, units:int) : int
    requires units > 0;
{
    (value / units) + (if (value % units) * 2 >= units then 1 else 0)
}
