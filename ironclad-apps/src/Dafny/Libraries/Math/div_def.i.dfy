//- Specs/implements mathematical div and mod, not the C version.
//- This may produce "surprising" results for negative values
//- For example, -3 div 5 is -1 and -3 mod 5 is 2.
//- Note this is consistent: -3 * -1 + 2 == 5
/*
static function mod(x:int, m:int) : int
    requires m > 0;
    decreases if x < 0 then (m - x) else x;
{
    if x < 0 then
        mod(m + x, m)
    else if x < m then
        x
    else
        mod(x - m, m)
}
*/

static function div(x:int, d:int) : int
    requires d != 0;
{
    x/d
}

static function mod(x:int, d:int) : int
    requires d != 0;
{
    x%d
}

static function div_recursive(x:int, d:int) : int
    requires d != 0;
{ INTERNAL_div_recursive(x,d) }

static function mod_recursive(x:int, d:int) : int
    requires d > 0;
{ INTERNAL_mod_recursive(x,d) }

static function mod_boogie(x:int, y:int) : int
    requires y != 0;
{ x % y } //- INTERNAL_mod_boogie(x,y) }

static function div_boogie(x:int, y:int) : int
    requires y != 0;
{ x / y } //-{ INTERNAL_div_boogie(x,y) }

static function my_div_recursive(x:int, d:int) : int
    requires d != 0;
{
    if d > 0 then
        my_div_pos(x, d)
    else
        -1 * my_div_pos(x, -1*d)
}

static function my_div_pos(x:int, d:int) : int
    requires d >  0;
    decreases if x < 0 then (d - x) else x;
{
    if x < 0 then
        -1 + my_div_pos(x+d, d)
    else if x < d then
        0
    else
        1 + my_div_pos(x-d, d)
}

static function my_mod_recursive(x:int, m:int) : int
    requires m > 0;
    decreases if x < 0 then (m - x) else x;
{
    if x < 0 then
        my_mod_recursive(m + x, m)
    else if x < m then
        x
    else
        my_mod_recursive(x - m, m)
}


//- Kept for legacy reasons:
//-static function INTERNAL_mod_boogie(x:int, m:int) : int   { x % y }
static function INTERNAL_mod_recursive(x:int, m:int) : int  
    requires m > 0;
{ my_mod_recursive(x, m) }

//-static function INTERNAL_div_boogie(x:int, m:int) : int   { x / m }
static function INTERNAL_div_recursive(x:int, d:int) : int 
    requires d != 0;
{ my_div_recursive(x, d) }


/*
static ghost method mod_test()
{
    assert -3 % 5 == 2;
    assert 10 % -5 == 0;
    assert 1 % -5 == 1;
    assert -3 / 5 == -1;
}
*/
