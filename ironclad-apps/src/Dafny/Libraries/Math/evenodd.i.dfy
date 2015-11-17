include "mul.i.dfy"
include "div.i.dfy"

static function IsEven(x:int) : bool
{
    exists y:int :: mul(y, 2) == x
}

static lemma lemma_no_half(i:int)
    ensures 2*i != 1;
{
/*
    if (i==0)
    {
    }
    else if (i>0)
    {
        lemma_mul_increases(i,2);
        assert 2<=mul(i,2);
        lemma_mul_is_commutative_forall();
        assert 2 <= 2*i;
        assert 1 != 2*i;
    }
    else
    {
        var mi:int := -i;
        assert 0<mi;
        lemma_mul_increases(mi,2);
        assert 2<=mul(mi,2);
        assert -1*2 >= -1*mul(mi,2);
        lemma_mul_is_mul_boogie(-1,mul(mi,2));
        lemma_mul_is_associative_forall();
        assert -2 >= mul(mul(-1,mi),2);
        assert mul(mul(-1,mi),2) <= -2;
        assert 2*i <= -2;
        assert 2*i <= 2*(-1);
        lemma_mul_inequality_converse_forall();
        assert 2*i <= -1;
    }
*/
}

//-datatype IntDivResult = IntDivResult_c(q:int, r:int);
//-
//-function DivMod(x:int, d:int) : IntDivResult
//-    requires d>0;
//-    ensures d*DivMod(x,d).q+DivMod(x,d).r == x;
//-    ensures 0<=DivMod(x,d).r<d;
//-{
//-    IntDivResult_c(x/d, x%d)
//-
//-}

/*
static lemma DivMod(x:int, d:int) returns (q:int, r:int)
    requires 0 <= x;
    requires 0 < d;
    ensures d*q+r == x;
    ensures 0<=r<d;
    ensures q == x/d;
    ensures r == x%d;
{
    q := x/d;
    r := x%d;

    lemma_fundamental_div_mod(x,d);
    assert x == d * (x / d) + x % d;
    assert x == d * q + r;
    lemma_mod_pos_bound(x,d);
}
*/

static lemma lemma_even_mod_0_pos(x:int)
//-    requires 0 <= x;
    ensures IsEven(x) <==> (mod(x, 2) == 0);
{
    lemma_mod_is_mod_boogie(x, 2);
    if (IsEven(x))
    {
        var y:int :| mul(y, 2) == x;
        lemma_mul_is_mul_boogie(y, 2);
        assert mod(x, 2) == 0;
    }
    if (mod(x, 2) == 0)
    {
        lemma_mul_is_mul_boogie(x / 2, 2);
        assert mul(x / 2, 2) == x;
        assert IsEven(x);
    }
/*
    var q:int,r:int := DivMod(x,2);
    lemma_mul_is_mul_boogie(2,q);
    assert 2*q+r == mul(2,q)+r == x;
    assert 0<=r<2;
    assert r==mod(x,2);

    if (mod(x,2) == 0)
    {
        assert r == 0;
        assert 2*q == x;
        lemma_mul_is_commutative(2,q);
        assert q*2 == x;
        assert IsEven(x);
    }
    else
    {
        assert r == 1;
        assert 2*q+1 == x;
        assert 1 == x-2*q;
        if (IsEven(x))
        {
            var y:int :| y*2 == x;
            lemma_mul_is_commutative(2,y);
            assert 2*y == x;
            assert 1 == 2*y - 2*q;
            lemma_mul_is_distributive_sub(2,y,q);
            assert 1 == 2*(y - q);
            var z:int := y - q;
            assert 1 == 2*z;
            lemma_no_half(z);
            assert false;
        }
        assert !IsEven(x);
    }
*/
}

static lemma lemma_x_odd(x:int)
    requires 0 <= x;
    requires !IsEven(x);
    ensures mod(x,2)==1;
{
    lemma_even_mod_0_pos(x);
    assert mod(x,2) != 0;
    lemma_mod_pos_bound(x,2);
    assert mod(x,2) < 2;
    assert mod(x,2) == 1;
}
