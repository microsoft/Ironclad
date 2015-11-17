include "power.i.dfy"
include "mul.i.dfy"
include "div_def.i.dfy"
include "div_boogie.i.dfy"
include "div_nonlinear.i.dfy"

//-////////////////////////////////////////////////////////////////////////////
//-
//- Core div lemmas, with named arguments.
//-
//-////////////////////////////////////////////////////////////////////////////

static lemma lemma_div_by_one_is_identity(x:int)
    ensures x/1 == x;
{
}

static lemma lemma_div_basics(x:int)
    ensures x != 0 ==> 0 / x == 0;
    ensures x / 1 == x;
    ensures x!=0 ==> x / x == 1;
{
    lemma_div_by_one_is_identity(x);
    forall x:int | x != 0 
        ensures x / x == 1;
        ensures 0 / x == 0;
    {
        lemma_div_by_self(x);
        lemma_div_of_0(x);
    }
}


static lemma lemma_small_div_converse()
    ensures forall x, d :: 0<=x && 0<d && x/d==0 ==> x < d;
{
    forall (x,d | 0<=x && 0<d && x/d==0)
        ensures x < d;
    {
        if (x >= d)
        {
            calc {
                1;
                    { lemma_div_basics(d); }
                d/d;
                <=  { lemma_div_is_ordered(d, x, d); }
                x/d;
            }
            assert false;
        }
    }
}


static lemma lemma_div_is_ordered_by_denominator(x:int, y:int, z:int)
    requires x >= 0;
    requires 1 <= y <= z;
    ensures x / y >= x / z;
    decreases x;
{
    lemma_div_is_div_recursive_forall();

    if (x < z)
    {
        lemma_div_is_ordered(0, x, y);
    }
    else
    {
        lemma_div_is_ordered(x-z, x-y, y);
        lemma_div_is_ordered_by_denominator(x-z, y, z);
    }
}

static lemma lemma_div_is_strictly_ordered_by_denominator(x:int, d:int)
    requires 0 < x;
    requires 1 < d;
    ensures x/d < x;
    decreases x;
{
    lemma_div_is_div_recursive_forall();
    if (x<d)
    {
    }
    else if (x==d)
    {
        calc {
            x/d;
            d/d;
            1+(d-d)/d;
            1+0/d;
            { lemma_div_of_0(d); }
            1;
            < d;
        }
    }
    else
    {
        lemma_div_is_strictly_ordered_by_denominator(x-d,d);
    }
}

static lemma lemma_dividing_sums(a:int, b:int, d:int, R:int)
    requires 0<d;
    requires R == a%d + b%d - (a+b)%d;
    ensures d*((a+b)/d) - R == d*(a/d) + d*(b/d);
{
    calc ==> {
        a%d + b%d == R + (a+b)%d;
        (a+b)-(a+b)%d - R == a-(a%d) + b - (b%d);
            {
                lemma_fundamental_div_mod(a+b,d);
                lemma_fundamental_div_mod(a,d);
                lemma_fundamental_div_mod(b,d);
            }
        d*((a+b)/d) - R == d*(a/d) + d*(b/d);
    }
}


//-static lemma lemma_negative_divisor(x:int, d:int)
//-    requires d < 0;
//-    ensures x / (-1*d) == -1*(x / d); 
//-{
//-    var q := x / (-1*d);
//-    var r := x % (-1*d);
//-    
//-    calc {
//-        x;
//-            { lemma_fundamental_div_mod(x, -1*d); }
//-        q * (-1*d) + r;
//-            { lemma_mul_is_associative(q, -1, d); }
//-        (q*-1)*d + r;
//-            { lemma_mul_is_commutative(q, -1); }
//-        (-q) * d + r;
//-    }
//-    lemma_mod_range(x, -1*d);
//-    lemma_fundamental_div_mod_converse(x, d, -q, r);
//-    assert x / d == -q;
//-    assert -1*(x/d) == q;
//-}


static lemma lemma_div_pos_is_pos(x:int, divisor:int)
    requires 0 <= x;
    requires 0 < divisor;
    ensures x / divisor >= 0;
{
    if (x < divisor) {
        lemma_small_div();
    } else {
        calc {
            x / divisor;
            { lemma_div_is_div_recursive_forall(); }
            1 + ((x - divisor) / divisor);
            >= { lemma_div_pos_is_pos(x-divisor, divisor); }
            0;
        }
    }
}
//-////////////////////////////////////////////////////////////////////////////
//-
//- Forall lemmas: these restate the core lemmas with foralls,
//- so callers needn't name the specific expressions to manipulate.
//-
//- These are all boilerplate transformations of args/requires/ensures
//- into forall args :: requires ==> ensures, with a correpsonding
//- mechanically generated forall proof that invokes the core lemma.

//-
//-////////////////////////////////////////////////////////////////////////////

static lemma lemma_div_basics_forall()
    ensures forall x :: x != 0 ==> 0 / x == 0;
    ensures forall x :: x / 1 == x;
    ensures forall x, y :: x >= 0 && y > 0 ==> x/y >= 0;
    ensures forall x, y :: x >= 0 && y > 0 ==> x/y <= x;
{
    forall (x:int)
        ensures x != 0 ==> 0 / x == 0;
        ensures x / 1 == x;
    {
        lemma_div_basics(x);
    }
    forall x:int, y:int | x >= 0 && y > 0
        ensures x / y >= 0;
        ensures x / y <= x;
    {
        lemma_div_pos_is_pos(x, y);
        lemma_div_is_ordered_by_denominator(x, 1, y);
    }
}

//////////////////////////////////////////////////////////////////////////////
//





static lemma lemma_div_neg_neg(x:int, d:int)
    requires d > 0;
    ensures x/d == -((-x+d-1)/d);
    decreases if x > 0 then x + 1 else -x;
{
    if (x<0) {
        calc {
            x/d;
                { lemma_div_is_div_recursive_forall(); }
            -1 + my_div_pos(x+d, d);
                { lemma_div_is_div_recursive_forall(); }
            -1 + (x+d)/d;
                {
                    if (x < -d)
                    {
                        lemma_div_neg_neg(x+d,d);
                    }
                    else
                    {
                        calc {
                            (x+d)/d;
                                { lemma_div_is_div_recursive_forall(); }
                            0;
                                { lemma_div_is_div_recursive_forall(); }
                            -((-(x+d)+d-1)/d);
                        }
                    }
                }
            -1 + -((-(x+d)+d-1)/d);
            -1 + -1*((-(x+d)+d-1)/d);
            -1 * (1 + ((-(x+d)+d-1)/d));
            -1 * (1 + ((-(x+d)+d-1)/d));
            { lemma_div_is_div_recursive_forall(); }
            -1 * ((-1*x+d-1)/d);
            -((-x+d-1)/d);
        }
    } else if (x<d) {
        calc {
            x/d;
            { lemma_div_is_div_recursive_forall(); }
            0;
            -(0);
            { lemma_div_is_div_recursive_forall(); }
            -((-x+d-1)/d);
        }
    } else {
        calc {
            -((-x+d-1)/d);
                { lemma_div_neg_neg(-x+d-1, d); }
            -(-((-(-x+d-1)+d-1)/d));
            -(-(((x-d+1)+d-1)/d));
            -(-((x-d+1+d-1)/d));
            -(-(x/d));
            x/d;
        }
    }
}


//-
//-////////////////////////////////////////////////////////////////////////////


/*******************************
 *  Useful lemmas about mod    *
 *******************************/

////////////////////////////////////////////////


////////////////////////////////////////////////

static lemma lemma_mod_2(x:int)
    requires x % 2 == 1;
    ensures (x+1) % 2 == 0;
{
}

static lemma lemma_mod2_plus(x:int)
    requires x >= 0;
    requires x % 2 == 1;
    ensures (x+1)%2 == 0;
{
}

static lemma lemma_mod2_plus2(x:int)
    requires x % 2 == 1;
    ensures (x+2) % 2 == 1;
{
}

static lemma lemma_mod32(x:int)
    requires x >= 32;
    ensures (x-32) % 32 == x % 32;
{
}

////////////////////////////////////////////////

////////////////////////////////////////////////

static lemma lemma_mod_remainder_neg_specific(x:int, m:int)
    requires  m > 0 && x < 0;
    ensures  0 <= x%m < m;
    decreases -1*x;
{
    lemma_mod_is_mod_recursive_forall();
    if (x + m >= 0) {
        lemma_mod_remainder_pos();
    } else {
        lemma_mul_is_mul_recursive_forall();
        lemma_mod_remainder_neg_specific(m+x, m);
    }
}

static lemma lemma_mod_remainder_neg()
    ensures forall x:int, m:int :: m > 0 && x < 0 ==> 0 <= x%m < m;
{
    forall x:int, m:int | m > 0 && x < 0
        ensures 0 <= x%m < m;
    {
        lemma_mod_remainder_neg_specific(x,m);
    }
}

static lemma lemma_mod_remainder_pos_specific(x:int, m:int)
    requires m > 0 && x >= 0;
    ensures 0 <= x % m  < m;
{
    lemma_mod_is_mod_recursive_forall();
    if x == 0 {
    } else if x < m {
    } else {
        lemma_mod_remainder_pos_specific(x - m, m);
    }
}

static lemma lemma_mod_remainder_pos()
    ensures forall x, m :: m > 0 && x >= 0 ==> 0 <= x % m  < m;
{
    forall x, m | m > 0 && x >= 0
        ensures 0 <= x % m < m;
    {
        lemma_mod_remainder_pos_specific(x,m);
    }
}


static lemma lemma_mod_remainder_specific(x:int, m:int)
    requires m > 0;
    ensures 0 <= x % m < m;
{
    if (x < 0) {
        lemma_mod_remainder_neg_specific(x, m);
    }
    else {
        lemma_mod_remainder_pos_specific(x, m);
    }
}
static lemma lemma_mod_remainder()
    ensures forall x:int, m:int :: m > 0 ==> 0 <= x%m < m;
{
    lemma_mod_remainder_pos();
    lemma_mod_remainder_neg();
}

static lemma lemma_mod_basics()
    ensures forall m:int :: m > 0 ==> m % m == 0;
    ensures forall x:int, m:int :: m > 0 ==> (x%m)% m == x%m;
{
    forall m:int | m>0 
        ensures m > 0 ==> m % m == 0;
    {
        lemma_mod_yourself(m);
    }

    forall (x,m | m>0)
        ensures (x%m)% m == x%m;
    {
        assert x%m < m;    
        lemma_small_mod(x%m,m);
    }
}

static lemma lemma_mod_properties()
    ensures forall m:int :: m > 0 ==> m % m == 0;
    ensures forall x:int, m:int :: m > 0 ==> (x%m)% m == x%m;
    ensures forall x:int, m:int :: m > 0 ==> 0 <= x%m < m;
{
    lemma_mod_basics();

    forall (x,m | m>0)
        ensures m > 0 ==> 0 <= x%m < m;
    {
        lemma_mod_remainder();
        assert x%m <m;
        assert x%m <m;
    }
}

static lemma lemma_mod_decreases(x:nat, d:nat)
    requires 0<d;
    ensures x%d <= x;
{
    lemma_mod_properties();
    if (x<d)
    {
        lemma_small_mod(x,d);
    }
}

static lemma lemma_mod_add_multiples_vanish(b:int, m:int)
    requires 0 < m;
    ensures (m + b) % m == b % m;
{
    var q1 := b / m;
    var r1 := b % m;
    var q2 := (m + b) / m - 1;
    var r2 := (m + b) % m;

    calc {
        b;
            { lemma_fundamental_div_mod(b, m); }
        m * q1 + r1;
    }

    calc {
        b;
            { lemma_fundamental_div_mod(m + b, m); }
        m * ((m + b) / m) - m + (m + b) % m;
        m * ((m + b) / m) + (-1 * m) + (m + b) % m;
            { lemma_mul_is_commutative_forall(); lemma_mul_is_distributive_forall(); }
        m * ((m + b) / m - 1) + r2;
        m * q2 + r2;
    }
    lemma_fundamental_div_mod_unique(m*q1 + r1, m, q1, r1, q2, r2);
}

static lemma lemma_mod_sub_multiples_vanish(b:int, m:int)
    requires 0 < m;
    ensures (-m + b) % m == b % m;
{
    var q1 := b / m;
    var r1 := b % m;
    var q2 := (-m + b) / m + 1;
    var r2 := (-m + b) % m;

    calc {
        b;
            { lemma_fundamental_div_mod(b, m); }
        m * q1 + r1;
    }

    calc {
        b;
            { lemma_fundamental_div_mod(-m + b, m); }
        m * ((-m + b) / m) + m + (-m + b) % m;
        m * ((-m + b) / m) + m * 1 + (-m + b) % m;
            { lemma_mul_is_distributive_forall(); }
        m * ((-m + b) / m + 1) + r2;
        m * q2 + r2;
    }
    lemma_fundamental_div_mod_unique(m*q1 + r1, m, q1, r1, q2, r2);
}

static lemma lemma_mod_multiples_vanish(a:int, b:int, m:int)
    decreases if a>0 then a else -a;
    requires 0 < m;
    ensures (m*a + b) % m == b % m;
{
    if (0 == a)
    {
        assert (m*a + b) % m == b % m;
    } else if (0 < a) {
        calc {
            (m*a + b) % m;
            (m*((a-1)+1) + b) % m;
                { lemma_mul_is_distributive_forall(); }
            (m*(a-1)+m*1 + b) % m;
                { lemma_mul_basics_forall(); }
            (m*(a-1) + m + b) % m;
                { lemma_mod_multiples_vanish(a-1,m+b,m); }
            (m + b) % m;
                { lemma_mod_add_multiples_vanish(b, m); }
            b % m;
        }
    } else {
        calc {
            (m*a + b) % m;
            (m*((a+1)-1) + b) % m;
                { lemma_mul_is_distributive_forall(); }
            (m*(a+1)+m*-1 + b) % m;
            (m*(a+1) - m + b) % m;
                { lemma_mod_multiples_vanish(a+1,-m+b,m); }
            (- m + b) % m;
                { lemma_mod_sub_multiples_vanish(b, m); }
            b % m;
        }
    }
}

static lemma lemma_add_mod_noop(x:int, y:int, m:int)
    requires 0 < m;
    ensures ((x % m) + (y % m)) % m == (x+y) % m;
{
    calc {
        (x%m + y%m) % m;
            {
                lemma_fundamental_div_mod(x,m);
                lemma_fundamental_div_mod(y,m);
            }
        (x - m*(x/m) + y - m*(y/m)) % m;
            {
                lemma_mul_unary_negation(m,x/m);
                lemma_mul_unary_negation(m,y/m);
            }
        (x + m*(-(x/m)) + y + m*(-(y/m))) % m;
            { lemma_mod_multiples_vanish(-(x/m), x+y+m*(-(y/m)), m); }
        (x + y + m*(-(y/m))) % m;
            { lemma_mod_multiples_vanish(-(y/m), x+y, m); }
        (x + y) % m;
    }
}

static lemma lemma_mod_equivalence(x:int, y:int, m:int)
    requires 0 < m;
    ensures x % m == y % m <==> (x - y) % m == 0;
{
    calc ==> {
        x % m == y % m;
            { lemma_fundamental_div_mod(x,m); }
        x - (m * (x/m)) == y % m;
            { lemma_fundamental_div_mod(y,m); }
        x - (m * (x/m)) == y - (m * (y/m));
        x - y == (m * (x/m)) - (m * (y/m));
            { lemma_mul_is_distributive_forall(); }
        x - y == m * (x/m - y/m);
        (x - y) % m == (m * (x/m - y/m)) % m;
            { lemma_mod_multiples_vanish(x/m - y/m, 0, m); } 
        (x - y) % m == 0 % m;
            { lemma_0_mod_anything(); }
        (x - y) % m == 0;
    }

    var k := ((x-y)/m);
    calc ==> {
        (x - y) % m == 0;
            { lemma_fundamental_div_mod(x-y,m); }
        (x - y) - m * ((x-y)/m) == 0;
        (x - y) - m * k == 0;
        x == y + m * k;
        x % m == (y + m * k) % m;
            { lemma_mod_multiples_vanish(k, y, m); }
        x % m == y % m;
    }
}

static lemma lemma_sub_mod_noop_helper(x:int, y:int, m:int)
    requires 0 < m;
    ensures  ((x % m) - (y % m)) % m == ((x % m) + (-y % m)) % m; 
{
    var minus_y := -y;
    var diff := ((x % m) - (y % m)) - ((x % m) + (-y % m));
    calc { 
        diff % m;
        calc {
            diff;
            ((x % m) - (y % m)) - ((x % m) + (-y % m));
             -(y % m) - (-y % m);
             -(y % m) - (minus_y % m);
                { lemma_fundamental_div_mod(y,m); }
             -(y - m * (y/m)) - (minus_y % m);
                { lemma_fundamental_div_mod(minus_y,m); }
            - (y - m * (y/m)) - (minus_y - m * (minus_y/m));
                { lemma_mul_is_distributive_forall(); }
            m * (y/m) + m * (minus_y/m);
                { lemma_mul_is_distributive_forall(); }
            m * (y/m + minus_y/m);
        }
        (m * (y/m + minus_y/m)) % m;
            { lemma_mod_multiples_vanish(y/m + minus_y/m, 0, m); }
        0 % m;
            { lemma_0_mod_anything(); }
        0;
    }
    lemma_mod_equivalence((x % m) - (y % m), (x % m) + (-y % m), m);
}

static lemma lemma_sub_mod_noop(x:int, y:int, m:int)
    requires 0 < m;
    ensures ((x % m) - (y % m)) % m == (x-y) % m;
{
    var A := -y;
    calc {
        (x-y) % m;
        (x+A) % m;
        { lemma_add_mod_noop(x, A, m); }
        ((x % m) + (A % m)) % m; 
        ((x % m) + (-y % m)) % m; 
        { lemma_sub_mod_noop_helper(x, y, m); }
        ((x % m) - (y % m)) % m;
    }
}

static lemma lemma_mod_adds(a:int, b:int, d:int)
    requires 0<d;
    ensures a%d + b%d == (a+b)%d + d*((a%d + b%d)/d);
    ensures (a%d + b%d) < d ==> a%d + b%d == (a+b)%d;
{
    calc {
        a%d + b%d;
            { lemma_fundamental_div_mod(a%d+b%d, d); }
        d*((a%d + b%d)/d) + (a%d + b%d)%d;
            { lemma_add_mod_noop(a, b, d); }
        d*((a%d + b%d)/d) + (a+b)%d;
    }
    if ((a%d + b%d) < d)
    {
        lemma_mod_properties();
        assert 0 <= a%d + b%d;
        lemma_small_div();
        assert (a%d + b%d)/d == 0;
        lemma_mul_basics_forall();
        assert d*((a%d + b%d)/d) == d*0 == 0;
        calc {
            a%d + b%d;
            (a+b)%d + d*((a%d + b%d)/d);
            (a+b)%d;
        }
    }
}

static lemma lemma_mod_neg_neg(x:int, d:int)
    requires d > 0;
    ensures x%d == (x*(1-d))%d;
{
    calc {
        (x*(1-d)) % d;
            { lemma_mul_is_distributive_forall(); }
        (x - x*d) % d;
            { lemma_mul_unary_negation_forall(); }
        (x + -1*x*d) % d;
            { lemma_mul_is_associative_forall(); lemma_mul_is_commutative_forall(); }
        (x + (-x)*d) % d;
            { lemma_mul_is_commutative(-x,d); }
        (d*(-x) + x) % d;
            { lemma_mod_multiples_vanish(-x, x, d); }
        x % d;
    }
}

static lemma lemma_fundamental_div_mod_unique_helper(x:int, d:nat, q1:int, r1:nat, q2:int, r2:nat)
    requires 0 < d;
    requires r1 < d;
    requires r2 < d;
    requires q1 > q2;
    requires x == q1 * d + r1;
    requires x == q2 * d + r2;
    ensures  q1 == q2;
{
    calc ==> {
       true;
       d * q1 - d * q2 + r1 - r2 == 0;
         { lemma_mul_is_distributive_forall(); }
       d * (q1 - q2) + r1 - r2 == 0;
       d * (q1 - q2) == r2 - r1;
       { lemma_mul_increases(q1-q2, d); }
       r2 - r1 >= d;
       false;
    }
}

static lemma lemma_fundamental_div_mod_unique(x:int, d:nat, q1:int, r1:nat, q2:int, r2:nat)
    requires 0 < d;
    requires r1 < d;
    requires r2 < d;
    requires x == d * q1 + r1;
    requires x == d * q2 + r2;
    ensures  q1 == q2;
    ensures  r1 == r2;
{
    if q1 == q2 {
        calc <==> {
            x == x;
            d * q1 + r1 == d * q2 + r2;
            r1 == r2;
        }
    } else {
        if (q1 > q2) {
            lemma_fundamental_div_mod_unique_helper(x, d, q1, r1, q2, r2);
        } else {
            lemma_fundamental_div_mod_unique_helper(x, d, q2, r2, q1, r1);
        }
    }
}

static lemma lemma_fundamental_div_mod_converse(x:int, d:int, q:int, r:int)
    requires d != 0;
    requires 0 <= r < d;
    requires x == q * d + r;
    ensures q == x/d;
    ensures r == x%d;
{
    if q != x / d || r != x % d {
        calc ==> {
            true;
                { lemma_fundamental_div_mod(x, d); }
            x == d * (x / d) + (x % d);
            x == d * (x / d) + (x % d);
                { lemma_mul_is_commutative_forall(); 
                  lemma_fundamental_div_mod_unique(x, d, q, r, x / d, x % d); }
            false;
        }
    }
}

static lemma lemma_mod_pos_bound(x:int, m:int)
    decreases x;
    requires 0 <= x;
    requires 0 < m;
    ensures  0 <= x%m < m;
{
    if (x < m)
    {
        lemma_mod_is_mod_recursive_forall();
    }
    else
    {
        assert 0 <= x - m;
        lemma_mod_is_mod_recursive_forall();
        lemma_mod_pos_bound(x -m, m);
    }
}


static lemma lemma_mul_mod_noop_left(x:int, y:int, m:int)
    requires 0 < m;
    ensures (x % m)*y % m == x*y % m;
{
    calc {
        (x*y) % m;
            { lemma_fundamental_div_mod(x,m); }
        ((m*(x/m) + x%m) * y) % m;
            { lemma_mul_is_distributive_forall(); }
        ((m*(x/m))*y + (x%m)*y) % m;
            { lemma_mul_is_associative_forall(); }
        (m*((x/m)*y) + (x%m)*y) % m;
            { lemma_add_mod_noop(m*((x/m)*y), (x%m)*y, m); }
        (((m*((x/m)*y)) % m) + (((x%m)*y) % m)) % m;
        (((m*((x/m)*y) + 0) % m) + (((x%m)*y) % m)) % m;
            { lemma_mod_multiples_vanish((x/m)*y, 0, m); lemma_small_mod(0, m); }
        ((0 % m) + (((x%m)*y) % m)) % m;
        { lemma_mod_of_zero_is_zero(m); }
        (((x%m)*y) % m) % m;
            { lemma_mod_properties(); }
        ((x%m)*y) % m;
    }
}

static lemma lemma_mul_mod_noop_right(x:int, y:int, m:int)
    requires 0 < m;
    ensures x*(y % m) % m == (x*y) % m;
{
    lemma_mul_is_commutative_forall();
    lemma_mul_mod_noop_left(y, x, m);
}

static lemma lemma_mul_mod_noop_general(x:int, y:int, m:int)
    requires 0 < m;
    ensures ((x % m) * y      ) % m == (x * y) % m;
    ensures ( x      * (y % m)) % m == (x * y) % m;
    ensures ((x % m) * (y % m)) % m == (x * y) % m;
{
    lemma_mod_properties();
    lemma_mul_mod_noop_left(x, y, m);
    lemma_mul_mod_noop_right(x, y, m);
    lemma_mul_mod_noop_right(x % m, y, m);
}


static lemma lemma_mul_mod_noop(x:int, y:int, m:int)
    requires 0 < m;
    ensures (x % m) * (y % m) % m == (x*y) % m;
{
    lemma_mul_mod_noop_general(x, y, m);
}

static lemma lemma_power_mod_noop(b:int, e:nat, m:int)
    decreases e;
    requires 0 < m;
    ensures power(b % m, e) % m == power(b, e) % m;
{
    reveal_power();
    lemma_mod_properties();
    if (e > 0)
    {
        calc {
            power(b % m, e) % m;
            ((b % m) * power(b % m, e - 1)) % m;
            { lemma_mul_mod_noop_general(b, power(b % m, e - 1), m); }
            ((b % m) * (power(b % m, e - 1) % m) % m) % m;
            { lemma_power_mod_noop(b, e - 1, m); }
            ((b % m) * (power(b, e - 1) % m) % m) % m;
            { lemma_mul_mod_noop_general(b, power(b, e - 1), m); }
            (b * (power(b, e - 1)) % m) % m;
            (b * (power(b, e - 1))) % m;
            power(b, e) % m;
        }
    }
}

static lemma lemma_mod_subtraction(x:nat, s:nat, d:nat)
    requires 0<d;
    requires 0<=s<=x%d;
    ensures x%d - s%d == (x-s)%d;
{
    lemma_mod_properties();
    calc {
        (x-s)%d;
            { lemma_mod_multiples_vanish(-(x/d), x-s, d); }
        (x-s+d*(-(x/d))) % d;
            { lemma_mul_unary_negation(d, x/d); }
        (x-d*(x/d)-s) % d;
            { lemma_fundamental_div_mod(x,d); }
        (x%d-s) % d;
            { lemma_small_mod(x%d-s, d); }
        x%d-s;
            { lemma_small_mod(s, d); }
        x%d - s%d;
    }
}

static lemma lemma_mod_ordering(x:nat, k:nat, d:nat)
    requires 1<d;
    requires 0<k;
    ensures 0<d*k;
    ensures x%d <= x%(d*k);
{
    lemma_mul_strictly_increases(d,k);
    calc {
        x%d + d*(x/d);
            { lemma_fundamental_div_mod(x,d); }
        x;
            { lemma_fundamental_div_mod(x,d*k); }
        x%(d*k) + (d*k)*(x/(d*k));
            { lemma_mul_is_associative_forall(); }
        x%(d*k) + d*(k*(x/(d*k)));
    }
    calc {
        x%d;
            { lemma_mod_properties(); }
        (x%d) % d;
            { lemma_mod_multiples_vanish(x/d - k*(x/(d*k)), x%d, d); }
        (x%d + d*(x/d - k*(x/(d*k)))) % d;
            { lemma_mul_is_distributive_sub_forall(); }
        (x%d + d*(x/d) - d*(k*(x/(d*k)))) % d;
        (x%(d*k)) % d;
        <= {
            lemma_mod_properties();
            lemma_mod_decreases(x%(d*k), d); }
        x%(d*k);
    }
}

//////////////////////////////////////////////////////////////////////////////
//


static lemma lemma_mod_multiples_basic(x:int, m:int)
    requires m > 0;
    requires x >= 0;
    ensures  (x * m) % m == 0;
    decreases if x > 0 then x else -x;
{
    lemma_mod_is_mod_recursive_forall();
    if (x < 0) {
        calc {
            (x * m) % m;
            (x * m + m) % m;
            (x * m + 1*m) % m;
                { lemma_mul_is_distributive_forall(); }
            ((x+1)*m) % m;
                { lemma_mod_multiples_basic(x+1, m); }
            0;
        }
    } else if (x == 0) {
        calc {
            (x*m)%m;
                {
                    assert x<m;
                    lemma_small_mod(x,m);
                }
            x;
            0;
        }
    } else {
        calc {
            (x * m)%m;
            (x*m - m)%m;
            { lemma_mul_properties(); }
            (x*m - 1*m)%m;
            { lemma_mul_properties(); }
            ((x-1)*m)%m;
            { lemma_mod_multiples_basic(x-1, m); }
            0;
        }
    }
}

//-
//-////////////////////////////////////////////////////////////////////////////


/************************************************************
 *  Lemmas that depend on properties of both div and mod    *
 ************************************************************/

//-/////////////////////////////////////////////////////
//- Proof that div is recursive div
//-/////////////////////////////////////////////////////
static lemma lemma_div_plus_one(x:int, d:int)
    requires d > 0;
    //-requires x >= 0;
    ensures 1 + x / d == (d + x) / d;
{
    var A := (d + x) / d;
    var Z := 1 + x / d;
    calc {
        d * A;
        d * ((d + x) / d);
        { lemma_fundamental_div_mod(d+x, d); }
        (d + x) - ((d + x) % d);
        { lemma_add_mod_noop(d, x, d); lemma_mod_properties(); } 
        (d + x) - x % d;
        { lemma_fundamental_div_mod(x, d); }
        d + d * (x / d);
        { lemma_mul_is_distributive_forall(); } 
        d * (1 + x / d);
        d * Z;
    }
    lemma_mul_equality_converse(A, Z, d);
    lemma_mul_is_commutative_forall();
}

static lemma lemma_div_minus_one(x:int, d:int)
    requires d > 0;
    ensures -1 + x / d == (-d + x) / d;
{
    var A := (-d + x) / d;
    var Z := -1 + x / d;
    calc {
        d * A;
        d * ((-d + x) / d);
        { lemma_fundamental_div_mod(x-d, d); }
        (x - d) - ((x - d) % d);
        { lemma_sub_mod_noop(x, d, d); lemma_mod_properties(); } 
        (x - d) - x % d;
        { lemma_fundamental_div_mod(x, d); }
        -d + d * (x / d);
        { lemma_mul_is_distributive_forall(); } 
        d * (-1 + x / d);
        d * Z;
    }
    lemma_mul_equality_converse(A, Z, d);
    lemma_mul_is_commutative_forall();
}

static lemma lemma_mod_mod(x:int, a:int, b:int)
    requires 0<a;
    requires 0<b;
    ensures 0<a*b;
    ensures (x%(a*b))%a == x%a;
{
    lemma_mul_strictly_positive_forall();
    calc {
        x;
            { lemma_fundamental_div_mod(x, a*b); }
        (a*b)*(x/(a*b)) + x % (a*b);
            { lemma_mul_is_associative_forall(); }
        a*(b*(x/(a*b))) + x % (a*b);
            { lemma_fundamental_div_mod(x%(a*b), a); }
        a*(b*(x/(a*b))) + a*(x%(a*b)/a) + (x%(a*b))%a;
            { lemma_mul_is_distributive_forall(); }
        a*(b*(x/(a*b)) + x%(a*b)/a) + (x%(a*b))%a;
    }
    lemma_mod_properties();
    lemma_mul_is_commutative_forall();
    lemma_fundamental_div_mod_converse(x, a, b*(x/(a*b)) + x%(a*b)/a, (x%(a*b))%a);
}

static lemma lemma_div_is_div_pos(x:int, d:int)
    requires d > 0;
    decreases if x >= 0 then x else -(x-d);
    ensures my_div_pos(x, d) == x / d;
{
    if x < 0 {
        calc {
            my_div_pos(x, d);
            -1 + my_div_pos(x+d, d);
            { lemma_div_is_div_pos(x+d, d); } 
            -1 + (x+d) / d;
            { lemma_div_minus_one(x+d, d); }
            (-d + x + d) / d;
            x / d;
        }
    } else if x < d {
        lemma_small_div();
    } else {
        calc {
            my_div_pos(x, d);
            1 + my_div_pos(x-d, d);
            { lemma_div_is_div_pos(x-d, d); } 
            1 + (x-d) / d;
            { lemma_div_plus_one(x-d, d); }
            x / d;
        }
    }
}

static lemma lemma_div_is_div_recursive(x:int, d:int)
    requires d > 0;
    ensures my_div_recursive(x, d) == x / d;
{
    lemma_div_is_div_pos(x, d); 


//
//-    if d > 0 {
//-       lemma_div_is_div_pos(x, d); 
//-    } else {
//-        calc {
//-            my_div_recursive(x, d);
//-            -1 * my_div_pos(x, -1*d);
//-                { lemma_div_is_div_pos(x, -1*d); }
//-            -1 * (x / (-1*d));
//-                { lemma_negative_divisor(x, d); }
//-            x / d;
//-       }
//-    }
}

static lemma lemma_div_is_div_recursive_forall()
    ensures forall x:int, d:int :: d > 0 ==> my_div_recursive(x, d) == x / d;
{
    forall x:int, d:int | d > 0
        ensures my_div_recursive(x, d) == x / d;
    {
        lemma_div_is_div_recursive(x, d);
    }
}

//-/////////////////////////////////////////////////////

//-/////////////////////////////////////////////////////
//- Proof that mod is recursive mod
//-/////////////////////////////////////////////////////

static lemma lemma_mod_is_mod_recursive(x:int, m:int)
    requires m > 0;
    ensures my_mod_recursive(x, m) == x % m;
    decreases if x < 0 then -x + m else x;
{

    if x < 0 { 
        calc { 
            my_mod_recursive(x, m);
            my_mod_recursive(x + m, m);
                { lemma_mod_is_mod_recursive(x + m, m); }
            (x + m) % m;
                { lemma_add_mod_noop(x, m, m); } 
            ((x % m) + (m % m)) % m;
                { lemma_mod_basics(); }
            (x % m) % m;
                { lemma_mod_basics(); }
            x % m;
        }
    } else if x < m { 
        lemma_small_mod(x, m);
    } else {
        calc { 
            my_mod_recursive(x, m);
            my_mod_recursive(x - m, m);
                { lemma_mod_is_mod_recursive(x - m, m); }
            (x - m) % m;
                { lemma_sub_mod_noop(x, m, m); } 
            ((x % m) - (m % m)) % m;
                { lemma_mod_basics(); }
            (x % m) % m;
                { lemma_mod_basics(); }
            x % m;
        }
    }
}

static lemma lemma_mod_is_mod_recursive_forall()
    ensures forall x:int, d:int :: d > 0 ==> my_mod_recursive(x, d) == x % d;
{
    forall x:int, d:int | d > 0
        ensures my_mod_recursive(x, d) == x % d;
    {
        lemma_mod_is_mod_recursive(x, d);
    }
}

//-/////////////////////////////////////////////////////


static lemma lemma_basic_div(d:int)
    requires d > 0;
    ensures forall x :: 0 <= x < d ==> x / d == 0;
{
    lemma_div_is_div_recursive_forall();
}

static lemma lemma_odd_div(d:int)
    requires d >= 0;
    requires d % 2 == 1;
    ensures 2 * (d / 2) + 1 == d;
{
    lemma_div_is_div_recursive_forall();
    if (d >= 2)
    {
        lemma_odd_div(d - 2);
    }
}


static lemma lemma_div_is_ordered(x:int, y:int, z:int)
    requires x <= y;
    requires z > 0;
    ensures x / z <= y / z;
    decreases if x >= 0 then x else z - x;
{
    if (x < 0) {
        calc <= {
            x / z;
            { lemma_div_is_div_recursive_forall(); }
            -1 + (x+z)/z;
            { lemma_div_is_ordered(x+z, y+z, z); }
            -1 + (y+z) / z;
            { lemma_div_is_div_recursive_forall(); }
            y / z;
        }
    }
    else if (x < z) {
        lemma_small_div();
        lemma_div_pos_is_pos(y, z);
    } else {
        calc <= {
            x / z;
            { lemma_div_is_div_recursive_forall(); }
            1 + (x-z) / z;
            { lemma_div_is_ordered(x-z, y-z, z); }
            1 + (y-z) / z;
            { lemma_div_is_div_recursive_forall(); }
            y / z;
        }
    }
}

static lemma lemma_div_decreases(x:int, d:int)
    requires 0<x;
    requires 1<d;
    ensures x/d < x;
{
    if (x<d)
    {
        lemma_small_div();
    }
    else
    {
        lemma_mul_strictly_increases(d,x);
        assert x < d*x;
        calc ==> {
            x <= x/d;
                { lemma_mul_inequality(x, x/d, d); lemma_mul_is_commutative_forall(); }
            d*x <= d*(x/d);
            d*x + x%d <= d*(x/d) + x%d;
                { lemma_fundamental_div_mod(x,d);
                    assert d*(x/d) + x%d == x;
                }
            d*x + x%d <= x;
                { lemma_mod_properties(); }
            d*x <= x;
            false;
        }
    }
}

static lemma lemma_div_nonincreasing(x:int, d:int)
    requires 0<=x;
    requires 0<d;
    ensures x/d <= x;
{
    if (1==d)
    {
        lemma_div_basics(x);
    }
    else if (x==0)
    {
        lemma_small_div();
    }
    else
    {
        lemma_div_decreases(x, d);
    }
}

lemma lemma_breakdown(a:int, b:int, c:int)
    requires 0<=a;
    requires 0<b;
    requires 0<c;
    ensures 0<b*c;
    ensures a%(b*c) == b * ((a/b)%c) + a%b;
{
    lemma_mul_strictly_positive_forall();
    lemma_div_pos_is_pos(a,b);
    assert 0<=a/b;

//-    lemma_mod_properties();
//-    assert a%b < b;
//-    assert 1<c;
//-    calc {
//-        b;
//-        <    { lemma_mul_strictly_increases(c,b); }
//-        c*b;
//-            { lemma_mul_is_commutative_forall(); }
//-        b*c;
//-    }
//-    lemma_mod_properties();
//-    assert (a%b)%(b*c) < b;

    calc {
        (b*(a/b)) % (b*c) + (a%b) % (b*c);
        <=    { lemma_part_bound1(a, b, c); }
        b*(c-1) + (a%b) % (b*c);
        <    { lemma_part_bound2(a, b, c); }
        b*(c-1) + b;
            { lemma_mul_basics_forall(); }
        b*(c-1) + mul(b,1);
            { lemma_mul_is_distributive_forall(); }
        b*(c-1+1);
        b*c;
    }

    calc {
        a % (b*c);
            { lemma_fundamental_div_mod(a,b); }
        (b*(a/b)+a%b) % (b*c);
            {
                lemma_mod_properties();
                assert 0<=a%b;
                lemma_mul_nonnegative(b,a/b);
                assert (b*(a/b)) % (b*c) + (a%b) % (b*c) < b*c;
                lemma_mod_adds(b*(a/b), a%b, b*c);
            }
        (b*(a/b)) % (b*c) + (a%b) % (b*c);
            {
                lemma_mod_properties();
                lemma_mul_increases(c,b);
                lemma_mul_is_commutative_forall();
                assert a%b<b<=b*c;
                lemma_small_mod(a%b,b*c);
                assert (a%b) % (b*c) == a%b;
            }
        (b*(a/b)) % (b*c) + a%b;
            { lemma_truncate_middle(a/b,b,c); }
        b * ((a/b)%c) + a%b;
    }
}

static lemma lemma_remainder_upper(x:int, divisor:int)
    requires 0 <= x;
    requires 0 < divisor;
    ensures   x - divisor < x / divisor * divisor;
{
    if (x < divisor) {
        lemma_mul_properties();
        lemma_small_div();
    } else {
        calc {
            x / divisor * divisor;
            { lemma_div_is_div_recursive_forall(); }
            (1 + (x-divisor) / divisor) * divisor;
            { lemma_mul_properties(); }
            1*divisor + ((x-divisor)/divisor) * divisor;
            > { lemma_remainder_upper(x-divisor, divisor); }
            1*divisor + ((x - divisor) - divisor);
            { lemma_mul_properties(); }
            x-divisor;
        }
    }
}

static lemma lemma_remainder_lower(x:int, divisor:int)
    requires 0 <= x;
    requires 0 < divisor;
    ensures  x >= x / divisor * divisor;
{

    if (x < divisor) {
        lemma_mul_properties();
        lemma_small_div();
    } else {
        calc {
            x / divisor * divisor;
            { lemma_div_is_div_recursive_forall(); }
            (1 + (x-divisor) / divisor) * divisor;
            { lemma_mul_properties(); }
            1*divisor + ((x-divisor) / divisor) * divisor;
            <= { lemma_remainder_lower(x-divisor, divisor); }
            1*divisor + x - divisor;
            { lemma_mul_properties(); }
            x;
        }
    }
}

static lemma lemma_remainder(x:int, divisor:int)
    requires 0 <= x;
    requires 0 < divisor;
    ensures  0 <= x - x / divisor * divisor < divisor;
{
    lemma_remainder_upper(x, divisor);
    lemma_remainder_lower(x, divisor);
}


static lemma lemma_div_denominator(x:int,c:nat,d:nat)
    requires 0 <= x;
    requires 0<c;
    requires 0<d;
    ensures c * d != 0;
    ensures (x/c)/d == x / (c*d);
{
    lemma_mul_strictly_positive_forall();
    //-assert 0 < c*d;
    var R := x % (c*d);
    lemma_mod_properties();
    //-assert 0<=R;

    lemma_div_pos_is_pos(R,c);
    //-assert 0 <= R/c;
    if (R/c >= d) {
        lemma_fundamental_div_mod(R, c);
//-        assert R >= c*(R/c);
        lemma_mul_inequality(d, R/c, c);
        lemma_mul_is_commutative_forall();
//-        assert c*(R/c) >= c*d;
//-        assert R >= c*d;
        assert false;
    }
    assert R/c < d;

    lemma_mul_basics_forall();
    lemma_fundamental_div_mod_converse(R/c, d, 0, R/c);
    assert (R/c) % d == R/c;

    lemma_fundamental_div_mod(R, c);
    assert c*(R/c) + R%c == R;

    assert c*((R/c) % d) + R%c == R;

    var k := x/(c*d);
    lemma_fundamental_div_mod(x, c*d);
    assert x == (c*d)*(x/(c*d)) + x % (c*d);
    assert R == x - (c*d)*(x/(c*d));
    assert R == x - (c*d)*k;

    calc {
        c*((x/c)%d) + x%c;
            { lemma_mod_multiples_vanish(-k, x/c, d); lemma_mul_is_commutative_forall(); }
        c*((x/c+(-k)*d) % d) + x%c;
            { lemma_hoist_over_denominator(x, (-k)*d, c); }
        c*(((x+(((-k)*d)*c))/c) % d) + x%c;
            { lemma_mul_is_associative(-k,d,c); }
        c*(((x+((-k)*(d*c)))/c) % d) + x%c;
            { lemma_mul_unary_negation(k,d*c); }
        c*(((x+(-(k*(d*c))))/c) % d) + x%c;
            { lemma_mul_is_associative(k,d,c); }
        c*(((x+(-(k*d*c)))/c) % d) + x%c;
        c*(((x-k*d*c)/c) % d) + x%c;
            {
                lemma_mul_is_associative_forall();
                lemma_mul_is_commutative_forall();
            }
        c*((R/c) % d) + x%c;
        c*(R/c) + x%c;
            { lemma_fundamental_div_mod(R,c);
                assert R == c*(R/c) + R % c;
                lemma_mod_mod(x,c,d);
                assert R%c == x%c;
            }
        R;
            { lemma_mod_is_mod_recursive_forall(); }
        R%(c*d);
        (x-(c*d)*k) % (c*d);
            { lemma_mul_unary_negation(c*d,k); }
        (x+(c*d)*(-k)) % (c*d);
            { lemma_mod_multiples_vanish(-k, x, c*d); }
        x % (c*d);
    }
    calc ==> {
        c*(x/c) + x%c - R == c*(x/c) - c*((x/c)%d);
            { lemma_fundamental_div_mod(x,c); }
        x - R == c*(x/c) - c*((x/c)%d);
    }
    calc ==> {
        true;
            { lemma_fundamental_div_mod(x/c,d); }
        d*((x/c)/d) == x/c - ((x/c)%d);
        c*(d*((x/c)/d)) == c*(x/c - ((x/c)%d));
            { lemma_mul_is_associative_forall(); }
        (c*d)*((x/c)/d) == c*(x/c - ((x/c)%d));
            { lemma_mul_is_distributive_forall(); }
        (c*d)*((x/c)/d) == c*(x/c) - c*((x/c)%d);
        (c*d)*((x/c)/d) == x - R;
            { lemma_fundamental_div_mod(x, c*d); }
        (c*d)*((x/c)/d) == (c*d)*(x/(c*d)) + x%(c*d) - R;
        (c*d)*((x/c)/d) == (c*d)*(x/(c*d));
            { lemma_mul_one_to_one(c*d, (x/c)/d, x/(c*d)); }
        (x/c)/d == x/(c*d);
    }
}

static lemma lemma_mul_hoist_inequality(x:int, y:int, z:int)
    requires 0 <= x;
    requires 0 < z;
    ensures x*(y/z) <= (x*y)/z;
{
    calc {
        (x*y)/z;
            { lemma_fundamental_div_mod(y, z); }
        (x*(z*(y/z)+y%z))/z;
            { lemma_mul_is_distributive_forall(); }
        (x*(z*(y/z))+x*(y%z))/z;
        >=  {
            lemma_mod_properties();
            lemma_mul_nonnegative(x, y%z);
            lemma_div_is_ordered(x*(z*(y/z)), x*(z*(y/z))+x*(y%z), z); }
        (x*(z*(y/z)))/z;
            { lemma_mul_is_associative_forall();
              lemma_mul_is_commutative_forall(); }
        (z*(x*(y/z)))/z;
            { lemma_div_multiples_vanish(x*(y/z), z); }
        x*(y/z);
    }
}

static lemma lemma_indistinguishable_quotients(a:int, b:int, d:int)
    requires 0<d;
    requires 0 <= a - a%d <= b < a + d - a%d;
    ensures a/d == b/d;
{
    lemma_fundamental_div_mod(a,d);
    lemma_div_multiples_vanish(a/d, d);
    calc {
        a/d;
        (d*(a/d))/d;
        (a - a%d)/d;
        <=
            { lemma_div_is_ordered(a-a%d, b, d); }
        b/d;
    }
    if (b/d > a/d)
    {
        calc {
            a - a%d + d;
            d*(a/d)+d;
               { lemma_mul_basics_forall(); }
            d*(a/d)+d*1;
               { lemma_mul_is_distributive_forall(); }
            d*(a/d+1);
            <= { lemma_mul_inequality(a/d+1, b/d, d);
                 lemma_mul_is_commutative_forall(); }
            d*(b/d);
            <= { lemma_mod_properties(); 
                 lemma_fundamental_div_mod(b,d); }
            b;
        }
        assert false;
    }
}

static lemma lemma_truncate_middle(x:int, b:int, c:int)
    requires 0<=x;
    requires 0<b;
    requires 0<c;
    ensures 0<b*c;
    ensures (b*x)%(b*c) == b*(x%c);
{
    lemma_mul_strictly_positive_forall();
    lemma_mul_nonnegative_forall();
    calc {
        b*x;
            { lemma_fundamental_div_mod(b*x,b*c); }
        (b*c)*((b*x)/(b*c)) + (b*x)%(b*c);
            { lemma_div_denominator(b*x,b,c); }
        (b*c)*(((b*x)/b)/c) + (b*x)%(b*c);
            { lemma_mul_is_commutative_forall(); lemma_div_by_multiple(x,b); }
        (b*c)*(x/c) + (b*x)%(b*c);
    }
    calc ==> {
        true;
            { lemma_fundamental_div_mod(x,c); }
        x == c*(x/c) + x%c;
        b*x == b*(c*(x/c) + x%c);
            { lemma_mul_is_distributive_forall(); }
        b*x == b*(c*(x/c)) + b*(x%c);
            { lemma_mul_is_associative_forall(); }
        b*x == (b*c)*(x/c) + b*(x%c);
    }
}

static lemma lemma_div_multiples_vanish_quotient(x:int, a:int, d:int)
    requires 0<x;
    requires 0<=a;
    requires 0<d;
    ensures 0 < x*d;
    ensures a/d == (x*a)/(x*d);
{
    lemma_mul_strictly_positive(x,d);
    calc {
        (x*a)/(x*d);
            {
                lemma_mul_nonnegative(x,a);
                lemma_div_denominator(x*a, x, d); }
        ((x*a)/x) / d;
            { lemma_div_multiples_vanish(a, x); }
        a / d;
    }
}

static lemma lemma_round_down(a:int, r:int, d:int)
    requires 0<d;
    requires a%d == 0;
    requires 0<=r<d;
    ensures a==d*((a+r)/d);
{
    lemma_fundamental_div_mod(a,d);
    assert a==d*(a/d);

    calc {
        (a+r)%d;
            { lemma_fundamental_div_mod(a,d); }
        (d*(a/d)+r)%d;
            { lemma_mod_multiples_vanish(a/d, r, d); }
        r%d;
            { lemma_small_mod(r,d); }
        r;
    }
    calc {
        a+r;
            { lemma_fundamental_div_mod(a+r,d); }
        d*((a+r)/d)+(a+r)%d;
        d*((a+r)/d)+r;
    }
}


static lemma lemma_div_multiples_vanish_fancy(x:int, b:int, d:int)
    requires 0<d;
    requires 0<=b<d;
    ensures (d*x + b)/d == x;
{
    calc {
        d*x + b;
            { lemma_fundamental_div_mod(d*x + b, d); }
        d*((d*x + b)/d) + (d*x + b)%d;
            { lemma_mod_multiples_vanish(x, b, d); lemma_small_mod(b,d); }
        d*((d*x + b)/d) + b;
    }
    lemma_mul_one_to_one_forall();
}

static lemma lemma_div_multiples_vanish(x:int, d:int)
    requires 0<d;
    ensures (d*x)/d == x;
{
    lemma_div_multiples_vanish_fancy(x, 0, d);
}


static lemma lemma_div_by_multiple(b:int, d:int)
    requires 0 <= b;
    requires 0 < d;
    ensures  (b*d) / d == b;
{   
    lemma_div_multiples_vanish(b,d);
}


static lemma lemma_div_by_multiple_is_strongly_ordered(x:int, y:int, m:int, z:int)
    requires 0 < m;
    requires 0 <= x < y;
    requires y == m * z;
    requires z > 0;
    ensures     x / z < y / z;
{
    lemma_div_by_multiple(m, z);
    assert(y / z == m);

    var k := x / z;
    var r := x - x / z * z;
    lemma_remainder(x, z);
    lemma_div_pos_is_pos(x, z);

    assert r >= 0;
    assert k*z <= k*z + r < m*z;
    lemma_div_by_multiple(k, z);
    assert (k*z) / z == k;

    lemma_mul_properties();

    calc {
        x / z;
        k;
        <    { lemma_mul_strict_inequality_converse(k,m,z); }
        m;
        y / z;
    }
}

static lemma lemma_hoist_over_denominator(x:int, j:int, d:nat)
    requires 0<d;
    ensures x/d + j == (x+j*d) / d;
{
    lemma_fundamental_div_mod(x+j*d, d);
    assert x+j*d == d*((x+j*d)/d) + (x+j*d)%d;
    assert x == d*((x+j*d)/d) + (x+j*d)%d - j*d;
    lemma_mul_is_commutative_forall();
    assert x == d*((x+j*d)/d) + (x+d*j)%d - j*d;
    lemma_mod_multiples_vanish(j, x, d);
    assert x == d*((x+j*d)/d) + x%d - j*d;

    lemma_fundamental_div_mod(x, d);
    assert x == d*(x/d) + x%d;

    assert d*(x/d) == d*((x+j*d)/d) - j*d;
    assert d*(x/d) + j*d == d*((x+j*d)/d);
        { lemma_mul_is_commutative_forall(); lemma_mul_is_distributive_forall(); }
    assert d*(x/d + j) == d*((x+j*d)/d);
        { lemma_mul_one_to_one(d, x/d+j, (x+j*d)/d); }
    assert x/d + j == (x+j*d)/d;
}

lemma lemma_part_bound1(a:int, b:int, c:int)
    requires 0<=a;
    requires 0<b;
    requires 0<c;
    ensures 0<b*c;
    ensures (b*(a/b) % (b*c)) <= b*(c-1);
{
    lemma_mul_strictly_positive_forall();
    calc {
        b*(a/b) % (b*c);
            { lemma_fundamental_div_mod(b*(a/b),b*c); }
        b*(a/b) - (b*c)*((b*(a/b))/(b*c));
            { lemma_mul_is_associative_forall(); }
        b*(a/b) - b*(c*((b*(a/b))/(b*c)));
            { lemma_mul_is_distributive_forall(); }
        b*((a/b) - (c*((b*(a/b))/(b*c))));
    }

    calc ==> {
        true;
            { lemma_mod_properties(); }
        b*(a/b) % (b*c) < b*c;
        b*((a/b) - (c*((b*(a/b))/(b*c)))) < b*c;
            { lemma_mul_is_commutative_forall(); lemma_mul_strict_inequality_converse_forall(); }
        ((a/b) - (c*((b*(a/b))/(b*c)))) < c;
        ((a/b) - (c*((b*(a/b))/(b*c)))) <= c-1;
            { lemma_mul_is_commutative_forall(); lemma_mul_inequality_forall(); }
        b*((a/b) - (c*((b*(a/b))/(b*c)))) <= b*(c-1);
        b*(a/b) % (b*c) <= b*(c-1);
    }
}

lemma lemma_part_bound2(a:int, b:int, c:int)
    requires 0<=a;
    requires 0<b;
    requires 0<c;
    ensures 0<b*c;
    ensures (a%b)%(b*c) < b;
{
    lemma_mul_strictly_positive_forall();
    lemma_mod_properties();
    assert a%b < b;
    lemma_mul_increases_forall();
    lemma_mul_is_commutative_forall();
    assert b <= b * c;
    assert 0 <= a%b < b * c;
    lemma_mod_properties();
    lemma_small_mod(a%b,b*c);
    assert (a%b)%(b*c) == a%b;
}

lemma lemma_mod_breakdown(a:int, b:int, c:int)
    requires 0<=a;
    requires 0<b;
    requires 0<c;
    ensures 0<b*c;
    ensures a%(b*c) == b * ((a/b)%c) + a%b;
{
    lemma_mul_strictly_positive_forall();
    lemma_div_pos_is_pos(a,b);
    assert 0<=a/b;

    calc {
        (b*(a/b)) % (b*c) + (a%b) % (b*c);
        <=    { lemma_part_bound1(a, b, c); }
        b*(c-1) + (a%b) % (b*c);
        <    { lemma_part_bound2(a, b, c); }
        b*(c-1) + b;
            { lemma_mul_basics_forall(); }
        b*(c-1) + mul(b,1);
            { lemma_mul_is_distributive_forall(); }
        b*(c-1+1);
        b*c;
    }

    calc {
        a % (b*c);
            { lemma_fundamental_div_mod(a,b); }
        (b*(a/b)+a%b) % (b*c);
            {
                lemma_mod_properties();
                assert 0<=a%b;
                lemma_mul_nonnegative(b,a/b);
                assert (b*(a/b)) % (b*c) + (a%b) % (b*c) < b*c;
                lemma_mod_adds(b*(a/b), a%b, b*c);
            }
        (b*(a/b)) % (b*c) + (a%b) % (b*c);
            {
                lemma_mod_properties();
                lemma_mul_increases(c,b);
                lemma_mul_is_commutative_forall();
                assert a%b<b<=b*c;
                lemma_small_mod(a%b,b*c);
                assert (a%b) % (b*c) == a%b;
            }
        (b*(a/b)) % (b*c) + a%b;
            { lemma_truncate_middle(a/b,b,c); }
        b * ((a/b)%c) + a%b;
    }
}


static lemma lemma_div_denominator_forall()
    ensures forall c:nat,d:nat :: 0 < c && 0 < d ==> c * d != 0;
    ensures forall x:int,c:nat,d:nat :: 0 <= x && 0 < c && 0 < d
        ==> (x/c)/d == x/(c*d);
{
    lemma_mul_nonzero_forall();
    forall (x:int,c:nat,d:nat | 0 <= x && 0 < c && 0 < d)
        ensures c * d != 0;
        ensures (x/c)/d == x/(c*d);
    {
        lemma_div_denominator(x,c,d);
    }
}
