include "mul_nonlinear.i.dfy"

static function mul(x:int, y:int) : int { x*y }

//-////////////////////////////////////////////////////////////
//- Recursive definitions that can be handy for proving 
//- properties we can't or don't want to rely on nonlinear for
//-////////////////////////////////////////////////////////////

static function mul_recursive(x:int, y:int) : int
{
 if x >= 0 then mul_pos(x, y)
 else -1*mul_pos(-1*x, y)
}

static function mul_pos(x:int, y:int) : int
 requires x >= 0;
{
 if x == 0 then 0
 else y + mul_pos(x - 1, y)
}

static lemma lemma_mul_is_mul_recursive(x:int, y:int)
    ensures x * y == mul_recursive(x, y);
{
    if x >= 0 {
        lemma_mul_is_mul_pos(x, y);
    } else {
        var neg_x := -1 * x;
        calc {
            mul_recursive(x, y);
            -1 * mul_pos(-1*x, y);
            -1 * mul_pos(neg_x, y);
            { lemma_mul_is_mul_pos(neg_x, y); }
            -1 * (neg_x * y);
            { lemma_mul_is_associative(-1, neg_x, y); }
            (-1 * neg_x) * y;
            { lemma_mul_is_associative(-1, -1, x); }
            ((-1 * -1) * x) * y;
            x * y;
        }
    }
}

static lemma lemma_mul_is_mul_pos(x:int, y:int)
    requires x >= 0;
    ensures x * y == mul_pos(x, y);
{
   if x == 0 {
   } else {
       calc {
           y + mul_pos(x - 1, y);
           { lemma_mul_is_mul_pos(x - 1, y); }
           y + (x-1)*y;
           1*y + (x-1)*y;
           { lemma_mul_is_commutative_forall(); lemma_mul_is_distributive_add(y, 1, x-1); }
           (1 + x - 1) * y;
           x * y;
       }
   }
}

//-////////////////////////////////////////////////////////////////////////////
//-
//- Core lemmas, with named arguments.
//-
//-////////////////////////////////////////////////////////////////////////////

static lemma lemma_mul_basics(x:int)
    ensures 0*x == 0;
    ensures x*0 == 0;
    ensures 1*x == x;
    ensures x*1 == x;
{
}

static lemma lemma_mul_is_commutative(x:int, y:int)
    ensures x*y == y*x;
{
}

static lemma lemma_mul_ordering_general()
    ensures forall x:int, y:int, b:int :: (0 < x && 0 < y && 0 <= x*y < b) ==> x < b && y < b;
{
    forall x:int, y:int, b:int | 0 < x && 0 < y && 0 <= x*y < b
        ensures x < b && y < b;
    {
        lemma_mul_ordering(x, y, b);
    }
}

static lemma lemma_mul_is_mul_boogie(x:int, y:int)
{
}

static lemma lemma_mul_inequality(x:int, y:int, z:int)
    requires x <= y;
    requires z >= 0;
    ensures  x*z <= y*z;
{
    if z == 0 {
    } else {
        if (x == y) {
        } else {
            lemma_mul_strict_inequality(x, y, z);
        }
    }
}

static lemma lemma_mul_upper_bound(x:int, x_bound:int, y:int, y_bound:int)
    requires x <= x_bound;
    requires y <= y_bound;
    requires 0<=x;
    requires 0<=y;
    ensures x*y <= x_bound * y_bound;
{
    lemma_mul_inequality(x, x_bound, y);
    lemma_mul_inequality(y, y_bound, x_bound);
}

//- This lemma is less precise than the non-strict version, since
//- it uses two < facts to achieve only one < result. Thus, use it with
//- caution -- it may be throwing away precision you'll require later.
static lemma lemma_mul_strict_upper_bound(x:int, x_bound:int, y:int, y_bound:int)
    requires x < x_bound;
    requires y < y_bound;
    requires 0<=x;
    requires 0<=y;
    ensures x*y < x_bound * y_bound;
{
    if (y_bound==1)
    {
        lemma_mul_strictly_positive(x_bound, y_bound);
    }
    else
    {
        calc
        {
            x*y;
            <=  { lemma_mul_upper_bound(x, x_bound-1, y, y_bound-1); }
            (x_bound-1)*(y_bound-1);
            <   { lemma_mul_strict_inequality(x_bound-1, x_bound, y_bound-1); }
            (y_bound-1)*x_bound;
            <   { lemma_mul_strict_inequality(y_bound-1, y_bound, x_bound); }
            x_bound * y_bound;
        }
    }
}

static lemma lemma_mul_left_inequality(x:int, y:int, z:int)
    requires x > 0;
    ensures y <= z ==> x*y <= x*z;
    ensures y < z ==> x*y < x*z;
{
    lemma_mul_is_commutative_forall();
    lemma_mul_inequality_forall();
    lemma_mul_strict_inequality_forall();
}

static lemma lemma_mul_strict_inequality_converse(x:int, y:int, z:int)
    requires x*z < y*z;
    requires z >= 0;
    ensures  x < y;
{
    if (x >= y)
    {
        lemma_mul_inequality(y, x, z);
        assert false;
    }
}

static lemma lemma_mul_inequality_converse(x:int, y:int, z:int)
    requires x*z <= y*z;
    requires z > 0;
    ensures  x <= y;
{
    if (x > y)
    {
        lemma_mul_strict_inequality(y, x, z);
        assert false;
    }
}

static lemma lemma_mul_equality_converse(x:int, y:int, z:int)
    requires x*z == y*z;
    requires 0<z;
    ensures x==y;
{
    if (x<y)
    {
        lemma_mul_strict_inequality(x, y, z);
    }
    if (y<x)
    {
        lemma_mul_strict_inequality(y, x, z);
    }
}

static lemma lemma_mul_is_distributive_add_other_way(x:int, y:int, z:int)
    ensures (y + z)*x == y*x + z*x;
{
    lemma_mul_is_distributive_add(x, y, z);
    lemma_mul_is_commutative(x, y);
    lemma_mul_is_commutative(x, z);
    lemma_mul_is_commutative(x, y + z);
}

static lemma lemma_mul_is_distributive_sub(x:int, y:int, z:int)
    ensures x*(y - z) == x*y - x*z;
    decreases if x >=0 then x else -1*x;
{
    lemma_mul_is_mul_recursive_forall();
    if (x == 0) {
    } else if (x > 0) {
        lemma_mul_is_distributive_sub(x - 1, y, z);
    } else {
        lemma_mul_is_distributive_sub(x + 1, y, z);
    }
}

static lemma lemma_mul_is_distributive(x:int, y:int, z:int)
    ensures x*(y + z) == x*y + x*z;
    ensures x*(y - z) == x*y - x*z;
    ensures (y + z)*x == y*x + z*x;
    ensures (y - z)*x == y*x - z*x;
    ensures x*(y + z) == (y + z)*x;
    ensures x*(y - z) == (y - z)*x;
    ensures x*y == y*x;
    ensures x*z == z*x;
{
    lemma_mul_is_distributive_add(x, y, z);
    lemma_mul_is_distributive_sub(x, y, z);
    lemma_mul_is_commutative_forall();
}

static lemma lemma_mul_strictly_increases(x:int, y:int)
    requires 1 < x;
    requires 0 < y;
    ensures y < x*y;
{
    if (1 < x && 0 < y)
    {
        lemma_mul_strict_inequality(1,x,y);
    }
}

static lemma lemma_mul_increases(x:int, y:int)
    requires 0<x;
    requires 0<y;
    ensures y <= x*y;
{
    if (0 < x && 0 < y)
    {
        lemma_mul_inequality(1,x,y);
        assert y <= x*y;
    }
}

static lemma lemma_mul_nonnegative(x:int, y:int)
    requires 0 <= x;
    requires 0 <= y;
    ensures  0 <= x*y;
{
    if (x == 0) {
    } else if (y == 0) {
    } else {
        lemma_mul_strictly_positive(x, y);
    }
}

static lemma lemma_mul_unary_negation(x:int, y:int)
    ensures (-x)*y == -(x*y) == x*(-y);
{
    calc {
        (-x)*y;
            { lemma_mul_is_associative(-1,x,y); }
        -1*x*y;
            { lemma_mul_is_associative(-1,x,y); }
        -1*(x*y);
    }
    calc {
        x*(-y);
            { lemma_mul_is_commutative_forall(); }
        (-y)*x;
            { lemma_mul_is_associative(-1,y,x); }
        -1*y*x;
            { lemma_mul_is_associative(-1,y,x); }
        -1*(x*y);
            { lemma_mul_is_commutative_forall(); }
        -(x*y);
    }
}

static lemma lemma_mul_one_to_one_pos(m:int, x:int, y:int)
    requires 0<m;
    requires m*x == m*y;
    ensures x == y;
{
    lemma_mul_is_commutative(x,m);
    lemma_mul_is_commutative(y,m);
    if (x<y)
    {
        lemma_mul_strict_inequality(x,y,m);
        assert m*x < m*y;
    }
    else if (x>y)
    {
        lemma_mul_strict_inequality(y,x,m);
        assert m*y < m*x;
    }
    assert x==y;
}

static lemma lemma_mul_one_to_one(m:int, x:int, y:int)
    requires m!=0;
    requires m*x == m*y;
    ensures x == y;
{
    if (m>0)
    {
        lemma_mul_one_to_one_pos(m,x,y);
    }
    else
    {
        lemma_mul_unary_negation(m,x);
        lemma_mul_unary_negation(m,y);
        lemma_mul_one_to_one_pos(-m,x,y);
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

static lemma lemma_mul_is_mul_recursive_forall()
    ensures forall x:int, y:int :: x * y == mul_recursive(x, y);
{
    forall x:int, y:int
        ensures x * y == mul_recursive(x, y);
    {
        lemma_mul_is_mul_recursive(x, y);
    }
}

static lemma lemma_mul_basics_forall()
    ensures forall x:int :: 0*x == 0;
    ensures forall x:int :: x*0 == 0;
    ensures forall x:int :: 1*x == x;
    ensures forall x:int :: x*1 == x;
{
}

static lemma lemma_mul_is_commutative_forall()
    ensures forall x:int, y:int :: x*y == y*x;
{
}

static lemma lemma_mul_ordering_forall()
    ensures forall x:int, y:int, b:int ::
        0 < x && 0 < y && 0 <= x*y < b
        ==> x < b && y < b;
{
    forall (x:int, y:int, b:int | 0 < x && 0 < y && 0 <= x*y < b)
        ensures x < b && y < b;
    {
        lemma_mul_ordering(x,y,b);
    }
}

static lemma lemma_mul_strict_inequality_forall()
    ensures  forall x:int, y:int, z:int ::
        x < y && z>0 ==> x*z < y*z;
{
    forall (x:int, y:int, z:int | x < y && z>0)
        ensures x*z < y*z;
    {
        lemma_mul_strict_inequality(x, y, z);
    }
}

static lemma lemma_mul_inequality_forall()
    ensures  forall x:int, y:int, z:int ::
        x <= y && z>=0 ==> x*z <= y*z;
{
    forall (x:int, y:int, z:int | x <= y && z>=0)
        ensures x*z <= y*z;
    {
        lemma_mul_inequality(x, y, z);
    }
}

static lemma lemma_mul_strict_inequality_converse_forall()
    ensures  forall x:int, y:int, z:int ::
        x*z < y*z && z>=0 ==> x < y;
{
    forall (x:int, y:int, z:int | x*z < y*z && z>=0)
        ensures x < y;
    {
        lemma_mul_strict_inequality_converse(x,y,z);
    }
}

static lemma lemma_mul_inequality_converse_forall()
    ensures  forall x:int, y:int, z:int ::
        x*z <= y*z && z>0 ==> x <= y;
{
    forall (x:int, y:int, z:int | x*z <= y*z && z>0)
        ensures x <= y;
    {
        lemma_mul_inequality_converse(x,y,z);
    }
}

static lemma lemma_mul_is_distributive_add_forall()
    ensures forall x:int, y:int, z:int :: x*(y + z) == x*y + x*z;
{
    forall (x:int, y:int, z:int)
        ensures x*(y + z) == x*y + x*z;
    {
        lemma_mul_is_distributive_add(x,y,z);
    }
}

static lemma lemma_mul_is_distributive_sub_forall()
    ensures forall x:int, y:int, z:int :: x*(y - z) == x*y - x*z;
{
    forall (x:int, y:int, z:int)
        ensures x*(y - z) == x*y - x*z;
    {
        lemma_mul_is_distributive_sub(x,y,z);
    }
}

static lemma lemma_mul_is_distributive_forall()
    ensures forall x:int, y:int, z:int :: x*(y + z) == x*y + x*z;
    ensures forall x:int, y:int, z:int :: x*(y - z) == x*y - x*z;
    ensures forall x:int, y:int, z:int :: (y + z)*x == y*x + z*x;
    ensures forall x:int, y:int, z:int :: (y - z)*x == y*x - z*x;
{
    lemma_mul_is_distributive_add_forall();
    lemma_mul_is_distributive_sub_forall();
    lemma_mul_is_commutative_forall();
}

static lemma lemma_mul_is_associative_forall()
    ensures forall x:int, y:int, z:int :: x * (y * z) == (x * y) * z;
{
    forall (x:int, y:int, z:int)
        ensures x * (y * z) == (x * y) * z;
    {
        lemma_mul_is_associative(x,y,z);
    }
}

static lemma lemma_mul_nonzero_forall()
    ensures forall x:int, y:int :: x*y != 0 <==> x != 0 && y != 0;
{
    forall (x:int, y:int)
        ensures x*y != 0 <==> x != 0 && y != 0;
    {
        lemma_mul_nonzero(x,y);
    }
}

static lemma lemma_mul_nonnegative_forall()
    ensures forall x:int, y:int :: 0 <= x && 0 <= y ==> 0 <= x*y;
{
    forall (x:int, y:int | 0 <= x && 0 <= y)
        ensures 0 <= x*y;
    {
        lemma_mul_nonnegative(x,y);
    }
}

static lemma lemma_mul_unary_negation_forall()
    ensures forall x:int, y:int :: (-x)*y == -(x*y) == x*(-y);
{
    forall (x:int, y:int) 
        ensures (-x)*y == -(x*y) == x*(-y);
    {
        lemma_mul_unary_negation(x,y);
    }
}

static lemma lemma_mul_strictly_increases_forall()
    ensures forall x:int, y:int :: (1 < x && 0 < y) ==> (y < x*y);
{
    forall (x:int, y:int | 1 < x && 0 < y)
        ensures y < x*y;
    {
        lemma_mul_strictly_increases(x,y);
    }
}

static lemma lemma_mul_increases_forall()
    ensures forall x:int, y:int :: (0 < x && 0 < y) ==> (y <= x*y);
{
    forall (x:int, y:int | 0 < x && 0 < y)
        ensures y <= x*y;
    {
        lemma_mul_increases(x,y);
    }
}

static lemma lemma_mul_strictly_positive_forall()
    ensures forall x:int, y:int :: (0 < x && 0 < y) ==> (0 < x*y);
{
    forall (x:int, y:int | 0 < x && 0 < y)
        ensures 0 < x*y;
    {
        lemma_mul_strictly_positive(x,y);
    }
}

static lemma lemma_mul_one_to_one_forall()
    ensures forall m:int, x:int, y:int :: (m!=0 && m*x == m*y) ==> x==y;
{
    forall (m:int, x:int, y:int | m!=0 && m*x == m*y)
        ensures x==y;
    {
        lemma_mul_one_to_one(m, x, y);
    }
}

//////////////////////////////////////////////////////////////////////////////
//




//
//////////////////////////////////////////////////////////////////////////////

static lemma lemma_mul_properties()
    ensures forall x:int, y:int :: x*y == y*x;
    ensures forall x:int :: x*0 == 0*x == 0;
    ensures forall x:int :: x*1 == 1*x == x;
    ensures forall x:int, y:int, z:int :: x < y && z > 0 ==> x*z < y*z;
    ensures forall x:int, y:int, z:int :: x <= y && z >= 0 ==> x*z <= y*z;
    ensures forall x:int, y:int, z:int :: x*(y + z) == x*y + x*z;
    ensures forall x:int, y:int, z:int :: x*(y - z) == x*y - x*z;
    ensures forall x:int, y:int, z:int :: (y + z)*x == y*x + z*x;
    ensures forall x:int, y:int, z:int :: (y - z)*x == y*x - z*x;
    ensures forall x:int, y:int, z:int :: x*y*z == x*y*z;
    ensures forall x:int, y:int :: x*y != 0 <==> x != 0 && y != 0;
    ensures forall x:int, y:int :: 0 <= x && 0 <= y ==> 0 <= x*y;
    ensures forall x:int, y:int, b:int :: 0 < x && 0 < y && 0 <= x*y < b ==> x < b && y < b;
    ensures forall x:int, y:int :: (1 < x && 0 < y) ==> (y < x*y);
    ensures forall x:int, y:int :: (0 < x && 0 < y) ==> (y <= x*y);
    ensures forall x:int, y:int :: (0 < x && 0 < y) ==> (0 < x*y);
{
    lemma_mul_strict_inequality_forall();
    lemma_mul_inequality_forall();
    lemma_mul_is_distributive_forall();
    lemma_mul_is_associative_forall();
    lemma_mul_ordering_forall();
    lemma_mul_nonzero_forall();
    lemma_mul_nonnegative_forall();
    lemma_mul_strictly_increases_forall();
    lemma_mul_increases_forall();
}

lemma lemma_mul_cancels_negatives(a:int, b:int)
    ensures a*b == (-a)*(-b);
{
    lemma_mul_properties();
}

//- Kept for legacy reasons:
static function INTERNAL_mul_recursive(x:int, y:int) : int { mul_recursive(x, y) }
