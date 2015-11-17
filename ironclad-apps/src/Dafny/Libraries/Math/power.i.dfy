include "power.s.dfy"
include "mul.i.dfy"

//-lemma lemma_mul_passes_harmlessly_through_mod(
//-    ensures mul(x,y) % m == mul(x

static lemma lemma_power_0(b:int)
    ensures power(b,0) == 1;
{
    reveal_power();
}

static lemma lemma_power_1(b:int)
    ensures power(b,1) == b;
{
    calc {
        power(b,1);
            { reveal_power(); }
        b*power(b,0);
            { lemma_power_0(b); }
        b*1;
            { lemma_mul_basics_forall(); }
        b;
    }
}

static lemma lemma_0_power(e:nat)
    requires e > 0;
    ensures power(0,e) == 0;
{
    reveal_power();
    lemma_mul_basics_forall();
    if (e != 1)
    {
        lemma_0_power(e - 1);
    }
}

static lemma lemma_1_power(e:nat)
    ensures power(1,e) == 1;
{
    reveal_power();
    lemma_mul_basics_forall();
    if (e != 0)
    {
        lemma_1_power(e - 1);
    }
}

static lemma lemma_power_adds(b:int, e1:nat, e2:nat)
    decreases e1;
    ensures power(b,e1)*power(b,e2) == power(b,e1+e2);
{
    if (e1==0)
    {
        calc {
            power(b,e1)*power(b,e2);
                { lemma_power_0(b); }
            1*power(b,e2);
                { lemma_mul_basics_forall(); }
            power(b,0+e2);
        }
    }
    else
    {
        calc {
            power(b,e1)*power(b,e2);
                { reveal_power(); }
            (b*power(b,e1-1))*power(b,e2);
                { lemma_mul_is_associative_forall(); }
            b*(power(b,e1-1)*power(b,e2));
                { lemma_power_adds(b, e1-1, e2); }
            b*power(b,e1-1+e2);
                { reveal_power(); }
            power(b,e1+e2);
        }
    }
}

static lemma lemma_power_multiplies(a:nat,b:nat,c:nat)
    decreases c;
    ensures 0<=b*c;
    ensures power(a,b*c) == power(power(a,b),c);
{
    lemma_mul_nonnegative(b,c);
    if (0==c)
    {
        lemma_mul_basics_forall();
        calc {
            power(a,b*c);
                { lemma_power_0(a); }
            1;
                { lemma_power_0(power(a,b)); }
            power(power(a,b),c);
        }
    }
    else
    {
        calc {
            b*c - b;
                { lemma_mul_basics_forall(); }
            b*c - mul(b,1);
                { lemma_mul_is_distributive_forall(); }
            b*(c-1);
        }
        lemma_mul_nonnegative(b,c-1);
        assert 0 <= b*c-b;

        calc {
            power(a,b*c);
            power(a,b+b*c-b);
                { lemma_power_adds(a,b,b*c-b); }
            power(a,b)*power(a,b*c-b);
            power(a,b)*power(a,b*(c-1));
                { lemma_power_multiplies(a,b,c-1); }
            power(a,b)*power(power(a,b),c-1);
                { reveal_power(); }
            power(power(a,b),c);
        }
    }
}

static lemma lemma_power_distributes(a:int, b:int, e:nat)
    decreases e;
    ensures power(a*b, e) == power(a, e) * power(b, e);
{
    reveal_power();
    lemma_mul_basics_forall();
    if (e > 0)
    {
        calc {
            power(a*b, e);
            (a*b) * power(a*b, e - 1);
            { lemma_power_distributes(a, b, e - 1); }
            (a*b) * (power(a, e - 1) * power(b, e - 1));
            { lemma_mul_is_associative_forall(); lemma_mul_is_commutative_forall(); }
            (a*power(a, e - 1)) * (b*power(b, e - 1));
            power(a,e) * power(b,e);
        }
        lemma_mul_is_distributive_forall();
    }
}

static lemma lemma_power_positive(b:int, e:nat)
    decreases e;
    requires 0<b;
    ensures 0<power(b,e);
{
    if (e==0)
    {
        reveal_power();
    }
    else
    {
        calc {
            power(b,e);
                { reveal_power(); }
            b*power(b,e-1);
            >    {
                    lemma_power_positive(b,e-1);
                    lemma_mul_strictly_positive_forall();
                }
            0;
        }
    }
}

static lemma lemma_power_increases(b:nat,e1:nat,e2:nat)
    requires 0<b;
    requires e1 <= e2;
    ensures power(b,e1) <= power(b,e2);
{
    calc {
        power(b,e1);
            { lemma_mul_basics_forall(); }
        mul(1,power(b,e1));
        <=    {
            lemma_power_positive(b, e2-e1);
            lemma_power_positive(b, e1);
            lemma_mul_inequality(1, power(b,e2-e1), power(b,e1));
        }
        power(b,e2-e1)*power(b,e1);
            { lemma_mul_is_commutative_forall(); }
        power(b,e1)*power(b,e2-e1);
            { lemma_power_adds(b,e1,e2-e1); }
        power(b,e2);
    }
}

static lemma lemma_power_strictly_increases(b:nat,e1:nat,e2:nat)
    requires 1<b;
    requires e1 < e2;
    ensures power(b,e1) < power(b,e2);
{
    calc {
        power(b,e1);
        <=  { lemma_power_increases(b,e1,e2-1); }
        power(b,e2-1);
        <  { lemma_power_1(b);
             lemma_power_positive(b,e2-1);
             lemma_power_positive(b,1);
             lemma_mul_strictly_increases(power(b,1), power(b,e2-1)); }
        power(b,1)*power(b,e2-1);
            { lemma_power_adds(b,1,e2-1); }
        power(b,e2);
    }
}

static lemma lemma_square_is_power_2(x:nat)
    ensures power(x,2) == x*x;
{
    calc {
        power(x,2);
            { reveal_power(); }
        x*power(x,1);
            { reveal_power(); }
        x*(x*power(x,0));
            { reveal_power(); }
        x*(x*1);
            { lemma_mul_basics_forall(); }
        x*x;
    }
}
