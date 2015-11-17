include "power2.s.dfy"
include "power2.i.dfy"
include "../Util/be_sequences.s.dfy"

//-////////////////////////////////////////////////////////////////////////////
//- Pure bitwise operations -- "pure" in that they're defined over nats,
//- not Word32s.

static function BitAnd(x:nat, y:nat) : nat
    requires IsBit(x);
    requires IsBit(y);
    ensures IsBit(BitAnd(x,y));
{
    if x==1 && y==1 then 1 else 0
}

static function PureBitwiseAnd(x:nat, y:nat) : nat
   decreases x+y;
{
    


    
    if (x==0 || y==0) then
        0
    else
        PureBitwiseAnd(x/2, y/2)*2 + BitAnd(x%2, y%2)
}












static predicate SelectBit(b:nat, x:nat)
{
    (x/power2(b)) % 2 == 1
}

static lemma lemma_SelectBit_mod(b:nat, x:nat, y:nat)
    requires 0<=b<y;
    ensures 0<=x%power2(y);
    ensures SelectBit(b,x) == SelectBit(b,x%power2(y));
    decreases b;
{
    lemma_mod_properties();
    var L2:=2;
    if (b==0)
    {
        lemma_power2_0_is_1();
        calc {
            SelectBit(b,x);
                { lemma_div_basics(x); }
            x % 2 == 1;
                { lemma_mod_is_mod_boogie(x,2); }
            x % L2 == 1;
                { lemma_mod_mod(x, L2, power2(y-1)); }
            (x%(L2*power2(y-1))) % L2 == 1;
                { lemma_mul_is_mul_boogie(2,power2(y-1)); }
            (x%(2*power2(y-1))) % L2 == 1;
                { lemma_mod_is_mod_boogie(x%(2*power2(y-1)),2); }
            (x%(2*power2(y-1))) % 2 == 1;
                { reveal_power2(); }
            (x%power2(y)) % 2 == 1;
                { lemma_div_basics(x%power2(y)); }
            SelectBit(b,x%power2(y));
        }
    }
    else
    {
        lemma_mul_strictly_positive(L2, power2(y-1));
        lemma_mul_strictly_positive(L2, power2(b-1));
        calc {
            SelectBit(b,x);
            (x/power2(b)) % 2 == 1;
                { reveal_power2(); }
            (x/(2*power2(b-1))) % 2 == 1;
                { lemma_mul_is_mul_boogie(2,power2(b-1)); }
            (x/(L2*power2(b-1))) % 2 == 1;
                { lemma_div_denominator(x,2,power2(b-1)); }
            ((x/L2)/power2(b-1)) % 2 == 1;
                { lemma_div_is_div_boogie(x,2); }
            ((x/2)/power2(b-1)) % 2 == 1;
            SelectBit(b-1,x/2);
                { lemma_SelectBit_mod(b-1, x/2, y-1); }
            SelectBit(b-1,(x/2)%power2(y-1));
            (((x/2)%power2(y-1))/power2(b-1)) % 2 == 1;
            {
              calc {
                ((x/2)%power2(y-1));
                    { lemma_mask_div_mod(x,y); }
                (x%(power2(y)))/2;
                    { lemma_div_is_div_boogie(x%power2(y),2); }
                (x%(power2(y)))/L2;
                    { reveal_power2(); lemma_mul_is_mul_boogie(2,power2(y-1)); }
                (x%(L2*power2(y-1)))/L2;
              }
            }
            (((x%(L2*power2(y-1)))/L2)/power2(b-1)) % 2 == 1;
                { lemma_div_denominator(x%(L2*power2(y-1)),2,power2(b-1)); }
            ((x%(L2*power2(y-1)))/(L2*power2(b-1))) % 2 == 1;
                { lemma_mul_is_mul_boogie(2,power2(y-1));
                  lemma_mul_is_mul_boogie(2,power2(b-1)); }
            ((x%(2*power2(y-1)))/(2*power2(b-1))) % 2 == 1;
                { reveal_power2(); }
            ((x%power2(y))/power2(b)) % 2 == 1;
            SelectBit(b,x%power2(y));
        }
    }
}

static lemma lemma_SelectBit_div(b:nat, x:nat, y:nat)
    requires 0<=y<=b;
    ensures 0<=x/power2(y);
    ensures SelectBit(b,x) == SelectBit(b-y,x/power2(y));
    decreases b;
{
    lemma_div_pos_is_pos(x,power2(y));
    calc {
        x/power2(b);
            { lemma_power2_adds(y,b-y); }
        x/(power2(y)*power2(b-y));
            { lemma_div_denominator(x,power2(y),power2(b-y)); }
        (x/power2(y))/power2(b-y);
    }
}

static lemma lemma_SelectBit_overflow(b:nat, x:nat)
    requires x < power2(b);
    ensures SelectBit(b,x) == false;
{
    lemma_small_div();
}

static lemma lemma_SelectBit_zero(x:nat)
    ensures (x==0) <==> forall b:nat :: !SelectBit(b,x);
    decreases x;
{
    if (x==0)
    {
        forall (b:nat)
            ensures !SelectBit(b,x);
        {
            lemma_power2_positive();
            lemma_SelectBit_overflow(b,x);
        }
    }
    if (forall b:nat :: !SelectBit(b,x))
    {
        if (x==1)
        {
            lemma_power2_0_is_1();
            lemma_div_is_div_boogie(x,1);
            assert SelectBit(0,x);
        }
        else if (x>1)
        {
            lemma_SelectBit_zero(x/2);
            var b:nat :| SelectBit(b,x/2);
            var L2 := 2;
            calc {
                (x/power2(b+1)) % 2;
                    { reveal_power2(); }
                (x/(2*power2(b))) % 2;
                    { lemma_mul_is_mul_boogie(2,power2(b)); }
                (x/(L2*power2(b))) % 2;
                    { lemma_div_denominator(x,2,power2(b)); }
                ((x/L2)/power2(b)) % 2;
                    { lemma_div_is_div_boogie(x,2); }
                ((x/2)/power2(b)) % 2;
                1;
            }
            assert SelectBit(b+1,x);
            assert false;
        }
        assert x==0;
    }
}

static predicate BitwiseAndPredicate(x:nat, y:nat, z:nat)
{
    forall b:nat :: (SelectBit(b, x) && SelectBit(b, y)) == SelectBit(b, z)
}

static lemma lemma_mask_div_mod(x:nat, c:nat)
    requires 0<c;
    ensures (x/2)%power2(c-1) == (x % power2(c))/2;
{
    var k := c-1;
    var L2 := 2;
    lemma_div_pos_is_pos(x,L2);
    lemma_mod_properties();
    lemma_power2_positive();
    lemma_mul_nonnegative(L2, power2(k));
    calc {
        L2*((x/2) % power2(k));
            { lemma_div_is_div_boogie(x,2); }
        L2*((x/L2) % power2(k));
            { lemma_truncate_middle(x/L2, 2, power2(k)); }
        (L2*(x/L2)) % (L2*power2(k));
            { lemma_fundamental_div_mod(x, 2); }
        (x-x%L2) % (L2*power2(k));
        {
            lemma_mod_ordering(x, power2(k), 2);
            lemma_mod_subtraction(x, x%L2, L2*power2(k));
        }
        x % (L2*power2(k)) - (x%L2) % (L2*power2(k));
            { lemma_mod_properties();
              lemma_mul_strictly_increases(L2,power2(k));
              lemma_small_mod(x%L2, L2*power2(k)); }
        x % (L2*power2(k)) - x%L2;
            { lemma_mod_mod(x, L2, power2(k)); }
        x % (L2*power2(k)) - (x%(L2*power2(k)))%L2;
            { lemma_fundamental_div_mod(x%(L2*power2(k)), L2); }
        L2*((x%(L2*power2(k)))/L2);
            { reveal_power2(); lemma_mul_is_mul_boogie(2, power2(k)); }
        L2*((x%power2(c))/L2);
            { lemma_div_is_div_boogie(x%power2(c),2); }
        L2*((x%power2(c))/2);
    }
    lemma_mul_is_commutative_forall();
    lemma_mul_equality_converse((x/2) % power2(k), (x%power2(c))/2, 2);
}

static lemma lemma_and_mask(x:nat, c:nat)
    ensures x%power2(c) == PureBitwiseAnd(x, power2(c)-1);
    decreases c;
{
    if (x==0)
    {
        calc {
            PureBitwiseAnd(x, power2(c)-1);
            0;
                { lemma_small_mod(x, power2(c)); }
            x%power2(c);
        }
    }
    else if (c==0)
    {
        lemma_power2_0_is_1();
        var L1:=1;
        calc {
            PureBitwiseAnd(x, power2(c)-1);
            0;
                { lemma_mod_properties(); }
            x%L1;
            x%power2(c);
        }
    }
    else
    {
        var L2 := 2;
        calc {
            (power2(c)-1)%2;
                { reveal_power2(); }
            1;
        }
        calc {
            x%2;
                { lemma_mod_is_mod_boogie(x,2); }
            x%L2;
                { lemma_mod_mod(x,2,power2(c-1)); }
            (x%(L2*power2(c-1)))%L2;
                { reveal_power2(); lemma_mul_is_mul_boogie(2,power2(c-1)); }
            (x%power2(c))%L2;
                { lemma_mod_is_mod_boogie(x%power2(c),2); }
            (x%power2(c))%2;
        }
        calc {
            PureBitwiseAnd(x, power2(c)-1);
            PureBitwiseAnd(x/2, (power2(c)-1)/2)*2 + BitAnd(x%2, (power2(c)-1)%2);
                { lemma_mask_div_2(c); }
            PureBitwiseAnd(x/2, power2(c-1)-1)*2 + BitAnd(x%2, (power2(c)-1)%2);
                { lemma_and_mask(x/2, c-1); }
            ((x/2)%power2(c-1))*2 + BitAnd(x%2, (power2(c)-1)%2);
            ((x/2)%power2(c-1))*2 + BitAnd(x%2, 1);
            ((x/2)%power2(c-1))*2 + x%2;
                { lemma_mask_div_mod(x,c); }
            2*((x%power2(c))/2) + x%2;
            2*((x%power2(c))/2) + (x%power2(c))%2;
            x%power2(c);
        }
    }
}

static lemma lemma_mask_structure(c:nat, b:nat)
    ensures SelectBit(b, power2(c)-1) == (b<c);
{
    if (b<c)
    {
        var Lm1 := -1;
        var L2 := 2;
        calc {
            SelectBit(b, power2(c)-1);
            ((power2(c)-1)/power2(b)) % 2 == 1;
                { lemma_power2_adds(c-b,b); }
            ((power2(c-b)*power2(b)-1)/power2(b)) % 2 == 1;
                { lemma_hoist_over_denominator(-1, power2(c-b), power2(b)); }
            ((-1)/power2(b) + power2(c-b)) % 2 == 1;
                { reveal_power2(); }
            ((-1)/power2(b) + 2*power2(c-b-1)) % 2 == 1;
            (-1)/power2(b) % 2 == 1;
                { lemma_div_is_div_boogie(-1,power2(b));
                    lemma_mod_is_mod_boogie(Lm1/power2(b), 2); }
            (Lm1)/power2(b) % L2 == 1;
                { lemma_div_neg_neg(Lm1, power2(b)); }
            -((-Lm1+power2(b)-1)/power2(b)) % L2 == 1;
            -(power2(b)/power2(b)) % L2 == 1;
                { lemma_div_basics(power2(b)); }
            Lm1 % L2 == 1;
                { lemma_mod_is_mod_boogie(-1, 2); }
            -1 % L2 == 1;
        }
    }
    else
    {
        lemma_power2_increases(c,b);
        lemma_small_div();
    }
}

static lemma lemma_SelectBit_shift(b:nat, x:nat)
    ensures SelectBit(b+1, x) == SelectBit(b, x/2);
{
    var L2:=2;
    calc {
        SelectBit(b+1, x);
        (x/power2(b+1)) % 2 == 1;
            { reveal_power2(); }
        (x/(2*power2(b))) % 2 == 1;
            { lemma_mul_is_mul_boogie(2, power2(b)); }
        (x/(L2*power2(b))) % 2 == 1;
            { lemma_div_denominator(x,2,power2(b)); }
        ((x/L2)/power2(b)) % 2 == 1;
            { lemma_div_is_div_boogie(x, 2); }
        ((x/2)/power2(b)) % 2 == 1;
        SelectBit(b, x/2);
    }
}

static lemma lemma_BitwiseAndPredicate_inner(x:nat, y:nat, z:nat)
    requires 0<x;
    requires 0<y;
    ensures BitwiseAndPredicate(x,y,z) ==
        (BitwiseAndPredicate(x/2,y/2,z/2) && BitAnd(x%2,y%2)==z%2);
{
    lemma_power2_0_is_1();
    lemma_div_basics(x);
    lemma_div_basics(y);
    lemma_div_basics(z);
    if (BitwiseAndPredicate(x,y,z))
    {
        forall (b:nat)
            ensures (SelectBit(b, x/2) && SelectBit(b, y/2)) == SelectBit(b, z/2);
        {
            calc {
                SelectBit(b, x/2) && SelectBit(b, y/2);
                    { lemma_SelectBit_shift(b, x); }
                SelectBit(b+1, x) && SelectBit(b, y/2);
                    { lemma_SelectBit_shift(b, y); }
                SelectBit(b+1, x) && SelectBit(b+1, y);
                SelectBit(b+1, z);
                    { lemma_SelectBit_shift(b, z); }
                SelectBit(b, z/2);
            }
        }
        assert BitwiseAndPredicate(x/2,y/2,z/2);
        calc {
            (x % 2 == 1) && (y % 2 == 1);
            ((x/power2(0)) % 2 == 1) && ((y/power2(0)) % 2 == 1);
            SelectBit(0, x) && SelectBit(0, y);
            SelectBit(0, z);
            (z/power2(0)) % 2 == 1;
            z % 2 == 1;
        }
        assert BitAnd(x%2,y%2)==z%2;
    }

    if (BitwiseAndPredicate(x/2,y/2,z/2) && BitAnd(x%2,y%2)==z%2)
    {
        forall (b:nat)
            ensures (SelectBit(b, x) && SelectBit(b, y)) == SelectBit(b, z);
        {
            if (b==0)
            {
                assert (SelectBit(b, x) && SelectBit(b, y)) == SelectBit(b, z);
            }
            else
            {
                var L2:=2;
                lemma_power2_positive();
                lemma_mul_strictly_positive(2, power2(b-1));
                lemma_div_pos_is_pos(x,L2);
                lemma_div_pos_is_pos(y,L2);
                lemma_div_pos_is_pos(z,L2);
                calc {
                    SelectBit(b, x) && SelectBit(b, y);
                    ((x/power2(b)) % 2 == 1) && ((y/power2(b)) % 2 == 1);
                        { reveal_power2(); }
                    ((x/(2*power2(b-1))) % 2 == 1) && ((y/(2*power2(b-1))) % 2 == 1);
                        { lemma_mul_is_mul_boogie(2,power2(b-1)); }
                    ((x/(L2*power2(b-1))) % 2 == 1) && ((y/(L2*power2(b-1))) % 2 == 1);
                        { lemma_div_denominator(x,2,power2(b-1));
                            lemma_div_denominator(y,2,power2(b-1)); }
                    (((x/L2)/power2(b-1)) % 2 == 1) && (((y/L2)/power2(b-1)) % 2 == 1);
                    SelectBit(b-1, x/L2) && SelectBit(b-1, y/L2);
                        { lemma_div_is_div_boogie(x,2);
                          lemma_div_is_div_boogie(y,2); }
                    SelectBit(b-1, x/2) && SelectBit(b-1, y/2);
                        //- case hypothesis
                    SelectBit(b-1, z/2);
                        { lemma_div_is_div_boogie(z,2); }
                    SelectBit(b-1, z/L2);
                    ((z/L2)/power2(b-1)) % 2 == 1;
                        { lemma_div_denominator(z,2,power2(b-1)); }
                    (z/(L2*power2(b-1))) % 2 == 1;
                        { lemma_mul_is_mul_boogie(2,power2(b-1)); }
                    (z/(2*power2(b-1))) % 2 == 1;
                        { reveal_power2(); }
                    ((z/power2(b)) % 2 == 1);
                    SelectBit(b, z);
                }
            }
        }
        assert BitwiseAndPredicate(x,y,z);
    }
}

static lemma lemma_BitwiseAnd_equivalence(x:nat, y:nat, z:nat)
    ensures BitwiseAndPredicate(x,y,z) == (PureBitwiseAnd(x,y)==z);
{
    if (x==0)
    {
        lemma_SelectBit_zero(x);
        lemma_SelectBit_zero(z);
    }
    else if (y==0)
    {
        lemma_SelectBit_zero(y);
        lemma_SelectBit_zero(z);
    }
    else
    {
        calc {
            BitwiseAndPredicate(x,y,z);
                { lemma_BitwiseAndPredicate_inner(x,y,z); }
            BitwiseAndPredicate(x/2,y/2,z/2) && BitAnd(x%2,y%2)==z%2;
            BitwiseAndPredicate(x/2,y/2,z/2) && BitAnd(x%2,y%2)==z%2;
                { lemma_BitwiseAnd_equivalence(x/2, y/2, z/2); }
            PureBitwiseAnd(x/2,y/2)==z/2 && BitAnd(x%2,y%2)==z%2;
            (PureBitwiseAnd(x/2, y/2)*2 + BitAnd(x%2, y%2)) == z;
            (PureBitwiseAnd(x,y)==z);
        }
    }
}
