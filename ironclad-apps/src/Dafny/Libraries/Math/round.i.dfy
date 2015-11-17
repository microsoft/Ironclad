include "round.s.dfy"
include "mul.i.dfy"
include "div.i.dfy"
include "../../Drivers/CPU/assembly_premium.i.dfy"

//-//////////////////////////////////////
//- RoundUpToMultiple
//-//////////////////////////////////////

static function method{:CompiledSpec} CompiledSpec_RoundUpToMultiple (x:int, m:int) : int
static function method{:CompiledSpec} CompiledSpec_DivideRoundingUp (x:int, m:int) : int
static function method{:CompiledSpec} CompiledSpec_DivideRoundingUp_premium (x:int, m:int) : int

static lemma lemma_RoundUpToMultiple_properties(x:int, m:int)
    requires m > 0;
    requires x >= 0;
    ensures RoundUpToMultiple(x, m) % m == 0;
    ensures x <= RoundUpToMultiple(x, m) < x + m;
    ensures RoundUpToMultiple(x, m) == (if x%m == 0 then x else x + m - x%m);
{
    var r := RoundUpToMultiple(x, m);

    lemma_div_pos_is_pos(x + m - 1, m);
    lemma_mod_multiples_basic(((x + m - 1) / m), m);

    ghost var a := x / m;
    ghost var b := x % m;
    lemma_div_pos_is_pos(x, m);
    lemma_mul_nonnegative(a, m);
    lemma_mul_is_commutative(a, m);
    lemma_fundamental_div_mod(x, m);
    assert x == m * a + b;

    if (b == 0) {
        calc {
            r;
            ((x + m - 1) / m) * m;
            ((m * a + m - 1) / m) * m;
            { lemma_fundamental_div_mod_converse(m * a + m - 1, m, a, m - 1); }
            a * m;
            x;
        }
    }
    else {
        calc <= { 1; { lemma_mod_properties(); } b; }
        calc <= { b; { lemma_mod_properties(); } m - 1; }
        lemma_mul_nonnegative(m, a+1);
        lemma_mul_is_commutative(m, a+1);
        calc {
            r;
            ((x + m - 1) / m) * m;
            ((m * a + b + m - 1) / m) * m;
            (((m * a + m) + b - 1) / m) * m;
            (((m * a + m * 1) + b - 1) / m) * m;
            { lemma_mul_is_distributive_add(m, a, 1); }
            ((m * (a + 1) + b - 1) / m) * m;
            { lemma_fundamental_div_mod_converse(m * (a+1) + b - 1, m, a + 1, b - 1); }
            (a + 1) * m;
            m * (a + 1);
            { lemma_mul_is_distributive_add(m, a, 1); }
            a * m + 1 * m;
            m * a + 1 * m;
            a * m + m;
        }
    }
}

static function RoundUpToMultiple_premium(x:int, m:int) : int
    requires m > 0;
    requires x >= 0;
    ensures RoundUpToMultiple(x, m) % m == 0;
    ensures x <= RoundUpToMultiple(x, m) < x + m;
    ensures RoundUpToMultiple(x, m) == (if x%m == 0 then x else x + m - x%m);
{
    lemma_RoundUpToMultiple_properties(x, m);
    RoundUpToMultiple(x, m)
}

//-//////////////////////////////////////
//- DivideRoundingUp
//-//////////////////////////////////////

static lemma Lemma_DivideRoundingUpPreservesWord32 (x:int, m:int)
    requires m > 0;
    ensures Word32(x) ==> Word32(DivideRoundingUp(x, m));
{
    if Word32(x) {
        if m == 1 {
            calc {
                DivideRoundingUp(x, m);
                (x / m) + (if x % m == 0 then 0 else 1);
                { Lemma_Mod1IsZero(x); }
                (x / m) + 0;
                x / m;
                { lemma_div_basics(x); }
                x;
            }
        }
        else {
            lemma_2toX();
            calc {
                0;
                <= { lemma_div_pos_is_pos(x, m); }
                x / m;
                <= (x / m) + (if x % m == 0 then 0 else 1);
                DivideRoundingUp(x, m);
           }
           calc {
                DivideRoundingUp(x, m);
                (x / m) + (if x % m == 0 then 0 else 1);
                <= (x / m) + 1;
                <= { lemma_div_is_ordered_by_denominator(x, 2, m); }
                (x / 2) + 1;
                <= power2(32) / 2 + 1;
            }
        }
    }
}

static lemma Lemma_Mod1IsZero (x:int)
    requires x >= 0;
    ensures x % 1 == 0;
{
    lemma_mod_is_mod_recursive_forall();
    if x >= 1 {
        Lemma_Mod1IsZero(x-1);
    }
}

static lemma Lemma_DivideRoundingUpProducesCeiling (x:int, m:int)
    requires x >= 0;
    requires m > 0;
    ensures x <= DivideRoundingUp(x, m) * m < x + m;
{
    if x % m == 0 {
        calc {
            DivideRoundingUp(x, m) * m;
            (x/m) * m;
            { lemma_mul_is_commutative(m, x/m); }
            m * (x/m);
            m * (x/m) + x % m;
            { lemma_fundamental_div_mod(x, m); }
            x;
        }
    }
    else {
        calc {
            DivideRoundingUp(x, m) * m;
            (x/m + 1) * m;
            { lemma_mul_is_commutative(m, x/m + 1); }
            m * (x/m + 1);
            { lemma_mul_is_distributive_add(m, x/m, 1); lemma_mul_is_mul_boogie(m, 1); }
            m * (x/m) + m * 1;
            m * (x/m) + m;
            { lemma_fundamental_div_mod(x, m); }
            x + m - x%m;
        }
        calc {
            x + m - x%m;
            > { lemma_mod_properties(); }
            x;
        }
        calc {
            x + m - x%m;
            < { lemma_mod_properties(); }
            x + m;
        }
    }
}

static lemma Lemma_DivideMultipleGeneral (x:int, y:int, m:int)
    requires m > 0;
    requires x >= 0;
    requires 0 <= y < m;
    ensures (x * m + y) / m == x;
{
    calc {
        x * m + y;
        { lemma_fundamental_div_mod(x * m + y, m); }
        m * ((x * m + y) / m) + ((x * m + y) % m);
        { lemma_mul_is_commutative(x, m); }
        { lemma_mod_multiples_vanish(x, y, m); }
        m * ((x * m + y) / m) + (y % m);
        { lemma_small_mod(y, m); }
        m * ((x * m + y) / m) + y;
        { lemma_mul_is_commutative(m, (x * m + y) / m); }
        ((x * m + y) / m) * m + y;
    }

    assert x * m == ((x * m + y) / m) * m;
    assert (x * m) / m == (((x * m + y) / m) * m) / m;
    lemma_div_by_multiple(x, m);
    lemma_mul_nonnegative(x, m);
    lemma_div_pos_is_pos(x * m + y, m);
    lemma_div_by_multiple((x * m + y) / m, m);
}

static lemma Lemma_DivideRoundingUpEquivalentFormula (x:int, m:int)
    requires x >= 0;
    requires m > 0;
    ensures DivideRoundingUp(x, m) == (x+m-1)/m;
    ensures DivideRoundingUp(x, m) == (x-1)/m+1;
{
    if x % m == 0 {
        calc {
            x+m-1;
            { lemma_fundamental_div_mod(x+m-1, m); }
            m * ((x+m-1)/m) + (x+m-1)%m;
            { lemma_small_mod(m-1, m); lemma_mod_adds(x, m-1, m); }
            m * ((x+m-1)/m) + m-1;
            { lemma_mul_is_commutative(m, (x+m-1)/m); }
            ((x+m-1)/m) * m + m-1;
        }
        assert x == ((x+m-1)/m) * m;
        lemma_div_pos_is_pos(x+m-1, m);
        lemma_div_by_multiple(((x+m-1)/m), m);
        assert x / m == ((x+m-1)/m);
    }
    else {
        calc {
            x + m - 1;
            { lemma_fundamental_div_mod(x, m); }
            m * (x/m) + (x%m) + m - 1;
            >= { lemma_mod_properties(); } m * (x/m) + 1 + m - 1;
            m * (x/m) + m;
            m * (x/m) + m * 1;
            { lemma_mul_is_distributive_add(m, x/m, 1); lemma_mul_is_mul_boogie(m, 1); }
            m * (x/m + 1);
            { lemma_mul_is_commutative(m, x/m+1); }
            (x/m + 1) * m;
        }

        calc {
            (x + m - 1) / m;
            >= { lemma_div_is_ordered((x/m + 1) * m, x + m - 1, m); }
            ((x/m + 1) * m) / m;
            { lemma_div_pos_is_pos(x, m); }
            { lemma_div_by_multiple(x/m + 1, m); }
            x/m + 1;
            DivideRoundingUp(x, m);
        }

        calc {
            x + m - 1;
            { lemma_fundamental_div_mod(x, m); }
            m * (x/m) + (x%m) + m - 1;
            < { lemma_mod_properties(); } m * (x/m) + m + m - 1;
            m * (x/m) + m * 1 + m - 1;
            { lemma_mul_is_distributive_add(m, x/m, 1); lemma_mul_is_mul_boogie(m, 1); }
            m * (x/m + 1) + m - 1;
            { lemma_mul_is_commutative(m, x/m+1); }
            (x/m + 1) * m + m - 1;
        }

        calc {
            (x + m - 1) / m;
            <= { lemma_div_is_ordered(x + m - 1, (x/m + 1) * m + m - 1, m); }
            ((x/m + 1) * m + m - 1) / m;
            { lemma_div_pos_is_pos(x, m); Lemma_DivideMultipleGeneral(x/m + 1, m-1, m); }
            x/m + 1;
            DivideRoundingUp(x, m);
        }
    }
    calc {
        (x-1)/m+1;
            { lemma_hoist_over_denominator(x-1, 1, m); }
        ((x-1)+mul(1,m)) / m;
            { lemma_mul_basics_forall(); }
        (x+m-1) / m;
    }
}

static function method DivideRoundingUp_premium (x:int, m:int) : int
    requires x >= 0;
    requires m > 0;
    ensures DivideRoundingUp_premium(x, m) == DivideRoundingUp(x, m);
    ensures DivideRoundingUp_premium(x, m) >= 0;
    ensures Word32(x) ==> Word32(DivideRoundingUp_premium(x, m));
    ensures x <= DivideRoundingUp_premium(x, m) * m < x + m;
    ensures DivideRoundingUp_premium(x, m) == (x + m - 1) / m;
    ensures DivideRoundingUp_premium(x, m) == (x-1)/m+1;
{
    calc {
        (x/m) + (if x % m == 0 then 0 else 1);
        >= x/m;
        >= { lemma_div_pos_is_pos(x, m); } 0;
    }
    Lemma_DivideRoundingUpPreservesWord32(x, m);
    Lemma_DivideRoundingUpProducesCeiling(x, m);
    Lemma_DivideRoundingUpEquivalentFormula(x, m);
    DivideRoundingUp(x, m)
}
