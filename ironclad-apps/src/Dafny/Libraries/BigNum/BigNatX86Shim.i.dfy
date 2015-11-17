include "Word32.i.dfy"
include "../../Drivers/CPU/assembly_premium.i.dfy"
include "../Util/seqs_and_ints.i.dfy"

static method Add32_two_arguments_ordered(a:nat, b:nat) returns (sum:nat, carry:nat)
    requires Word32(a);
    requires Word32(b);
    requires a<=b;
    ensures Word32(sum);
    ensures carry==0 || carry==1;
    ensures a+b == sum + 0x100000000 * carry;
{
    lemma_2toX();
    lemma_word32(a);
    lemma_word32(b);
    lemma_mod0x100000000(a + b);

    sum := asm_Add(a, b);
    carry := if sum < b then 1 else 0;

/*
    lemma_2toX();
    lemma_word32(a);
    lemma_word32(b);

    lemma_mod_properties();
    lemma_mod0x100000000(a+b);
    lemma_mod_is_mod_boogie(a+b, Width());
    lemma_mul_is_commutative_forall();

    var tsum := asm_Add(a, b);
    carry := if tsum < b then 1 else 0;

    if (a+b < Width())
    {
        calc {
            tsum;
            (a+b) % Width();
            a+b;
            >= b;
        }
        assert carry == 0;
        lemma_small_div();
        assert (a+b)/Width() == carry;
    } else {
        lemma_mod_properties();
        assert tsum < a+b;
        assert tsum < b;
        assert carry == 1;
        lemma_div_basics(Width());
        lemma_div_is_ordered(Width(), a+b, Width());
        assert 0 < (a+b)/Width();
        if (2 <= (a+b)/Width())
        {
            var L2 := 2;
            calc {
                2*Width();
                    { lemma_mul_is_mul_boogie(L2, Width()); }
                L2*Width();
                <= { lemma_mul_inequality(2, (a+b)/Width(), Width()); }
                ((a+b)/Width())*Width();
                <= { lemma_fundamental_div_mod(a+b, Width()); }
                a+b;
                <   { lemma_mul_strict_inequality_forall(); }
                Width() + Width();
            }
            assert false;
        }
        assert (a+b)/Width() < 2;
        assert (a+b)/Width() == carry;
    }

    calc {
        a+b;
            { lemma_fundamental_div_mod(a+b, Width()); }
        Width() * ((a+b)/Width()) + (a+b)%Width();
        Width() * ((a+b)/Width()) + tsum;
        Width() * carry + tsum;
        tsum + carry * Width();
    }
    sum := tsum;
*/
}

static method Add32_two_arguments(a:nat, b:nat) returns (sum:nat, carry:nat)
    requires Word32(a);
    requires Word32(b);
    ensures Word32(sum);
    ensures carry==0 || carry==1;
    ensures a+b == sum + 0x100000000 * carry;
{
    if (a<=b)
    {
        sum,carry := Add32_two_arguments_ordered(a, b);
    } else {
        sum,carry := Add32_two_arguments_ordered(b, a);
    }
}

static method Add32_with_carry(a:nat, b:nat, c:nat) returns (sum:nat, carry:nat)
    requires Word32(a);
    requires Word32(b);
    requires c==0 || c==1;
    ensures Word32(sum);
    ensures carry==0 || carry==1;
    ensures a+b+c == sum + carry * Width();
{
    lemma_2toX();
    lemma_word32(a);
    lemma_word32(b);
//-    lemma_mul_basics_forall();

    var psum,pcarry;
    if (a<=b)
    {
        psum,pcarry := Add32_two_arguments(a,b);
    } else {
        psum,pcarry := Add32_two_arguments(b,a);
    }
    var qsum,qcarry := Add32_two_arguments(c, psum);

/*
    assert a+b == psum + pcarry * Width();
    assert c == -psum + qsum + qcarry * Width();
    assert a+b+c == pcarry * Width() + qsum + qcarry * Width();
    calc {
        pcarry * Width() + qcarry * Width();
            { lemma_mul_is_distributive_forall(); }
        (pcarry + qcarry) * Width();
    }
    assert a+b+c == (pcarry + qcarry) * Width() + qsum;
    assert 0 <= pcarry <= 1;
    assert 0 <= qcarry <= 1;
*/

    sum := qsum;
    var zcarry;
    carry,zcarry := Add32_two_arguments(pcarry, qcarry);
    lemma_mul_is_mul_boogie(carry, 0x100000000);

/*
    if (zcarry > 0)
    {
        calc {
            Width();
            <=  { lemma_mul_increases(zcarry, Width()); }
            zcarry * Width();
            <=
            carry + zcarry * Width();
            pcarry + qcarry;
            <=
            2;
        }
    }
    assert zcarry == 0;
    lemma_mul_basics(zcarry);
*/
}

static method Sub32_two_arguments(a:nat, b:nat) returns (difference:nat, carry:nat)
    requires Word32(a);
    requires Word32(b);
    ensures Word32(difference);
    ensures carry==0 || carry==1;
    ensures a-b == difference - 0x100000000 * carry;
{
    lemma_2toX();
    lemma_word32(a);
    lemma_word32(b);

//-    lemma_mod_properties();
    lemma_mod0x100000000(a-b);
//-    lemma_mod_is_mod_boogie(a-b, Width());
//-    lemma_mul_is_commutative_forall();

    difference := asm_Sub(a, b);
    carry := if a>=b then 0 else 1;

}

static method Sub32_with_borrow(a:nat, b:nat, c:nat) returns (difference:nat, carry:nat)
    requires Word32(a);
    requires Word32(b);
    requires c==0 || c==1;
    ensures Word32(difference);
    ensures carry==0 || carry==1;
    ensures a-b-c == difference - carry * Width();
{
    lemma_2toX();
//-    lemma_mul_is_distributive_forall();
//-    lemma_mul_basics_forall();

    var pdiff, pcarry, qcarry;
    pdiff, pcarry := Sub32_two_arguments(a,b);
    difference, qcarry := Sub32_two_arguments(pdiff, c);
    carry := if (pcarry == 1 || qcarry == 1) then 1 else 0;
    assert carry == pcarry + qcarry;
    lemma_mul_is_mul_boogie(carry, 0x100000000);
}

static method Product32(a:nat, b:nat) returns (l:nat, h:nat)
    requires Word32(a);
    requires Word32(b);
    ensures Word32(l);
    ensures Word32(h);
    ensures l+(h*Width()) == a*b;
{
    lemma_2toX();
    lemma_word32_Word32();
    var hi,lo := asm_Mul64(a,b);

    ghost var ab := a*b;

    calc {
        a*b;
        ab;
            { lemma_fundamental_div_mod(ab, 0x100000000); }
        0x100000000 * (ab / 0x100000000) + ab % 0x100000000;
            { lemma_mod0x100000000(ab); } 
        0x100000000 * (ab / 0x100000000) + mod0x100000000(ab); 
        0x100000000 * (ab / 0x100000000) + mod0x100000000(a*b); 
        0x100000000 * (ab / 0x100000000) + lo;
        0x100000000 * ((a*b) / 0x100000000) + lo;
            { lemma_mul_is_commutative_forall(); }
        ((a*b) / 0x100000000) * 0x100000000 + lo;
        hi * 0x100000000 + lo;
        hi * Width() + lo;
    }

    l := lo;
    h := hi;
}

static lemma lemma_small_division(n:nat, d:nat) 
    requires Word32(n);
    requires Word32(d);
    requires 0 < d;
    ensures (n / d) % 0x100000000 == n / d;
{
    lemma_2toX();
    if d == 1 {
    } else if n == 0 {
        lemma_div_of_0(d);
        assert 0 / d == 0;
        assert 0 % 0x100000000 == 0;
    } else {
        calc < {
            n / d;
            { lemma_div_decreases(n, d); }
            n;
            power2(32);
        }
        calc <= {
            0;
            { lemma_div_pos_is_pos(n, d); }
            n / d;
        }
        { lemma_small_mod(n / d, 0x100000000); }
    }
}

static method Divide32(n:nat, d:nat) returns (q:nat, r:nat)
    requires Word32(n);
    requires Word32(d);
    requires 0 < d;
    ensures Word32(q);
    ensures Word32(r);
    ensures 0<=r<d;
    ensures q*d + r == n;
{
    q := Asm_Div(n, d);
    r := Asm_Mod(n, d);

    lemma_2toX();

    calc {
        q*d + r;
        mod0x100000000(n / d) * d + (n % d);
        { lemma_mod0x100000000(n/d); }
        ((n / d) % 0x100000000) * d + (n % d);
        { lemma_small_division(n, d); }
        (n / d) * d + (n % d);
        { lemma_mul_is_commutative(n/d, d); }
        d * (n / d) + (n % d);
        { lemma_fundamental_div_mod(n, d); }
        n;
    }
    calc ==> {
        r == n % d;
        { lemma_mod_properties(); }
        0 <= r < d;
    }
}

