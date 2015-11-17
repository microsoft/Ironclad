//-include "../../BigNum/BigNatDiv.i.dfy"
//-include "../../BigNum/BigNum.i.dfy"
include "../../FatNat/FatInt.i.dfy"
include "division.i.dfy"

static predicate opposing_signs(x:int, y:int)
{
    x==0
    || y==0
    || (x<0 <==> y>=0)
}

datatype Egcd_data = Egcd_data_c(
        R:array<int>,
        X:FatInt,
        Y:FatInt,
        next_R:array<int>,
        next_R_zero:bool,
        next_X:FatInt,
        next_Y:FatInt
        );

datatype Egcd_ghost = Egcd_ghost_c(
        a:nat,
        b:nat
        );

predicate {:heap} Egcd_invariant(d:Egcd_data, g:Egcd_ghost)
    reads d.R;
    reads d.X.value;
    reads d.Y.value;
    reads d.next_R;
    reads d.next_X.value;
    reads d.next_Y.value;
{
    true
    && (WellformedFatNat(d.R))
    && (WellformedFatInt(d.X))
    && (WellformedFatInt(d.Y))
    && (WellformedFatNat(d.next_R))
    && (WellformedFatInt(d.next_X))
    && (WellformedFatInt(d.next_Y))
    && (J(d.R) != 0)
    && (g.b == 0
        ==> J(d.next_R)==0 && FIV(d.X) == 1 && FIV(d.Y) == 0)
    && (g.a * FIV(     d.X) + g.b * FIV(     d.Y) == J(     d.R))
    && (g.a * FIV(d.next_X) + g.b * FIV(d.next_Y) == J(d.next_R))
    //- && (gcd(J(A), g.b) == gcd(J(R), J(d.next_R)))
    && (forall c:nat :: is_gcd(J(d.R), J(d.next_R), c) ==> is_gcd(g.a, g.b, c))
    && ((J(d.next_R)==0) <==> (BEWordSeqToInt(d.next_R[..])==0))
    && (d.next_R_zero <==> J(d.next_R)==0)
}

predicate {:heap} Extended_gcd_requires(A:array<int>, B:array<int>)
    reads A;
    reads B;
{
       (A!=null)
    && (IsWordSeq(A[..]))
    && (B!=null)
    && (IsWordSeq(B[..]))
    && (1<=BEWordSeqToInt(A[..]))
    && (BEWordSeqToInt(B[..]) < BEWordSeqToInt(A[..]))
}

predicate {:heap} Extended_gcd_ensures(A:array<int>, B:array<int>, X:FatInt, Y:FatInt)
    reads A;
    reads B;
    reads X.value;
    reads Y.value;
    requires Extended_gcd_requires(A, B);
{
       (WellformedFatInt(X))
//-    && (X.value.Length < power2(27))
    && (WellformedFatInt(Y))
//-    && (Y.value.Length < power2(27))
    && (0 <= BEWordSeqToInt(A[..])*FIV(X) + BEWordSeqToInt(B[..])*FIV(Y))
    && (0 <= BEWordSeqToInt(B[..])) //- satisfy precondition. Need a premium.
    && (is_gcd(BEWordSeqToInt(A[..]), BEWordSeqToInt(B[..]), BEWordSeqToInt(A[..])*FIV(X) + BEWordSeqToInt(B[..])*FIV(Y)))

    //- These size constraints are used to show downstream modesty,
    //- but also to show that the solution for 'd' is within a phi of [0,phi).
    && ((FIV(X)==1 && FIV(Y)==0) || -BEWordSeqToInt(B[..]) <= FIV(X) <= BEWordSeqToInt(B[..]))
    && (-BEWordSeqToInt(A[..]) <= FIV(Y) <= BEWordSeqToInt(A[..]))
    && (opposing_signs(FIV(X), FIV(Y)))
    && (FIV(X)!=0 || FIV(Y)!=0)
}

method Extended_gcd_init(A:array<int>, B:array<int>) returns (d:Egcd_data, ghost g:Egcd_ghost)
    requires Extended_gcd_requires(A, B);
    ensures g.a == BEWordSeqToInt(A[..]);
    ensures g.b == BEWordSeqToInt(B[..]);
    ensures Egcd_invariant(d, g);
{
    ghost var a := J(A);
    ghost var b := J(B);

    lemma_2toX();
    var X := MakeSmallLiteralFatInt(1);
    var x_ref := X.value; //- do something real to X.value to convince dafnycc it's allocated
    var Y := MakeSmallLiteralFatInt(0);
    var y_ref := Y.value; //- do something real to Y.value to convince dafnycc it's allocated
    var      R := A;
    var next_R := B;
    var next_X := Y;
    var next_Y := X;

    calc {
        a * FIV(X) + b * FIV(Y);
        a * 1 + b * 0;
        a;
        J(R);
    }

    calc {
        a * FIV(next_X) + b * FIV(next_Y);
        a * 0 + b * 1;
        J(next_R);
    }

    var next_R_zero := FatNatIsZero(next_R);
    d := Egcd_data_c(R, X, Y, next_R, next_R_zero, next_X, next_Y);
    g := Egcd_ghost_c(a, b);
}

method {:timeLimitMultiplier 3} Extended_gcd_step(d:Egcd_data, ghost g:Egcd_ghost) returns (d':Egcd_data, ghost g':Egcd_ghost)
    requires Egcd_invariant(d, g);
    requires !d.next_R_zero;
    ensures Egcd_invariant(d', g');
    ensures g'==g;  
        
    ensures 0 <= J(d'.next_R) < J(d.next_R);
{
    var dr_ref := d.R; //- do something real to d.R to convince dafnycc it's allocated
    var dnr_ref := d.next_R; //- do something real to d.next_R to convince dafnycc it's allocated
    var dx_ref := d.X.value; //- do something real to d.X.value to convince dafnycc it's allocated
    var dy_ref := d.Y.value; //- do something real to d.Y.value to convince dafnycc it's allocated
    var dnx_ref := d.next_X.value; //- do something real to d.next_X.value to convince dafnycc it's allocated
    var dny_ref := d.next_Y.value; //- do something real to d.next_Y.value to convince dafnycc it's allocated

    var Q, M := FatNatDiv(d.R, d.next_R);
    calc {
        J(d.next_R)*J(Q);
            { lemma_mul_is_commutative_forall(); }
        J(Q)*J(d.next_R);
    }
    lemma_fundamental_div_mod_converse(J(d.R), J(d.next_R), J(Q), J(M));
    assert J(M) < J(d.next_R);
//-        lemma_modesty_word_value_equivalence(M);
//-        lemma_modesty_word_value_equivalence(d.next_R);

    var X' := FatIntMul(FatInt_ctor(false, Q), d.next_X);
    var x_ref := X'.value; //- do something real to X'.value to convince dafnycc it's allocated
    X' := FatIntSub(d.X, X');
    x_ref := X'.value; //- do something real to X'.value to convince dafnycc it's allocated
    assert WellformedFatInt(d.Y);
    assert WellformedFatInt(d.next_Y);
    var Y' := FatIntMul(FatInt_ctor(false, Q), d.next_Y);
    var y_ref := Y'.value; //- do something real to Y'.value to convince dafnycc it's allocated
    assert WellformedFatInt(d.Y);
    Y' := FatIntSub(d.Y, Y');
    y_ref := Y'.value; //- do something real to Y'.value to convince dafnycc it's allocated

    ghost var r := J(d.R);
    ghost var nr := J(d.next_R);
    ghost var x := FIV(d.X);
    ghost var y := FIV(d.Y);
    ghost var nx := FIV(d.next_X);
    ghost var ny := FIV(d.next_Y);
    ghost var x' := FIV(X');
    ghost var y' := FIV(Y');
    ghost var a := g.a;
    ghost var b := g.b;
    assert a * x + b * y == r; //- loop invariant
    assert a * nx + b * ny == nr; //- loop invariant
    calc {
//-        J(A)*FIV(X') + J(B)*FIV(Y');
        a * x' + b * y';
        a * (x - (r / nr) * nx) + b * (y - (r / nr) * ny);
        { lemma_mul_is_distributive(a, x, (r / nr) * nx); }
        { lemma_mul_is_distributive(b, y, (r / nr) * ny); }
        a * x + b * y - (a * ((r / nr) * nx) + b * ((r / nr) * ny));
        { lemma_mul_is_commutative_forall(); }
        { lemma_mul_is_associative_forall(); }
        a * x + b * y - (a * nx * (r / nr) + b * ny * (r / nr));
        { lemma_mul_is_distributive(r / nr, a * nx, b * ny); }
        a * x + b * y - (a * nx + b * ny) * (r / nr);
        r - nr * (r / nr);
        { lemma_fundamental_div_mod(r, nr); }
        r % nr;
        J(M);
    }

    forall g:nat
        ensures is_gcd(nr, r % nr, g) ==> is_gcd(a, b, g);
    {
        if (is_gcd(nr, r % nr, g))
        {
            calc ==> {
                divides(g, r % nr) && divides(g, nr);
                { lemma_divides_multiple(g, nr, r / nr); }
                divides(g, r % nr) && divides(g, nr * (r / nr));
                { lemma_divides_sum(g, r % nr, nr * (r / nr)); }
                divides(g, r % nr + nr * (r / nr));
                divides(g, nr * (r / nr) + r % nr);
                { lemma_fundamental_div_mod(r, nr); }
                divides(g, r);
            }
            forall x:int
                ensures g < x ==> !(divides(x, r) && divides(x, nr));
            {
                if (g < x && divides(x, r) && divides(x, nr))
                {
                    calc {
                        (r % nr) % x;
                        { lemma_fundamental_div_mod(nr, x); }
                        (r % (x * (nr / x) + nr % x)) % x;
                        (r % (x * (nr / x))) % x;
                        {
                            calc ==> {
                                true;
                                { lemma_nothing_bigger_divides(nr); }
                                x <= nr;
                                { lemma_div_is_ordered(x, nr, x); }
                                x / x <= nr / x;
                                { lemma_div_basics(x); }
                                1 <= nr / x;
                            }
                        }
                        { lemma_mod_mod(r, x, nr / x); }
                        r % x;
                    }

                    assert divides(x, r % nr);
                    assert false; //- due to is_gcd(nr, r % nr, g)
                }
            }
            assert is_gcd(r, nr, g);
            assert is_gcd(a, b, g); //- by loop invariant
        }
    }

    var next_R_zero := FatNatIsZero(M);
    d' := Egcd_data_c(d.next_R, d.next_X, d.next_Y, M, next_R_zero, X', Y');
    g' := Egcd_ghost_c(a, b);
}

method Extended_gcd_conclusion(A:array<int>, B:array<int>, d:Egcd_data, ghost g:Egcd_ghost) returns (X:FatInt, Y:FatInt)
    requires Extended_gcd_requires(A, B);
    requires Egcd_invariant(d, g);
    requires J(d.next_R)==0;    //- loop termination condition
    requires BEWordSeqToInt(A[..]) == g.a;
    requires BEWordSeqToInt(B[..]) == g.b;
    ensures Extended_gcd_ensures(A, B, X, Y);
{
    var dr_ref := d.R; //- do something real to d.R to convince dafnycc it's allocated
    var dnr_ref := d.next_R; //- do something real to d.next_R to convince dafnycc it's allocated
    var dx_ref := d.X.value; //- do something real to d.X.value to convince dafnycc it's allocated
    var dy_ref := d.Y.value; //- do something real to d.Y.value to convince dafnycc it's allocated
    var dnx_ref := d.next_X.value; //- do something real to d.next_X.value to convince dafnycc it's allocated
    var dny_ref := d.next_Y.value; //- do something real to d.next_Y.value to convince dafnycc it's allocated

    X := d.X;
    Y := d.Y;
    ghost var r := J(d.R);
    ghost var x := FIV(X);
    ghost var y := FIV(Y);
    ghost var a := g.a;
    ghost var b := g.b;

    calc {
        is_gcd(r, 0, r);
        { lemma_anything_divides_itself(r); }
        { lemma_anything_divides_zero(r); }
        { lemma_nothing_bigger_divides(r); }
        true;
    }

    assert is_gcd(r, 0, r);
    //- loop invariant: is_gcd(r, J(next_R), r) ==> is_gcd(a, b, r)
    //- loop termination: J(next_R) == 0
    assert is_gcd(a, b, r);
    //- loop invariant: r == a * x + b * y

    assert is_gcd(a, b, a * x + b * y);

    
    //- put x, y into canonical form where 0 <= y < a
    //-   y := y % a;
    //-   x := x + b * (y / a);
    calc {
        a * (x + b * (y / a)) + b * (y % a);
        { lemma_mul_is_distributive(a, x, b * (y / a)); }
        a * x + a * (b * (y / a)) + b * (y % a);
        calc {
            a * (b * (y / a));
                { lemma_mul_is_associative(a, b, y/a); }
            (a * b) * (y / a);
                { lemma_mul_is_commutative_forall(); }
            (b * a) * (y / a);
                { lemma_mul_is_associative(b, a, y/a); }
            b * (a * (y / a));
        }
        a * x + b * (a * (y / a)) + b * (y % a);
        { lemma_mul_is_distributive(b, a * (y / a), y % a); }
        a * x + b * (a * (y / a) + (y % a));
        { lemma_fundamental_div_mod(y, a); }
        a * x + b * y;
    }

    //- ensures -I(A) <= BV(Y) <= I(A);
//-    lemma_mod_remainder_specific(y, a);

    //- ensures (FIV(X)==1 && FIV(Y)==0) || -J(B) <= FIV(X) <= J(B);
    if (b == 0)
    {
        calc {
            x;
            x + 0 * (y / a);
            x + b * (y / a);
            1;
        }
        
        calc {
            y;
            y % a;
            0;
        }
//-
//-            
//-        calc {
//-            x == 1;
//-            //-{ lemma_mul_is_mul_boogie(b, y / a); }
//-            x + b * (y / a) == 1;
//-        }
//-        calc {
//-            y == 0;
//-            //-{ lemma_mod_is_mod_boogie(0, a); }
//-            y % a == 0;
//-        }
    }
    else
    {
        calc ==> {
            true;
            { lemma_nothing_bigger_divides(a); }
            { lemma_nothing_bigger_divides(b); }
            r <= a && r <= b;
        }
        calc ==> {
            0 <= y % a <= a - 1;
            { lemma_mul_inequality(y % a, a - 1, b); }
            { lemma_mul_inequality(0, y % a, b); }
//-            { lemma_mul_basics(b); }
            0 <= (y % a) * b <= (a - 1) * b;
            { lemma_mul_is_distributive(b, a, 1); }
//-            { lemma_mul_basics(b); }
            0 <= (y % a) * b <= a * b - b;
//-            { lemma_mul_is_commutative_forall(); }
            0 <= b * (y % a) <= a * b - b;
            a * (x + b * (y / a))     <= a * (x + b * (y / a)) + b * (y % a) <= a * (x + b * (y / a)) + a * b - b;
            a * (x + b * (y / a))     <= r                                   <= a * (x + b * (y / a)) + a * b - b;
            a * (x + b * (y / a))     <= r                                   <= a * (x + b * (y / a)) + a * b;
            { lemma_mul_is_distributive(a, x + b * (y / a), b); }
            a * (x + b * (y / a))     <= r                                   <= a * (x + b * (y / a) + b);
            { lemma_div_is_ordered(a * (x + b * (y / a)), r, a); }
            { lemma_div_is_ordered(r, a * (x + b * (y / a) + b), a); }
            a * (x + b * (y / a)) / a <= r / a                               <= a * (x + b * (y / a) + b) / a;
            { lemma_div_multiples_vanish(x + b * (y / a), a); }
            { lemma_div_multiples_vanish(x + b * (y / a) + b, a); }
            x + b * (y / a)           <= r / a                               <= x + b * (y / a) + b;
            { assert 0 <= r <= a; }
            { lemma_small_div(); }
//-            { lemma_div_basics(a); }
            x + b * (y / a)           <= 1                             &&  0 <= x + b * (y / a) + b;
            -b <= x + b * (y / a) <= b;
        }
    }

//-    assert Y.value.Length < power2(27);
    var YQ, YC := FatIntDiv(Y, FatInt_ctor(false, A));
    var yq_ref := YQ.value; //- do something real to YQ.value to convince dafnycc it's allocated
    var yc_ref := YC.value; //- do something real to YC.value to convince dafnycc it's allocated

    lemma_fundamental_div_mod_converse(FIV(Y), J(A), FIV(YQ), FIV(YC));
    assert J(YC.value) < J(A);
//-    lemma_modesty_word_value_equivalence(YC.value);
//-    lemma_modesty_word_value_equivalence(A);
    Y := YC;

    var XC := FatIntMul(FatInt_ctor(false, B), YQ);
    var xc_ref := XC.value; //- do something real to XC.value to convince dafnycc it's allocated
    X := FatIntAdd(X, XC);
    var x_ref := X.value; //- do something real to X.value to convince dafnycc it's allocated
//-    lemma_modesty_word_value_equivalence(X.value);
//-    lemma_modesty_word_value_equivalence(B);

    //- renaming these symbols to catch up with new values of X, Y
    x := FIV(X);
    y := FIV(Y);

    //- ensures FIV(X)!=0 || FIV(Y)!=0;
    calc <==> {
        x == 0 && y == 0;
        { assert is_gcd(a, b, a * x + b * y); lemma_mul_basics(a); lemma_mul_basics(b); }
//-        { lemma_mul_is_mul_boogie(a, 0); }
//-        { lemma_mul_is_mul_boogie(b, 0); }
        is_gcd(a, b, 0);
        false;
    }

    //- ensures opposing_signs(FIV(X), FIV(Y));
    if (b != 0)
    {
        calc ==> {
            1 <= x && 1 <= y;
            { lemma_mul_inequality(1, x, a); }
            { lemma_mul_inequality(1, y, b); }
//-            { lemma_mul_basics(a); }
//-            { lemma_mul_basics(b); }
            a <= x * a && b <= y * b;
//-            { lemma_mul_is_commutative_forall(); }
              { lemma_mul_is_commutative(a, b); lemma_mul_is_commutative(y, b); }
            a <= a * x && b <= b * y;
            a + b <= a * x + b * y;
            r     <  a * x + b * y;
            false;
        }
    }
    
//-    assert A.Length < power2(27);
//-    var Xc := CanonicalizeFatInt(X);
//-    ghost var pv := power2(32);
//-    lemma_2toX();
//-    assert x < a;
                      
//-    calc {
//-        BEDigitSeqToInt(pv, Xc.value[..]);
//-        BEDigitSeqToInt(pv, X.value[..]);
//-        <
//-        BEDigitSeqToInt(pv, A[..]);
//-    }
//-    lemma_CanonicalLength_inherit(pv, Xc.value[..], A[..], power2(27));
//-    assert (Xc.value.Length < power2(27));
//-
//-    var Yc := CanonicalizeFatInt(Y);
//-    lemma_CanonicalLength_inherit(pv, Yc.value[..], A[..], power2(27));
//-
//-    X := Xc;
//-    Y := Yc;

    assert a == BEWordSeqToInt(A[..]);
    assert b == BEWordSeqToInt(B[..]);
}

method Extended_gcd(A:array<int>, B:array<int>) returns (X:FatInt, Y:FatInt)
//-    decreases J(A);
    requires Extended_gcd_requires(A, B);
    ensures Extended_gcd_ensures(A, B, X, Y);
{
    var d;
    ghost var g;
    d,g := Extended_gcd_init(A, B);
    while (!d.next_R_zero)
        invariant Egcd_invariant(d, g);
        invariant g.a == BEWordSeqToInt(A[..]);
        invariant g.b == BEWordSeqToInt(B[..]);
        decreases J(d.next_R);
    {
        d, g := Extended_gcd_step(d, g);
    }
    X,Y := Extended_gcd_conclusion(A, B, d, g);
}
