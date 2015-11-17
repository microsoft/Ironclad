include "../Util/seqs_canonical.i.dfy"
include "FatNatDiv.i.dfy"
include "../FleetNat/FleetNatMUl.i.dfy"
include "CanonicalArrays.i.dfy"
include "WordBoundHack.i.dfy"






method FatNatModuloUsingReciprocal(X:array<int>, N:array<int>, Nreciprocal:FNDivReciprocal) returns (R:array<int>)
    requires X!=null && IsWordSeq(X[..]);
    requires N!=null && IsWordSeq(N[..]);
//-    requires X.Length < power2(27);
    requires 0 <= BEWordSeqToInt(X[..]);
    requires 0 < BEWordSeqToInt(N[..]);
    requires FNDivReciprocalValid(Nreciprocal, N);
    ensures R!=null && IsWordSeq(R[..]);
    ensures BEWordSeqToInt(X[..]) % BEWordSeqToInt(N[..]) == BEWordSeqToInt(R[..]);
    ensures BEWordSeqToInt(R[..]) < BEWordSeqToInt(N[..]);
{
    ProfileTally(Tally_FatNatMod(), 1);

    var Q:array<int>;
    Q,R := FatNatDivUsingReciprocal(X,N,Nreciprocal);

    lemma_mul_is_commutative_forall();
    lemma_fundamental_div_mod_converse(
        BEWordSeqToInt(X[..]), BEWordSeqToInt(N[..]), BEWordSeqToInt(Q[..]), BEWordSeqToInt(R[..]));
}

method FatNatModulo(X:array<int>, N:array<int>) returns (R:array<int>)
    requires X!=null && IsWordSeq(X[..]);
    requires N!=null && IsWordSeq(N[..]);
//-    requires X.Length < power2(27);
    requires 0 <= BEWordSeqToInt(X[..]);
    requires 0 < BEWordSeqToInt(N[..]);
    ensures R!=null && IsWordSeq(R[..]);
    ensures BEWordSeqToInt(X[..]) % BEWordSeqToInt(N[..]) == BEWordSeqToInt(R[..]);
    ensures BEWordSeqToInt(R[..]) < BEWordSeqToInt(N[..]);
{
    R := FatNatModuloUsingReciprocal(X, N, FNDivUnknownReciprocal());
}

lemma lemma_lengths_squared(pv:int, X:seq<int>, Y:seq<int>, e:nat, Z:seq<int>)
    requires pv==power2(32);
    requires IsDigitSeq(pv, X);
    requires IsDigitSeq(pv, Y);
//-    requires 0<BEWordSeqToInt(X);
//-    requires 0<BEWordSeqToInt(Y);
    requires |X| < power2(e);
    requires |Y| < power2(e);
    requires IsCanonicalDigitSeq(pv, Z);
    requires BEWordSeqToInt(X)*BEWordSeqToInt(Y)==BEWordSeqToInt(Z);
    ensures |Z| < power2(e+2);
{
    lemma_2toX();
    var Xv := BEWordSeqToInt(X);
    var Yv := BEWordSeqToInt(Y);
    var Zv := BEWordSeqToInt(Z);

    if (Xv==0 || Yv==0)
    {
        if (|Z|>0)
        {
            lemma_mul_basics_forall();
            calc {
                0;
                <   { lemma_power_positive(pv,|Z|-1);
                      lemma_mul_strictly_positive(Z[0], power(pv,|Z|-1)); }
                Z[0]*power(pv,|Z|-1);
                <=  { lemma_BEDigitSeqToInt_bound(pv, Z); }
                Zv;
            }
            assert false;
        }
        lemma_power2_positive();
    }
    else
    {
        calc {
            Zv;
            Xv*Yv;
            <=   {
                lemma_BEDigitSeqToInt_bound(pv, X);
                lemma_BEDigitSeqToInt_bound(pv, Y);
                lemma_mul_inequality(Xv, power(pv,|X|)-1, Yv);
                lemma_mul_inequality(Yv, power(pv,|Y|)-1, power(pv,|X|)-1);
                lemma_mul_is_commutative_forall();
                }
            (power(pv, |X|)-1) * (power(pv,|Y|)-1);
                { lemma_mul_is_distributive_forall(); }
            power(pv, |X|)*(power(pv, |Y|)-1) - mul(1,(power(pv, |Y|)-1));
                { lemma_mul_basics_forall(); }
            power(pv, |X|)*(power(pv, |Y|)-1) - (power(pv, |Y|)-1);
            <  {
                 reveal_BEDigitSeqToInt_private();
                 calc {
                    1;
                    <
                    pv;
                        { lemma_power_1(pv); }
                    power(pv,1);
                    <=  { lemma_power_increases(pv,1,|Y|); }
                    power(pv,|Y|);
                  }
                }
            power(pv, |X|)*(power(pv, |Y|)-1);
                { lemma_mul_is_distributive_forall(); }
            power(pv, |X|)*power(pv, |Y|)-mul(power(pv, |X|),1);
                { lemma_mul_basics_forall(); }
            power(pv, |X|)*power(pv, |Y|)-power(pv, |X|);
            <=  { lemma_power_positive(pv, |X|); }
            power(pv, |X|)*power(pv, |Y|)-1;
                { lemma_power_adds(pv, |X|, |Y|); }
            power(pv, |X|+|Y|)-1;
                { lemma_power2_unfolding(32, |X|+|Y|);
                  lemma_mul_is_mul_boogie(32, |X|+|Y|); }
            power2(32*(|X|+|Y|))-1;
            <=  {
                calc {
                    |X|+|Y|;
                    <
                    power2(e)+power2(e);
                        { lemma_mul_is_mul_boogie(2,power2(e)); }
                    mul(2,power2(e));
                        { lemma_power2_1_is_2(); }
                    mul(power2(1),power2(e));
                        { lemma_power2_adds(1,e); }
                    power2(e+1);
                }
                lemma_power2_increases(32*(|X|+|Y|), 32*power2(e+1)); }
            power2(32*power2(e+1));
                { lemma_power2_unfolding(32, power2(e+1));
                  lemma_mul_is_mul_boogie(32, power2(e+1)); }
            power(pv, power2(e+1));
            <=   { lemma_power2_strictly_increases(e+1,e+2);
                  lemma_power_increases(pv, power2(e+1), power2(e+2)-1); }
            power(pv, power2(e+2)-1);
        }
        lemma_CanonicalLengthBound(pv, Z, power2(e+2)-1);
        assert |Z| < power2(e+2);
    }
}

datatype FatNatModExp_data = FatNatModExp_data_c(
    bp2:int,
    B:array<int>,
    E:array<int>,
    N:array<int>,
    R:array<int>,
    ec:int,
    E1:array<int>,
    one:array<int>);

datatype FatNatModExp_ghost = FatNatModExp_ghost_c(
    Bv:int,
    Ev:int,
    Nv:int,
    Rv:int,
    E1v:int,
    Onev:int);

predicate FatNatRepresents(a:array<int>, av:int)
    reads a;
{
    a!=null
    && IsWordSeq(a[..])
    && BEWordSeqToInt(a[..]) == av
    && 0<=BEWordSeqToInt(a[..])     
}

predicate {:heap} FatNatModExp_invariant(d:FatNatModExp_data, g:FatNatModExp_ghost)
    reads d.B;
    reads d.E;
    reads d.N;
    reads d.R;
    reads d.E1;
    reads d.one;
{
    true
    && FatNatRepresents(d.B, g.Bv)
//-    && (d.B.Length < power2(25))
    && g.Bv != 0

    && FatNatRepresents(d.E, g.Ev)
    && (0 <= d.bp2 <= d.ec < power2(32))
    && FatNatBitCount(d.E[..], d.ec)

    && FatNatRepresents(d.N, g.Nv)
//-    && (d.N.Length < power2(25))
    && FatNatRepresents(d.R, g.Rv)

//-    && (IsCanonicalDigitSeq(power2(32), d.R[..]))
    && d.R != null
    && (IsWordSeq(d.R[..]))

//-    && (d.R.Length < power2(25))
    && (g.Rv < g.Nv)

    && FatNatRepresents(d.E1, g.E1v)
    && (g.E1v < power2(d.bp2))

    && FatNatRepresents(d.one, g.Onev)
    && g.Onev == 1

    && ((power(g.Bv,g.E1v) * power(g.Rv,power2(d.bp2))) % g.Nv
        == power(g.Bv,g.Ev) % g.Nv)
}

method FatNatModExp_init(
        B:array<int>,
        E:array<int>,
        N:array<int>)
    returns (d:FatNatModExp_data, ghost g:FatNatModExp_ghost)
    requires B!=null && IsWordSeq(B[..]);
    requires E!=null && IsWordSeq(E[..]);
    requires N!=null && IsWordSeq(N[..]);
    requires BEWordSeqToInt(B[..])!=0;
    requires 1 < BEWordSeqToInt(N[..]);
//-    requires BEWordSeqToInt(E[..]) < power2(power2(31));
//-    requires B.Length < power2(25);
//-    requires N.Length < power2(25);
    ensures FatNatModExp_invariant(d, g);
    ensures d.B == B;
    ensures d.E == E;
    ensures d.N == N;
{
    ghost var pv := power2(32);
    lemma_2toX32();
    lemma_mul_basics_forall();

    ghost var Bs := B[..];
    ghost var Bv := BEWordSeqToInt(Bs);
    ghost var Es := E[..];
    ghost var Ev := BEWordSeqToInt(Es);
    ghost var Ns := N[..];
    ghost var Nv := BEWordSeqToInt(Ns);

    lemma_BEDigitSeqToInt_bound(pv, Bs);
    lemma_BEDigitSeqToInt_bound(pv, Es);
    lemma_BEDigitSeqToInt_bound(pv, Ns);

    var one := MakeBELiteralArray(1);
    ghost var Ones := one[..];
    ghost var Onev := BEWordSeqToInt(Ones);

    var ec:nat := FatNatCountBits(E);
    constrain_word_from_overflowing(ec);
//-    if (power2(32) <= ec)
//-    {
//-        calc {
//-            power2(power2(31));
//-            <   { lemma_2toX32();
//-                lemma_power2_strictly_increases(power2(31), power2(32)-1); }
//-            power2(power2(32)-1);
//-            <=  { lemma_power2_increases(power2(32)-1, ec-1); }
//-            Ev;
//-            <
//-            power2(power2(31));
//-        }
//-        assert false;
//-    }
    d := FatNatModExp_data_c(ec, B, E, N, one, ec, E, one);
    g := FatNatModExp_ghost_c(Bv, Ev, Nv, Onev, Ev, Onev);

    lemma_1_power(power2(ec));
}

lemma {:heap} lemma_E_propagation(d:FatNatModExp_data, ghost g:FatNatModExp_ghost,
    E_subv:int, R_bigv:int, bp2':nat)
    requires FatNatModExp_invariant(d, g);
    requires 0<d.bp2;   //- loop continue condition
    requires 0 <= E_subv;
    requires bp2' == d.bp2-1;
    requires power2(bp2') <= g.E1v; //- case 'use_this_product' condition
    requires R_bigv == (g.Rv*g.Rv % g.Nv)*g.Bv;
    requires E_subv == g.E1v - power2(bp2');
    ensures mul(power(g.Bv,E_subv), power(R_bigv % g.Nv,power2(bp2'))) % g.Nv
        == power(g.Bv,g.Ev) % g.Nv;
{
    lemma_power2_increases(bp2', d.bp2);
    calc {
        mul(power(g.Bv,E_subv), power(R_bigv % g.Nv,power2(bp2'))) % g.Nv;
        mul(power(g.Bv,g.E1v-power2(bp2')), power((g.Rv*g.Rv % g.Nv)*g.Bv % g.Nv,power2(bp2'))) % g.Nv;
            { lemma_mul_mod_noop_general(power(g.Bv,g.E1v-power2(bp2')), power((g.Rv*g.Rv % g.Nv)*g.Bv % g.Nv,power2(bp2')), g.Nv); }
        mul(power(g.Bv,g.E1v-power2(bp2')), power((g.Rv*g.Rv % g.Nv)*g.Bv % g.Nv,power2(bp2')) % g.Nv) % g.Nv;
        calc {
            power(R_bigv % g.Nv,power2(bp2')) % g.Nv;
            power((g.Rv*g.Rv % g.Nv)*g.Bv % g.Nv,power2(bp2')) % g.Nv;
                { lemma_mul_mod_noop_general(g.Rv*g.Rv, g.Bv, g.Nv); }
            power(g.Rv*g.Rv*g.Bv % g.Nv,power2(bp2')) % g.Nv;
                { lemma_power_mod_noop(g.Rv*g.Rv*g.Bv, power2(bp2'), g.Nv); }
            power(g.Rv*g.Rv*g.Bv,power2(bp2')) % g.Nv;
                { lemma_power_distributes(g.Rv*g.Rv, g.Bv, power2(bp2')); }
            power(g.Rv*g.Rv,power2(bp2')) * power(g.Bv,power2(bp2')) % g.Nv;
                { lemma_square_is_power_2(g.Rv); }
            power(power(g.Rv,2),power2(bp2')) * power(g.Bv,power2(bp2')) % g.Nv;
                { lemma_power_multiplies(g.Rv, 2, power2(bp2')); }
            power(g.Rv,mul(2,power2(bp2'))) * power(g.Bv,power2(bp2')) % g.Nv;
                { lemma_mul_is_mul_boogie(2, power2(bp2')); }
            power(g.Rv,2*power2(bp2')) * power(g.Bv,power2(bp2')) % g.Nv;
                { reveal_power2(); }
            power(g.Rv,power2(bp2'+1)) * power(g.Bv,power2(bp2')) % g.Nv;
        }
        mul(power(g.Bv,g.E1v-power2(bp2')), power(g.Rv,power2(bp2'+1)) * power(g.Bv,power2(bp2')) % g.Nv) % g.Nv;
            { lemma_mul_mod_noop_general(power(g.Bv,g.E1v-power2(bp2')), power(g.Rv,power2(bp2'+1)) * power(g.Bv,power2(bp2')), g.Nv); }
        mul(power(g.Bv,g.E1v-power2(bp2')), power(g.Rv,power2(bp2'+1)) * power(g.Bv,power2(bp2'))) % g.Nv;
            { lemma_mul_is_associative_forall(); lemma_mul_is_commutative_forall(); }
        mul(power(g.Bv,g.E1v-power2(bp2')) * power(g.Bv,power2(bp2')), power(g.Rv,power2(bp2'+1))) % g.Nv;
            { lemma_power_adds(g.Bv, g.E1v-power2(bp2'), power2(bp2')); }
        (power(g.Bv,g.E1v) * power(g.Rv,power2(bp2'+1))) % g.Nv;
        power(g.Bv,g.Ev) % g.Nv;
    }
}

method FatNatModExp_step_add(d:FatNatModExp_data, Nreciprocal:FNDivReciprocal, ghost g:FatNatModExp_ghost,
    bp2':nat, E2:array<int>, ghost E2v:int,
    R2:array<int>, ghost R2v:int,
    R2modN:array<int>, ghost R2modNv:int)
    returns (E_sub:array<int>, ghost E_subv:int, R':array<int>, ghost Rv':int)
    requires FatNatModExp_invariant(d, g);
    requires 0<d.bp2;   //- loop continue condition
    requires bp2' == d.bp2-1;
    requires power2(bp2') <= g.E1v; //- case 'use_this_product' condition
    requires FatNatRepresents(E2, E2v);
    requires E2v == power2(bp2');
    requires FatNatRepresents(R2, R2v);
    requires R2v == g.Rv * g.Rv;
    requires FatNatRepresents(R2modN, R2modNv);
    requires R2modNv==R2v % g.Nv;
    requires FNDivReciprocalValid(Nreciprocal, d.N);
    ensures FatNatRepresents(R', Rv');
//-    ensures IsCanonicalDigitSeq(power2(32), R'[..]);
    ensures IsWordSeq(R'[..]);
    ensures Rv' < g.Nv;
    ensures FatNatRepresents(E_sub, E_subv);
    ensures E_subv < power2(bp2');
    ensures ((power(g.Bv,E_subv) * power(Rv',power2(bp2'))) % g.Nv
        == power(g.Bv,g.Ev) % g.Nv);
{
    var db_ref := d.B; //- do something real to d.B so dafnycc realizes it's allocated
    var de_ref := d.E; //- do something real to d.E so dafnycc realizes it's allocated
    var dn_ref := d.N; //- do something real to d.N so dafnycc realizes it's allocated
    var dr_ref := d.R; //- do something real to d.R so dafnycc realizes it's allocated
    var de1_ref := d.E1; //- do something real to d.E1 so dafnycc realizes it's allocated
    var done_ref := d.one; //- do something real to d.one so dafnycc realizes it's allocated
    var recip_ref := if Nreciprocal.FNDivKnownReciprocal? then Nreciprocal.TwoTo32wDividedByD else d.B; //- do something real to Nreciprocal.TwoTo32wDividedByD

    ghost var pv := power2(32);
    E_sub := FatNatSub(d.E1, E2);
    E_subv := BEWordSeqToInt(E_sub[..]);

    assert E_subv <= g.E1v;

    calc {
        E_subv;
        g.E1v - E2v;
        g.E1v - power2(bp2');
        <
        power2(bp2'+1) - power2(bp2');
            { reveal_power2(); }
        2*power2(bp2') - power2(bp2');
        power2(bp2');
    }

    var R_big_nc := FleetNatMul(R2modN, d.B);
//-    var R_big := CanonicalizeArray(R_big_nc);   //- UNDONE length constraints
    var R_big := R_big_nc;

    ghost var R_bigv := BEWordSeqToInt(R_big_nc[..]);
    lemma_E_propagation(d, g, E_subv, R_bigv, bp2');
    calc {
        0;
        <= { lemma_mod_properties(); }
        R2modNv;
    }
    lemma_mul_nonnegative(R2modNv, g.Bv);

    calc {
        R2modNv;
        <   { lemma_mod_properties(); }
        g.Nv;
    }
//-    lemma_CanonicalLength_inherit(pv, CanonicalizeSeq(pv, R2modN[..]), d.N[..], power2(25));
//-    lemma_lengths_squared(pv, CanonicalizeSeq(pv, R2modN[..]), d.B[..], 25, R_big[..]);
    var Rnc' := FatNatModuloUsingReciprocal(R_big, d.N, Nreciprocal);
    ghost var Rncv' := BEWordSeqToInt(Rnc'[..]);

//-  R' := CanonicalizeArray(Rnc');  //- UNDONE length constraints
    R' := Rnc';

    Rv' := BEWordSeqToInt(R'[..]);
    lemma_BEDigitSeqToInt_bound(pv, R'[..]);
}

method FatNatModExp_step_noadd(d:FatNatModExp_data, ghost g:FatNatModExp_ghost,
    bp2':nat, E2:array<int>, ghost E2v:int,
    R2:array<int>, ghost R2v:int,
    R2modN:array<int>, ghost R2modNv:int)
    returns (E_sub:array<int>, ghost E_subv:int, R':array<int>, ghost Rv':int)
    requires FatNatModExp_invariant(d, g);
    requires 0<d.bp2;   //- loop continue condition
    requires bp2' == d.bp2-1;
    requires g.E1v < power2(bp2'); //- case 'use_this_product' condition
    requires FatNatRepresents(E2, E2v);
    requires E2v == power2(bp2');
    requires FatNatRepresents(R2, R2v);
    requires R2v == g.Rv * g.Rv;
    requires FatNatRepresents(R2modN, R2modNv);
    requires R2modNv==R2v % g.Nv;
    ensures FatNatRepresents(R', Rv');
//-    ensures IsCanonicalDigitSeq(power2(32), R'[..]);
    ensures IsWordSeq(R'[..]);
    ensures Rv' < g.Nv;
    ensures FatNatRepresents(E_sub, E_subv);
    ensures E_subv < power2(bp2');
    ensures ((power(g.Bv,E_subv) * power(Rv',power2(bp2'))) % g.Nv
        == power(g.Bv,g.Ev) % g.Nv);
{
    E_sub := d.E1;
    E_subv := BEWordSeqToInt(E_sub[..]);
    calc {
        E_subv;
        g.E1v;
        < E2v;
        power2(bp2');
    }
    calc {
        mul(power(g.Bv,g.E1v), power(R2modNv,power2(bp2'))) % g.Nv;
            { lemma_mul_mod_noop_general(power(g.Bv,g.E1v), power(R2modNv,power2(bp2')), g.Nv); }
        mul(power(g.Bv,g.E1v), power(R2modNv,power2(bp2')) % g.Nv) % g.Nv;
        calc {
            power(R2modNv,power2(bp2')) % g.Nv;
            power(g.Rv*g.Rv % g.Nv,power2(bp2')) % g.Nv;
                { lemma_power_mod_noop(g.Rv*g.Rv, power2(bp2'), g.Nv); }
            power(g.Rv*g.Rv,power2(bp2')) % g.Nv;
                { lemma_square_is_power_2(g.Rv); }
            power(power(g.Rv,2),power2(bp2')) % g.Nv;
                { lemma_power_multiplies(g.Rv, 2, power2(bp2')); }
            power(g.Rv,mul(2,power2(bp2'))) % g.Nv;
                { lemma_mul_is_mul_boogie(2, power2(bp2')); }
            power(g.Rv,2*power2(bp2')) % g.Nv;
                { reveal_power2(); }
            power(g.Rv,power2(bp2'+1)) % g.Nv;
        }
        mul(power(g.Bv,g.E1v), power(g.Rv,power2(bp2'+1)) % g.Nv) % g.Nv;
            { lemma_mul_mod_noop_general(power(g.Bv,g.E1v), power(g.Rv,power2(bp2'+1)), g.Nv); }
        mul(power(g.Bv,g.E1v), power(g.Rv,power2(bp2'+1))) % g.Nv;
        power(g.Bv,g.Ev) % g.Nv;
    }

//-  R' := CanonicalizeArray(R2modN);  //- UNDONE length constraints
    R' := R2modN;

    Rv' := BEWordSeqToInt(R'[..]);
//-    assert IsCanonicalDigitSeq(power2(32), R'[..]);
    calc {
        Rv';
        R2modNv;
        R2v % g.Nv;
        <   { lemma_mod_properties(); }
        g.Nv;
    }
}

method FatNatModExp_step(d:FatNatModExp_data, Nreciprocal:FNDivReciprocal, ghost g:FatNatModExp_ghost)
    returns (d':FatNatModExp_data, ghost g':FatNatModExp_ghost)
    requires FatNatModExp_invariant(d, g);
    requires 0<d.bp2;   //- loop continue condition
    requires FNDivReciprocalValid(Nreciprocal, d.N);
    ensures FatNatModExp_invariant(d', g');
    ensures d'.B == d.B;
    ensures d'.E == d.E;
    ensures d'.N == d.N;
    ensures d'.bp2 < d.bp2;
{
    var db_ref := d.B; //- do something real to d.B so dafnycc realizes it's allocated
    var de_ref := d.E; //- do something real to d.E so dafnycc realizes it's allocated
    var dn_ref := d.N; //- do something real to d.N so dafnycc realizes it's allocated
    var dr_ref := d.R; //- do something real to d.R so dafnycc realizes it's allocated
    var de1_ref := d.E1; //- do something real to d.E1 so dafnycc realizes it's allocated
    var done_ref := d.one; //- do something real to d.one so dafnycc realizes it's allocated
    var recip_ref := if Nreciprocal.FNDivKnownReciprocal? then Nreciprocal.TwoTo32wDividedByD else d.B; //- do something real to Nreciprocal.TwoTo32wDividedByD

    ghost var pv := power2(32);
    lemma_2toX32();
    lemma_mul_basics_forall();

    lemma_power_positive(g.Bv,power2(d.ec-d.bp2));
//-    ghost var bp2 := d.bp2;
    var bp2' := d.bp2 - 1;

    var R2nc:array<int> := FleetNatMul(d.R, d.R); //- nc == "non-canonical"
    ghost var R2ncv := BEWordSeqToInt(R2nc[..]);

//-  var R2 := CanonicalizeArray(R2nc;  //- UNDONE length constraints
    var R2 := R2nc;
    ghost var R2v := BEWordSeqToInt(R2[..]);

//-    lemma_lengths_squared(pv, d.R[..], d.R[..], 25, R2[..]);
//-    assert R2.Length < power2(27);

    lemma_mul_nonnegative(g.Rv, g.Rv);
    var R2modN := FatNatModuloUsingReciprocal(R2, d.N, Nreciprocal);
    ghost var R2modNv := BEWordSeqToInt(R2modN[..]);
    lemma_BEDigitSeqToInt_bound(pv, R2modN[..]);

    var E2:array<int> := BitShiftLeft_Array(d.one, bp2');
    ghost var E2v := BEWordSeqToInt(E2[..]);
    calc {
        E2v;
        g.Onev*power2(bp2');
            { lemma_mul_basics_forall(); }
        power2(bp2');
    }

    var R':array<int>;
    ghost var Rv':int;
    var E_sub:array<int>;
    ghost var E_subv:int;
    var cmpE1E2 := FatNatCompare(d.E1, E2);
    var use_this_product:bool := (!cmpE1E2.CmpLt?);
    if (use_this_product)
    {
        E_sub,E_subv,R',Rv' := FatNatModExp_step_add(d, Nreciprocal, g, bp2', E2, E2v, R2, R2v, R2modN, R2modNv);
    }
    else
    {
        E_sub,E_subv,R',Rv' := FatNatModExp_step_noadd(d, g, bp2', E2, E2v, R2, R2v, R2modN, R2modNv);
    }

    
    
    
    
    R' := CanonicalizeArray(R');
    
    var E1' := E_sub;
    d' := FatNatModExp_data_c(bp2', d.B, d.E, d.N, R', d.ec, E1', d.one);
    g' := FatNatModExp_ghost_c(g.Bv, g.Ev, g.Nv, Rv', BEWordSeqToInt(E1'[..]), g.Onev);
    lemma_BEDigitSeqToInt_bound(pv, d'.R[..]);

//-    lemma_CanonicalLength_inherit(pv, R'[..], d.N[..], power2(25));
}

method FatNatModExp_conclusion(d:FatNatModExp_data, ghost g:FatNatModExp_ghost)
    requires FatNatModExp_invariant(d, g);
    requires d.bp2==0;  //- loop termination condition
    ensures 0<=BEWordSeqToInt(d.E[..]);   //- to meet precondition on next line
    ensures power(BEWordSeqToInt(d.B[..]),BEWordSeqToInt(d.E[..])) % BEWordSeqToInt(d.N[..])
        == BEWordSeqToInt(d.R[..]);
    ensures BEWordSeqToInt(d.R[..]) < BEWordSeqToInt(d.N[..]);
    ensures FatNatModExp_invariant(d, g);
{
    calc {
        power(g.Bv,g.Ev) % g.Nv;
            //- loop invariant
        mul(power(g.Bv,g.E1v), power(g.Rv,power2(d.bp2))) % g.Nv;
            { lemma_power2_0_is_1(); } //- loop termination
        mul(power(g.Bv,0), power(g.Rv,1)) % g.Nv;
            { lemma_power_0(g.Bv); lemma_power_1(g.Rv); }
        mul(1, g.Rv) % g.Nv;
            { lemma_mul_basics_forall(); }
        g.Rv % g.Nv;
            { lemma_small_mod(g.Rv, g.Nv); }
        g.Rv;
    }
}

method FatNatModExpUsingReciprocal(B:array<int>, E:array<int>, N:array<int>, Nreciprocal:FNDivReciprocal) returns (R:array<int>)
    requires B!=null && IsWordSeq(B[..]);
    requires E!=null && IsWordSeq(E[..]);
    requires N!=null && IsWordSeq(N[..]);
    requires BEWordSeqToInt(B[..])!=0;
    requires 1 < BEWordSeqToInt(N[..]);
//-    requires BEWordSeqToInt(E[..]) < power2(power2(31));
    requires FNDivReciprocalValid(Nreciprocal, N);
//-    requires B.Length < power2(25);
//-    requires N.Length < power2(25);
    ensures R!=null;
    ensures IsWordSeq(R[..]);
    ensures 0<=BEWordSeqToInt(E[..]);   //- to meet precondition on next line
    ensures power(BEWordSeqToInt(B[..]),BEWordSeqToInt(E[..])) % BEWordSeqToInt(N[..])
        == BEWordSeqToInt(R[..]);
    ensures BEWordSeqToInt(R[..]) < BEWordSeqToInt(N[..]);
{
    ProfileTally(Tally_FatNatModExp(), 1);

    var recip_ref := if Nreciprocal.FNDivKnownReciprocal? then Nreciprocal.TwoTo32wDividedByD else B; //- do something real to Nreciprocal.TwoTo32wDividedByD

    var d;
    ghost var g;
    d,g := FatNatModExp_init(B, E, N);
    var db_ref := d.B; //- do something real to d.B so dafnycc realizes it's allocated
    var de_ref := d.E; //- do something real to d.E so dafnycc realizes it's allocated
    var dn_ref := d.N; //- do something real to d.N so dafnycc realizes it's allocated
    var dr_ref := d.R; //- do something real to d.R so dafnycc realizes it's allocated
    var de1_ref := d.E1; //- do something real to d.E1 so dafnycc realizes it's allocated
    var done_ref := d.one; //- do something real to d.one so dafnycc realizes it's allocated
    while (d.bp2 != 0)
        decreases d.bp2;
        invariant d.B == B;
        invariant d.E == E;
        invariant d.N == N;
        invariant FatNatModExp_invariant(d, g);
        invariant IsWordSeq(d.R[..]);
    {
        d,g := FatNatModExp_step(d, Nreciprocal, g);
        db_ref := d.B; //- do something real to d.B so dafnycc realizes it's allocated
        de_ref := d.E; //- do something real to d.E so dafnycc realizes it's allocated
        dn_ref := d.N; //- do something real to d.N so dafnycc realizes it's allocated
        dr_ref := d.R; //- do something real to d.R so dafnycc realizes it's allocated
        de1_ref := d.E1; //- do something real to d.E1 so dafnycc realizes it's allocated
        done_ref := d.one; //- do something real to d.one so dafnycc realizes it's allocated
//-        print d.R.Length;
//-        print "\n";
    }
    FatNatModExp_conclusion(d, g);
    R := d.R;
}

method FatNatModExp(B:array<int>, E:array<int>, N:array<int>) returns (R:array<int>)
    requires B!=null && IsWordSeq(B[..]);
    requires E!=null && IsWordSeq(E[..]);
    requires N!=null && IsWordSeq(N[..]);
    requires BEWordSeqToInt(B[..])!=0;
    requires 1 < BEWordSeqToInt(N[..]);
//-    requires BEWordSeqToInt(E[..]) < power2(power2(31));
//-    requires B.Length < power2(25);
//-    requires N.Length < power2(25);
    ensures R!=null && IsWordSeq(R[..]);
    ensures 0<=BEWordSeqToInt(E[..]);   //- to meet precondition on next line
    ensures power(BEWordSeqToInt(B[..]),BEWordSeqToInt(E[..])) % BEWordSeqToInt(N[..])
        == BEWordSeqToInt(R[..]);
    ensures BEWordSeqToInt(R[..]) < BEWordSeqToInt(N[..]);
{
    R := FatNatModExpUsingReciprocal(B, E, N, FNDivUnknownReciprocal());
}
