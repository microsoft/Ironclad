include "Word32.i.dfy"
include "BigNatCore.i.dfy"
include "BigNatX86Shim.i.dfy"
include "BigNatCompare.i.dfy"

datatype Problem = Problem_ctor(
    A:BigNat, B:BigNat, c:nat);

static predicate WellformedCarry(carry:nat)
    { carry==0 || carry==1 }

static predicate WellformedProblem(p:Problem)
    { WellformedBigNat(p.A) && WellformedBigNat(p.B) && WellformedCarry(p.c) }

static predicate WorksheetProblemsWellformed(ps:seq<Problem>)
    { forall i :: 0 <= i < |ps| ==> WellformedProblem(ps[i]) }

static function method ZeroProblem(p:Problem) : bool
    requires WellformedProblem(p);
    { zero(p.A) && zero(p.B) && p.c==0 }

static predicate WorksheetProblemsConnected(p0:Problem, s0:nat, p1:Problem)
    requires WellformedProblem(p0);
    requires Word32(s0);
    requires WellformedProblem(p1);
{
    p1.A == hi(p0.A)
    && p1.B == hi(p0.B)
    && lo(p0.A) + lo(p0.B) + p0.c == s0 + p1.c *  Width()
    && !ZeroProblem(p0)
}

static predicate WellformedSolutions(ss:seq<int>)
{
    forall i :: 0 <= i < |ss| ==> ss[i]>=0 && Word32(ss[i])
}

static predicate WorksheetConsistent(ps:seq<Problem>, ss:seq<int>)
{
    WorksheetProblemsWellformed(ps)
    && |ps| == |ss|+1
    && WellformedSolutions(ss)
    && (forall i:nat :: i < |ps|-1 ==>
        WorksheetProblemsConnected(ps[i], ss[i], ps[i+1]))
}

static predicate WorksheetComplete(ps:seq<Problem>, ss:seq<int>)
{
    WorksheetConsistent(ps, ss)
    && ZeroProblem(ps[|ps|-1])
}

static predicate problem_smaller(p0:Problem, p1:Problem)
    requires WellformedProblem(p0);
    requires WellformedProblem(p1);
{
    I(p0.A) < I(p1.A)
    || (I(p0.A) == I(p1.A)
        && I(p0.B) < I(p1.B))
    || (I(p0.A) == I(p1.A)
        && I(p0.B) == I(p1.B)
        && p0.c < p1.c)
}

static method solve_one_(p:Problem) returns (s:nat, pnew:Problem)
    requires WellformedProblem(p);
    requires !ZeroProblem(p);
    ensures s>=0 && Word32(s);
    ensures WellformedProblem(pnew);
    ensures Word32(s);
    ensures WorksheetProblemsConnected(p,s,pnew);
    ensures problem_smaller(pnew, p);
    ensures ZeroProblem(pnew) ==> s != 0;
{
    var m:nat,c:nat := Add32_with_carry(lo(p.A), lo(p.B), p.c);
    s := m;
    pnew := Problem_ctor(hi(p.A), hi(p.B), c);

    if |p.A.words|==0 && |p.B.words|==0 {
    } else if |p.A.words|==0 {
    } else {
    }

    lemma_2to32();
    lemma_mul_is_mul_boogie_Width();
    reveal_I();
/* TODO: should dafnycc support ghost if statements in non-ghost methods?
    if (ZeroProblem(pnew))
    {
        if (s==0)
        {
            calc {
                0;
                s;
                lo(p.A) + lo(p.B) + p.c - c*Width();
                lo(p.A) + lo(p.B) + p.c - pnew.c*Width();
                    { lemma_mul_basics_forall(); }
                lo(p.A) + lo(p.B) + p.c;
            }
            assert !ZeroProblem(p);
            assert false;
        }
        assert s != 0;
    }

    if (I(p.A)!=0) {
        lemma_hi_decreases(p.A);
    } else if (I(p.B)!=0) {
        lemma_hi_decreases(p.A);
        lemma_hi_decreases(p.B);
    } else {
        lemma_hi_decreases(p.A);
        lemma_hi_decreases(p.B);
        assert p.c > 0;        //- !ZeroProblem(p)
        assert p.c == 1;    //- WellformedProblem(p)
        if (pnew.c > 0)
        {
            calc {
                s+pnew.c*Width();
                lo(p.A) + lo(p.B) + c;
                    { assert zero(p.A); }
                0 + lo(p.B) + c;
                    { assert zero(p.B); }
                0 + 0 + c;
                c;
                1;
            }
            assert pnew.c == 1;
            calc {
                1;
                <    { lemma_2to32(); }
                Width();
                    { lemma_mul_basics(Width()); }
                pnew.c*Width();
            }
            assert false;
        }
        assert pnew.c < p.c;
    }
*/
}

static method BigNatAdd_(A:BigNat, B:BigNat) returns (ss:seq<int>, ghost ps:seq<Problem>)
    requires WellformedBigNat(A);
    requires WellformedBigNat(B);
    ensures |ps|>0;
    ensures ps[0].A == A;
    ensures ps[0].B == B;
    ensures ps[0].c == 0;
    ensures WorksheetComplete(ps,ss);
    ensures |ss|>0 ==> ss[|ss|-1]>0;
{
    var p:Problem := Problem_ctor(A,B,0);
    ps := [ p ];
    ss := [];

    lemma_I_is_nonnegative_forall();

    while (!ZeroProblem(p))    
        decreases I(p.A),I(p.B),p.c;
        invariant 0 < |ps|;
        invariant ps[|ps|-1] == p;
        invariant WorksheetConsistent(ps, ss);
        invariant ps[0].A==A && ps[0].B==B && ps[0].c==0;
        invariant WellformedProblem(p);
        invariant forall i :: 0<=i<|ps|-1 ==> !ZeroProblem(ps[i]);
        invariant ZeroProblem(p) ==> (|ss|>0 ==> ss[|ss|-1]>0);
    {
        ghost var pold := p;
        var s:nat,pnew:Problem := solve_one_(p);
        ss := ss + [s];
        ps := ps + [pnew];

        assert WorksheetProblemsConnected(p,s,pnew);
        assert ps[|ps|-2] == p;
        assert ss[|ss|-1] == s;
        assert ps[|ps|-1] == pnew;
        assert WorksheetProblemsConnected(ps[|ps|-2], ss[|ss|-1], ps[|ps|-1]);



        assert forall i :: 0 <= i < |ps|-1 ==> WorksheetProblemsConnected(ps[i], ss[i], ps[i+1]);
        assert WorksheetConsistent(ps, ss);
        assert ZeroProblem(p) ==> ss[|ss|-1]>0;
/* TODO: should dafnycc support forall statement in non-ghost methods?
        forall (i:nat | i < |ps|-1)
            ensures WorksheetProblemsConnected(ps[i], ss[i], ps[i+1]);
        {
            if (i < |ps|-2)
            {
                //- induction hypothesis WorksheetConsistent(ps,ss);
                assert WorksheetProblemsConnected(ps[i], ss[i], ps[i+1]);
            }
            else
            {
                //- solve_one ensures
                assert WorksheetProblemsConnected(p, s, pnew);
                assert WorksheetProblemsConnected(ps[i], ss[i], ps[i+1]);
            }
        }
        assert WorksheetConsistent(ps, ss);

        if (ZeroProblem(p))
        {
            assert ss[|ss|-1]>0;
        }
*/

        assert problem_smaller(pnew,p);
        p := pnew;

        lemma_I_is_nonnegative_forall();
        assert 0<=I(p.A);
        assert 0<=I(p.B);
    }
}

static function ProblemValue(p:Problem) : int
    requires WellformedProblem(p);
{
    I(p.A) + I(p.B) + p.c
}

static predicate WellformedBigNatSeq(R:seq<BigNat>)
{
    forall i :: 0 <= i < |R| ==> WellformedBigNat(R[i])
}

static predicate WellformedWordSeq(s:seq<int>)
{
    forall i :: 0 <= i < |s| ==> s[i]>=0 && Word32(s[i])
}

//-////////////////////////////////////////////////////////////////////////////
//- These functions define the relationship between a sequence of words
//- and a sequence of BigNats formed from subsequences of the word seq.
//- That's so that we can show that the high-place-value partial sums
//- (one word at a time) can be viewed as correct BigNat solutions to the
//- truncated problems. Then we inductively include low-order words one
//- at a time until we've reconstructed the original problem.

static predicate BigNatsForSumWords_Base(ss:seq<int>, R:seq<BigNat>)
    requires WellformedBigNatSeq(R);
{
    |R| == |ss|+1
    && R[|R|-1] == BigNat_ctor([])
    && R[0] == BigNat_ctor(ss)
}

static predicate BigNatsForSumWords_Nonzero(ss:seq<int>, R:seq<BigNat>)
    requires WellformedBigNatSeq(R);
    requires BigNatsForSumWords_Base(ss, R);
    { forall i :: 0 <= i < |ss| ==> nonzero(R[i]) }

static predicate BigNatsForSumWords_Assembly(ss:seq<int>, R:seq<BigNat>)
    requires WellformedBigNatSeq(R);
    requires BigNatsForSumWords_Base(ss, R);
    { forall i :: 0 <= i <=|ss| ==> R[i] == BigNat_ctor(ss[i..]) }

static predicate ShiftRelation(M:seq<BigNat>, i:nat)
    requires WellformedBigNatSeq(M);
    requires i < |M|-1;
{ I(M[i]) == I(M[i+1]) *  Width() + lo(M[i]) }

static predicate ShiftRelationSeq(ss:seq<int>, R:seq<BigNat>)
    requires WellformedBigNatSeq(R);
    requires |R| == |ss|+1;
{    forall i :: 0 <= i < |ss| ==> ShiftRelation(R, i) }

static lemma ShiftRelationLemma(M:seq<BigNat>, i:nat)
    requires WellformedBigNatSeq(M);
    requires i < |M|-1;
    requires ShiftRelation(M,i);
    ensures I(M[i]) == I(M[i+1]) *  Width() + lo(M[i]);
{
    reveal_I();
}

static predicate BigNatsForSumWords(ss:seq<int>, R:seq<BigNat>)
    requires WellformedBigNatSeq(R);
{
    BigNatsForSumWords_Base(ss,R)
    && BigNatsForSumWords_Nonzero(ss, R)
    && BigNatsForSumWords_Assembly(ss, R)
    && ShiftRelationSeq(ss,R)
}

static lemma ConstructBigNatsFromSumWords_lemma(ss:seq<int>, R:seq<BigNat>)
    requires WellformedBigNatSeq(R);
    requires WellformedWordSeq(ss);
    requires |ss|>0;
    requires ss[|ss|-1] > 0;
    requires |R| == |ss|+1;
    requires BigNatsForSumWords(ss[1..],R[1..]);
    requires nonzero(R[0]);
    requires R[0] == BigNat_ctor(ss);
    ensures BigNatsForSumWords_Base(ss,R);
    ensures BigNatsForSumWords(ss,R);
{
    forall (i:nat | i < |ss|)
        ensures nonzero(R[i]);
    {
        if (i>0)
        {
            assert nonzero(R[1..][i-1]);
            assert nonzero(R[i]);
        }
    }
    assert BigNatsForSumWords_Nonzero(ss,R);

    forall (i:nat | i <=|ss|)
        ensures R[i] == BigNat_ctor(ss[i..]);
    {
        if (i==0)
        {
            assert ss == ss[0..];
        }
        else
        {
            assert R[1..][i-1] == R[i];
            assert ss[1..][i-1..] == ss[i..];
        }
    }
    assert BigNatsForSumWords_Assembly(ss,R);

    forall (i:nat | i < |ss|)
        ensures ShiftRelation(R, i);
    {
        if (i==0)
        {
            reveal_I();
            assert ShiftRelation(R, 0);
        }
        else
        {
            assert R[1..][i-1] == R[i];
            calc ==>
            {
                ShiftRelationSeq(ss[1..],R[1..]);
                ShiftRelation(R[1..], i-1);
                ShiftRelation(R, i);
            }
        }
    }
    assert ShiftRelationSeq(ss,R);
}

static lemma ConstructBigNatsFromSumWords_(ss:seq<int>) returns (R:seq<BigNat>)
    requires WellformedWordSeq(ss);
    requires |ss|>0 ==> ss[|ss|-1] > 0;
    ensures WellformedBigNatSeq(R);
    ensures BigNatsForSumWords(ss,R);
{
    var r:BigNat := BigNat_ctor(ss);
    var tail:seq<BigNat>;

    if |ss|==0
    {
        tail := [];
        R := [r] + tail;
    } else {
        tail := ConstructBigNatsFromSumWords_(ss[1..]);
        R := [r] + tail;
        var next:BigNat:= tail[0];
        ConstructBigNatsFromSumWords_lemma(ss, R);
    }
}

static lemma lemma_accumulate(s:int, ss:seq<int>, ps:seq<Problem>, Ms:seq<BigNat>)
    decreases |ss|-s;
    requires 0<=s<=|ss|;
    requires WorksheetComplete(ps,ss);
    requires WellformedBigNatSeq(Ms);
    requires BigNatsForSumWords(ss,Ms);
    ensures I(Ms[s]) == ProblemValue(ps[s]);
{
    if (s==|ss|)
    {
        calc
        {
            ProblemValue(ps[s]);
            I(ps[s].A) + I(ps[s].B) + ps[s].c;
                { reveal_I(); }
            0;
                { reveal_I(); }
            I(Ms[s]);
        }
    }
    else
    {
        calc {
            I(Ms[s]);
                { ShiftRelationLemma(Ms, s); }
            I(Ms[s+1]) *  Width() + lo(Ms[s]);
            I(Ms[s+1]) *  Width() + ss[s];
            I(Ms[s+1]) * Width() + lo(ps[s].A)+lo(ps[s].B)+ps[s].c - ps[s+1].c * Width();
                { lemma_accumulate(s+1, ss, ps, Ms); }
            I(Ms[s+1]) * Width() + lo(ps[s].A)+lo(ps[s].B)+ps[s].c - ((I(Ms[s+1]) - I(ps[s+1].A)) - I(ps[s+1].B)) * Width();
                //-{    lemma_mul_properties(); }
                { lemma_mul_is_commutative(Width(), (I(Ms[s+1]) - I(ps[s+1].A)) - I(ps[s+1].B)); }
            I(Ms[s+1]) * Width() + lo(ps[s].A)+lo(ps[s].B)+ps[s].c - Width() * ((I(Ms[s+1]) - I(ps[s+1].A)) - I(ps[s+1].B));
                //-{    lemma_mul_properties(); }
                { lemma_mul_is_distributive_sub(Width(), I(Ms[s+1]) - I(ps[s+1].A), I(ps[s+1].B)); }
            I(Ms[s+1]) * Width() + lo(ps[s].A)+lo(ps[s].B)+ps[s].c - (Width() * (I(Ms[s+1]) - I(ps[s+1].A)) - Width() *  I(ps[s+1].B));
                //-{    lemma_mul_properties(); }
                { lemma_mul_is_distributive_sub(Width(), I(Ms[s+1]), I(ps[s+1].A)); }
            I(Ms[s+1]) * Width() + lo(ps[s].A)+lo(ps[s].B)+ps[s].c - (Width() * I(Ms[s+1]) - Width() * I(ps[s+1].A) - Width() * I(ps[s+1].B));
                //-{    lemma_mul_properties(); }
                { lemma_mul_is_commutative(Width(),I(Ms[s+1])); }
            Width() * I(Ms[s+1]) + lo(ps[s].A)+lo(ps[s].B)+ps[s].c - (Width() * I(Ms[s+1]) - Width() * I(ps[s+1].A) - Width() * I(ps[s+1].B));
            Width() * I(Ms[s+1]) + lo(ps[s].A)+lo(ps[s].B)+ps[s].c - Width() * I(Ms[s+1]) + Width() * I(ps[s+1].A) + Width() * I(ps[s+1].B);
                    //- Collapse the canceling terms
            lo(ps[s].A)+Width() * I( ps[s+1].A ) +lo(ps[s].B)+ps[s].c+Width() * I(ps[s+1].B);
                {
                    lemma_mul_is_commutative(Width(),I( ps[s+1].A ));
                    lemma_mul_is_commutative(Width(),I( ps[s+1].B ));
                }
            lo(ps[s].A)+I( ps[s+1].A ) * Width() +lo(ps[s].B)+ps[s].c+I(ps[s+1].B) * Width();
            lo(ps[s].A)+I(hi(ps[s].A)) * Width() +lo(ps[s].B)+I(hi(ps[s].B)) * Width() +ps[s].c;
                { lemma_hilo(ps[s].A); lemma_hilo(ps[s].B); }
            I(ps[s].A) + I(ps[s].B)+ps[s].c;
            ProblemValue(ps[s]);
        }
    }
}

static method BigNatAdd(A:BigNat, B:BigNat) returns (R:BigNat)
    requires WellformedBigNat(A);
    requires WellformedBigNat(B);
    ensures WellformedBigNat(R);
    ensures I(A)+I(B) == I(R);
{
    var ss:seq<int>;
    ghost var ps:seq<Problem>;
    ss,ps := BigNatAdd_(A,B);
    ghost var Ms:seq<BigNat> := ConstructBigNatsFromSumWords_(ss);
        //- Ms[i] is the BigNat formed by ss[i..]. It includes Ms[|ss|], which is always BigNat_ctor([]) (0)

    R := BigNat_ctor(ss);
    calc {
        I(R);
        I(Ms[0]);
            { lemma_accumulate(0,ss,ps,Ms); }
        ProblemValue(ps[0]);
        I(ps[0].A) + I(ps[0].B) + ps[0].c;
        I(ps[0].A) + I(ps[0].B);
        I(A) + I(B);
        }
}
