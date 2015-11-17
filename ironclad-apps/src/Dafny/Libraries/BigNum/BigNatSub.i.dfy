include "Word32.i.dfy"
include "BigNatCore.i.dfy"
include "BigNatPartial.i.dfy"
include "BigNatX86Shim.i.dfy"

include "../Util/ProfileIfc.i.dfy"

datatype sub_Problem = sub_Problem_ctor(
    A:BigNat, B:BigNat, c:nat);

static predicate WellformedBorrow(borrow:nat)
    { borrow==0 || borrow==1 }

static predicate sub_WellformedProblem(p:sub_Problem)
{
    WellformedBigNat(p.A)
    && WellformedBigNat(p.B)
    && I(p.A) >= (I(p.B) + p.c)
    && WellformedBorrow(p.c)
}

static predicate sub_WorksheetProblemsWellformed(ps:seq<sub_Problem>)
    { forall i :: 0 <= i < |ps| ==> sub_WellformedProblem(ps[i]) }

static predicate method sub_ZeroProblem(p:sub_Problem)
    requires sub_WellformedProblem(p);
    { zero(p.A) && zero(p.B) && p.c==0 }

static predicate sub_WorksheetProblemsConnected(p0:sub_Problem, s0:nat, p1:sub_Problem)
    requires sub_WellformedProblem(p0);
    requires Word32(s0);
    requires sub_WellformedProblem(p1);
{
    p1.A == hi(p0.A)
    && p1.B == hi(p0.B)
    && lo(p0.A) - lo(p0.B) - p0.c == s0 - p1.c *  Width()
    && !sub_ZeroProblem(p0)
}

static predicate sub_WellformedSolutions(ss:seq<int>)
{
    forall i :: 0 <= i < |ss| ==> ss[i]>=0 && Word32(ss[i])
}

static predicate sub_IncompleteWorksheetConsistent(ps:seq<sub_Problem>, ss:seq<int>)
{
    sub_WorksheetProblemsWellformed(ps)
    && |ps| == |ss|+1
    && sub_WellformedSolutions(ss)
    && (forall i:nat :: i < |ps|-1 ==>
        sub_WorksheetProblemsConnected(ps[i], ss[i], ps[i+1]))
}

static predicate sub_WorksheetConsistent(ps:seq<sub_Problem>, ss:seq<int>)
{
    sub_IncompleteWorksheetConsistent(ps, ss)
    && sub_ZeroProblem(ps[|ps|-1])
}

static lemma lemma_sub_solve_one(p:sub_Problem, m:nat, c:nat, pnew:sub_Problem)
    requires sub_WellformedProblem(p);
    requires !zero(p.A);
    requires Word32(m);
    requires c==0 || c==1;
    requires lo(p.A)-lo(p.B)-p.c == m - c*Width();
    requires pnew == sub_Problem_ctor(hi(p.A), hi(p.B), c);
    ensures sub_WellformedProblem(pnew);
    ensures Word32(m);
    ensures sub_WorksheetProblemsConnected(p, m, pnew);
    ensures I(pnew.A) < I(p.A);
{
    lemma_2to32();
    lemma_mul_is_mul_boogie_Width();
    reveal_I();

    if (I(pnew.A) < I(pnew.B) + pnew.c)    //- proof by contradiction
    {
        calc {
            I(p.A);
                { lemma_hilo(p.A); }
            I(hi(p.A))*Width() + lo(p.A);
            I(pnew.A)*Width() + lo(p.A);
            <=    { lemma_mul_inequality(I(pnew.A), (I(pnew.B) + pnew.c - 1), Width()); }
            (I(pnew.B) + pnew.c - 1) * Width() + lo(p.A);
                { lemma_mul_is_distributive_add_other_way(Width(), I(pnew.B) + pnew.c, -1); }
            I(pnew.B)*Width() + pnew.c*Width() + (-1) * Width() + lo(p.A);
                { lemma_mul_unary_negation(-1,Width()); }
            I(pnew.B)*Width() + pnew.c*Width() - 1 * Width() + lo(p.A);
                { lemma_mul_basics(Width()); }
            I(pnew.B)*Width() + pnew.c*Width() - Width() + lo(p.A);
            I(pnew.B)*Width() - Width() + m + lo(p.B) + p.c;
            <    { assert m < Width(); }
            I(pnew.B)*Width() + lo(p.B) + p.c;
            I(hi(p.B))*Width() + lo(p.B) + p.c;
                { lemma_hilo(p.B); }
            I(p.B) + p.c;
        }
        assert false;
    }
    assert I(pnew.A) >= I(pnew.B) + pnew.c;
    assert sub_WellformedProblem(pnew);

    if (|p.A.words| == 1)
    {
        calc {
            I(pnew.A);
            I(hi(p.A));
                { reveal_I(); }
            0;
            <
                //- WellformedBigNat(p.A) && |p.A.words|==1
            p.A.words[0];
                { lemma_mul_basics_forall(); }
            0 * Width()+p.A.words[0];
                { reveal_I(); }
            I(BigNat_ctor(p.A.words[1..])) * Width()+p.A.words[0];
                { reveal_I(); }
            I(p.A);
        }
    }
    else
    {
        assert |hi(p.A).words|>0;
        assert !zero(hi(p.A));
        calc {
            I(pnew.A);
            I(hi(p.A));
            <    {
                assert 1<Width();
                assert 0<I(hi(p.A));
                lemma_mul_strictly_increases(Width(), I(hi(p.A)));
                }
            Width() * I(hi(p.A));
                { lemma_mul_is_commutative_forall(); }
            I(hi(p.A)) * Width();
            <=
            I(hi(p.A)) * Width()+p.A.words[0];
            I(BigNat_ctor(p.A.words[1..])) * Width()+p.A.words[0];
                { reveal_I(); }
            I(p.A);
        }
    }
}

static method sub_solve_one_(p:sub_Problem) returns (s:nat, pnew:sub_Problem)
    requires sub_WellformedProblem(p);
    requires !zero(p.A);
    ensures sub_WellformedProblem(pnew);
    ensures Word32(s);
    ensures sub_WorksheetProblemsConnected(p, s, pnew);
    ensures I(pnew.A) < I(p.A);
{
    var m:nat,c:nat := Sub32_with_borrow(lo(p.A), lo(p.B), p.c);
    s := m;
    pnew := sub_Problem_ctor(hi(p.A), hi(p.B), c);

    lemma_sub_solve_one(p, m, c, pnew);
}

static method BigNatSub_(A:BigNat, B:BigNat) returns (ss:seq<int>, ghost ps:seq<sub_Problem>)
    requires WellformedBigNat(A);
    requires WellformedBigNat(B);
    requires I(A) >= I(B);
    ensures |ps|>0;
    ensures ps[0].A == A;
    ensures ps[0].B == B;
    ensures ps[0].c == 0;
    ensures sub_WorksheetConsistent(ps,ss);
{
    var start_problem:sub_Problem := sub_Problem_ctor(A,B,0);
    var p:sub_Problem := start_problem;
    ps := [ p ];
    ss := [];

    while (!sub_ZeroProblem(p))
        decreases I(p.A);
        invariant sub_IncompleteWorksheetConsistent(ps, ss);
        invariant sub_WellformedProblem(p);
        invariant ps[0] == start_problem;
        invariant ps[|ps|-1] == p;
    {
        var s:nat,pnew:sub_Problem := sub_solve_one_(p);
        assert(I(pnew.A) < I(p.A));
        ss := ss + [s];
        ps := ps + [pnew];

//-        assert sub_WorksheetProblemsConnected(p, s, pnew);    // TODO delete
            //- should fall straight out of sub_solve_one_!
//-        assert sub_WellformedSolutions(ss);

        
        
        

        p := pnew;
    }

    assert sub_ZeroProblem(ps[|ps|-1]);
    assert sub_WorksheetConsistent(ps, ss);
}

static function sub_ProblemValue(p:sub_Problem) : int
    requires sub_WellformedProblem(p);
{
    I(p.A) - I(p.B) - p.c
}

static predicate sub_WellformedBigNatSeq(R:seq<BigNat>)
{
    forall i :: 0 <= i < |R| ==> WellformedBigNat(R[i])
}

//-////////////////////////////////////////////////////////////////////////////
//- These functions define the relationship between a sequence of words
//- and a sequence of BigNats formed from subsequences of the word seq.
//- That's so that we can show that the high-place-value partial sums
//- (one word at a time) can be viewed as correct BigNat solutions to the
//- truncated problems. Then we inductively include low-order words one
//- at a time until we've reconstructed the original problem.

static predicate sub_BigNatsForSumWords_Base(ss:seq<int>, R:seq<BigNat>)
    requires IsWordSeq(ss);
    requires sub_WellformedBigNatSeq(R);
{
    |R| == |ss|+1
    && R[|R|-1] == TruncatingBigNatCtor([])
    && R[0] == TruncatingBigNatCtor(ss)
}

static predicate sub_BigNatsForSumWords_Assembly(ss:seq<int>, R:seq<BigNat>)
    requires sub_WellformedBigNatSeq(R);
    requires IsWordSeq(ss);
    requires sub_BigNatsForSumWords_Base(ss, R);
    { forall i :: 0 <= i <=|ss| ==> R[i] == TruncatingBigNatCtor(ss[i..]) }

static predicate sub_ShiftRelation(M:seq<BigNat>, i:nat)
    requires sub_WellformedBigNatSeq(M);
    requires i < |M|-1;
{ I(M[i]) == I(M[i+1]) *  Width() + lo(M[i]) }

static predicate sub_ShiftRelationSeq(ss:seq<int>, R:seq<BigNat>)
    requires sub_WellformedBigNatSeq(R);
    requires |R| == |ss|+1;
{    forall i :: 0 <= i < |ss| ==> sub_ShiftRelation(R, i) }

static lemma sub_ShiftRelationLemma(M:seq<BigNat>, i:nat)
    requires sub_WellformedBigNatSeq(M);
    requires i < |M|-1;
    requires sub_ShiftRelation(M,i);
    ensures I(M[i]) == I(M[i+1]) *  Width() + lo(M[i]);
{
    reveal_I();
}

static predicate sub_BigNatsForSumWords(ss:seq<int>, R:seq<BigNat>)
    requires IsWordSeq(ss);
    requires sub_WellformedBigNatSeq(R);
{
    sub_BigNatsForSumWords_Base(ss,R)
    && sub_BigNatsForSumWords_Assembly(ss, R)
    && sub_ShiftRelationSeq(ss,R)
}

static lemma sub_ConstructBigNatsFromSumWords_lemma(ss:seq<int>, R:seq<BigNat>)
    requires sub_WellformedBigNatSeq(R);
    requires IsWordSeq(ss);
    requires |ss|>0;
    requires |R| == |ss|+1;
    requires sub_BigNatsForSumWords(ss[1..],R[1..]);
    requires R[0] == TruncatingBigNatCtor(ss);
    ensures sub_BigNatsForSumWords_Base(ss,R);
    ensures sub_BigNatsForSumWords(ss,R);
{

    forall (i:nat | i <=|ss|)
        ensures R[i] == TruncatingBigNatCtor(ss[i..]);
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
    assert sub_BigNatsForSumWords_Assembly(ss,R);

    forall (i:nat | i < |ss|)
        ensures sub_ShiftRelation(R, i);
    {
        if (i==0)
        {
            if (zero(R[0]))
            {
                calc {
                    ss[0];
                        { lemma_TruncatingBigNat_alignment(ss, R[0]); }
                    0;
                    lo(R[0]);
                }
            }
            else
            {
                calc {
                    ss[0];
                        { lemma_TruncatingBigNat_alignment(ss, R[0]); }
                    lo(R[0]);
                }
            }
            calc {
                I(R[0]);
                I(TruncatingBigNatCtor(ss));
                    { lemma_TruncatingBigNat_hilo(ss); }
                I(TruncatingBigNatCtor(ss[1..]))*Width() + ss[0];
                    //- inductive application of sub_BigNatsForSumWords_Assembly
                I(R[1])*Width() + ss[0];
                    //- proven above this calc
                I(R[1])*Width() + lo(R[0]);
            }
            assert sub_ShiftRelation(R, 0);
        }
        else
        {
            assert R[1..][i-1] == R[i];
            calc ==> {
                sub_ShiftRelationSeq(ss[1..],R[1..]);
                sub_ShiftRelation(R[1..], i-1);
                sub_ShiftRelation(R, i);
            }
        }
    }
    assert sub_ShiftRelationSeq(ss,R);
}

static ghost method sub_ConstructBigNatsFromSumWords_(ss:seq<int>) returns (R:seq<BigNat>)
    requires IsWordSeq(ss);
    ensures sub_WellformedBigNatSeq(R);
    ensures sub_BigNatsForSumWords(ss,R);
{
    var r:BigNat := TruncatingBigNatCtor(ss);
    var tail:seq<BigNat>;

    if |ss|==0
    {
        tail := [];
        R := [r] + tail;
    } else {
        tail := sub_ConstructBigNatsFromSumWords_(ss[1..]);
        R := [r] + tail;
        sub_ConstructBigNatsFromSumWords_lemma(ss, R);
    }
}

static lemma sub_lemma_accumulate(s:int, ss:seq<int>, ps:seq<sub_Problem>, Ms:seq<BigNat>)
    decreases |ss|-s;
    requires 0<=s<=|ss|;
    requires sub_WorksheetConsistent(ps,ss);
    requires sub_WellformedBigNatSeq(Ms);
    requires sub_BigNatsForSumWords(ss,Ms);
    ensures I(Ms[s]) == sub_ProblemValue(ps[s]);
{
    if (s==|ss|)
    {
        calc
        {
            sub_ProblemValue(ps[s]);
            I(ps[s].A) - I(ps[s].B) - ps[s].c;
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
                { sub_ShiftRelationLemma(Ms, s); }
            I(Ms[s+1]) *  Width() + lo(Ms[s]);
                {
                    lemma_TruncatingBigNat_alignment(ss[s..], Ms[s]);
                    if (0 == |Ms[s].words|)
                    {
                        assert zero(Ms[s]);
                        calc {
                            lo(Ms[s]);
                            0;
                            ss[s..][0];
                            ss[s];
                        }
                    } else {
                        calc {
                            lo(Ms[s]);
                            Ms[s].words[0];
                            ss[s..][0];
                            ss[s];
                        }
                    }
                }
            I(Ms[s+1]) *  Width() + ss[s];
                //- sub_WorksheetProblemsConnected(ps[s],ss[s],ps[s+1]);
            I(Ms[s+1]) * Width() + lo(ps[s].A)-lo(ps[s].B)-ps[s].c + ps[s+1].c * Width();
                {
                    sub_lemma_accumulate(s+1, ss, ps, Ms);
                    assert ps[s+1].c == -I(Ms[s+1]) + I(ps[s+1].A) - I(ps[s+1].B);
                }
            I(Ms[s+1]) * Width() + lo(ps[s].A)-lo(ps[s].B)-ps[s].c + (-I(Ms[s+1]) + I(ps[s+1].A) - I(ps[s+1].B)) * Width();
                { lemma_mul_is_commutative(Width(), -I(Ms[s+1]) + I(ps[s+1].A) - I(ps[s+1].B)); }
            I(Ms[s+1]) * Width() + lo(ps[s].A)-lo(ps[s].B)-ps[s].c + Width() * (I(ps[s+1].A) - I(Ms[s+1]) - I(ps[s+1].B));
                { lemma_mul_is_distributive_sub(Width(), I(ps[s+1].A) - I(Ms[s+1]), I(ps[s+1].B)); }
            I(Ms[s+1]) * Width() + lo(ps[s].A)-lo(ps[s].B)-ps[s].c + Width() * (I(ps[s+1].A) - I(Ms[s+1])) - Width() * I(ps[s+1].B);
                { lemma_mul_is_distributive_sub(Width(), I(ps[s+1].A), I(Ms[s+1])); }
            I(Ms[s+1]) * Width() + lo(ps[s].A)-lo(ps[s].B)-ps[s].c + (Width() * I(ps[s+1].A) - Width() * I(Ms[s+1]) - Width() * I(ps[s+1].B));
            I(Ms[s+1]) * Width() + lo(ps[s].A)-lo(ps[s].B)-ps[s].c + Width() * I(ps[s+1].A) - Width() * I(Ms[s+1]) - Width() * I(ps[s+1].B);
                { lemma_mul_is_commutative(Width(),I(Ms[s+1])); }
            Width() * I(Ms[s+1]) + lo(ps[s].A)-lo(ps[s].B)-ps[s].c + Width() * I(ps[s+1].A) - Width() * I(Ms[s+1]) - Width() * I(ps[s+1].B);
                //- cancel terms
            lo(ps[s].A)-lo(ps[s].B)-ps[s].c + Width() * I(ps[s+1].A) - Width() * I(ps[s+1].B);
                //- rearrange terms
            Width() * I(ps[s+1].A) + lo(ps[s].A) - (Width() * I(ps[s+1].B) + lo(ps[s].B)) - ps[s].c;
                //- sub_WorksheetProblemsConnected(ps[s],...,ps[s+1]);
            Width() * I(hi(ps[s].A)) + lo(ps[s].A) - (Width() * I(hi(ps[s].B)) + lo(ps[s].B)) - ps[s].c;
                {
                    lemma_mul_is_commutative(Width(), I(hi(ps[s].A)));
                    lemma_mul_is_commutative(Width(), I(hi(ps[s].B)));
                    lemma_hilo(ps[s].A);
                    lemma_hilo(ps[s].B);
                }
            I(ps[s].A) - I(ps[s].B) - ps[s].c;
            sub_ProblemValue(ps[s]);
        }
    }
}

static method BigNatSub(A:BigNat, B:BigNat) returns (R:BigNat)
    requires WellformedBigNat(A);
    requires WellformedBigNat(B);
    requires I(A) >= I(B);
    ensures WellformedBigNat(R);
    ensures I(A)-I(B) == I(R);
{
    //-ProfileTally(Tally_BigNatSub(), 1);

    var ss:seq<int>;
    ghost var ps:seq<sub_Problem>;
    ss,ps := BigNatSub_(A,B);
    ghost var Ms:seq<BigNat> := sub_ConstructBigNatsFromSumWords_(ss);
        //- Ms[i] is the BigNat formed by ss[i..]. It includes Ms[|ss|], which is always TruncatingBigNatCtor([]) (0)

    R := TruncatingBigNatCtor_impl(ss);
    calc {
        I(R);
        I(Ms[0]);
            { sub_lemma_accumulate(0,ss,ps,Ms); }
        sub_ProblemValue(ps[0]);
        I(ps[0].A) - I(ps[0].B) - ps[0].c;
        I(ps[0].A) - I(ps[0].B);
        I(A) - I(B);
        }
}

