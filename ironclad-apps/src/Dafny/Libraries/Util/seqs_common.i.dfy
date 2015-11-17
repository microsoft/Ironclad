include "../Math/power.i.dfy"
include "../Math/div.i.dfy"
include "be_sequences.s.dfy"




lemma lemma_BEInterpretation(pv:int, A:seq<int>, i:int)
    
    requires 1<pv;
    requires IsDigitSeq(pv, A);
    requires 0<=i<=|A|;
    ensures BEDigitSeqToInt(pv, A) ==
        BEDigitSeqToInt(pv, A[..|A|-i]) * power(pv,i) + BEDigitSeqToInt(pv, A[|A|-i..]);
    decreases |A|;
{
    reveal_BEDigitSeqToInt_private();
    lemma_mul_basics_forall();
    if (|A|==0)
    {
    }
//-    else if (i==|A|)
//-    {
//-        assert A[|A|-i..] == A; //- OBSERVE
//-    }
    else if (i==0)
    {
        lemma_power_0(pv);
        calc {
            BEDigitSeqToInt(pv, A);
            mul(BEDigitSeqToInt(pv, A), 1); //- OBSERVE
            BEDigitSeqToInt(pv, A) * power(pv,i);
            BEDigitSeqToInt(pv, A) * power(pv,i) + BEDigitSeqToInt(pv, []);
                { assert A[..|A|] == A; //- OBSERVE
                }
            BEDigitSeqToInt(pv, A[..|A|]) * power(pv,i) + BEDigitSeqToInt(pv, A[|A|..]);
            BEDigitSeqToInt(pv, A[..|A|-i]) * power(pv,i) + BEDigitSeqToInt(pv, A[|A|-i..]);
        }
    }
    else
    {
        var Al := A[..|A|-i];
        var Ar := A[|A|-i..];
        assert A==Al+Ar;

        var As := A[..|A|-1];
        var Atail := A[|A|-1];
        assert A == As + [Atail];
        assert IsDigitSeq(pv, As);

        var Asl := As[..|As|-(i-1)];
        var Asr := As[|As|-(i-1)..];
        assert As == Asl+Asr;

        assert |Asl| == |Al|;
        assert Asl == Al;

        calc {
            BEDigitSeqToInt(pv, A);
                { assert A[0..|A|-1]==As; 
                }
            BEDigitSeqToInt(pv, As) * pv + Atail;
                { lemma_BEInterpretation(pv, As, i-1); }
            (BEDigitSeqToInt(pv, As[..|As|-(i-1)]) * power(pv,i-1) + BEDigitSeqToInt(pv, As[|As|-(i-1)..])) * pv + Atail;
            (BEDigitSeqToInt(pv, Asl) * power(pv,i-1) + BEDigitSeqToInt(pv, Asr)) * pv + Atail;
                { lemma_mul_is_distributive_forall(); }
            BEDigitSeqToInt(pv, Asl)*power(pv,i-1)*pv + BEDigitSeqToInt(pv, Asr)*pv + Atail;
                { lemma_mul_is_associative_forall(); }
            BEDigitSeqToInt(pv, Asl)*(power(pv,i-1)*pv) + BEDigitSeqToInt(pv, Asr)*pv + Atail;
                { lemma_power_1(pv); }
            BEDigitSeqToInt(pv, Asl)*(power(pv,i-1)*power(pv,1)) + BEDigitSeqToInt(pv, Asr)*pv + Atail;
                { lemma_power_adds(pv,i-1,1); }
            BEDigitSeqToInt(pv, Asl) * power(pv,i)
                + BEDigitSeqToInt(pv, Asr)*pv + Atail;
                { assert Ar[0..|Ar|-1] == Asr; }
            BEDigitSeqToInt(pv, Asl) * power(pv,i) + BEDigitSeqToInt(pv, Ar);
            BEDigitSeqToInt(pv, Al) * power(pv,i) + BEDigitSeqToInt(pv, Ar);
            BEDigitSeqToInt(pv, A[..|A|-i]) * power(pv,i) + BEDigitSeqToInt(pv, A[|A|-i..]);
        }
    }
}


lemma lemma_BEDigitSeqToInt_singleton(pv:int, v:int)
    requires 1<pv;
    requires IsDigitSeq(pv, [v]);
    ensures BEDigitSeqToInt(pv, [v]) == v;
{
    reveal_BEDigitSeqToInt_private();
    lemma_mul_basics_forall();
    assert [v][0..|[v]|-1] == [];   //- OBSERVE
    calc {
        BEDigitSeqToInt(pv, [v]);
        BEDigitSeqToInt(pv, [])*pv+v;
        v;
    }
}









//    




//    
//    










//














//


//




//



//













//

//    







//
////
//
//
//
////
//
////
//
//
////
////    
////    
//
//
//
////
//
//
//
////
////


//
//








