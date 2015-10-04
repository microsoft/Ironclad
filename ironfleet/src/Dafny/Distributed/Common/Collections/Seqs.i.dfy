include "Seqs.s.dfy"

module Collections__Seqs_i {
import opened Collections__Seqs_s 

lemma SeqAdditionIsAssociative<T>(a:seq<T>, b:seq<T>, c:seq<T>)
    ensures a+(b+c) == (a+b)+c;
{
}

predicate ItemAtPositionInSeq<T>(s:seq<T>, v:T, idx:int)
{
    0 <= idx < |s| && s[idx] == v
}

lemma Lemma_ItemInSeqAtASomePosition<T>(s:seq<T>, v:T)
    requires v in s;
    ensures  exists idx :: ItemAtPositionInSeq(s, v, idx);
{
    var idx :| 0 <= idx < |s| && s[idx] == v;
    assert ItemAtPositionInSeq(s, v, idx);
}

function FindIndexInSeq<T>(s:seq<T>, v:T):int
    ensures var idx := FindIndexInSeq(s, v);
            if idx >= 0 then
                idx < |s| && s[idx] == v
            else
                v !in s;
{
    if v in s then
        Lemma_ItemInSeqAtASomePosition(s, v);
        var idx :| ItemAtPositionInSeq(s, v, idx);
        idx
    else
        -1
}

lemma Lemma_IdenticalSingletonSequencesHaveIdenticalElement<T>(x:T, y:T)
    requires [x] == [y];
    ensures  x == y;
{
    calc {
        x;
        [x][0];
        [y][0];
        y;
    }
}

//////////////////////////////////////////////////////////
//  Combining sequences of sequences
//////////////////////////////////////////////////////////
function SeqCat<T>(seqs:seq<seq<T>>) : seq<T>
{
    if |seqs| == 0 then []
    else seqs[0] + SeqCat(seqs[1..])
}

function SeqCatRev<T>(seqs:seq<seq<T>>) : seq<T>
{
    if |seqs| == 0 then []
    else SeqCatRev(all_but_last(seqs)) + last(seqs)
}

lemma lemma_SeqCat_adds<T>(A:seq<seq<T>>, B:seq<seq<T>>)
    ensures SeqCat(A + B) == SeqCat(A) + SeqCat(B);
{
    if |A| == 0 {
    } else {
        calc {
            SeqCat(A + B);
                { assert (A + B)[0] == A[0];  assert (A + B)[1..] == A[1..] + B; }
            A[0] + SeqCat(A[1..] + B);
            A[0] + SeqCat(A[1..]) + SeqCat(B);
            SeqCat(A) + SeqCat(B);
        }
    }
}

lemma lemma_SeqCatRev_adds<T>(A:seq<seq<T>>, B:seq<seq<T>>)
    ensures SeqCatRev(A + B) == SeqCatRev(A) + SeqCatRev(B);
{
    if |B| == 0 {
        assert SeqCatRev(B) == [];
        assert A+B == A;
    } else {
        calc {
            SeqCatRev(A + B);
                { assert last(A + B) == last(B);  assert all_but_last(A + B) == A + all_but_last(B); }
            SeqCatRev(A + all_but_last(B)) + last(B);
             SeqCatRev(A) + SeqCatRev(all_but_last(B)) + last(B);
            SeqCatRev(A) + SeqCatRev(B);
        }
    }
}

lemma lemma_SeqCat_equivalent<T>(seqs:seq<seq<T>>)
    ensures SeqCat(seqs) == SeqCatRev(seqs);
{
    if |seqs| == 0 {
    } else {
        calc {
            SeqCatRev(seqs);
            SeqCatRev(all_but_last(seqs)) + last(seqs);
                { lemma_SeqCat_equivalent(all_but_last(seqs)); }
            SeqCat(all_but_last(seqs)) + last(seqs);
            SeqCat(all_but_last(seqs)) + SeqCat([last(seqs)]);
                { lemma_SeqCat_adds(all_but_last(seqs), [last(seqs)]); 
                  assert seqs == all_but_last(seqs) + [last(seqs)]; }
            SeqCat(seqs);
        }

    }
}


}
