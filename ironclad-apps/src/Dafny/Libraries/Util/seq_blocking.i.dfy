include "seq_blocking.s.dfy"
include "seqs_simple.i.dfy"
include "arrays_and_seqs.i.dfy"
include "../Math/round.i.dfy"
include "../Math/div.i.dfy"
include "../Math/mul.i.dfy"

static lemma Lemma_SubtractOneBlock(block_num:int, block_size:int, block_index:int)
    ensures (block_num-1)*block_size + block_index == block_num * block_size + block_index - block_size;
{
    calc {
        (block_num-1)*block_size;
        { lemma_mul_is_commutative(block_num-1, block_size);}
        block_size * (block_num-1);
        { lemma_mul_is_distributive_sub(block_size, block_num, 1); }
        (block_size * block_num) - (block_size * 1);
        (block_size * block_num) - block_size;
        { lemma_mul_is_commutative(block_size, block_num); }
        (block_num * block_size) - block_size;
    }
}

static lemma{:dafnycc_conservative_seq_triggers} Lemma_BlockedSequenceContainsElement(os:seq<int>, block_size:int, block_num:int, block_index:int)
    requires 0 <= block_index < block_size;
    requires 0 <= block_num;
    requires 0 <= block_num * block_size + block_index < |os|;
    ensures block_num < |BreakIntoBlocks(os, block_size)|;
    ensures block_index < |BreakIntoBlocks(os, block_size)[block_num]|;
    ensures 0 <= block_num * block_size + block_index;
    ensures os[block_num * block_size + block_index] == BreakIntoBlocks(os, block_size)[block_num][block_index];
{
    reveal_BreakIntoBlocks();
    calc {
        |os|;
        > block_num * block_size + block_index;
        >= { lemma_mul_inequality(0, block_num, block_size); lemma_mul_is_mul_boogie(0, block_size); }
           (0 * block_size) + block_index;
        == 0 + block_index;
        >= 0;
    }
    assert |os| > 0;

    calc {
        block_num * block_size + block_index;
        >= { lemma_mul_inequality(0, block_num, block_size); lemma_mul_is_mul_boogie(0, block_size); }
           (0 * block_size) + block_index;
        == 0 + block_index;
        >= 0;
    }

    if |os| < block_size {
        if block_num >= 1 {
            calc {
                |os|;
                > block_num * block_size + block_index;
                >= { lemma_mul_inequality(1, block_num, block_size); lemma_mul_is_mul_boogie(1, block_size); }
                   (1 * block_size) + block_index;
                == block_size + block_index;
                >= block_size;
                >= |os|;
            }
            assert false;
        }
        assert 0 == block_num < |BreakIntoBlocks(os, block_size)|;
        calc {
            |BreakIntoBlocks(os, block_size)[block_num]|;
            == |os|;
            > block_num * block_size + block_index;
            == { lemma_mul_is_mul_boogie(0, block_size); }
               0 * block_size + block_index;
            == block_index;
        }
        calc {
            os[block_num * block_size + block_index];
            { lemma_mul_is_mul_boogie(0, block_size); }
            os[0 * block_size + block_index];
            os[block_index];
            BreakIntoBlocks(os, block_size)[0][block_index];
            BreakIntoBlocks(os, block_size)[block_num][block_index];
        }
    }
    else {
        if block_num > 0 {
            calc {
                (block_num-1)*block_size + block_index;
                >= { lemma_mul_nonnegative(block_num-1, block_size); }
                   0 + block_index;
                >= 0;
            }
            calc {
                (block_num-1)*block_size + block_index;
                { Lemma_SubtractOneBlock(block_num, block_size, block_index); }
                block_num * block_size - block_size + block_index;
                < |os| - block_size;
                == |os[block_size..]|;
            }
            Lemma_BlockedSequenceContainsElement(os[block_size..], block_size, block_num-1, block_index);
            calc {
                os[block_num * block_size + block_index];
                calc {
                    block_num * block_size + block_index;
                    >= { lemma_mul_inequality(1, block_num, block_size); lemma_mul_is_mul_boogie(1, block_size); }
                       1 * block_size + block_index;
                    == block_size + block_index;
                    >= block_size;
                }
                { lemma_seq_suffix(os, block_size, block_num * block_size + block_index); }
                os[block_size..][block_num * block_size + block_index - block_size];
                { Lemma_SubtractOneBlock(block_num, block_size, block_index); }
                os[block_size..][(block_num-1) * block_size + block_index];
                { Lemma_BlockedSequenceContainsElement(os[block_size..], block_size, block_num-1, block_index); }
                BreakIntoBlocks(os[block_size..], block_size)[block_num-1][block_index];
                ([os[..block_size]] + BreakIntoBlocks(os[block_size..], block_size))[block_num][block_index];
                BreakIntoBlocks(os, block_size)[block_num][block_index];
            }
        }
        else {
            calc {
                os[block_num * block_size + block_index];
                { lemma_mul_is_mul_boogie(0, block_size); }
                os[0 * block_size + block_index];
                os[block_index];
                os[..block_size][block_index];
                ([os[..block_size]] + BreakIntoBlocks(os[block_size..], block_size))[0][block_index];
                ([os[..block_size]] + BreakIntoBlocks(os[block_size..], block_size))[block_num][block_index];
                BreakIntoBlocks(os, block_size)[block_num][block_index];
            }
        }
    }
}

static lemma Lemma_BlockedSequencePrefixContainsElement(os:seq<int>, prefix_size:int, block_size:int, block_num:int, block_index:int)
    requires 0 <= block_index < block_size;
    requires 0 <= block_num;
    requires 0 <= prefix_size;
    requires 0 <= block_num * block_size + block_index < prefix_size <= |os|;
    ensures block_num < |BreakIntoBlocks(os, block_size)|;
    ensures block_index < |BreakIntoBlocks(os, block_size)[block_num]|;
    ensures block_num < |BreakIntoBlocks(os[..prefix_size], block_size)|;
    ensures block_index < |BreakIntoBlocks(os[..prefix_size], block_size)[block_num]|;
    ensures os[block_num * block_size + block_index] == BreakIntoBlocks(os[..prefix_size], block_size)[block_num][block_index];
{
    Lemma_BlockedSequenceContainsElement(os, block_size, block_num, block_index);
    Lemma_BlockedSequenceContainsElement(os[..prefix_size], block_size, block_num, block_index);
    calc {
        os[block_num * block_size + block_index];
        (os[..prefix_size] + os[prefix_size..])[block_num * block_size + block_index];
        os[..prefix_size][block_num * block_size + block_index];
        BreakIntoBlocks(os[..prefix_size], block_size)[block_num][block_index];
    }
}

static lemma Lemma_AllBlocksAreOfEqualSize(os:seq<int>, block_size:int)
    requires 0 < block_size;
    requires |os| % block_size == 0;
    ensures |BreakIntoBlocks(os, block_size)| == |os| / block_size;
    ensures forall blk :: 0 <= blk < |BreakIntoBlocks(os, block_size)| ==> |BreakIntoBlocks(os, block_size)[blk]| == block_size;
{
    reveal_BreakIntoBlocks();
    var num_blocks := |os| / block_size;
    var blocks := BreakIntoBlocks(os, block_size);

    calc {
        |os|;
        { lemma_fundamental_div_mod(|os|, block_size); }
        block_size * (|os| / block_size) + |os| % block_size;
        block_size * num_blocks + |os| % block_size;
        block_size * num_blocks + 0;
        block_size * num_blocks;
    }

    if |os| == 0 {
        lemma_div_basics(block_size);
    }
    else if |os| < block_size {
        calc {
            (0 * block_size) + |os|;
            |os|;
        }
        lemma_fundamental_div_mod_converse(|os|, block_size, 0, |os|);
        assert |os| % block_size == |os| == 0;
        assert false;
    }
    else {
        calc {
            num_blocks;
            == |os| / block_size;
            >= { lemma_div_is_ordered(block_size, |os|, block_size); }
               block_size / block_size;
            { lemma_div_basics(block_size); }
            1;
        }
        calc {
            |os[block_size..]| % block_size;
            (|os| - block_size) % block_size;
            (-1 * block_size + |os|) % block_size;
            (block_size * -1 + |os|) % block_size;
            { lemma_mul_is_mul_boogie(block_size, -1);
              lemma_mod_multiples_vanish(-1, |os|, block_size); }
            |os| % block_size;
            0;
        }
        Lemma_AllBlocksAreOfEqualSize(os[block_size..], block_size);
        assert |BreakIntoBlocks(os[block_size..], block_size)| == |os[block_size..]| / block_size;
        calc {
            |blocks|;
            1 + |BreakIntoBlocks(os[block_size..], block_size)|;
            1 + |os[block_size..]| / block_size;
            1 + (|os| - block_size) / block_size;
            1 + (block_size * num_blocks - block_size) / block_size;
            1 + (block_size * num_blocks - 1 * block_size) / block_size;
            { lemma_mul_is_mul_boogie(1, block_size);
              lemma_mul_is_commutative(1, block_size);
              lemma_mul_is_distributive_sub(block_size, num_blocks, 1); }
            1 + (block_size * (num_blocks - 1)) / block_size;
            { lemma_mul_is_commutative(block_size, num_blocks - 1);
              lemma_div_by_multiple(num_blocks - 1, block_size); }
            1 + (num_blocks - 1);
            |os| / block_size;
        }
    }
}

static lemma Lemma_AllBlocksAreWordSeqs(os:seq<int>, block_size:int)
    requires 0 < block_size;
    requires IsWordSeq(os);
    ensures forall blk :: 0 <= blk < |BreakIntoBlocks(os, block_size)| ==> IsWordSeq(BreakIntoBlocks(os, block_size)[blk]);
{
    reveal_BreakIntoBlocks();
    if (|os| >= block_size)
    {
        Lemma_AllBlocksAreWordSeqs(os[block_size..], block_size);
        assert BreakIntoBlocks(os, block_size) == [os[..block_size]] + BreakIntoBlocks(os[block_size..], block_size); //- dafnycc triggering
    }
}

static predicate BlockBoundariesAreWithinSequence(i:int, block_size:int, len:int)
{
    0 <= i*block_size <= (i+1)*block_size <= len
}

static lemma Lemma_BoundariesOfSeqBlock(s:seq<int>, block_size:int)
    requires 0 < block_size;
    requires |s| % block_size == 0;
    ensures forall i :: 0 <= i < (|s| / block_size) ==> BlockBoundariesAreWithinSequence(i, block_size, |s|);
    ensures |s| == (|s| / block_size) * block_size;
{
    Lemma_AllBlocksAreOfEqualSize(s, block_size);

    var num_blocks := |s| / block_size;

    calc {
        |s|;
        { lemma_fundamental_div_mod(|s|, block_size); }
        block_size * (|s| / block_size) + |s| % block_size;
        block_size * num_blocks + |s| % block_size;
        block_size * num_blocks + 0;
        block_size * num_blocks;
        { lemma_mul_is_commutative(block_size, num_blocks); }
        num_blocks * block_size;
    }

    forall j | 0 <= j < num_blocks
        ensures 0 <= j*block_size;
    {
        lemma_mul_nonnegative(j, block_size);
    }

    forall j | 0 <= j < num_blocks
        ensures j*block_size <= (j+1)*block_size <= |s|;
    {
        calc {
            j*block_size;
            <= { lemma_mul_inequality(j, j+1, block_size); }
               (j+1)*block_size;
        }
        calc {
            (j+1) * block_size;
            <= { lemma_mul_inequality(j+1, num_blocks, block_size); }
               num_blocks * block_size;
            |s|;
        }
    }
}

static lemma Lemma_EqualBlockingCausesSpecificSubsequences(s:seq<int>, block_size:int, i:int)
    requires 0 < block_size;
    requires |s| % block_size == 0;
    requires 0 <= i < (|s| / block_size);
    ensures 0 <= i*block_size <= (i+1)*block_size <= |s|;
    ensures |BreakIntoBlocks(s, block_size)| == |s| / block_size;
    ensures BreakIntoBlocks(s, block_size)[i] == s[i*block_size .. (i+1)*block_size];
{
    Lemma_AllBlocksAreOfEqualSize(s, block_size);
    Lemma_BoundariesOfSeqBlock(s, block_size);
    assert BlockBoundariesAreWithinSequence(i, block_size, |s|);

    if i == 0 {
        calc <= {1; {reveal_BreakIntoBlocks();} |s|;}
        if |s| < block_size {
            lemma_small_div();
            assert |s| / block_size == 0;
            assert false;
        }
        else if |s| == block_size {
            calc {
                BreakIntoBlocks(s, block_size)[i];
                { reveal_BreakIntoBlocks(); }
                [s][i];
                [s][0];
                s;
                s[0..|s|];
                s[0..block_size];
                s[0*block_size..1*block_size];
                { lemma_mul_is_mul_boogie(0, block_size); }
                s[i*block_size..1*block_size];
                { reveal_BreakIntoBlocks(); }
                s[i*block_size..(i+1)*block_size];
            }
        }
        else {
            calc {
                BreakIntoBlocks(s, block_size)[i];
                BreakIntoBlocks(s, block_size)[0];
                { reveal_BreakIntoBlocks(); }
                ([s[..block_size]] + BreakIntoBlocks(s[block_size..], block_size))[0];
                s[..block_size];
                s[0..block_size];
                s[0*block_size..1*block_size];
                { lemma_mul_is_mul_boogie(0, block_size); }
                s[i*block_size..1*block_size];
                { lemma_mul_is_mul_boogie(1, block_size); }
                s[i*block_size..(i+1)*block_size];
            }
        }
    }
    else {
        if |s| < block_size {
            lemma_small_div();
            assert |s| / block_size == 0;
            assert false;
        }
        else if |s| == block_size {
            calc {|s| / block_size; { reveal_BreakIntoBlocks(); } 1;}
            assert false;
        }
        else {
            calc {
                BreakIntoBlocks(s, block_size)[i];
                { reveal_BreakIntoBlocks(); }
                ([s[..block_size]] + BreakIntoBlocks(s[block_size..], block_size))[i];
                BreakIntoBlocks(s[block_size..], block_size)[i-1];
                { calc {
                      (|s| - block_size) % block_size;
                      (-block_size + |s|) % block_size;
                      (block_size * -1 + |s|) % block_size;
                      { lemma_mod_multiples_vanish(-1, |s|, block_size); }
                      { lemma_mul_is_mul_boogie(block_size, -1); }
                      |s| % block_size;
                      0;
                  }
                  calc {
                      i-1;
                      < |s|/block_size - 1;
                      { lemma_hoist_over_denominator(|s|, -1, block_size); lemma_mul_is_mul_boogie(-1, block_size); }
                      (|s| + -1 * block_size) / block_size;
                      (|s| - block_size)/block_size;
                  }
                  Lemma_EqualBlockingCausesSpecificSubsequences(s[block_size..], block_size, i-1); }
                s[block_size..][(i-1)*block_size..(i-1+1)*block_size];
                s[block_size..][(i-1)*block_size..i*block_size];
                { lemma_mul_nonnegative(i - 1, block_size); /* dafnycc */ }
                s[(i-1)*block_size+block_size..i*block_size+block_size];
                s[(i-1)*block_size+block_size*1..i*block_size+block_size];
                { lemma_mul_is_commutative(i-1, block_size); }
                s[block_size*(i-1)+block_size*1..i*block_size+block_size];
                { lemma_mul_is_mul_boogie(block_size, 1); lemma_mul_is_distributive_add(block_size, i-1, 1); }
                s[block_size*(i-1+1)..i*block_size+block_size];
                s[block_size*i..i*block_size+block_size];
                { lemma_mul_is_commutative(i, block_size); }
                s[i*block_size..block_size*i+block_size];
                s[i*block_size..block_size*i+block_size*1];
                { lemma_mul_is_mul_boogie(block_size, 1); lemma_mul_is_distributive_add(block_size, i, 1); }
                s[i*block_size..block_size*(i+1)];
                { lemma_mul_is_commutative(i+1, block_size); }
                s[i*block_size..(i+1)*block_size];
            }
        }
    }
}

static method DivideSeqIntoEqualBlocks(s:seq<int>, block_size:int) returns (r:seq<seq<int>>)
    requires 0 < block_size;
    requires |s| % block_size == 0;
    ensures r == BreakIntoBlocks(s, block_size);
    ensures forall i :: 0 <= i < |r| ==> |r[i]| == block_size;
{
    Lemma_AllBlocksAreOfEqualSize(s, block_size);

    var num_blocks := |s| / block_size;
    var i := 0;
    r := [];

    Lemma_BoundariesOfSeqBlock(s, block_size);

    assert forall j :: 0 <= j < num_blocks ==> BlockBoundariesAreWithinSequence(j, block_size, |s|);

    while i < num_blocks
        invariant 0 <= i <= num_blocks;
        invariant |r| == i;
        invariant forall j :: 0 <= j < i ==> BlockBoundariesAreWithinSequence(j, block_size, |s|) &&
                                             r[j] == s[j*block_size .. (j+1)*block_size];
    {
        assert BlockBoundariesAreWithinSequence(i, block_size, |s|);
        r := r + [s[i * block_size .. (i+1) * block_size]];
        i := i + 1;
    }

    assert |r| == |BreakIntoBlocks(s, block_size)|;

    forall j | 0 <= j < num_blocks
        ensures r[j] == BreakIntoBlocks(s, block_size)[j];
    {
        Lemma_EqualBlockingCausesSpecificSubsequences(s, block_size, j);
    }
}

static function{:opaque} PadSequenceToMultiple(os:seq<int>, block_size:int) : seq<int>
    requires 0 < block_size;
{
    if |os| % block_size == 0 then os
    else os + RepeatDigit(0, block_size - (|os| % block_size))
}

static function PadAndBreakIntoBlocks(os:seq<int>, block_size:int) : seq<seq<int>>
    requires 0 < block_size;
{
    BreakIntoBlocks(PadSequenceToMultiple(os, block_size), block_size)
}

static lemma lemma_PadSequenceToMultiple_premium_properties(os:seq<int>, block_size:int)
    requires 0 < block_size;
    ensures var padded_len := RoundUpToMultiple(|os|, block_size);
            var num_blocks := padded_len / block_size;
            |PadSequenceToMultiple(os, block_size)| == padded_len &&
            padded_len % block_size == 0 &&
            (forall i :: 0 <= i < num_blocks ==> 0 <= block_size*i == i*block_size) &&
            (forall i :: 0 <= i < num_blocks ==> i*block_size == block_size*i <= (i+1)*block_size == block_size*(i+1) <= padded_len) &&
            (forall i :: 0 <= i < num_blocks ==> 0 <= block_size*i == i*block_size <= (i+1)*block_size == block_size*(i+1) <= padded_len);
{
    reveal_BreakIntoBlocks();
    reveal_PadSequenceToMultiple();
    var padded_len := RoundUpToMultiple_premium(|os|, block_size);
    var num_blocks := padded_len / block_size;

    if |os| % block_size != 0 {
        calc {
            |PadSequenceToMultiple(os, block_size)|;
            |os + RepeatDigit(0, block_size - |os| % block_size)|;
            |os| + |RepeatDigit_premium(0, block_size - |os| % block_size)|;
            { lemma_mod_remainder_pos_specific(|os|, block_size); }
            |os| + block_size - |os| % block_size;
        }
    }

    forall i | 0 <= i < num_blocks
        ensures 0 <= block_size*i == i*block_size;
    {
        lemma_mul_nonnegative(block_size, i);
        lemma_mul_is_commutative(i, block_size);
    }

    forall i | 0 <= i < num_blocks
        ensures i*block_size == block_size*i <= (i+1)*block_size == block_size*(i+1) <= padded_len;
    {
        calc {
            i*block_size;
            <= { lemma_mul_inequality(i, i+1, block_size); }
               (i+1)*block_size;
        }
        calc {
            (i+1) * block_size;
            <= { lemma_mul_inequality(i+1, num_blocks, block_size); }
               num_blocks * block_size;
            { lemma_mul_is_commutative(num_blocks, block_size); }
            block_size * num_blocks;
            { lemma_fundamental_div_mod(padded_len, block_size); }
            padded_len - padded_len % block_size;
            padded_len;
        }
        lemma_mul_is_commutative(i, block_size);
        lemma_mul_is_commutative(i+1, block_size);
    }
}

static function PadSequenceToMultiple_premium(os:seq<int>, block_size:int) : seq<int>
    requires 0 < block_size;
    ensures var padded_len := RoundUpToMultiple(|os|, block_size);
            var num_blocks := padded_len / block_size;
            |PadSequenceToMultiple(os, block_size)| == padded_len &&
            padded_len % block_size == 0 &&
            (forall i :: 0 <= i < num_blocks ==> 0 <= block_size*i == i*block_size) &&
            (forall i :: 0 <= i < num_blocks ==> i*block_size == block_size*i <= (i+1)*block_size == block_size*(i+1) <= padded_len) &&
            (forall i :: 0 <= i < num_blocks ==> 0 <= block_size*i == i*block_size <= (i+1)*block_size == block_size*(i+1) <= padded_len);
{
    lemma_PadSequenceToMultiple_premium_properties(os, block_size);
    PadSequenceToMultiple(os, block_size)
}

static lemma lemma_PadAndBreakIntoBlocks_premium_properties(os:seq<int>, block_size:int)
    requires 0 < block_size;
    ensures var padded_len := RoundUpToMultiple(|os|, block_size);
            var num_blocks := padded_len / block_size;
            |PadSequenceToMultiple(os, block_size)| == padded_len &&
            padded_len % block_size == 0 &&
            |PadAndBreakIntoBlocks(os, block_size)| == num_blocks &&
            (forall i :: 0 <= i < num_blocks ==> |PadAndBreakIntoBlocks(os, block_size)[i]| == block_size &&
                                                 BlockBoundariesAreWithinSequence(i, block_size, padded_len) &&
                                                 PadAndBreakIntoBlocks(os, block_size)[i] ==
                                                     PadSequenceToMultiple(os, block_size)[i*block_size..(i+1)*block_size]);
{
    var ps := PadSequenceToMultiple_premium(os, block_size);
    var padded_len := |ps|;
    var num_blocks := padded_len / block_size;

    Lemma_AllBlocksAreOfEqualSize(ps, block_size);
    forall i | 0 <= i < num_blocks
        ensures PadAndBreakIntoBlocks(os, block_size)[i] == ps[i*block_size..(i+1)*block_size];
    {
        Lemma_EqualBlockingCausesSpecificSubsequences(ps, block_size, i);
    }
}

static function PadAndBreakIntoBlocks_premium(os:seq<int>, block_size:int) : seq<seq<int>>
    requires 0 < block_size;
    ensures var padded_len := RoundUpToMultiple(|os|, block_size);
            var num_blocks := padded_len / block_size;
            |PadSequenceToMultiple(os, block_size)| == padded_len &&
            padded_len % block_size == 0 &&
            |PadAndBreakIntoBlocks(os, block_size)| == num_blocks &&
            (forall i :: 0 <= i < num_blocks ==> |PadAndBreakIntoBlocks(os, block_size)[i]| == block_size &&
                                                 BlockBoundariesAreWithinSequence(i, block_size, padded_len) &&
                                                 PadAndBreakIntoBlocks(os, block_size)[i] ==
                                                     PadSequenceToMultiple(os, block_size)[i*block_size..(i+1)*block_size]);
{
    lemma_PadAndBreakIntoBlocks_premium_properties(os, block_size);
    PadAndBreakIntoBlocks(os, block_size)
}

static method PadSequenceToMultiple_impl(os:seq<int>, block_size:int) returns (ps:seq<int>)
    requires 0 < block_size;
    ensures ps == PadSequenceToMultiple(os, block_size);
{
    reveal_PadSequenceToMultiple();
    if |os| % block_size == 0 {
        ps := os;
    }
    else {
        var rs := RepeatDigit_impl(0, block_size - |os| % block_size);
        ps := os + rs;
    }
}

static method PadAndBreakIntoBlocks_impl(os:seq<int>, block_size:int) returns (r:seq<seq<int>>)
    requires 0 < block_size;
    ensures r == PadAndBreakIntoBlocks_premium(os, block_size);
{
    reveal_PadSequenceToMultiple();
    var ps := PadSequenceToMultiple_impl(os, block_size);
    assert ps == PadSequenceToMultiple_premium(os, block_size);
    r := DivideSeqIntoEqualBlocks(ps, block_size);
}

static lemma lemma_PadAndBreakIntoBlocksMaintainsByteSequence(os:seq<int>, block_size:int)
    requires 0 < block_size;
    requires IsByteSeq(os);
    ensures forall i :: 0 <= i < |PadAndBreakIntoBlocks(os, block_size)| ==> IsByteSeq(PadAndBreakIntoBlocks(os, block_size)[i]);
{
    reveal_BreakIntoBlocks();
    reveal_PadSequenceToMultiple();
    var ps := PadSequenceToMultiple_premium(os, block_size);
    var bs := BreakIntoBlocks(ps, block_size);
    lemma_2toX();

    if (|os| % block_size != 0) {
        forall i | 0 <= i < |ps|
            ensures IsByte(ps[i]);
        {
            if i >= |os| {
                calc {
                    ps[i];
                    (os + RepeatDigit(0, block_size - (|os| % block_size)))[i];
                    RepeatDigit(0, block_size - (|os| % block_size))[i-|os|];
                    RepeatDigit_premium(0, block_size - (|os| % block_size))[i-|os|];
                    0;
                }
            }
        }
    }

    forall i | 0 <= i < |bs|
        ensures IsByteSeq(bs[i]);
    {
        lemma_PadAndBreakIntoBlocks_premium_properties(os, block_size);
        assert BlockBoundariesAreWithinSequence(i, block_size, |ps|);
        assert bs[i] == ps[i*block_size..(i+1)*block_size];
    }
}
