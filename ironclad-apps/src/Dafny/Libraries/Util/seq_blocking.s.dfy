include "be_sequences.s.dfy"

static function{:opaque} BreakIntoBlocks(os:seq<int>, block_size:int) : seq<seq<int>>
    requires 0 < block_size;
    decreases |os|;
{
    if |os| == 0 then []
    else if |os| < block_size then [os]
    else [os[..block_size]] + BreakIntoBlocks(os[block_size..], block_size)
}
