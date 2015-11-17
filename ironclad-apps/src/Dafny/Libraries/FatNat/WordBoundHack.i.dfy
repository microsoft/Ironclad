include "../Util/DebugPrint.i.dfy"
include "../Util/Halter.i.dfy"






method constrain_word_from_overflowing(word:nat)
    ensures word<power2(32);
{
    //- TakeTopBits must already have failed with an overflow.
    
    
    
    
    
    
    lemma_2toX();
    if (0xffffffff <= word)
    {
        HaltMachine(0x50);
    }
}

