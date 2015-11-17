include "../../Drivers/CPU/assembly_premium.i.dfy"
include "../Math/bit_vector_lemmas_premium.i.dfy"

//- Implements an Xorshift random number generator based on the example from:
//- http://en.wikipedia.org/wiki/Xorshift

method update_state(w:int, x:int, y:int, z:int) returns (w':int, x':int, y':int, z':int)
    requires Word32(w)  && Word32(x)  && Word32(y)  && Word32(z);
    ensures  Word32(w') && Word32(x') && Word32(y') && Word32(z');
{
    lemma_2toX();
    var t := Asm_BitwiseXor(x, Asm_LeftShift(x, 11));
    x' := y;
    y' := z;
    z' := w;
    w' := Asm_BitwiseXor(w, Asm_BitwiseXor(Asm_RightShift(w, 19), Asm_BitwiseXor(t, Asm_RightShift(t, 8)))); 
}

method insecure_get_random(num_bytes:int) returns (random_bytes:seq<int>)
    requires Word32(num_bytes);
    ensures IsByteSeqOfLen(random_bytes, num_bytes);
{
    //- Use rdtsc as a seed
    var x, y := Asm_Rdtsc();
    var w := 5331;
    var z := 4229;

    lemma_2toX();

    //- Iterate the PRNG a few times to absorb the rdtsc 'randomness'
    var i := 0;
    while (i < 100) 
        invariant Word32(w) && Word32(x) && Word32(y) && Word32(z);
    {
        w, x, y, z := update_state(w, x, y, z);
        i := i + 1;
    }

    //- Generate the actual 'random' bytes requested
    var bytes := [];
    i := 0;
    while (i < num_bytes) 
        invariant 0 <= i <= num_bytes;
        invariant IsByteSeqOfLen(bytes, i);
        invariant Word32(w) && Word32(x) && Word32(y) && Word32(z);
    {
        w, x, y, z := update_state(w, x, y, z);

        var rand_byte := Asm_BitwiseAnd(w, 0xFF);
        lemma_and_with_ff_premium();

        //- Grab the lowest byte for our collection
        bytes := [rand_byte] + bytes;
        i := i + 1;
    }

    random_bytes := bytes;
}
