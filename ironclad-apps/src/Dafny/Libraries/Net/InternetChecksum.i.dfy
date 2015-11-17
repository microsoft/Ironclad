//-<NuBuild BasmEnableSymdiff true />
include "../Math/power2.s.dfy"
include "../Math/bit_vector_lemmas_premium.i.dfy"
include "../../Drivers/CPU/assembly.s.dfy"
include "../../Drivers/CPU/assembly_premium.i.dfy"
include "../Util/word_bits.i.dfy"
include "../Util/relational.s.dfy"

//-
//- The "Internet Checksum" is the checksum used for error-checking of the IPv4
//- header (see RFC 791) as well as for error-checking of the UDP (see RFC 768)
//- and TCP (see RFC 793) headers and payloads.
//-
//- The checksum is the 16 bit one's complement of the one's complement sum of
//- all the 16 bit values covered by the checksum.  If an odd number of bytes
//- are being checksummed, a virtual zero byte is added at the end.
//-
//- See also RFC 1071.
//-

method InternetChecksum(Data:seq<int>)
    returns (Checksum:int)
    requires IsByteSeq(Data);
    requires |Data| > 0;
    requires public(Data);
    ensures Word16(Checksum);
    ensures public(Checksum);
{
    lemma_power2_32();

    Checksum := PartialChecksum(Data);
    Checksum := Asm_BitwiseAnd(Asm_BitwiseNot(Checksum), 0xffff);

    lemma_and_with_ffff_premium();
}

method PartialChecksum(Data:seq<int>)
    returns (Checksum:int)
    requires IsByteSeq(Data);
    requires |Data| > 0;
    requires public(Data);
    ensures Word16(Checksum);
    ensures public(Checksum);
{
    lemma_power2_32();

    Checksum := 0;
    var Index := 0;

    while (Index < |Data| - 1)
        invariant Index >= 0;
        invariant Word16(Checksum);
        invariant public(Index);
        invariant public(Checksum);
        invariant public(Data);
    {
        Checksum := OnesComplementSum16(Checksum, Data[Index] * 0x100 + Data[Index + 1]);
        Index := Index + 2;
    }

    if (Index < |Data|)
    {
        Checksum := OnesComplementSum16(Checksum, Data[Index] * 0x100);
    }
}

method OnesComplementSum16(x:int, y:int)
    returns (Sum:int)
    requires Word16(x);
    requires Word16(y);
    requires public(x);
    requires public(y);
    ensures Word16(Sum);
    ensures public(Sum);
{
    //-
    //- First calculate the conventional sum.
    //-
    Sum := x + y;

    //-
    //- To convert this value into a 16 bit one's complement representation,
    //- we need to check whether this sum has overflowed the maximum 16 bit
    //- value.  If so, we need to perform an "end-around carry".  This entails
    //- taking the overflow (i.e. carry) value and adding it back into the sum.
    //-
    //- Note that the maximum value the conventional sum of two unsigned 16 bit
    //- values can reach is 2 * 0xffff = 0x1fffe.  This means that at most the
    //- overflow is a single carry bit, which we can safely add back into our
    //- remaining value (i.e. max 0xfffe) without concern for another overflow.
    //-
    if (Sum >= 0x10000)
    {
        Sum := Sum - 0x10000 + 1;
    }
}
