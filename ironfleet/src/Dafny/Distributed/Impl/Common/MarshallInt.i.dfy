include "../../Common/Native/NativeTypes.s.dfy"
//include "../../../Libraries/Util/seqs_transforms.i.dfy"
include "Util.i.dfy"

module Common__MarshallInt_i {
import opened Native__NativeTypes_s
//import opened Util__seqs_transforms_i
import opened Common__Util_i

/*  Doesn't appear to be in use at present
method MarshallUint32_guts(n:uint32, data:array<byte>, index:uint64)
    requires data != null;
    requires int(index) + int(Uint32Size()) <= data.Length;
    requires 0 <= int(index) + int(Uint32Size()) < 0x1_0000_0000_0000_0000;  // Needed to prevent overflow on the next line
    requires data.Length < 0x1_0000_0000_0000_0000;
    modifies data;
    ensures  BEByteSeqToUint32(data[index..index+uint64(Uint32Size())]) == n;
    ensures  data[0..index] == old(data[0..index]);
    ensures  data[index+uint64(Uint32Size())..] == old(data[index+uint64(Uint32Size())..]);
{
    data[index  ] := byte( n/0x1000000);
    data[index+1] := byte((n/  0x10000)%0x100);
    data[index+2] := byte((n/    0x100)%0x100);
    data[index+3] := byte( n           %0x100);
    ghost var i := int(n);
    ghost var bs := [ i / 16777216, (i / 65536) % 256, (i / 256) % 256, i % 256 ];
    assert SeqByteToByteSeq(data[index..index+4]) == bs;

    lemma_2toX();
    BEWordToByte_literal(int(n), bs);
}
*/

method MarshallUint64_guts(n:uint64, data:array<byte>, index:uint64)
    requires data != null;
    requires int(index) + int(Uint64Size()) <= data.Length;
    requires 0 <= int(index) + int(Uint64Size()) < 0x1_0000_0000_0000_0000;  // Needed to prevent overflow on the next line
    requires data.Length < 0x1_0000_0000_0000_0000;
    modifies data;
    ensures  SeqByteToUint64(data[index..index+uint64(Uint64Size())]) == n;
    ensures  data[0..index] == old(data[0..index]);
    ensures  data[index+uint64(Uint64Size())..] == old(data[index+uint64(Uint64Size())..]);
{
    data[index  ] := byte( n/0x1000000_00000000);
    data[index+1] := byte((n/  0x10000_00000000)%0x100);
    data[index+2] := byte((n/    0x100_00000000)%0x100);
    data[index+3] := byte((n/      0x1_00000000)%0x100);
    data[index+4] := byte((n/         0x1000000)%0x100);
    data[index+5] := byte((n/           0x10000)%0x100);
    data[index+6] := byte((n/             0x100)%0x100);
    data[index+7] := byte( n                    %0x100);

    lemma_2toX();

    assert data[index..index+uint64(Uint64Size())] == Uint64ToSeqByte(n);
    lemma_BEUintToSeqByte_invertability(data[index..index+uint64(Uint64Size())], int(n), 8);
}


} 
