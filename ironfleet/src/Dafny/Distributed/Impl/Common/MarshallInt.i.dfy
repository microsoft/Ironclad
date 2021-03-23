include "../../Common/Native/NativeTypes.s.dfy"
include "Util.i.dfy"

module Common__MarshallInt_i {
import opened Native__NativeTypes_s
import opened Native__NativeTypes_i
import opened Common__Util_i
import opened Math__power2_i

/*  Doesn't appear to be in use at present
method MarshallUint32_guts(n:uint32, data:array<byte>, index:uint64)
  requires data != null
  requires (index as int) + (Uint32Size() as int) <= data.Length
  requires 0 <= (index as int) + (Uint32Size() as int) < 0x1_0000_0000_0000_0000  // Needed to prevent overflow on the next line
  requires data.Length < 0x1_0000_0000_0000_0000
  modifies data
  ensures  BEByteSeqToUint32(data[index .. index + Uint32Size() as uint64]) == n
  ensures  data[0..index] == old(data[0..index])
  ensures  data[index + Uint32Size() as uint64 ..] == old(data[index + Uint32Size() as uint64..])
{
  data[index  ] := ( n/0x1000000) as byte;
  data[index+1] := ((n/  0x10000)%0x100) as byte;
  data[index+2] := ((n/    0x100)%0x100) as byte;
  data[index+3] := ( n           %0x100) as byte;
  ghost var i := n as int;
  ghost var bs := [ i / 16777216, (i / 65536) % 256, (i / 256) % 256, i % 256 ];
  assert SeqByteToByteSeq(data[index..index+4]) == bs;

  lemma_2toX();
  BEWordToByte_literal(n as int, bs);
}
*/

method MarshallUint64_guts(n:uint64, data:array<byte>, index:uint64)
  requires (index as int) + (Uint64Size() as int) <= data.Length
  requires 0 <= (index as int) + (Uint64Size() as int) < 0x1_0000_0000_0000_0000  // Needed to prevent overflow on the next line
  requires data.Length < 0x1_0000_0000_0000_0000
  modifies data
  ensures  SeqByteToUint64(data[index..index+(Uint64Size() as uint64)]) == n
  ensures  data[0..index] == old(data[0..index])
  ensures  data[index+(Uint64Size() as uint64)..] == old(data[index+(Uint64Size() as uint64)..])
{
  data[index  ] :=  (n/0x1000000_00000000)        as byte;
  data[index+1] := ((n/  0x10000_00000000)%0x100) as byte;
  data[index+2] := ((n/    0x100_00000000)%0x100) as byte;
  data[index+3] := ((n/      0x1_00000000)%0x100) as byte;
  data[index+4] := ((n/         0x1000000)%0x100) as byte;
  data[index+5] := ((n/           0x10000)%0x100) as byte;
  data[index+6] := ((n/             0x100)%0x100) as byte;
  data[index+7] := ( n                    %0x100) as byte;

  lemma_2toX();

  assert data[index..index+(Uint64Size() as uint64)] == Uint64ToSeqByte(n);
  lemma_BEUintToSeqByte_invertability(data[index..index+(Uint64Size() as uint64)], n as int, 8);
}


} 
