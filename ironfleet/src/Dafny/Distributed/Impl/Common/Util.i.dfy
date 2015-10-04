include "../../Common/Native/NativeTypes.i.dfy"
include "../../Common/Native/Io.s.dfy"
include "../../../Libraries/Math/power2.i.dfy"

module Common__Util_i {
import opened Native__NativeTypes_i
import opened Native__Io_s
import opened Math__power2_i

// Uses BigIntegers.  If you can, consider using the Opt versions below
method seqToArray_slow<A>(s:seq<A>) returns(a:array<A>)
    ensures  a != null;
    ensures  a[..] == s;
{
    var len := |s|;
    a := new A[len];
    var i := 0;
    while (i < len)
        invariant 0 <= i <= len;
        invariant a[..i] == s[..i];
    {
        a[i] := s[i];
        i := i + 1;
    }
}

// Uses BigIntegers.  If you can, consider using the Opt versions below
/*
method seqIntoArray_slow<A>(s:seq<A>, a:array<A>, index:nat)
    requires a != null;
    requires index + |s| <= a.Length;
    modifies a;
    ensures  a[..] == old(a[0..index]) + s + old(a[index + |s|..]);
{
    var i := index;

    while (i < index + |s|)
        invariant index <= i <= index + |s| <= a.Length;
        invariant a[..] == old(a[0..index]) + s[0..(i-index)] + old(a[i..]);
    {
        a[i] := s[i - index];
        i := i + 1;
        assert a[..] == old(a[0..index]) + s[0..(i-index)] + old(a[i..]);
    }
}
*/

method seqIntoArrayOpt<A>(s:seq<A>, a:array<A>)
    requires a != null;
    requires |s| == a.Length;
    requires |s| < 0x1_0000_0000_0000_0000;
    modifies a;
    ensures  a[..] == s;
{
    var i:uint64 := 0;

    while i < uint64(|s|)
        invariant 0 <= int(i) <= a.Length;
        invariant a[..] == s[0..i] + old(a[i..]);
    {
        a[i] := s[i];
        i := i + 1;
    }
}

method seqToArrayOpt<A>(s:seq<A>) returns(a:array<A>)
    requires |s| < 0x1_0000_0000_0000_0000;
    ensures  a != null;
    ensures  a[..] == s;
    ensures fresh(a);
{
    a := new A[uint64(|s|)];
    seqIntoArrayOpt(s, a);
}

method seqIntoArrayChar(s:seq<char>, a:array<char>)
    requires a != null;
    requires |s| == a.Length;
    requires |s| < 0x1_0000_0000_0000_0000;
    modifies a;
    ensures  a[..] == s;
{
    var i:uint64 := 0;

    while i < uint64(|s|)
        invariant 0 <= int(i) <= a.Length;
        invariant a[..] == s[0..i] + old(a[i..]);
    {
        a[i] := s[i];
        i := i + 1;
    }
}

method RecordTimingSeq(name:seq<char>, start:uint64, end:uint64)
    requires 0 < |name| < 0x1_0000_0000_0000_0000;
{
    var name_array := new char[|name|];

    seqIntoArrayChar(name, name_array);

    var time:uint64;
    if start <= end {
        time := end - start;
    } else {
        time := 0xFFFF_FFFF_FFFF_FFFF;
    }

    Time.RecordTiming(name_array, time);
}

function BEByteSeqToInt(bytes:seq<byte>) : int
    decreases |bytes|;
{
    if bytes == [] then 0
    else BEByteSeqToInt(bytes[..|bytes|-1]) * 256 + int(bytes[|bytes|-1])
}

lemma lemma_BEByteSeqToInt_bound(bytes:seq<byte>)
    ensures 0 <= BEByteSeqToInt(bytes);
    ensures BEByteSeqToInt(bytes) < power2(8*|bytes|);
{
    lemma_2toX();
    if bytes == [] {
    } else {
        calc {
            BEByteSeqToInt(bytes[..|bytes|-1]) + 1;
            <=
            power2(8*(|bytes|-1));
        }

        calc {
            BEByteSeqToInt(bytes);
            BEByteSeqToInt(bytes[..|bytes|-1]) * 256 + int(bytes[|bytes|-1]);
            < 
            BEByteSeqToInt(bytes[..|bytes|-1]) * 256 + 256;
            BEByteSeqToInt(bytes[..|bytes|-1]) * 256 + 1 * 256;
            (BEByteSeqToInt(bytes[..|bytes|-1]) + 1) * 256; 
            <=
            power2(8*(|bytes|-1)) * 256; 
            power2(8*(|bytes|-1)) * power2(8); 
                { lemma_power2_adds(8*(|bytes|-1), 8); }
            power2(8*|bytes|);
        }
    }
}

/*  Doesn't appear to be in use at present
lemma lemma_BEByteSeqToUint32_properties(bs:seq<byte>)
    requires |bs| == int(Uint32Size());
    ensures  var ret := uint32(bs[0]) * 256*256*256 + uint32(bs[1]) * 256*256 + uint32(bs[2]) * 256 + uint32(bs[3]);
             int(ret) == BEByteSeqToInt(bs);
{
    lemma_2toX(); 
    lemma_BEByteSeqToInt_bound(bs);
    var ret := uint32(bs[0]) * 256*256*256 + uint32(bs[1]) * 256*256 + uint32(bs[2]) * 256 + uint32(bs[3]);
    calc {
        BEByteSeqToInt(bs);
        BEByteSeqToInt(bs[..|bs|-1]) * 256 + int(bs[|bs|-1]);
            { assert bs[..|bs|-1][..|bs[..|bs|-1]|-1] == bs[..|bs|-2]; }
        (BEByteSeqToInt(bs[..|bs|-2]) * 256 + int(bs[|bs|-2])) * 256 + int(bs[|bs|-1]);
        ((BEByteSeqToInt(bs[..|bs|-3]) * 256 + int(bs[|bs|-3])) * 256 + int(bs[|bs|-2])) * 256 + int(bs[|bs|-1]);
        (((BEByteSeqToInt(bs[..|bs|-4]) * 256 + int(bs[|bs|-4])) * 256 + int(bs[|bs|-3])) * 256 + int(bs[|bs|-2])) * 256 + int(bs[|bs|-1]);
        int(ret);
    }
}
*/

lemma lemma_BEByteSeqToUint64_properties(bs:seq<byte>)
    requires |bs| == int(Uint64Size());
    ensures  var ret := uint64(bs[0]) * 256*256*256*0x100000000 + uint64(bs[1]) * 256*256*0x100000000 + uint64(bs[2]) * 256*0x100000000 + uint64(bs[3]) * 0x100000000 +
                        uint64(bs[4]) * 256*256*256 + uint64(bs[5]) * 256*256 + uint64(bs[6]) * 256 + uint64(bs[7]);
             int(ret) == BEByteSeqToInt(bs);
{
    lemma_2toX();
    var ret := uint64(bs[0]) * 256*256*256*0x100000000 + uint64(bs[1]) * 256*256*0x100000000 + uint64(bs[2]) * 256*0x100000000 + uint64(bs[3]) * 0x100000000 +
                            uint64(bs[4]) * 256*256*256 + uint64(bs[5]) * 256*256 + uint64(bs[6]) * 256 + uint64(bs[7]);

    var byteSeq := bs;

    calc {
        BEByteSeqToInt(bs);
        BEByteSeqToInt(bs[..|bs|-1]) * 256 + int(bs[|bs|-1]);
            { assert bs[..|bs|-1][..|bs[..|bs|-1]|-1] == bs[..|bs|-2]; }
        (BEByteSeqToInt(bs[..|bs|-2]) * 256 + int(bs[|bs|-2])) * 256 + int(bs[|bs|-1]);
            { assert bs[..|bs|-2][..|bs[..|bs|-2]|-1] == bs[..|bs|-3]; }
        ((BEByteSeqToInt(bs[..|bs|-3]) * 256 + int(bs[|bs|-3])) * 256 + int(bs[|bs|-2])) * 256 + int(bs[|bs|-1]);
            { assert bs[..|bs|-3][..|bs[..|bs|-3]|-1] == bs[..|bs|-4]; }
        (((BEByteSeqToInt(bs[..|bs|-4]) * 256 + int(bs[|bs|-4])) * 256 + int(bs[|bs|-3])) * 256 + int(bs[|bs|-2])) * 256 + int(bs[|bs|-1]);
            { assert bs[..|bs|-4][..|bs[..|bs|-4]|-1] == bs[..|bs|-5]; }
        ((((BEByteSeqToInt(bs[..|bs|-5]) * 256 + int(bs[|bs|-5])) * 256 + int(bs[|bs|-4])) * 256 + int(bs[|bs|-3])) * 256 + int(bs[|bs|-2])) * 256 + int(bs[|bs|-1]);
            { assert bs[..|bs|-5][..|bs[..|bs|-5]|-1] == bs[..|bs|-6]; }
        (((((BEByteSeqToInt(bs[..|bs|-6]) * 256 + int(bs[|bs|-6])) * 256 + int(bs[|bs|-5])) * 256 + int(bs[|bs|-4])) * 256 + int(bs[|bs|-3])) * 256 + int(bs[|bs|-2])) * 256 + int(bs[|bs|-1]);
            { assert bs[..|bs|-6][..|bs[..|bs|-6]|-1] == bs[..|bs|-7]; }
        ((((((BEByteSeqToInt(bs[..|bs|-7]) * 256 + int(bs[|bs|-7])) * 256 + int(bs[|bs|-6])) * 256 + int(bs[|bs|-5])) * 256 + int(bs[|bs|-4])) * 256 + int(bs[|bs|-3])) * 256 + int(bs[|bs|-2])) * 256 + int(bs[|bs|-1]);
        (((((((BEByteSeqToInt(bs[..|bs|-8]) * 256 + int(bs[|bs|-8])) * 256 + int(bs[|bs|-7])) * 256 + int(bs[|bs|-6])) * 256 + int(bs[|bs|-5])) * 256 + int(bs[|bs|-4])) * 256 + int(bs[|bs|-3])) * 256 + int(bs[|bs|-2])) * 256 + int(bs[|bs|-1]);
        int(ret);
    }
}

/*  Doesn't appear to be in use at present
function method BEByteSeqToUint32(bs:seq<byte>) : uint32
    requires |bs| == int(Uint32Size());
    ensures 0 <= BEByteSeqToInt(SeqByteToByteSeq(bs)) < 0x100000000;    // Need for the cast on the next line
    ensures BEByteSeqToUint32(bs) == uint32(BEByteSeqToInt(SeqByteToByteSeq(bs)));
{
    lemma_2toX(); //byteIsUint32_forall();
    //byteIsUint32(bs[0]); byteIsUint32(bs[1]); byteIsUint32(bs[2]); byteIsUint32(bs[3]);
    //byteIsByte(bs[0]); byteIsByte(bs[1]); byteIsByte(bs[2]); byteIsByte(bs[3]);
    //byteTimes0x100IsWord(bs[2]); byteTimes0x10000IsWord(bs[1]); byteTimes0x1000000IsWord(bs[0]);
    lemma_BEByteSeqToUint32_properties(bs);
    uint32(bs[uint64(0)]) * 256*256*256 + uint32(bs[uint64(1)]) * 256*256 + uint32(bs[uint64(2)]) * 256 + uint32(bs[uint64(3)])
}
*/

// renamed from BEByteSeqToUint64 to SeqByteToUint64
// "BEByteSeq" is a seq<int> with a byte precondition constraint, to
// access the generic pv library.
// So let's have SeqByte be a Dafny seq<byte>.
function method SeqByteToUint64(bs:seq<byte>) : uint64
    requires |bs| == int(Uint64Size());
    ensures 0 <= BEByteSeqToInt(bs) < 0x10000000000000000;    // Need for the cast on the next line
    ensures SeqByteToUint64(bs) == uint64(BEByteSeqToInt(bs));
{
    lemma_2toX();
    lemma_BEByteSeqToUint64_properties(bs);
    uint64(bs[uint64(0)]) * 256*256*256*0x100000000 + uint64(bs[uint64(1)]) * 256*256*0x100000000 + uint64(bs[uint64(2)]) * 256*0x100000000 + uint64(bs[uint64(3)]) * 0x100000000 +
    uint64(bs[uint64(4)]) * 256*256*256 + uint64(bs[uint64(5)]) * 256*256 + uint64(bs[uint64(6)]) * 256 + uint64(bs[uint64(7)])
}

function BEUintToSeqByte(v:int, width:int) : seq<byte>
    ensures width >= 0 && v >= 0 ==> |BEUintToSeqByte(v, width)| == width;
{
    if width > 0 && v >= 0 then
        BEUintToSeqByte(v/0x100, width - 1) + [ byte(v % 0x100) ]
    else
        []
}

lemma lemma_BEUintToSeqByte_invertability(bytes:seq<byte>, val:int, width:nat)
    requires bytes == BEUintToSeqByte(val, width);
    requires 0 <= val < power2(8*width);
    requires |bytes| == width;
    ensures  BEByteSeqToInt(bytes) == val;
{
    lemma_2toX32();
    if width == 0 {
        assert BEUintToSeqByte(val, width) == [];
        assert power2(width) == 1;
        assert val == 0;
    } else {
        calc {
            val / 0x100;
            < { lemma_power2_adds(8*width-8, 8);
                lemma_div_by_multiple_is_strongly_ordered(val, power2(8*width), power2(8*width-8), power2(8)); }
            power2(8*width) / 0x100;
            power2(8*width) / power2(8);
                { lemma_power2_div_is_sub(8, 8*width); }
            power2(8*(width - 1));
        }

        calc {
            BEByteSeqToInt(bytes);
            BEByteSeqToInt(bytes[..|bytes|-1]) * 256 + int(bytes[|bytes|-1]);
                { lemma_BEUintToSeqByte_invertability(bytes[..|bytes|-1], val / 0x100, width - 1); }
            (val / 0x100) * 256 + int(bytes[|bytes|-1]);
            val;
        }
    }
}

lemma lemma_BEByteSeqToInt_invertability(bytes:seq<byte>, val:int, width:nat)
    requires BEByteSeqToInt(bytes) == val;
    requires 0 <= val < power2(8*width);
    requires |bytes| == width;
    ensures  bytes == BEUintToSeqByte(val, width);
{
    lemma_2toX32();
    if width == 0 {
        assert BEUintToSeqByte(val, width) == [];
        assert power2(width) == 1;
        assert val == 0;
    } else {
        calc {
            val / 0x100;
            < { lemma_power2_adds(8*width-8, 8);
                lemma_div_by_multiple_is_strongly_ordered(val, power2(8*width), power2(8*width-8), power2(8)); }
            power2(8*width) / 0x100;
            power2(8*width) / power2(8);
                { lemma_power2_div_is_sub(8, 8*width); }
            power2(8*(width - 1));
        }

        calc {
            BEUintToSeqByte(val, width);
            BEUintToSeqByte(val/0x100, width - 1) + [ byte(val % 0x100) ];
                { lemma_BEByteSeqToInt_invertability(bytes[..|bytes|-1], val / 0x100, width - 1); }
            bytes[..|bytes|-1] + [ byte(val % 0x100) ];
            bytes;
        }
    }
}

lemma lemma_BEByteSeqToInt_BEUintToSeqByte_invertability()
    ensures forall bytes:seq<byte>, width:nat :: 
            |bytes| == width ==> bytes == BEUintToSeqByte(BEByteSeqToInt(bytes), width);
    ensures forall val:int, width:nat :: 0 <= val < power2(8*width) ==>
            val == BEByteSeqToInt(BEUintToSeqByte(val, width));
{
    forall bytes:seq<byte>, width:nat | |bytes| == width 
        ensures bytes == BEUintToSeqByte(BEByteSeqToInt(bytes), width);
    {
        lemma_BEByteSeqToInt_bound(bytes);
        lemma_BEByteSeqToInt_invertability(bytes, BEByteSeqToInt(bytes), width);
    }
    forall val:int, width:nat | 0 <= val < power2(8*width)
        ensures val   == BEByteSeqToInt(BEUintToSeqByte(val, width));
    {
        lemma_BEUintToSeqByte_invertability(BEUintToSeqByte(val, width), val, width);
    }
}


function method Uint64ToSeqByte(u:uint64) : seq<byte>
    ensures Uint64ToSeqByte(u) == BEUintToSeqByte(int(u), 8);
{
    ghost var pv := 256;
    var bs := [
        byte(u/0x100000000000000),
        byte((u/  0x1000000000000) % 0x100),
        byte((u/    0x10000000000) % 0x100),
        byte((u/      0x100000000) % 0x100),
        byte((u/        0x1000000) % 0x100),
        byte((u/          0x10000) % 0x100),
        byte((u/            0x100) % 0x100),
        byte((u                  ) % 0x100) ];
    lemma_2toX();
    var u_int := int(u);
    calc {
        BEUintToSeqByte(u_int, 8);
        BEUintToSeqByte(u_int/0x100, 7) + [ byte(u_int % 0x100) ];
        BEUintToSeqByte((u_int/0x100/0x100), 6) + [ byte((u_int/0x100) % 0x100) ] + [ byte(u_int % 0x100) ];
            { lemma_div_denominator(int(u_int), 0x100, 0x100); }
        BEUintToSeqByte((u_int/0x10000), 6) + [ byte((u_int/0x100) % 0x100) ] + [ byte(u_int % 0x100) ];
            { lemma_div_denominator(int(u_int), 0x10000, 0x100); }
        BEUintToSeqByte(u_int/0x1000000, 5) + [ byte((u_int / 0x10000) % 0x100) ] + [ byte((u_int/0x100) % 0x100) ] + [ byte(u_int % 0x100) ];
            { lemma_div_denominator(int(u_int), 0x1000000, 0x100); }
        BEUintToSeqByte(u_int/0x100000000, 4) + [ byte((u_int / 0x1000000) % 0x100) ] + [ byte((u_int / 0x10000) % 0x100) ] + [ byte((u_int/0x100) % 0x100) ] + [ byte(u_int % 0x100) ];
            { lemma_div_denominator(int(u_int), 0x100000000, 0x100); }
        BEUintToSeqByte(u_int/0x10000000000, 3) + [ byte((u_int / 0x100000000) % 0x100) ] + [ byte((u_int / 0x1000000) % 0x100) ] + [ byte((u_int / 0x10000) % 0x100) ] + [ byte((u_int/0x100) % 0x100) ] + [ byte(u_int % 0x100) ];
            { lemma_div_denominator(int(u_int), 0x10000000000, 0x100); }
        BEUintToSeqByte(u_int/0x1000000000000, 2) + [ byte((u_int / 0x10000000000) % 0x100) ] + [ byte((u_int / 0x100000000) % 0x100) ] + [ byte((u_int / 0x1000000) % 0x100) ] + [ byte((u_int / 0x10000) % 0x100) ] + [ byte((u_int/0x100) % 0x100) ] + [ byte(u_int % 0x100) ];
            { lemma_div_denominator(int(u_int), 0x1000000000000, 0x100); }
        BEUintToSeqByte(u_int/0x100000000000000, 1) + [ byte((u_int / 0x1000000000000) % 0x100) ] + [ byte((u_int / 0x10000000000) % 0x100) ] + [ byte((u_int / 0x100000000) % 0x100) ] + [ byte((u_int / 0x1000000) % 0x100) ] + [ byte((u_int / 0x10000) % 0x100) ] + [ byte((u_int/0x100) % 0x100) ] + [ byte(u_int % 0x100) ];
            { lemma_div_denominator(int(u_int), 0x100000000000000, 0x100); }
        BEUintToSeqByte(u_int/0x10000000000000000, 0) + [ byte((u_int / 0x100000000000000) % 0x100) ] + [ byte((u_int / 0x1000000000000) % 0x100) ] + [ byte((u_int / 0x10000000000) % 0x100) ] + [ byte((u_int / 0x100000000) % 0x100) ] + [ byte((u_int / 0x1000000) % 0x100) ] + [ byte((u_int / 0x10000) % 0x100) ] + [ byte((u_int/0x100) % 0x100) ] + [ byte(u_int % 0x100) ];
    }
    bs
}

function method SeqByteToUint16(bs:seq<byte>) : uint16
    requires |bs| == int(Uint16Size());
    ensures 0 <= BEByteSeqToInt(bs) < 0x10000000000000000;    // Need for the cast on the next line
    ensures BEByteSeqToInt(bs) < 0x10000;
    ensures SeqByteToUint16(bs) == uint16(BEByteSeqToInt(bs));
{
    lemma_2toX();
    lemma_BEByteSeqToInt_bound(bs);
    uint16(bs[uint64(0)]) * 256 + uint16(bs[uint64(1)])
}

function method Uint16ToSeqByte(u:uint16) : seq<byte>
    ensures Uint16ToSeqByte(u) == BEUintToSeqByte(int(u), 2);
{
    ghost var pv := 256;
    var s := [
        byte((u/            0x100) % 0x100),
        byte((u                  ) % 0x100) ];
    lemma_2toX();
    var u_int := int(u);
    calc {
        BEUintToSeqByte(u_int, 2);
        BEUintToSeqByte(u_int/0x100, 1) + [ byte(u_int % 0x100) ];
        BEUintToSeqByte((u_int/0x100/0x100), 0) + [ byte((u_int/0x100) % 0x100) ] + [ byte(u_int % 0x100) ];
            { lemma_div_denominator(int(u_int), 0x100, 0x100); }
        BEUintToSeqByte((u_int/0x10000), 0) + [ byte((u_int/0x100) % 0x100) ] + [ byte(u_int % 0x100) ];
    }
    s
}

} 
