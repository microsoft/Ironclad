include "hmac_common.s.dfy"
include "../../../Drivers/CPU/assembly_premium.i.dfy"
include "../../Util/integer_sequences_premium.i.dfy"
include "sha_padding.i.dfy"

//-///////////////////////////////////////////////////
//- ConstPad lemmas
//-///////////////////////////////////////////////////

static lemma lemma_ConstPad_properties(len:int, const:int)
    requires len >= 0;
    requires Mod32_const(len) == 0;
    requires Word32(const);
    ensures IsBitSeq(ConstPad(len, const));
    ensures |ConstPad(len, const)| == len;
    ensures ConstPad(len, const) == if len <= 0 then [] else BEWordToBitSeq(const) + ConstPad(len - 32, const);
{
    reveal_ConstPad();
    if len == 0 {
    }
    else {
        reveal_Mod32_const();
        lemma_ConstPad_properties(len - 32, const);
        assert BEWordToBitSeq_premium(const) == BEWordToBitSeq(const);
    }
}

static function ConstPad_premium(len:int, const:int) : seq<int>
    requires len >= 0;
    requires Mod32_const(len) == 0;
    requires Word32(const);
    ensures IsBitSeq(ConstPad_premium(len, const));
    ensures |ConstPad_premium(len, const)| == len;
    ensures ConstPad_premium(len, const) == if len <= 0 then [] else BEWordToBitSeq(const) + ConstPad(len - 32, const);
{
    lemma_ConstPad_properties(len, const);
    ConstPad(len, const)
}

static function Ipad_premium(len:int) : seq<int>
    requires len >= 0;
    requires Mod32_const(len) == 0;
    ensures IsBitSeq(Ipad_premium(len));
    ensures |Ipad_premium(len)| == len;
{
    lemma_2toX();
    lemma_ConstPad_properties(len, 0x36363636);
    Ipad(len)
}

static function Opad_premium(len:int) : seq<int>
    requires len >= 0;
    requires Mod32_const(len) == 0;
    ensures IsBitSeq(Opad_premium(len));
    ensures |Opad_premium(len)| == len;
{
    lemma_2toX();
    lemma_ConstPad_properties(len, 0x5c5c5c5c);
    Opad(len)
}

//-///////////////////////////////////////////////////
//- SeqXor lemmas
//-///////////////////////////////////////////////////

static lemma{:dafnycc_conservative_seq_triggers} lemma_SeqXor_properties(a: seq<int>, b: seq<int>)
    requires IsBitSeq(a);
    requires IsBitSeq(b);
    requires |a|==|b|;
    ensures |SeqXor(a, b)| == |a|;
    ensures forall i :: 0 <= i < |a| ==> SeqXor(a, b)[i] == Xor(a[i], b[i]);
{
    reveal_SeqXor();
    if |a| != 0 {
        lemma_SeqXor_properties(a[1..], b[1..]);
    }
}

static function SeqXor_premium(a: seq<int>, b: seq<int>) : seq<int>
    requires IsBitSeq(a);
    requires IsBitSeq(b);
    requires |a|==|b|;
    ensures |SeqXor_premium(a, b)| == |a|;
    ensures forall i {:trigger a[i]}{:trigger b[i]}{:trigger SeqXor_premium(a, b)[i]} :: 0 <= i < |a| ==>
        SeqXor_premium(a, b)[i] == Xor(a[i], b[i]);
{
    lemma_SeqXor_properties(a, b);
    SeqXor(a, b)
}

static lemma{:dafnycc_conservative_seq_triggers} lemma_SeqXor_Split(a: seq<int>, A: seq<int>, b: seq<int>, B: seq<int>)
    requires IsBitSeq(a) && IsBitSeq(b) && IsBitSeq(A) && IsBitSeq(B);
    requires |a| == |b| && |A| == |B|;
    ensures SeqXor_premium(a + A, b + B) == SeqXor_premium(a, b) + SeqXor_premium(A, B);
{
    if a == [] {
        assert a + A == A;
        assert b + B == B;
    } else {
        calc {
            SeqXor(a + A, b + B);
            { reveal_SeqXor(); }
            { assert a + A == [a[0]] + (a[1..] + A); assert b + B == [b[0]] + (b[1..] + B); }
            [Xor(a[0], b[0])] + SeqXor(a[1..] + A, b[1..]+B);
            { lemma_SeqXor_Split(a[1..], A, b[1..], B); }
            [Xor(a[0], b[0])] + SeqXor(a[1..], b[1..]) + SeqXor(A, B);
            { reveal_SeqXor(); }
            SeqXor(a, b) + SeqXor(A, B);
        }
    }
}


static lemma lemma_mul_mod_32(x:int, y:int)
    requires x == 32 * y;
    ensures  x % 32 == 0;
{
}


static lemma lemma_SeqXor_WordSeqToBitSeq(i:int, pad:seq<int>, key:seq<int>, const:int)
    requires |pad| == |key| == i;
    requires Word32(const);
    requires forall j {:trigger pad[j]}{:trigger key[j]} :: 0 <= j < |pad| ==> Word32(pad[j]) && Word32(key[j]);
    requires forall j {:trigger pad[j]}{:trigger key[j]} :: 0 <= j < |pad| ==> pad[j] == Asm_BitwiseXor(key[j], const);
    ensures Mod32_const(i*32) == 0;
    ensures BEWordSeqToBitSeq_premium(pad) == SeqXor(BEWordSeqToBitSeq_premium(key), ConstPad_premium(i*32, const));
{
    calc { Mod32_const(i*32); { lemma_Mod32_const(i*32); } 0; }
    if i == 0 {
        reveal_SeqXor();
        assert BEWordSeqToBitSeq_premium(pad) == SeqXor(BEWordSeqToBitSeq_premium(key), ConstPad_premium(i*32, const));
    } else {
        var len0 := i * 32;
        var len1 := (i - 1) * 32;
        ghost var x := SeqXor_premium(BEWordToBitSeq_premium(key[0]), BEWordToBitSeq_premium(const));
        lemma_mul_mod_32(len0, i);
        calc { Mod32_const(len0); { reveal_Mod32_const(); } 0; }
        calc {
            SeqXor_premium(BEWordSeqToBitSeq_premium(key), ConstPad_premium(len0, const));
            { lemma_WordSeqToBitSeqChopHead(key); }
            SeqXor_premium(BEWordToBitSeq_premium(key[0]) + BEWordSeqToBitSeq_premium(key[1..]), ConstPad_premium(len0, const));
            { reveal_Mod32_const(); }
            SeqXor_premium(BEWordToBitSeq_premium(key[0]) + BEWordSeqToBitSeq_premium(key[1..]),
                   BEWordToBitSeq_premium(const) + ConstPad_premium(len1, const));
            { assert len1 % 32 == 0; }
            { assert |ConstPad_premium(len1, const)| == len1; }
            { lemma_SeqXor_Split(BEWordToBitSeq_premium(key[0]), BEWordSeqToBitSeq_premium(key[1..]),
                                 BEWordToBitSeq_premium(const), ConstPad_premium(len1, const)); }
            SeqXor_premium(BEWordToBitSeq_premium(key[0]), BEWordToBitSeq_premium(const)) +
                SeqXor_premium(BEWordSeqToBitSeq_premium(key[1..]), ConstPad_premium(len1, const));
            x + SeqXor_premium(BEWordSeqToBitSeq_premium(key[1..]), ConstPad_premium(len1, const));
            { assert |pad[1..]| == |key[1..]| == i - 1; }
            { lemma_SeqXor_WordSeqToBitSeq(i - 1, pad[1..], key[1..], const); }
            { assert BEWordSeqToBitSeq_premium(pad[1..]) == SeqXor_premium(BEWordSeqToBitSeq_premium(key[1..]), ConstPad_premium(len1, const)); }
            x + BEWordSeqToBitSeq_premium(pad[1..]);
            SeqXor_premium(BEWordToBitSeq_premium(key[0]), BEWordToBitSeq_premium(const)) + BEWordSeqToBitSeq_premium(pad[1..]);
            { lemma_SeqXor_properties(BEWordToBitSeq_premium(key[0]), BEWordToBitSeq_premium(const)); }
            { assert forall j :: 0 <= j < |BEWordToBitSeq_premium(key[0])| ==>
                  SeqXor_premium(BEWordToBitSeq_premium(key[0]),
                         BEWordToBitSeq_premium(const))[j] == BEWordToBitSeq_premium(Asm_BitwiseXor(key[0], const))[j]; }
            BEWordToBitSeq_premium(Asm_BitwiseXor(key[0], const)) + BEWordSeqToBitSeq_premium(pad[1..]);
            BEWordToBitSeq_premium(pad[0]) + BEWordSeqToBitSeq_premium(pad[1..]);
            { lemma_WordSeqToBitSeqChopHead(pad); }
            BEWordSeqToBitSeq_premium(pad);
        }
    }
}

//-///////////////////////////////////////////////////
//- HMAC
//-///////////////////////////////////////////////////

static method xor_pad(key:array<int>, const:int) returns (pad:array<int>)
    requires key != null && key.Length == 16;
    requires forall i {:trigger key[i]} :: 0 <= i < key.Length ==> Word32(key[i]);
    requires Word32(const);
    ensures fresh(pad);
    ensures forall i {:trigger pad[i]} :: 0 <= i < pad.Length ==> Word32(pad[i]);
    ensures pad.Length == 16;
    ensures Mod32_const(512) == 0;
    ensures BEWordSeqToBitSeq_premium(pad[..]) == SeqXor(BEWordSeqToBitSeq_premium(key[..]), ConstPad_premium(512, const));
{
    pad := new int[16];

    var i := 0;
    while (i < 16)
        invariant 0 <= i <= 16;
        invariant forall j {:trigger pad[j]} :: 0 <= j < i ==> Word32(pad[j]);
        invariant forall j {:trigger pad[j]}{:trigger key[j]} :: 0 <= j < i ==> pad[j] == Asm_BitwiseXor(key[j], const);
    {
        pad[i] := Asm_BitwiseXor(key[i], const);
        i := i + 1;
    }
    lemma_SeqXor_WordSeqToBitSeq(16, pad[..], key[..], const);
    calc { Mod32_const(512); { reveal_Mod32_const(); } 0; }
}

static lemma lemma_padded_length_32(x:int, y:int)
    requires x >= 0 && y >= 0;
    requires PaddedLength(32*x) / 32 == y;
    ensures  y * 32 == PaddedLength(32*x);
{
    reveal_NumPaddingZeroes();
    reveal_PaddedLength();

    calc {
        y * 32;
        (PaddedLength(32*x) / 32) * 32;
        ((32*x + 1 + NumPaddingZeroes(32*x) + 64) / 32) * 32;
        ((32*x + 1 + ((959 - (32*x) % 512) % 512) + 64) / 32) * 32;
        32*x + 1 + ((959 - (32*x) % 512) % 512) + 64;
        PaddedLength(32*x);
    }
}

static method {:timeLimitMultiplier 4} consolidate_arrays(a:array<int>, b:array<int>) returns (c:array<int>)
    requires a != null && b != null;
    requires forall i {:trigger a[i]} :: 0 <= i < a.Length ==> Word32(a[i]);
    requires forall i {:trigger b[i]} :: 0 <= i < b.Length ==> Word32(b[i]);
    ensures fresh(c);
    ensures forall i {:trigger c[i]} :: 0 <= i < c.Length ==> Word32(c[i]);
    ensures c.Length * 32 == PaddedLength(32*(a.Length+b.Length));
    ensures c.Length >= a.Length + b.Length;
    ensures c[..a.Length+b.Length] == a[..] + b[..];
    ensures a[..] == old(a[..]);
    ensures b[..] == old(b[..]);
{
    calc { true; { reveal_PaddedLength(); } 0 <= a.Length + b.Length <= PaddedLength(32*(a.Length+b.Length))/ 32; }
    c := new int[PaddedLength(32*(a.Length+b.Length))/ 32];
    assert c.Length >= a.Length + b.Length;

    var i := 0;
    while (i < a.Length)
        invariant 0 <= i <= a.Length;
        invariant forall j :: 0 <= j < a.Length ==> Word32(a[j]);
        invariant forall j :: 0 <= j < i ==> c[j] == a[j] && Word32(c[j]);
        invariant a[..] == old(a[..]);
        invariant b[..] == old(b[..]);
    {
        c[i] := a[i];
        i := i+1;
    }

    var k := 0;
    while (k < b.Length)
        invariant 0 <= k <= b.Length;
        invariant i == k + a.Length;
        invariant a.Length <= i <= a.Length + b.Length;
        invariant forall j :: 0 <= j < a.Length ==> c[j] == a[j] && Word32(c[j]);
        invariant forall j :: 0 <= j < k ==> c[j+a.Length] == b[j];
//-        invariant forall j :: a.Length <= j < a.Length + k ==> c[j] == b[j-a.Length];
        invariant forall j :: a.Length <= j < a.Length + k ==> Word32(c[j]);
        invariant a[..] == old(a[..]);
        invariant b[..] == old(b[..]);
    {
        c[i] := b[k];
        i := i + 1;
        k := k + 1;
    }

    while (i < c.Length)
        invariant a.Length + b.Length <= i <= c.Length;
        invariant forall j :: 0 <= j < a.Length ==> c[j] == a[j] && Word32(c[j]);
        invariant forall j :: a.Length <= j < a.Length + b.Length ==> c[j] == b[j-a.Length] && Word32(c[j]);
        invariant forall j :: a.Length + b.Length <= j < i ==> Word32(c[j]);
        invariant a[..] == old(a[..]);
        invariant b[..] == old(b[..]);
    {
        lemma_2toX();
        c[i] := 0;
        i := i + 1;
    }

    assert forall j :: 0 <= j < a.Length ==> c[..a.Length + b.Length][j] == a[j];
    assert forall j :: a.Length <= j < a.Length + b.Length ==> c[..a.Length + b.Length][j] == b[j - a.Length] && Word32(c[j]);

    lemma_padded_length_32(a.Length+b.Length, c.Length);
}

static method HMAC_outer_input(key: array<int>, inner_hash: array<int>) returns (input: array<int>)
    requires IsWordArray(key);
    requires key.Length == 16;
    requires IsWordArray(inner_hash);
    ensures fresh(input);
    ensures IsWordArray(input);
    ensures input.Length * 32 == PaddedLength(32*(16+inner_hash.Length));
    ensures 16+inner_hash.Length <= input.Length;
    ensures Mod32_const(|key[..]|*32) == 0;
    ensures BEWordSeqToBitSeq_premium(input[..]) == SeqXor(BEWordSeqToBitSeq_premium(key[..]), Opad_premium(|key[..]|*32)) + BEWordSeqToBitSeq_premium(inner_hash[..]) + BEWordSeqToBitSeq_premium(input[16+inner_hash.Length..]);
{
    ghost var old_key := key[..];
    lemma_2toX();
    var opad := xor_pad(key, 0x5c5c5c5c);
    assert old_key == key[..];

    ghost var old_opad := opad[..];

    input := consolidate_arrays(opad, inner_hash);
    assert key[..] == old_key;
    assert opad[..] == old_opad;

    ghost var sum := opad.Length + inner_hash.Length;
    calc {
        BEWordSeqToBitSeq_premium(input[..]);
        { lemma_WordSeqToBitSeqChop(input[..], input[..sum], input[sum..]); }
        BEWordSeqToBitSeq_premium(input[..sum]) + BEWordSeqToBitSeq_premium(input[sum..]);
        BEWordSeqToBitSeq_premium(opad[..] + inner_hash[..]) + BEWordSeqToBitSeq_premium(input[sum..]);
        { lemma_WordSeqToBitSeqChop(opad[..] + inner_hash[..], opad[..], inner_hash[..]); }
        BEWordSeqToBitSeq_premium(opad[..]) + BEWordSeqToBitSeq_premium(inner_hash[..]) + BEWordSeqToBitSeq_premium(input[sum..]);
        { reveal_Mod32_const(); }
        SeqXor(BEWordSeqToBitSeq_premium(key[..]), Opad(|key[..]|*32)) + BEWordSeqToBitSeq_premium(inner_hash[..]) + BEWordSeqToBitSeq_premium(input[sum..]);
    }
}

static lemma lemma_HMAC_inner_input1(key: array<int>, data: array<int>, input:array<int>, ipad:array<int>)
    requires key != null;
    requires data != null;
    requires input != null;
    requires ipad != null;
    requires forall i {:trigger key[i]} :: 0 <= i < key.Length ==> Word32(key[i]);
    requires forall i {:trigger data[i]} :: 0 <= i < data.Length ==> Word32(data[i]);
    requires forall i {:trigger input[i]} :: 0 <= i < input.Length ==> Word32(input[i]);
    requires forall i {:trigger ipad[i]} :: 0 <= i < ipad.Length ==> Word32(ipad[i]);
    requires ipad.Length + data.Length <= input.Length;
    requires input[..(ipad.Length + data.Length)] == ipad[..] + data[..];
    requires Mod32_const(|key[..]|*32) == 0;
    requires |BEWordSeqToBitSeq_premium(key[..])| == |Ipad_premium(|key[..]|*32)|;
    requires BEWordSeqToBitSeq_premium(ipad[..]) == SeqXor_premium(BEWordSeqToBitSeq_premium(key[..]), Ipad_premium(|key[..]|*32));
    ensures BEWordSeqToBitSeq_premium(input[..]) == SeqXor_premium(BEWordSeqToBitSeq_premium(key[..]), Ipad_premium(|key[..]|*32)) + BEWordSeqToBitSeq_premium(data[..]) + BEWordSeqToBitSeq_premium(input[(ipad.Length + data.Length)..]);
{
    ghost var sum := ipad.Length + data.Length;
    calc {
        BEWordSeqToBitSeq_premium(input[..]);
        { lemma_WordSeqToBitSeqChop(input[..], input[..sum], input[sum..]); }
        BEWordSeqToBitSeq_premium(input[..sum]) + BEWordSeqToBitSeq_premium(input[sum..]);
        BEWordSeqToBitSeq_premium(ipad[..] + data[..]) + BEWordSeqToBitSeq_premium(input[sum..]);
        { lemma_WordSeqToBitSeqChop(ipad[..] + data[..], ipad[..], data[..]); }
        BEWordSeqToBitSeq_premium(ipad[..]) + BEWordSeqToBitSeq_premium(data[..]) + BEWordSeqToBitSeq_premium(input[sum..]);
        { reveal_Mod32_const(); }
        SeqXor_premium(BEWordSeqToBitSeq_premium(key[..]), Ipad_premium(|key[..]|*32)) +
            BEWordSeqToBitSeq_premium(data[..]) + BEWordSeqToBitSeq_premium(input[sum..]);
    }
}

static lemma lemma_HMAC_inner_input2(len:int, dataLength32:int, inputLength32:int)
    requires inputLength32 == PaddedLength(512 + dataLength32);
    requires 0 <= len <= dataLength32;
    ensures len + 512 <= PaddedLength(len + 512) <= inputLength32;
{
    reveal_PaddedLength();
    reveal_NumPaddingZeroes();
    lemma_PaddedLengthMonotonic(len+512, 512+dataLength32);
}

static method HMAC_inner_input(key: array<int>, data: array<int>, len: int) returns (input: array<int>)
    requires Word32(len);
    requires key != null && key.Length == 16;
    requires forall i {:trigger key[i]} :: 0 <= i < key.Length ==> Word32(key[i]);
    requires data != null;
    requires 0 <= len <= data.Length * 32;
    requires forall i {:trigger data[i]} :: 0 <= i < data.Length ==> Word32(data[i]);
    ensures fresh(input);
    ensures forall i {:trigger input[i]} :: 0 <= i < input.Length ==> Word32(input[i]);
    ensures len + 512 <= PaddedLength(len + 512) <= input.Length * 32;
    ensures input.Length >= 16 + data.Length;
    ensures Mod32_const(|key[..]|*32) == 0;
    ensures BEWordSeqToBitSeq_premium(input[..]) == SeqXor_premium(BEWordSeqToBitSeq_premium(key[..]), Ipad_premium(|key[..]|*32)) + BEWordSeqToBitSeq_premium(data[..]) + BEWordSeqToBitSeq_premium(input[16+data.Length..]);
{
    ghost var old_key := key[..];
    lemma_2toX();
    var ipad := xor_pad(key, 0x36363636);
    assert old_key == key[..];

    ghost var old_ipad := ipad[..];

    input := consolidate_arrays(ipad, data);
    assert key[..] == old_key;
    assert ipad[..] == old_ipad;

    reveal_Mod32_const();
    lemma_HMAC_inner_input1(key, data, input, ipad);
    lemma_HMAC_inner_input2(len, data.Length * 32, input.Length * 32);
}
