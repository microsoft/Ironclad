
include "../../Drivers/CPU/assembly_premium.i.dfy"
include "../Math/BitwiseOperations.i.dfy"

static lemma lemma_SelectBit_is_IntBit_spec(b:nat, x:nat)
    requires b<32;
    requires x<power2(32);
    ensures SelectBit(b,x) == IntBit_spec(31-b, x);
{
    lemma_power2_1_is_2();
    var bitseq := BEIntToDigitSeq_premium(2, 32, x);

    lemma_power2_is_power_2(32);
//-    assert x < power2(32) == power(2, 32);
//-    assert |BEIntToDigitSeq(2, 32, x)| == 32;

    assert |bitseq| == 32;
    var L2 := 2;
    var d := 31-b;
    lemma_power_positive(2,b);
    calc {
        IntBit_spec(d, x);
            { assert 0 <= d < |bitseq|; }
        if 0 <= d < |BEWordToBitSeq(x)| then BEWordToBitSeq(x)[d] == 1 else UndefinedBit(d, x);
//-        BEWordToBitSeq(x)[d] == 1;
//-        BEIntToDigitSeq(2, 32, x)[d] == 1;
        bitseq[d] == 1;
            { lemma_BEDigitSeq_extract(2, bitseq, b); }
        (BEDigitSeqToInt(2, bitseq) / power(2, b)) % L2 == 1;
            { lemma_BEInt_decoding_general(2, 32, x); }
        (x / power(2, b)) % L2 == 1;
            { lemma_mod_is_mod_boogie(x / power(2, b), 2); }
        (x / power(2, b)) % 2 == 1;
            { lemma_power2_is_power_2(b); }
        SelectBit(b, x);
    }
}

static lemma lemma_Asm_BitwiseAnd_is_PureBitwiseAnd(x:nat, y:nat)
    requires Word32(x);
    requires Word32(y);
    ensures Asm_BitwiseAnd(x,y) == PureBitwiseAnd(x,y);
{
    var z := Asm_BitwiseAnd(x,y);
    forall (i | 0 <= i < 32)
        ensures SelectBit(i, z) == (SelectBit(i, x) && SelectBit(i, y));
    {
        lemma_SelectBit_is_IntBit_spec(i, z);
        lemma_SelectBit_is_IntBit_spec(i, x);
        lemma_SelectBit_is_IntBit_spec(i, y);
    }
    forall (i | 32 <= i)
        ensures !SelectBit(i,z);
    {
        lemma_power2_increases(32,i);
        lemma_SelectBit_overflow(i, z);
    }
    forall (i:nat)
        ensures SelectBit(i, z) == (SelectBit(i, x) && SelectBit(i, y));
    {
        if (i>=32)
        {
            lemma_power2_increases(32,i);
            lemma_SelectBit_overflow(i, x);
        }
    }
    lemma_BitwiseAnd_equivalence(x,y,z);
}

static lemma lemma_Asm_BitwiseAnd(x:int, c:nat)
    requires Word32(x);
    requires 0<c<=32;
    ensures Word32(power2(c)-1);
    ensures Asm_BitwiseAnd(x,power2(c)-1)==x%power2(c);
{
    lemma_power2_increases(c,32);
    calc {
        Asm_BitwiseAnd(x,power2(c)-1);
            { lemma_Asm_BitwiseAnd_is_PureBitwiseAnd(x, power2(c)-1); }
        PureBitwiseAnd(x, power2(c)-1);
            { lemma_and_mask(x, c); }
        x%power2(c);
    }
}


static lemma lemma_WordToByte_properties(w:int, bs:seq<int>)
    requires Word32(w);
    requires bs == [ w / 16777216, (w / 65536) % 256, (w / 256) % 256, w % 256 ];
    ensures IsByteSeq(bs);
    ensures BEWordSeqToByteSeq([w])==bs;
{
    lemma_2toX();
    calc {
        w;
            { lemma_fundamental_div_mod(w, 256); lemma_mul_is_commutative_forall(); }
        mul(div(w,256),256) + mod(w, 256);
            { lemma_fundamental_div_mod(div(w,256), 256); lemma_mul_is_commutative_forall(); }
        mul(mul(div(div(w,256),256),256) + mod(div(w,256),256),256) + mod(w, 256);
            { lemma_div_denominator_forall(); }
        mul(mul(div(w,mul(256,256)),256) + mod(div(w,256),256),256) + mod(w, 256);
            { lemma_mul_is_mul_boogie(256, 256); }
        mul(mul(div(w,65536),256) + mod(div(w,256),256),256) + mod(w, 256);
            { lemma_fundamental_div_mod(div(w,65536), 256); lemma_mul_is_commutative_forall(); }
        mul(mul(mul(div(div(w,65536),256),256) + mod(div(w,65536),256),256) + mod(div(w,256),256),256) + mod(w, 256);
            { lemma_div_denominator_forall(); }
        mul(mul(mul(div(w,mul(65536,256)),256) + mod(div(w,65536),256),256) + mod(div(w,256),256),256) + mod(w, 256);
            { lemma_mul_is_mul_boogie(65536, 256); }
        mul(mul(mul(div(w,16777216),256) + mod(div(w,65536),256),256) + mod(div(w,256),256),256) + mod(w, 256);
        mul(mul(mul(div(w,16777216),power2(8)) + mod(div(w,65536),256),power2(8)) + mod(div(w,256),256),power2(8)) + mod(w, 256);
        mul(mul(mul(w/16777216,power2(8)) + mod(w/65536,256),power2(8)) + mod(w/256,256),power2(8)) + mod(w, 256);
        mul(mul(mul(w/16777216,power2(8)) + (w/65536)%256,power2(8)) + (w/256)%256,power2(8)) + w%256;
    }

    reveal_BEDigitSeqToInt_private();
    lemma_mul_basics_forall();
    var ws := [w];
    calc {
        BEByteSeqToInt(bs);
            { lemma_BEByteSeqToInt_unpack_four(bs, []); }
        BEByteSeqToInt([])*power2(32)
            + (((bs[|bs|-4])*power2(8) + bs[|bs|-3])*power2(8) + bs[|bs|-2])*power2(8) + bs[|bs|-1];
        (((bs[0])*power2(8) + bs[1])*power2(8) + bs[2])*power2(8) + bs[3];
        mul(mul(mul(bs[0],power2(8)) + bs[1],power2(8)) + bs[2],power2(8)) + bs[3];
        mul(mul(mul(w/16777216,power2(8)) + (w/65536)%256,power2(8)) + (w/256)%256,power2(8)) + w%256;
        w;
        BEDigitSeqToInt(power2(32), ws[0..0])*power2(32) + ws[0];
        BEWordSeqToInt(ws);
    }

    lemma_BEDigitSeqToInt_bound(power2(8), bs);
    lemma_BEDigitSeqToInt_invertibility(power2(8), BEByteSeqToInt(bs), bs);
}


static lemma lemma_WordToByte_concatenation(ws:seq<int>, prefix_words:seq<int>, suffix_words:seq<int>, bs:seq<int>, prefix_bytes:seq<int>, suffix_bytes:seq<int>)
    requires IsWordSeq(ws);
    requires IsWordSeq(prefix_words);
    requires IsWordSeq(suffix_words);
    requires ws == prefix_words + suffix_words;
    requires IsByteSeq(bs);
    requires IsByteSeq(prefix_bytes);
    requires IsByteSeq(suffix_bytes);
    requires bs == prefix_bytes + suffix_bytes;
    requires |suffix_words| == 1;
    requires |suffix_bytes| == 4;
    requires BEByteSeqToInt(prefix_bytes) == BEWordSeqToInt(prefix_words);
    requires BEByteSeqToInt(suffix_bytes) == BEWordSeqToInt(suffix_words);
    ensures BEByteSeqToInt(bs) == BEWordSeqToInt(ws);
{
    reveal_BEDigitSeqToInt_private();
    lemma_2toX();
    lemma_mul_basics_forall();
    calc {
        BEByteSeqToInt(bs);
            { lemma_BEByteSeqToInt_strip_four(bs, prefix_bytes, suffix_bytes); }
        BEByteSeqToInt(prefix_bytes) * power2(32) + BEByteSeqToInt(suffix_bytes);
        BEWordSeqToInt(prefix_words) * power2(32) + BEWordSeqToInt(suffix_words);
        BEWordSeqToInt(prefix_words) * power2(32) + (BEDigitSeqToInt(power2(32), suffix_words[0..0])*power2(32) + suffix_words[0]);
        BEWordSeqToInt(prefix_words) * power2(32) + (BEDigitSeqToInt(power2(32), [])*power2(32) + suffix_words[0]);
        BEWordSeqToInt(prefix_words) * power2(32) + (mul(0,power2(32)) + suffix_words[0]);
        BEWordSeqToInt(prefix_words) * power2(32) + suffix_words[0];
            { assert suffix_words[0] == ws[|ws|-1]; }
        BEWordSeqToInt(prefix_words) * power2(32) + ws[|ws|-1];
            { assert prefix_words == ws[0..|ws|-1]; }
        BEDigitSeqToInt(power2(32), ws[0..|ws|-1])*power2(32) + ws[|ws|-1];
        BEWordSeqToInt(ws);
    }
}

static lemma lemma_divide_power2_24(w:int)
    requires Word32(w);
    ensures w/power2(24) < 256;
{
    lemma_2toX();
    calc {
        w/power2(24);
        div(w,16777216);
        { lemma_div_is_div_boogie(w, 16777216); }
        w/16777216;
        <
        256;
    }
}

static lemma lemma_Asm_Div_premiumer(x:int, d:int, q:int)
    requires Word32(x);
    requires Word32(d);
    requires 0<d;
    requires q==Asm_Div(x,d);
    ensures q==x/d;
{
    lemma_2toX();
    calc {
        q;
        mod0x100000000(x/d);
        { lemma_mod0x100000000(x/d); }
        (x/d) % 0x100000000;
        (x/d) % power2(32);
        {
            lemma_power2_positive();
            lemma_div_pos_is_pos(x, d);
            lemma_div_nonincreasing(x, d);
            lemma_small_mod(x/d, power2(32));
            assert x/d < power2(32);
        }
        x/d;
    }
}

static method BEWordArrayToByteArray(wa:array<int>, ba:array<int>)
    requires wa!=null;
    requires ba!=null;
    requires wa!=ba;
    requires ba.Length == wa.Length*4;
    requires IsWordSeq(wa[..]);
    modifies ba;
    ensures IsByteSeq(ba[..]);
    ensures BEWordSeqToByteSeq(wa[..])==ba[..];
{
    lemma_2toX32();
    var i:=0;
    var j:=0;
//-    calc {
//-        BEWordSeqToByteSeq_premium(wa[..i]);
//-        BEWordSeqToByteSeq([]);
//-        { reveal_BEDigitSeqToInt_private(); }
//-        ba[..j];
//-    }
    while (i<wa.Length)
        invariant 0<=i<=wa.Length;
        invariant j==i*4;
        invariant IsByteSeq(ba[..j]);
        invariant BEWordSeqToByteSeq_premium(wa[..i])==ba[..j];
    {
        ghost var ws := wa[..i];
        ghost var bs := ba[..j];
        assert IsByteSeq(bs[..j]);
        assert BEWordSeqToByteSeq_premium(ws)==bs;

        ba[j] := Asm_Div(wa[i],16777216);
        ba[j+1] := Asm_BitwiseAnd(Asm_Div(wa[i],65536), 255);
        ba[j+2] := Asm_BitwiseAnd(Asm_Div(wa[i],256), 255);
        ba[j+3] := Asm_BitwiseAnd(wa[i], 255);

        lemma_mod_properties();
        lemma_divide_power2_24(wa[i]);
        lemma_Asm_Div_premiumer(wa[i], 16777216, ba[j]);
        lemma_Asm_Div_premiumer(wa[i], 65536, Asm_Div(wa[i],65536));
        lemma_Asm_Div_premiumer(wa[i], 256, Asm_Div(wa[i],256));
        assert ba[j]<256;
        lemma_Asm_BitwiseAnd(Asm_Div(wa[i],65536), 8);
        lemma_Asm_BitwiseAnd(Asm_Div(wa[i],256), 8);
        lemma_Asm_BitwiseAnd(wa[i], 8);
        assert(ba[j+1]<256);
        assert(ba[j+2]<256);
        assert(ba[j+3]<256);
        assert forall k :: 0<=k<j ==> 0<=bs[k]<256;
        assert forall k :: 0<=k<j ==> ba[k]==bs[k];
        assert forall k :: 0<=k<j ==> 0<=ba[k]<256;

        ghost var bss := ba[j..j+4];
        lemma_div_is_div_boogie(wa[i], 16777216);
        lemma_div_is_div_boogie(wa[i], 65536);
        lemma_mod_is_mod_boogie(wa[i]/65536, 256);
        lemma_div_is_div_boogie(wa[i], 256);
        lemma_mod_is_mod_boogie(wa[i]/256, 256);
        lemma_mod_is_mod_boogie(wa[i], 256);
        lemma_WordToByte_properties(wa[i], ba[j..j+4]);

        ghost var wss := [wa[i]];
        lemma_BEWordSeqToInt_BEIntToByteSeq(bs, ws);
        calc {
            BEByteSeqToInt(bs[..j]);
                { assert bs[..j] == bs; }
            BEByteSeqToInt(bs);
//-            BEByteSeqToInt(ba[..j]);
//-            BEByteSeqToInt(bs);
            BEWordSeqToInt(ws);
            BEWordSeqToInt(wa[..i]);
        }

        lemma_BEWordSeqToInt_BEIntToByteSeq(bss, wss);
        calc {
            BEByteSeqToInt(bss);
            { lemma_BEIntToByteSeq_BEWordSeqToInt(bss, wss); }
            BEWordSeqToInt(wss);
        }
        assert BEByteSeqToInt(bss) == BEWordSeqToInt(wss);  //- OBSERVE
        lemma_WordToByte_concatenation(wa[..i+1], wa[..i], wss, ba[..j+4], bs[..j], bss);
        lemma_BEIntToByteSeq_BEWordSeqToInt(ba[..j+4], wa[..i+1]);

        i:=i+1;
        j:=j+4;
    }

    assert ba[..j] == ba[..];
    assert wa[..i] == wa[..];
    assert IsByteSeq(ba[..j]);
    assert BEWordSeqToByteSeq(wa[..i])==ba[..j];
}
