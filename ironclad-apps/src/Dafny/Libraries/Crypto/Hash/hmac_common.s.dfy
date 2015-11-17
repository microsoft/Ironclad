include "../../Util/be_sequences.s.dfy"

//-////////////////////////////////////////////////////////////////////////////
//- HMAC specification based on:
//- http://csrc.nist.gov/publications/fips/fips198-1/FIPS-198-1_final.pdf
//-////////////////////////////////////////////////////////////////////////////

static function Xor(a:int, b:int) : int
{ if a!=b then 1 else 0 }

static function{:opaque} SeqXor(a: seq<int>, b: seq<int>) : seq<int>
    requires IsBitSeq(a);
    requires IsBitSeq(b);
    requires |a|==|b|;
{
    if |a| == 0 then
        []
    else
        [ Xor(a[0], b[0]) ] + SeqXor(a[1..], b[1..])
}

static function {:autoReq} {:opaque} ConstPad(len:int, const:int) : seq<int>
//-    requires len % 32 == 0;



{
    if len <= 0 then
        []
    else
        BEWordToBitSeq(const) + ConstPad(len - 32, const)
}

static function {:autoReq} Opad(len:int) : seq<int>



{
    ConstPad(len, 0x5c5c5c5c)
}

static function {:autoReq} Ipad(len:int) : seq<int>



{
    ConstPad(len, 0x36363636)
}
