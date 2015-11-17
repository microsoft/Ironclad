include "../Util/seqs_and_ints.i.dfy"
include "../Util/seqs_common.i.dfy"
include "../FatNat/FatNatCommon.i.dfy"
include "../FatNat/CanonicalArrays.i.dfy"

//- dafnycc was having a hard time stringing these together.
lemma lemma_FasterCopyArray_helper(dst:array<int>, doff:int, rdi:int, src:array<int>, soff:int, rsi:int)
    requires dst!=null;
    requires src!=null;
    requires 0<=doff<rdi<=dst.Length;
    requires 0<=soff<rsi<=src.Length;
    requires rdi-doff == rsi-soff;
    requires dst[doff..rdi-1] == src[soff..rsi-1];
    requires dst[rdi-1] == src[rsi-1];
    ensures dst[doff..rdi] == src[soff..rsi];
{
    var dsub := dst[doff..rdi];
    var ssub := src[soff..rsi];
    var len := |dsub|;
    assert len==|ssub|==rdi-doff==rsi-soff;
    forall (i | 0<=i<|dsub|)
        ensures dsub[i]==ssub[i];
    {
        if (i==len-1)
        {
            calc
            {
                dsub[i];
                dst[doff..rdi][i];
                dst[doff+i];
                dst[rdi-1];
                src[rsi-1];
                src[soff+i];
                src[soff..rsi][i];
                ssub[i];
            }
        }
        else
        {
            calc
            {
                    dsub[i];
                    dst[doff..rdi][i];
                    dst[doff+i];
                    dst[doff..rdi-1][i];
                    src[soff..rsi-1][i];
                    src[soff+i];
                    src[soff..rsi][i];
                    ssub[i];
            }
        }
    }
    assert dsub==ssub;
}

method {:timeLimitMultiplier 2} FasterCopyArray(dst:array<int>, doff:nat, src:array<int>, soff:nat, count:nat)
    requires src!=null;
    requires soff+count <= src.Length;
    requires dst!=null;
    requires doff+count <= dst.Length;
    requires src!=dst;
    modifies dst;
    ensures dst[doff..doff+count] == src[soff..soff+count];
    ensures dst[..doff] == old(dst[..doff]);
    ensures dst[doff+count..] == old(dst[doff+count..]);
{
    var rdi := doff;
    var rsi := soff;
    var rcount := count;
    while (rcount>8)
        invariant 0<=rcount<=count;
        invariant rdi + rcount == doff + count;
        invariant rsi + rcount == soff + count;
        invariant dst[doff..rdi] == src[soff..rsi];
        invariant dst[..doff] == old(dst[..doff]);
        invariant dst[doff+count..] == old(dst[doff+count..]);
    {
        assert dst[doff..rdi] == src[soff..rsi];
        dst[rdi] := src[rsi]; rdi:=rdi+1; rsi:=rsi+1;
        lemma_FasterCopyArray_helper(dst, doff, rdi, src, soff, rsi);

        assert dst[doff..rdi] == src[soff..rsi];
        dst[rdi] := src[rsi]; rdi:=rdi+1; rsi:=rsi+1;
        lemma_FasterCopyArray_helper(dst, doff, rdi, src, soff, rsi);

        assert dst[doff..rdi] == src[soff..rsi];
        dst[rdi] := src[rsi]; rdi:=rdi+1; rsi:=rsi+1;
        lemma_FasterCopyArray_helper(dst, doff, rdi, src, soff, rsi);

        assert dst[doff..rdi] == src[soff..rsi];
        dst[rdi] := src[rsi]; rdi:=rdi+1; rsi:=rsi+1;
        lemma_FasterCopyArray_helper(dst, doff, rdi, src, soff, rsi);

        assert dst[doff..rdi] == src[soff..rsi];
        dst[rdi] := src[rsi]; rdi:=rdi+1; rsi:=rsi+1;
        lemma_FasterCopyArray_helper(dst, doff, rdi, src, soff, rsi);

        assert dst[doff..rdi] == src[soff..rsi];
        dst[rdi] := src[rsi]; rdi:=rdi+1; rsi:=rsi+1;
        lemma_FasterCopyArray_helper(dst, doff, rdi, src, soff, rsi);

        assert dst[doff..rdi] == src[soff..rsi];
        dst[rdi] := src[rsi]; rdi:=rdi+1; rsi:=rsi+1;
        lemma_FasterCopyArray_helper(dst, doff, rdi, src, soff, rsi);

        assert dst[doff..rdi] == src[soff..rsi];
        dst[rdi] := src[rsi]; rdi:=rdi+1; rsi:=rsi+1;
        lemma_FasterCopyArray_helper(dst, doff, rdi, src, soff, rsi);

        assert dst[doff..rdi] == src[soff..rsi];
        rcount := rcount - 8;
    }

    while (rcount>0)
        invariant 0<=rcount<=count;
        invariant rdi + rcount == doff + count;
        invariant rsi + rcount == soff + count;
        invariant dst[doff..rdi] == src[soff..rsi];
        invariant dst[..doff] == old(dst[..doff]);
        invariant dst[doff+count..] == old(dst[doff+count..]);
    {
        dst[rdi] := src[rsi]; rdi:=rdi+1; rsi:=rsi+1;
        rcount := rcount - 1;
        lemma_FasterCopyArray_helper(dst, doff, rdi, src, soff, rsi);
        assert dst[doff..rdi] == src[soff..rsi];
    }
}

method CountNonzeroDigits(c:array<int>) returns (digits:int)
    requires c!=null;
    ensures 0<=digits<=c.Length;
    ensures forall i :: 0<=i<c.Length-digits ==> c[i]==0;
    requires IsWordSeq(c[..]);
    ensures BEWordSeqToInt(c[..]) == BEWordSeqToInt(SelectDigitRange(c[..], digits, 0));
    ensures BEWordSeqToInt(c[..]) < power(power2(32), digits);
    ensures (BEWordSeqToInt(c[..])==0 && digits==0)
        || (0<digits && power(power2(32), digits-1) <= BEWordSeqToInt(c[..]));
{
    var zeros := 0;
    var clen := c.Length;
    while (zeros < clen && c[zeros]==0)
        invariant 0<=zeros<=clen;
        invariant forall i :: 0<=i<zeros ==> c[i]==0;
    {
        zeros := zeros + 1;
    }
    digits := c.Length - zeros;

    lemma_2toX();
    lemma_LeadingZeros(power2(32), SelectDigitRange(c[..], digits, 0), c[..]);
    lemma_BEDigitSeqToInt_bound(power2(32), SelectDigitRange(c[..], digits, 0));
    if (digits==0)
    {
        reveal_BEDigitSeqToInt_private();
        assert BEWordSeqToInt(c[..])==0;
    } else {
        lemma_power_positive(power2(32), digits-1);
        lemma_mul_inequality(1, SelectDigitRange(c[..], digits, 0)[0], power(power2(32), digits-1));
    }
}

method FleetCopy_copy_step(c:array<int>, a:array<int>, adigits:int)
    requires a!=null;
    requires IsDigitSeq(power2(32), a[..]);
    requires a!=c;
    requires c!=null;
    requires adigits <= c.Length;
    requires 0<=adigits<=a.Length;
    modifies c;
    ensures adigits<=c.Length;
    ensures c[c.Length-adigits..]==a[a.Length-adigits..];
    ensures IsDigitSeq(power2(32), c[c.Length-adigits..]);
{
    var alen := a.Length;
    var clen := c.Length;
    var cz:=clen-adigits;
    var ai:=alen-adigits;
    var ci:=cz;
    ghost var az := alen-adigits;
    while (ai<alen)
        invariant alen-adigits<=ai<=alen;
        invariant clen-adigits<=ci<=clen;
        invariant alen-ai == clen-ci;
        invariant c[cz..ci] == a[az..ai];
    {
        c[ci] := a[ai];
        ai:=ai+1;
        ci:=ci+1;
        assert c[cz..ci-1] == a[az..ai-1];
        lemma_FasterCopyArray_helper(c, cz, ci, a, az, ai);
    }
    assert c[cz..clen] == c[cz..];
    assert a[az..alen] == a[az..];
}

method FleetCopy_zero_step(c:array<int>, adigits:int)
    requires c!=null;
    requires 0 <= adigits <= c.Length;
    modifies c;
    ensures forall i :: 0<=i<c.Length-adigits ==> c[i]==0;
    ensures c[c.Length-adigits..] == old(c[c.Length-adigits..]);
{
    var cz:=c.Length-adigits;

    var ci:=0;
    while (ci<cz)
        invariant 0<=ci<=cz;
        invariant c[c.Length-adigits..] == old(c[c.Length-adigits..]);
        invariant forall j :: 0<=j<ci ==> c[j]==0;
    {
        c[ci] := 0;
        ci:=ci+1;
    }
}

lemma lemma_FleetCopy_IsDigitSeq(asq:seq<int>, is:seq<int>, cs:seq<int>, adigits:int)
    requires IsDigitSeq(power2(32), asq);
    requires 0<=adigits<=|asq|;
    requires adigits<=|is|;
    requires forall i :: 0<=i<|asq|-adigits ==> asq[i]==0;
    requires is[|is|-adigits..]==asq[|asq|-adigits..];
    requires IsDigitSeq(power2(32), is[|is|-adigits..]);
    requires |is|<=|cs|;
    requires forall i :: 0<=i<|cs|-adigits ==> cs[i]==0;
    requires cs[|cs|-adigits..] == is[|is|-adigits..];
    ensures IsDigitSeq(power2(32), cs);
    ensures BEDigitSeqToInt(power2(32), asq) == BEDigitSeqToInt(power2(32), cs);
{
    ghost var pv := power2(32);
    lemma_2toX();
    ghost var az := |asq| - adigits;
    ghost var cz := |cs| - adigits;
    forall (i | 0<=i<|cs|)
        ensures 0<=cs[i]<pv;
    {
        if (i>=cz)
        {
            calc {
                cs[i];
                cs[cz..][i-cz];
                asq[az..][i-cz];
                asq[i-cz+az];
                asq[i-|cs|+adigits+|asq|-adigits];
                asq[i-|cs|+|asq|];
            }
        }
    }
    ghost var azeros := |asq|-adigits;
    ghost var shorta := asq[azeros..];
    lemma_LeadingZeros(power2(32), shorta, cs[..]);
    lemma_LeadingZeros(power2(32), shorta, asq[..]);
}

//- mimics polar's mpi_copy





method FleetCopy(c:array<int>, a:array<int>, minlen:nat) returns (c':array<int>)
    requires a!=null;
    requires IsDigitSeq(power2(32), a[..]);
    requires a!=c;
    requires c != null; 
    modifies c;
    ensures c'!=null;
    ensures c'==c || fresh(c');
    ensures minlen <= c'.Length;
    ensures IsDigitSeq(power2(32), c'[..]);
    ensures BEDigitSeqToInt(power2(32), c'[..]) == BEDigitSeqToInt(power2(32), a[..]);
{
    var alen := a.Length;
    if (/*c!=null &&*/ alen==c.Length && minlen<=c.Length) //- Fastpath
    {
        FasterCopyArray(c,0,a,0,alen);
        c':=c;
        calc {  //- OBSERVE SEQ
            c'[..];
            c[..];
            c[0..alen];
            a[0..alen];
            a[..];
        }
        return;
    }

    ghost var pv := power2(32);
    lemma_2toX();
    var adigits:int := CountNonzeroDigits(a);

    var mindigits := adigits;
    if (mindigits < minlen)
    {
        mindigits := minlen;
    }
    if (/*c==null ||*/ c.Length < mindigits)
    {
        c' := new int[mindigits];
    }
    else
    {
        c' := c;
    }
    ghost var c'len := c'.Length;
    assert adigits<=c'len;

    ghost var asq := a[..];
    FleetCopy_copy_step(c', a, adigits);
    ghost var is := c'[..];
    FleetCopy_zero_step(c', adigits);

    lemma_FleetCopy_IsDigitSeq(asq, is, c'[..], adigits);
}

method FleetGrow(c:array<int>, minlen:nat) returns (c':array<int>)
    requires c!=null;
    requires IsDigitSeq(power2(32), c[..]);
    requires c.Length < minlen;    //- else why call me?
    ensures c'!=null;
    ensures c'==c || fresh(c');
    ensures minlen == c'.Length;
    ensures IsDigitSeq(power2(32), c'[..]);
    ensures BEDigitSeqToInt(power2(32), c'[..]) == BEDigitSeqToInt(power2(32), c[..]);
    ensures c'[c'.Length-c.Length..] == c[..];
{
    c' := new int[minlen];
    ghost var asq := c[..];
    FleetCopy_copy_step(c', c, c.Length);
    ghost var is := c'[..];
    FleetCopy_zero_step(c', c.Length);

    lemma_FleetCopy_IsDigitSeq(asq, is, c'[..], c.Length);
}

method FleetAlloc(len:nat) returns (c:array<int>)
    ensures c!=null;
    ensures fresh(c);
    ensures c.Length == len;
    ensures forall i :: 0<=i<len ==> c[i]==0;
    ensures BEDigitSeqToInt(power2(32), c[..]) == 0;
{
    c := new int[len];
    FleetCopy_zero_step(c, 0);
    lemma_2toX();
    lemma_LeadingZeros(power2(32), [], c[..]);
    reveal_BEDigitSeqToInt_private();
}

//- This generalized version tolerates h<|a| and 0<l.

lemma lemma_BEInterpretation_Select_general(pv:int, a:seq<int>, h:int, m:int, l:int)
    requires 1<pv;
    requires 0<=l<=m<=h<=|a|;
    requires IsDigitSeq(pv, SelectDigitRange(a, h, l));
    ensures IsDigitSeq(pv, SelectDigitRange(a, h, m));
    ensures IsDigitSeq(pv, SelectDigitRange(a, m, l));
    ensures BEDigitSeqToInt(pv, SelectDigitRange(a, h, m))*power(pv,m-l)
            + BEDigitSeqToInt(pv, SelectDigitRange(a, m, l))
        == BEDigitSeqToInt(pv, SelectDigitRange(a, h, l));
{
    lemma_SelectDigitSubrange(a, h, m, l);
    lemma_BEInterpretation(pv, SelectDigitRange(a, h, l), m-l);
}

lemma lemma_Select_subrange(a:seq<int>, b:seq<int>, h:int, hi:int, li:int, l:int)
    requires 0<=l<=li<=hi<=h<=|a|==|b|;
    requires SelectDigitRange(a, h, l) == SelectDigitRange(b, h, l);
    ensures SelectDigitRange(a, hi, li) == SelectDigitRange(b, hi, li);
{
    var ai := SelectDigitRange(a, hi, li);
    var bi := SelectDigitRange(b, hi, li);
    assert |ai| == |bi|;
    forall (i | 0<=i<|ai|)
        ensures ai[i] == bi[i];
    {
        var xi := h-hi+i;
        calc {
            ai[i];
            SelectDigitRange(a, hi, li)[i];
            a[|a|-hi..|a|-li][i];
            a[|a|-hi+i];
            a[|a|-h+xi];
            a[|a|-h..|a|-l][xi];
            SelectDigitRange(a, h, l)[xi];
            SelectDigitRange(b, h, l)[xi];
            b[|b|-h..|b|-l][xi];
            b[|b|-h+xi];
            b[|b|-hi+i];
            b[|b|-hi..|b|-li][i];
            SelectDigitRange(b, hi, li)[i];
            bi[i];
        }
    }
    assert ai==bi;
}

lemma lemma_asm_Add_properties(x:int, y:int, z:int, c:int)
    requires word32(x);
    requires word32(y);
    requires z == mod0x100000000(x + y);
    requires c==0 || c==1;
    requires (c==1) <==> (z < y);
    ensures z == (x+y) % 0x100000000;
    ensures x+y == z + 0x100000000*c;
{
    var pv := 0x100000000;
    lemma_mod0x100000000(x+y);
    lemma_word32(x);
    lemma_word32(y);
    lemma_mod_properties();
    lemma_fundamental_div_mod(x+y, pv);
}

lemma lemma_BEWordSeqToInt_SelectDigitRange_empty(s:seq<int>)
    requires IsDigitSeq(power2(32), s);
    ensures BEWordSeqToInt(SelectDigitRange(s, 0, 0)) == 0;
{
    assert SelectDigitRange(s, 0, 0) == [];
    reveal_BEDigitSeqToInt_private();
}

lemma lemma_PluckDigit_general(s:seq<int>, h:int, i:int, l:int)
    requires IsDigitSeq(power2(32), s);
    requires 0<=l<=i<h<=|s|;
    ensures BEWordSeqToInt(SelectDigitRange(s, h, l))
        == BEWordSeqToInt(SelectDigitRange(s, h, i+1)) * power(power2(32), i+1-l)
         + DigitAt(s, i) * power(power2(32), i-l)
         + BEWordSeqToInt(SelectDigitRange(s, i, l));
{
    var pv := power2(32); lemma_2toX();
    calc {
        BEWordSeqToInt(SelectDigitRange(s, h, l));
            { lemma_BEInterpretation_Select_general(pv, s, h, i+1, l); }
        BEDigitSeqToInt(pv, SelectDigitRange(s, h, i+1))*power(pv,i+1-l)
            + BEDigitSeqToInt(pv, SelectDigitRange(s, i+1, l));
            { lemma_BEInterpretation_Select_general(pv, s, i+1, i, l); }
        BEDigitSeqToInt(pv, SelectDigitRange(s, h, i+1))*power(pv,i+1-l)
            + BEDigitSeqToInt(pv, SelectDigitRange(s, i+1, i))*power(pv,i-l)
            + BEDigitSeqToInt(pv, SelectDigitRange(s, i, l));
            { lemma_SelectSingletonRange(s, i+1, i); }
        BEDigitSeqToInt(pv, SelectDigitRange(s, h, i+1))*power(pv,i+1-l)
            + BEDigitSeqToInt(pv, [DigitAt(s,i)])*power(pv,i-l)
            + BEDigitSeqToInt(pv, SelectDigitRange(s, i, l));
            { lemma_BEDigitSeqToInt_singleton(pv, DigitAt(s,i)); }
        BEDigitSeqToInt(pv, SelectDigitRange(s, h, i+1))*power(pv,i+1-l)
            + DigitAt(s,i)*power(pv,i-l)
            + BEDigitSeqToInt(pv, SelectDigitRange(s, i, l));
    }
}

lemma lemma_PluckDigit(s:seq<int>, i:int)
    requires IsDigitSeq(power2(32), s);
    requires 0 <= i < |s|;
    ensures BEWordSeqToInt(s)
        == BEWordSeqToInt(SelectDigitRange(s, |s|, i+1)) * power(power2(32), i+1)
         + DigitAt(s, i) * power(power2(32), i)
         + BEWordSeqToInt(SelectDigitRange(s, i, 0));
{
    assert SelectDigitRange(s, |s|, 0) == s;    //- OBSERVE SEQ
    lemma_PluckDigit_general(s, |s|, i, 0);
}


