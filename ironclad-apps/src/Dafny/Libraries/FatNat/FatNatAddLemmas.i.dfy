include "FatNatCommon.i.dfy"
include "../BigNum/BigNatX86Shim.i.dfy"
include "../../Drivers/CPU/assembly.i.dfy"

predicate HappyDigit(s:seq<int>, si:int, i:int)
    requires 0 <= si;
    requires si+8 <= |s|;
    requires 0 <= i < 8;
{
    0 <= s[|s|-1-(si+i)] < 0x100000000
}

lemma {:timeLimitMultiplier 2} lemma_Add32_unrolled_8_glue(
    a:seq<int>, ai:int, b:seq<int>, bi:int, s:seq<int>, si:int, c_in:int,
    c_out:int, ghost c1:int, ghost c2:int, ghost c3:int, ghost c4:int, ghost c5:int, ghost c6:int, ghost c7:int,
    loopcarries:seq<int>, oldcarries:seq<int>, allcarries:seq<int>)
    
    //- Add32_unrolled_8 requires
     requires IsWordSeq(a);
     requires 0 <= ai;
     requires ai+8 <= |a|;
     requires IsWordSeq(b);
     requires 0 <= bi;
     requires bi+8 <= |b|;
     requires 0 <= si;
     requires si+8 <= |s|;
     requires 0<=c_in<=1;

    //- Add32_unrolled_8 ensures
     requires 0<=c_out<=1;
     requires 
         s[FatNatAddIndex(|s|,si,0)] ==  
            mod0x100000000(a[|a|-1-(ai+0)] +b[|b|-1-(bi+0)] + c_in);
     requires 
         s[FatNatAddIndex(|s|,si,1)] ==  
            mod0x100000000(a[|a|-1-(ai+1)] +b[|b|-1-(bi+1)] + c1);
     requires 
         s[FatNatAddIndex(|s|,si,2)] ==  
            mod0x100000000(a[|a|-1-(ai+2)] +b[|b|-1-(bi+2)] + c2);
     requires 
         s[FatNatAddIndex(|s|,si,3)] ==  
            mod0x100000000(a[|a|-1-(ai+3)] +b[|b|-1-(bi+3)] + c3);
     requires 
         s[FatNatAddIndex(|s|,si,4)] ==  
            mod0x100000000(a[|a|-1-(ai+4)] +b[|b|-1-(bi+4)] + c4);
     requires 
         s[FatNatAddIndex(|s|,si,5)] ==  
            mod0x100000000(a[|a|-1-(ai+5)] +b[|b|-1-(bi+5)] + c5);
     requires 
         s[FatNatAddIndex(|s|,si,6)] ==  
            mod0x100000000(a[|a|-1-(ai+6)] +b[|b|-1-(bi+6)] + c6);
     requires 
         s[FatNatAddIndex(|s|,si,7)] ==  
            mod0x100000000(a[|a|-1-(ai+7)] +b[|b|-1-(bi+7)] + c7);

     requires c1 == if a[|a|-1-(ai+0)] +b[|b|-1-(bi+0)] + c_in >= 0x100000000 then 1 else 0;
     requires c2 == if a[|a|-1-(ai+1)] +b[|b|-1-(bi+1)] + c1 >= 0x100000000 then 1 else 0;
     requires c3 == if a[|a|-1-(ai+2)] +b[|b|-1-(bi+2)] + c2 >= 0x100000000 then 1 else 0;
     requires c4 == if a[|a|-1-(ai+3)] +b[|b|-1-(bi+3)] + c3 >= 0x100000000 then 1 else 0;
     requires c5 == if a[|a|-1-(ai+4)] +b[|b|-1-(bi+4)] + c4 >= 0x100000000 then 1 else 0;
     requires c6 == if a[|a|-1-(ai+5)] +b[|b|-1-(bi+5)] + c5 >= 0x100000000 then 1 else 0;
     requires c7 == if a[|a|-1-(ai+6)] +b[|b|-1-(bi+6)] + c6 >= 0x100000000 then 1 else 0;
     requires c_out == if a[|a|-1-(ai+7)] +b[|b|-1-(bi+7)] + c7 >= 0x100000000 then 1 else 0;

     requires IsDigitSeq(power2(32), a);
     requires IsDigitSeq(power2(32), b);
     requires loopcarries == [ c_out, c7, c6, c5, c4, c3, c2, c1 ];
     requires |oldcarries| == si+1;
     requires oldcarries[0] == c_in;
     requires allcarries == loopcarries + oldcarries;
     requires IsDigitSeq(power2(32), s[|s|-si..]);

    ensures IsDigitSeq(power2(32), s[|s|-(si+8)..]);
    ensures IsDigitSeq(2, loopcarries);
    ensures forall i :: 0<=i<8 ==>
        DigitAt(s, si+i) + DigitAt(loopcarries, i) * 0x100000000
        == DigitAt(a, ai+i) + DigitAt(b, bi+i) + DigitAt(allcarries, si+i);
{
    lemma_2toX();

    forall (i | 0<=i<8)
        ensures DigitAt(s,si+i) ==  
            mod0x100000000(DigitAt(a, ai+i) + DigitAt(b, bi+i) + DigitAt(allcarries,si+i));
    {
    }

    forall (i | 0<=i<8)
        ensures HappyDigit(s, si, i);
    {
        if (i==0) {
            lemma_mod0x100000000(a[|a|-1-(ai+0)] +b[|b|-1-(bi+0)] + c_in);
        } else if (i==1) {
            lemma_mod0x100000000(a[|a|-1-(ai+1)] +b[|b|-1-(bi+1)] + c1);
        } else if (i==2) {
            lemma_mod0x100000000(a[|a|-1-(ai+2)] +b[|b|-1-(bi+2)] + c2);
        } else if (i==3) {
            lemma_mod0x100000000(a[|a|-1-(ai+3)] +b[|b|-1-(bi+3)] + c3);
        } else if (i==4) {
            lemma_mod0x100000000(a[|a|-1-(ai+4)] +b[|b|-1-(bi+4)] + c4);
        } else if (i==5) {
            lemma_mod0x100000000(a[|a|-1-(ai+5)] +b[|b|-1-(bi+5)] + c5);
        } else if (i==6) {
            lemma_mod0x100000000(a[|a|-1-(ai+6)] +b[|b|-1-(bi+6)] + c6);
        } else if (i==7) {
            lemma_mod0x100000000(a[|a|-1-(ai+7)] +b[|b|-1-(bi+7)] + c7);
        }
    }

    var stail := s[|s|-(si+8)..];
    forall (ri | 0<=ri<|stail|)
        ensures 0<=stail[ri]<power2(32);
    {
        var i := 7-ri;
        assert |stail| == si+8;
        if (ri < 8)
        {
            assert HappyDigit(s, si, i);
            lemma_mod_properties();
            assert stail[ri] == s[|s|-1-(si+i)];
        }
        else
        {
            assert stail[ri] == s[|s|-si..][ri-8];  //- OBSERVE SEQ
        }
    }

    forall (i | 0<=i<8)
        ensures DigitAt(allcarries,si+i+1) ==
            if DigitAt(a,ai+i) +DigitAt(b,bi+i) + DigitAt(allcarries,si+i) >= 0x100000000 then 1 else 0;
    {
        var co := DigitAt(allcarries,si+i+1);
        var ei := if DigitAt(a,ai+i) +DigitAt(b,bi+i) + DigitAt(allcarries,si+i) >= 0x100000000 then 1 else 0;
        if (i==0)
        {
            assert c1 == DigitAt(allcarries, si+i+1);
            assert c_in == DigitAt(allcarries, si+i);
            assert co == ei;
        } else if (i==1) {
            assert c2 == DigitAt(allcarries, si+i+1);
            assert c1 == DigitAt(allcarries, si+i);
            assert co == ei;
        } else if (i==2) {
            assert c3 == DigitAt(allcarries, si+i+1);
            assert c2 == DigitAt(allcarries, si+i);
            assert co == ei;
        } else if (i==3) {
            assert c4 == DigitAt(allcarries, si+i+1);
            assert c3 == DigitAt(allcarries, si+i);
            assert co == ei;
        } else if (i==4) {
            assert c5 == DigitAt(allcarries, si+i+1);
            assert c4 == DigitAt(allcarries, si+i);
            assert co == ei;
        } else if (i==5) {
            assert c6 == DigitAt(allcarries, si+i+1);
            assert c5 == DigitAt(allcarries, si+i);
            assert co == ei;
        } else if (i==6) {
            assert c7 == DigitAt(allcarries, si+i+1);
            assert c6 == DigitAt(allcarries, si+i);
            assert co == ei;
        } else if (i==7) {
            assert c_out == DigitAt(allcarries, si+i+1);
            assert c7 == DigitAt(allcarries, si+i);
            assert co == ei;
        } else {
            assert false;
        }
    }

    forall (i | 0<=i<8)
        ensures
        DigitAt(s, si+i) + DigitAt(loopcarries, i) * 0x100000000
        == DigitAt(a, ai+i) + DigitAt(b, bi+i) + DigitAt(allcarries, si+i);
    {
        var va := DigitAt(a, ai+i);
        var vb := DigitAt(b, bi+i);
        var vs := DigitAt(s, si+i);
        var ci := DigitAt(allcarries, si+i);
        var cox := DigitAt(allcarries, si+i+1);
        lemma_mod0x100000000(va + vb + ci);
        var fs := (va+vb+ci);
        assert 0 <= fs < 0x200000000;
        assert vs == fs % 0x100000000;
        assert cox == if fs >= 0x100000000 then 1 else 0;
        assert cox == fs/0x100000000;
        lemma_fundamental_div_mod_converse(fs, 0x100000000, cox, vs);
        assert vs + cox*0x100000000 == fs;

    }
}


lemma lemma_FatNatAddUnrolledLoop_DigitSeq_preservation(oldc:seq<int>, sc:seq<int>, j:int)
    requires |oldc|==|sc|;
    requires 0<=j<|oldc|;
    requires IsDigitSeq(power2(32), oldc[|oldc|-j..]);
    requires forall i :: 0<=i<|sc| && !(j<=i<j+8) ==> sc[|sc|-1-i]==oldc[|sc|-1-i];
    ensures IsDigitSeq(power2(32), sc[|sc|-j..]);
{
    var pv:=power2(32);
    forall (i | 0<=i<j)
        ensures 0 <= sc[|sc|-j..][i] < pv;
    {
        ghost var wi := |sc|-j+i;
        ghost var ri := |sc|-1-wi;

        //-ensures forall i :: 0<=i<s.Length && !(si<=i<si+8) ==> s[s.Length-1-i]==old(s[s.Length-1-i]);
        assert 0<=ri<|sc| && !(j<=ri<j+8);
        assert sc[|sc|-1-ri] == oldc[|oldc|-1-ri];

        calc {
            sc[|sc|-j..][i];
            sc[wi];
            sc[|sc|-1-ri];
            oldc[|sc|-1-ri];
            oldc[wi];
            oldc[|oldc|-j..][wi-|oldc|+j];
        }
        assert 0 <= oldc[|oldc|-j..][wi-|oldc|+j] < pv;
    }
}
