


include "../../Libraries/Util/insecure_prng.i.dfy"
include "../../Libraries/FleetNat/FleetNatAdd.i.dfy"
include "../../Libraries/FleetNat/FleetNatMul.i.dfy"
include "../../Libraries/FatNat/FatNatMod.i.dfy"
include "../../Drivers/IO/pci.i.dfy"

//-
//- A wrapper utility for benchmarking various parts of the system.
//-

method print_array(alabel:int, a:array<int>)
    requires 0 <= alabel < 120;
    requires a != null;
    requires IsDigitSeq(power2(32), a[..]);
{
    var i := 0;
    while (i < a.Length) 
        invariant 0 <= i <= a.Length;
        invariant IsDigitSeq(power2(32), a[..i]); 
    {
        debug_print(alabel, a[i]);
        i := i+1;
    }

}

method repeat_array(v:int, l:nat) returns (a:array<int>)
    requires 0<=v<power2(32);
	ensures a!=null;
    ensures fresh(a);
    ensures a.Length == l;
    ensures forall i :: 0<=i<l ==> a[i]==v;
    ensures IsDigitSeq(power2(32), a[..]);
    ensures 0<l ==> v <=BEWordSeqToInt(a[..]);
{
    a := new int[l];
    var j := 0;
    while (j < l)
        invariant 0<=j<=l;
        invariant forall i :: 0<=i<j ==> a[i]==v;
    {
        a[j] := v;
        j := j + 1;
    }
    if (0<l)
    {
        lemma_2toX();
        ghost var pv := power2(32);
        calc {
            v * 1;
                { lemma_power_0(pv); }
            v * power(pv, 0);
            <=  { lemma_power_increases(pv,0,l-1); lemma_mul_inequality(power(pv,0), power(pv,l-1), v); }
            v * power(pv, l-1);
            v * power(pv, |a[..]|-1);
            a[..][0] * power(pv, |a[..]|-1);
                <= { lemma_BEDigitSeqToInt_bound(power2(32), a[..]); }
            BEDigitSeqToInt(pv, a[..]);
        }
    }
}
    
method DecryptTest()
    returns (Result:int)
    ensures public(true);
{
    lemma_2toX();

    var BeginHigh, BeginLow, EndHigh, EndLow;

    var iters := 0;
    
    var B := repeat_array(0x9724106f, 32);
//-    assert 0<BEWordSeqToInt(B[..]);
    var E := repeat_array(0xfac8a69f, 32);
    var N := repeat_array(0x78065cc5, 32);
//-    assert 1<BEWordSeqToInt(N[..]);
    var nReciprocal := FatNatComputeReciprocal(N);
    if (nReciprocal.FNDivKnownReciprocal?)
    {
        debug_print(0x87, 0x55555555);
//-        assert FNDivReciprocalValid(nReciprocal, N);
    } else {
        debug_print(0x87, 0x01010101);
//-        assert FNDivReciprocalValid(nReciprocal, N);
    }

    BeginHigh, BeginLow := Asm_Rdtsc();

    /*
    var Q,R := FatNatDivUsingReciprocal(B, N, nReciprocal);
    */

    iters := 0;
    while (iters < 500)
        invariant B!=null && IsWordSeq(B[..]) && 0<BEWordSeqToInt(B[..]);
        invariant E!=null && IsWordSeq(E[..]) && 0<BEWordSeqToInt(E[..]);
        invariant N!=null && IsWordSeq(N[..]) && 1<BEWordSeqToInt(N[..]);
        invariant FNDivReciprocalValid(nReciprocal, N);
        decreases 1000000-iters;
    {
        var R := FatNatModExpUsingReciprocal(B, E, N, nReciprocal);

        iters := iters + 1;
    }

    EndHigh, EndLow := Asm_Rdtsc();
    Result := 0;
    
    debug_print(0x89, BeginHigh);
    debug_print(0x89, BeginLow);
    debug_print(0x89, EndHigh);
    debug_print(0x89, EndLow);
}

//-
//- Main benchmark app entry point.
//-
method AddPerfTests()
    returns (Result:int)
    ensures public(true);
{
    lemma_2toX();

    var BeginHigh, BeginLow, EndHigh, EndLow;

    var iters := 0;
    var a := repeat_array(0x22, 32);
    var b := repeat_array(0x77, 32);
    var n := repeat_array(0x18476263, 32);
    var c := new int[32];
    var i := 0;

    BeginHigh, BeginLow := Asm_Rdtsc();

    iters := 0;
    while (iters < 20000)
        invariant a!=null;
        invariant b!=null;
        invariant c!=null;
        invariant n!=null;
        invariant a!=b;
        invariant fresh(a);
        invariant fresh(b);
        invariant fresh(c);
        invariant IsWordSeq(a[..]);
        invariant 0<BEWordSeqToInt(a[..]);
        invariant IsWordSeq(b[..]);
        invariant IsWordSeq(n[..]);
        invariant 1<BEWordSeqToInt(n[..]);
        decreases 1000000-iters;
    {
//- Cut here for 'nocarryinline' case
//-          c[0] := a[0] + b[0];
//-          c[1] := a[1] + b[1];
//-          c[2] := a[2] + b[2];
//-          c[3] := a[3] + b[3];
//-          c[4] := a[4] + b[4];
//-          c[5] := a[5] + b[5];
//-          c[6] := a[6] + b[6];
//-          c[7] := a[7] + b[7];
//-          c[8] := a[8] + b[8];
//-          c[9] := a[9] + b[9];
//-          c[10] := a[10] + b[10];
//-          c[11] := a[11] + b[11];
//-          c[12] := a[12] + b[12];
//-          c[13] := a[13] + b[13];
//-          c[14] := a[14] + b[14];
//-          c[15] := a[15] + b[15];
//-          c[16] := a[16] + b[16];
//-          c[17] := a[17] + b[17];
//-          c[18] := a[18] + b[18];
//-          c[19] := a[19] + b[19];
//-          c[20] := a[20] + b[20];
//-          c[21] := a[21] + b[21];
//-          c[22] := a[22] + b[22];
//-          c[23] := a[23] + b[23];
//-          c[24] := a[24] + b[24];
//-          c[25] := a[25] + b[25];
//-          c[26] := a[26] + b[26];
//-          c[27] := a[27] + b[27];
//-          c[28] := a[28] + b[28];
//-          c[29] := a[29] + b[29];
//-          c[30] := a[30] + b[30];
//-          c[31] := a[31] + b[31];

//- Cut here for 'nocarry' case
//-        i := 0;
//-        while (i<32)
//-            invariant 0<=i<=32;
//-            decreases 32-i;
//-        {
//-            c[i] := a[i] + b[i];
//-            i := i + 1;
//-        }

//- Cut here for 'unrolled' case
//-       i := 0;
//-       while (i<32)
//-           invariant 0<=i<=32;
//-           decreases 32-i;
//-       {
//-           var lastcarry := 0;
//-           ghost var c1,c2,c3,c4,c5,c6,c7;
//-           lastcarry,c1,c2,c3,c4,c5,c6,c7 := Add32_unrolled_8(a, i, b, i, c, i, lastcarry);
//-           i := i + 8;
//-       }

//- Cut here for 'alloc' case
//-       c := new int[32];
//-       i := 0;
//-       while (i<32)
//-           invariant 0<=i<=32;
//-           decreases 32-i;
//-       {
//-           var lastcarry := 0;
//-           ghost var c1,c2,c3,c4,c5,c6,c7;
//-           lastcarry,c1,c2,c3,c4,c5,c6,c7 := Add32_unrolled_8(a, i, b, i, c, i, lastcarry);
//-           i := i + 8;
//-       }


//- Cut here for 'fleetwithcopy' case
//-        CopyArray(c, 0, a, 0, 32);
//-        ghost var dummycarry;
//-        dummycarry := FleetNatAddSimple(c, b);

//- Cut here for 'fleetinplace' case
//-        ghost var dummycarry;
//-        dummycarry := FleetNatAddSimple(b, a);

//- Cut here for 'copyonly' case
//-        CopyArray(c, 0, a, 0, 32);

//- Cut here for 'copyinline' case
//-          c[0] := a[0];
//-          c[1] := a[1];
//-          c[2] := a[2];
//-          c[3] := a[3];
//-          c[4] := a[4];
//-          c[5] := a[5];
//-          c[6] := a[6];
//-          c[7] := a[7];
//-          c[8] := a[8];
//-          c[9] := a[9];
//-          c[10] := a[10];
//-          c[11] := a[11];
//-          c[12] := a[12];
//-          c[13] := a[13];
//-          c[14] := a[14];
//-          c[15] := a[15];
//-          c[16] := a[16];
//-          c[17] := a[17];
//-          c[18] := a[18];
//-          c[19] := a[19];
//-          c[20] := a[20];
//-          c[21] := a[21];
//-          c[22] := a[22];
//-          c[23] := a[23];
//-          c[24] := a[24];
//-          c[25] := a[25];
//-          c[26] := a[26];
//-          c[27] := a[27];
//-          c[28] := a[28];
//-          c[29] := a[29];
//-          c[30] := a[30];
//-          c[31] := a[31];

//- Cut here for 'fastercopyarray' case
//-        FasterCopyArray(c, 0, a, 0, 32);

//- Cut here for 'fleetcopy' case
//-        c := FleetCopy(c, a);

//- Cut here for 'fleetnatadd-ab' case
//-        c := FleetNatAdd(c, a, b);

//- Cut here for 'fleetnatadd-cc' case
//-        a := FleetNatAdd(a, a, b);
//-        b := FleetCopy(b, a, 0);

//- Cut here for 'fatnatmul' case
//-        c := FatNatMul(a, b);

//- Cut here for 'fleetnatmul' case
        c := FleetNatMul(a, b);

//        c := FatNatModExp(a, b, n);
//        assume fresh(c); 

        iters := iters + 1;
    }

    EndHigh, EndLow := Asm_Rdtsc();
    Result := 0;
    
    debug_print(0x89, BeginHigh);
    debug_print(0x89, BeginLow);
    debug_print(0x89, EndHigh);
    debug_print(0x89, EndLow);
    debug_print(0x8a, a.Length);
    debug_print(0x8a, b.Length);
    debug_print(0x8a, c.Length);
}

method Main()
    returns (Result:int)
    ensures public(true);
{
//    Result := AddPerfTests();
    Result := DecryptTest();
}
