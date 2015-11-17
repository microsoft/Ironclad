include "../../Drivers/CPU/assembly_premium.i.dfy"
include "../../Libraries/Util/integer_sequences.i.dfy"
include "../../Libraries/Util/word_bits.i.dfy"
include "../../Libraries/Crypto/Hash/sha1.i.dfy"
include "../../Libraries/Crypto/Hash/sha256.i.dfy"
include "../../Libraries/Crypto/RSA/RSA.i.dfy"
include "../../Libraries/Crypto/RSA/RSAOps.i.dfy"
include "../../Libraries/Crypto/RSA/RSA_Decrypt.i.dfy"
include "BenchmarkList.i.dfy"
include "../../Libraries/BigNum/BigNatTestLib.i.dfy"
include "../../Libraries/Crypto/RSA/RSAPublicWrapper.i.dfy"

//-
//- Core utilities for benchmarking various parts of the system.
//-

datatype BenchmarkState = NopState() 
                        | RsaState(keypair:RSAKeyPairImpl, text:seq<int>) 
                        | RsaKeyGenState(num_key_bits:int) 
                        | FatNatAddState(a:array<int>, b:array<int>)
                        | ShaState(arr_is_words:bool, arr:array<int>, use_original:bool)

predicate {:opaque} {:heap} WellformedBenchmarkState(state:BenchmarkState)
    reads if state.FatNatAddState? then state.a else null;
    reads if state.FatNatAddState? then state.b else null;
    reads if state.ShaState? then state.arr else null;
{
    if state.RsaState? then WellformedRSAKeyPairImpl(state.keypair)
                         && IsByteSeq(state.text)
                         && 0 < |state.text| <= state.keypair.pub.size - 11
    else if state.RsaKeyGenState? then 20 < state.num_key_bits < power2(28)
    else if state.FatNatAddState? then state.a != null 
                                    && state.b != null 
                                    && IsDigitSeq(power2(32), state.a[..]) 
                                    && IsDigitSeq(power2(32), state.b[..])
    else if state.ShaState? then state.arr != null 
                              && if state.arr_is_words then
                                  (  Word32(state.arr.Length*32) 
                                  && state.arr.Length*32 < power2(64) 
                                  && IsWordSeq(state.arr[..]))
                                 else 
                                  (  Word32(state.arr.Length*8) 
                                  && state.arr.Length*8 < power2(64) 
                                  && IsByteSeq(state.arr[..]))
    else true
}

predicate {:opaque} CorrectBenchmarkState(state:BenchmarkState, Benchmark:int)
{
    if Benchmark == BenchmarkFatAdd() || Benchmark == BenchmarkFatAddSlowly() then state.FatNatAddState?
    else if Benchmark == BenchmarkSha256() then state.ShaState?
    else if Benchmark == BenchmarkRsaEncrypt() || Benchmark == BenchmarkRsaDecrypt() then state.RsaState?
    else if Benchmark == BenchmarkRsaKeyGen() then state.RsaKeyGenState?
    else true
}

method ZeroArray(arr:array<int>)
    requires arr != null;
    modifies arr;
    ensures IsByteSeq(arr[..]);
{
    var i := 0;
    while (i < arr.Length) 
        invariant 0 <= i <= arr.Length;
        invariant IsByteSeq(arr[..i]);
    {
        arr[i] := 0;
        assert arr[..i+1] == arr[..i] + [arr[i]];   //- dafnycc
        i := i + 1;
    }
    assert arr[..] == arr[..arr.Length];
}

method make_array(val:int, len:int) returns (a:array<int>)
    requires 0 <= val < power2(32);
    requires len > 0;
    ensures a != null; 
    ensures fresh(a);
    ensures a.Length == len;
    ensures forall i:int :: 0 <= i < len ==> a[i] == val;
{
    a := new int[len];

    var i := 0;
    while (i < a.Length) 
        invariant 0 <= i <= a.Length;
        //-invariant IsDigitSeq(power2(32), a[..i]); 
        invariant forall j:int :: 0 <= j < i ==> a[j] == val;
    {
        lemma_2toX();
        a[i] := val;
        assert a[..i+1] == a[..i] + [a[i]];   //- this line added for DafnyCC's sake
        i := i + 1;
    }
    //-assert IsDigitSeq(power2(32), a[0..a.Length]); 
    assert a[..] == a[0..a.Length];
    //-assert IsDigitSeq(power2(32), a[..]); 
}


method mkFatNatAddState() returns (state:BenchmarkState)
    ensures state.FatNatAddState?;
    ensures state.a != null && state.b != null; 
    ensures fresh(state.a) && fresh(state.b);
    ensures IsDigitSeq(power2(32), state.a[..]) && IsDigitSeq(power2(32), state.b[..]);
    ensures WellformedBenchmarkState(state);
{
    lemma_2toX();
    var a := make_array(42,32);
    var b := make_array(12,32);

    state := FatNatAddState(a, b);
    reveal_WellformedBenchmarkState();
}

method mkShaState(use_words:bool,use_original:bool, len_bits:int) returns (valid:bool, state:BenchmarkState)
    ensures valid ==> state.ShaState?;
    ensures valid ==> WellformedBenchmarkState(state);
{
    lemma_2toX();
    valid := true;

    if len_bits <= 0 || len_bits > 0x1000000 || len_bits / 32 <= 0 || len_bits / 8 <= 0 {
        return false, NopState();
    }

    var a;
    if (use_words) {
        var len_words := len_bits / 32;
        a := make_array(42,len_words);
    } else {
        var len_bytes := len_bits / 8;
        a := make_array(42,len_bytes);
    }

    state := ShaState(use_words, a, use_original);
    reveal_WellformedBenchmarkState();
}

method mkRsaState(num_key_bits:int) returns (state:BenchmarkState)
    requires 100 < num_key_bits < 0x10000;
    requires TPM_ready();
    modifies this`TPM;   
    modifies this`IoMemPerm;
    ensures state.RsaState?;
    ensures WellformedBenchmarkState(state);
    ensures TPM_ready();
{
    lemma_2toX();

    var TestKeyPair:RSAKeyPairImpl;

    calc {
        0x10000;
        < { lemma_2toX32(); }
        power2(28);
    }
    TestKeyPair := RSAKeyGen(num_key_bits);
    var s := RepeatDigit_impl(42, TestKeyPair.pub.size - 11);

    state := RsaState(TestKeyPair, s);
    reveal_WellformedBenchmarkState();
}

method prepare_state(Benchmark:int, num_key_bits:int, use_words:bool, use_original:bool, len_bits:int) returns (valid:bool,state:BenchmarkState)
    //-requires IsByte(Benchmark);
    //-requires 100 < num_key_bits < 0x10000;
    requires TPM_ready();
    modifies this`TPM;   
    modifies this`IoMemPerm;
    ensures valid ==> WellformedBenchmarkState(state);
    ensures valid ==> CorrectBenchmarkState(state, Benchmark);
    ensures TPM_ready();
{
    state := NopState();
    valid := true;
    if Benchmark == BenchmarkFatAdd() || Benchmark == BenchmarkFatAddSlowly() {
        state := mkFatNatAddState();
    } else if Benchmark == BenchmarkRsaEncrypt() || Benchmark == BenchmarkRsaDecrypt() {
        if 100 < num_key_bits < 0x10000 {
            state := mkRsaState(num_key_bits);
        } else {
            valid := false;
            state := NopState();
        }
    } else if Benchmark == BenchmarkRsaKeyGen() {
        if 100 < num_key_bits < 0x10000 {
            calc {
                0x10000;
                < { lemma_2toX32(); }
                power2(28);
            }
            state := RsaKeyGenState(num_key_bits);
        } else {
            valid := false;
            state := NopState();
        }
    } else if Benchmark == BenchmarkSha256() {
        valid,state := mkShaState(use_words, use_original, len_bits);
    }
    reveal_WellformedBenchmarkState();
    reveal_CorrectBenchmarkState();
}


method BenchmarkOp(Benchmark:int, state:BenchmarkState) returns (TestResult:seq<int>,state':BenchmarkState)
    requires TPM_ready();
    requires WellformedBenchmarkState(state);
    requires CorrectBenchmarkState(state, Benchmark);
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures TPM_ready();
    ensures WellformedBenchmarkState(state');
    ensures CorrectBenchmarkState(state', Benchmark);
{
    state' := state;
    if (Benchmark == 0)
    {
        //- No-op benchmark.
        TestResult := [];
        state' := NopState();
        reveal_WellformedBenchmarkState();
        reveal_CorrectBenchmarkState();
    }
    else if (Benchmark == 2)
    {
        assert Benchmark == BenchmarkSha256();
        reveal_WellformedBenchmarkState();
        reveal_CorrectBenchmarkState();
        if (state.arr_is_words) {
            if (state.use_original) {
                var dummy_TestResult_array := SHA256_impl_Words_arrays_original(state.arr);
            } else {
                var dummy_TestResult_array := SHA256_impl_Words_arrays(state.arr);
            }
        } else {
            if (state.use_original) {
                var dummy_TestResult_array := SHA256_impl_Bytes_arrays_original(state.arr);
            } else {
                var dummy_TestResult_array := SHA256_impl_Bytes_arrays(state.arr);
            }
        }
        TestResult := [];
    }
    else if (Benchmark == 3)
    {
        assert Benchmark == BenchmarkRsaKeyGen();
        reveal_WellformedBenchmarkState();
        reveal_CorrectBenchmarkState();
        var dummy_keys := RSAKeyGen(state.num_key_bits);
        TestResult := [];
    }
    else if (Benchmark == 4)
    {
        assert Benchmark == BenchmarkRsaEncrypt();
        reveal_WellformedBenchmarkState();
        reveal_CorrectBenchmarkState();
        TestResult := Encrypt(state.keypair.pub, state.text);
    }
    else if (Benchmark == 5)
    {
        assert Benchmark == BenchmarkRsaDecrypt();
        reveal_WellformedBenchmarkState();
        reveal_CorrectBenchmarkState();
        var success;
        success, TestResult := Decrypt(state.keypair, state.text);
    }
    else if (Benchmark == 14)
    {
        assert Benchmark == BenchmarkFatAdd();
        reveal_WellformedBenchmarkState();
        reveal_CorrectBenchmarkState();
        var c := FatNatAdd_optimized(state.a, state.b);
        TestResult := [];
        //-state' := FatNatAddState(state.a, c);
        state' := FatNatAddState(state.a, state.b);
        //-state' := FatNatAddState(c, c);
        reveal_WellformedBenchmarkState();
    }
    else if (Benchmark == 15) 
    {
        assert Benchmark == BenchmarkFatAddSlowly();
        reveal_WellformedBenchmarkState();
        reveal_CorrectBenchmarkState();
        var a_ref := state.a;
        var b_ref := state.b;
        var c := FatNatAdd(state.a, state.b);
        TestResult := [];
        //-state' := FatNatAddState(state.a, c);
        state' := FatNatAddState(state.a, state.b);
        //-state' := FatNatAddState(c, c);
        reveal_WellformedBenchmarkState();
    } 
    else 
    {
        TestResult := [];
        state' := NopState();
        reveal_WellformedBenchmarkState();
        reveal_CorrectBenchmarkState();
    }



    /*
    else if (Benchmark == BenchmarkSha1())
    {
        //-
        //- SHA1 Benchmark - Hash a block of bytes.
        //-
        CopyArraySimple(TestArray, TestInput);
        assert ti == TestInput[..];
        assert IsByteSeq(TestInput[..]);
        assert IsByteSeq(TestArray[..]);
        var dummy_TestResult_array := SHA1_impl_Bytes_arrays(TestArray);
    }
    else if (Benchmark == BenchmarkDuplicateArray())
    {
        CopyArraySimple(TestArray, TestInput);
        //-assert ti == TestInput[..];
    }
    else if (Benchmark == BenchmarkRsaKeyGen())
    {
        var TestKeyPair:RSAKeyPairImpl;

        //-
        //- RSA KeyGen Benchmark - Generate a public/private key pair.
        //-
        assert TestValue > 20;  //- OBSERVE!
        assert TestValue < 0x10000;  //- OBSERVE!
        calc
        {
            0x10000;
            < { lemma_2toX32(); }
            power2(28);
        }

        debug_print(0x90, 0x09001000+TestValue);
        TestKeyPair := RSAKeyGen(TestValue);
        debug_print(0x90, 0x09002000);
        //- Save the keypair for future use.
        state' := BenchmarkState_c(KeyPairOptPresent(TestKeyPair));
    }
    else if (Benchmark == BenchmarkRsaEncrypt())
    {
//-        debug_print(0x90, 0x090e0001);
        if (state.kpo.KeyPairOptPresent?)
        {
//-            debug_print(0x90, 0x090e0002);
            var KeyPair := state.kpo.keypair;
            if (TestValue <= KeyPair.pub.size-12)
            {
//-                debug_print(0x90, 0x090e0003);
                //- RSA Encrypt with fake key.
                TestResult := Encrypt(KeyPair.pub, TestSeq);
//-                debug_print(0x90, 0x090e0004);
            }
            else
            {
//-                debug_print(0x90, 0x090e0040);
//-                debug_print(0x90, TestValue);
//-                debug_print(0x90, KeyPair.pub.size);
//-                debug_print(0x90, 0x090e004f);
            }
//-            debug_print(0x90, 0x090e0005);
        }
//-        debug_print(0x90, 0x090e0006);
    }
    else if (Benchmark == BenchmarkRsaDecrypt())
    {
        if (state.kpo.KeyPairOptPresent?)
        {
            var KeyPair := state.kpo.keypair;
            if (TestValue <= KeyPair.pub.size-12)
            {
                var result;
                if (|TestSeq|==0)
                {
                    debug_print(0x90, 0xffff0001);
                }
                else
                {
                    var divr := TestValue / 4;
                    var mulr := divr * 4;
                    var modr := TestValue - mulr;
                    assert modr == TestValue % 4;
                    if (modr==0)
                    {
                        assert TestValue%4==0;
                        result,TestResult := Decrypt(KeyPair, TestSeq);
                    }
                    else
                    {
                        debug_print(0x90, 0xffff0002);
                    }
                }
            }
        }
    }
    else if (Benchmark == BenchmarkTpmExtractRandom())
    {
        //-
        //- TPM benchmark - Extract random bytes from the TPM.
        //-
        lemma_2toX();
        TestResult := get_random(TestValue);
    }
    else if (Benchmark == BenchmarkByteSeqToWordSeq())
    {
        //-
        //- Benchmark ByteSeqToWordSeq method.
        //-
        ghost var TestPadding:seq<int>;
        TestResult, TestPadding := BEByteSeqToWordSeq_impl(TestSeq);
    }
    else if (Benchmark == BenchmarkWordSeqToByteSeq())
    {
        //-
        //- Benchmark WordSeqToByteSeq method.
        //-
        lemma_2toX();
        TestResult := BEWordSeqToByteSeq_impl(TestSeq);
    }
    */
}

//-
//- Time a particular benchmark for the given number of iterations.
//-
method {:timeLimitMultiplier 2} TimeIt(Benchmark:int, Iterations:int, state:BenchmarkState, dummy_array:array<int>)
    returns (BeginHigh:int, BeginLow:int, EndHigh:int, EndLow:int, TestResult:seq<int>, state':BenchmarkState)
    requires Word32(Iterations);
    requires dummy_array != null;
    requires TPM_ready();
    requires WellformedBenchmarkState(state);
    requires CorrectBenchmarkState(state, Benchmark);
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures TPM_ready();
    ensures Word32(BeginHigh);
    ensures Word32(BeginLow);
    ensures Word32(EndHigh);
    ensures Word32(EndLow);
    ensures WellformedBenchmarkState(state');
    ensures CorrectBenchmarkState(state, Benchmark);
{
    lemma_2toX();

    var a_ref := if state.FatNatAddState? then state.a else 
                 if state.ShaState? then state.arr else dummy_array;  //- DafnyCC
    var b_ref := if state.FatNatAddState? then state.b else dummy_array;  //- DafnyCC

    TestResult := [];

    var RemainingIterations:int := Iterations;
    state' := state;
    var a'_ref := if state'.FatNatAddState? then state'.a else dummy_array;  //- DafnyCC
    var b'_ref := if state'.FatNatAddState? then state'.b else dummy_array;  //- DafnyCC

    debug_print(0x90, 0x09000010);

    //-
    //- Take starting timestamp.
    //-
    BeginHigh, BeginLow := Asm_Rdtsc();

    //-//////////////
    calc {
        true;
        ==> { reveal_WellformedBenchmarkState(); }
        WellformedBenchmarkState(state');  
    }
    //-//////////////

    //-
    //- Repeatedly do the thing we're timing.
    //-
    while (RemainingIterations > 0)
        decreases RemainingIterations;
        invariant RemainingIterations >= 0;
        invariant TPM_ready();
        invariant WellformedBenchmarkState(state');
        invariant CorrectBenchmarkState(state', Benchmark);
    {
        var a'_ref := if state'.FatNatAddState? then state'.a else 
                      if state'.ShaState? then state'.arr else dummy_array;      //- DafnyCC
        var b'_ref := if state'.FatNatAddState? then state'.b else dummy_array;  //- DafnyCC

        TestResult, state' := BenchmarkOp(Benchmark, state');
        RemainingIterations := RemainingIterations - 1;
    }

    var a'2_ref := if state'.FatNatAddState? then state'.a else 
                   if state'.ShaState? then state'.arr else dummy_array;      //- DafnyCC
    var b'2_ref := if state'.FatNatAddState? then state'.b else dummy_array;  //- DafnyCC

    //-
    //- Take ending timestamp.
    //-
    EndHigh, EndLow := Asm_Rdtsc();

    //-//////////////
    calc {
        true;
        ==> { reveal_WellformedBenchmarkState(); }
        WellformedBenchmarkState(state');  
    }
    //-//////////////
}

//-
//- Time a particular benchmark (that requires a RSA key) for the given number of iterations.
//-
//-method TimeItWithRSAKey(Benchmark:int, Iterations:int, TestValue:int, TestData:seq<int>)
//-    returns (BeginHigh:int, BeginLow:int, EndHigh:int, EndLow:int, TestResult:seq<int>)
//-    requires IsByte(Benchmark);
//-    requires Word16(Iterations);
//-    requires Word16(TestValue);
//-    requires IsByteSeq(TestData);
//-    requires TPM_ready();
//-    modifies this`TPM;
//-    modifies this`IoMemPerm;
//-    ensures TPM_ready();
//-    ensures Word32(BeginHigh);
//-    ensures Word32(BeginLow);
//-    ensures Word32(EndHigh);
//-    ensures Word32(EndLow);
//-{
//-    lemma_2toX();
//-
//-    var RemainingIterations := Iterations;
//-
//-    //-
//-    //- Pre-benchmark prep work.
//-    //- Some of this is specific to particular benchmarks.
//-    //-
//-    var TestBlock:seq<int> := [];
//-    var TestKeyPair:RSAKeyPairImpl;
//-    TestResult := [];
//-    var ActualValue := TestValue;
//-
//-    var NeedRSASizedValue:bool := Benchmark == BenchmarkRsaEncrypt();
//-    if (NeedRSASizedValue && ActualValue > 245)
//-    {
//-        //- RSA request too big.
//-        debug_print(0x90, 0xde012210);
//-        ActualValue := 245;
//-    }
//-
//-    TestBlock := RepeatDigit_impl(0x1c, ActualValue);
//-
//-    //-
//-    //- Generate a 2048-bit public/private key pair.
//-    //-
//-    calc
//-    {
//-        2048;
//-        < { lemma_2toX32(); } power2(29);
//-    }
//-    TestKeyPair := RSAKeyGen(2048);
//-    assert TestKeyPair.pub.size >= 2048 / 8;
//-//-    assert TestKeyPair.pub.size % 4 == 0;
//-    assert NeedRSASizedValue ==> |TestBlock| <= TestKeyPair.pub.size - 11;
//-
//-    //-
//-    //- Take starting timestamp.
//-    //-
//-    BeginHigh, BeginLow := Asm_Rdtsc();
//-
//-    //-
//-    //- Repeatedly do the thing we're timing.
//-    //-
//-    while (RemainingIterations > 0)
//-        decreases RemainingIterations;
//-        invariant RemainingIterations >= 0;
//-        invariant TPM_ready();
//-        invariant WellformedRSAKeyPairImpl(TestKeyPair);
//-    {
//-        if (Benchmark == BenchmarkRsaEncrypt())
//-        {
//-            TestResult := Encrypt(TestKeyPair.pub, TestBlock);
//-        }
//-        else if (Benchmark == BenchmarkRsaDecrypt())
//-        {
//-            var result;
//-            result,TestResult := Decrypt(TestKeyPair, TestBlock);
//-        }
//-        else if (Benchmark == BenchmarkRsaDigestedSign())
//-        {
//-            //- RSA Digested Sign.
//-        }
//-        else if (Benchmark == BenchmarkRsaDigestedVerify())
//-        {
//-            //- RSA Digested Verify.
//-        }
//-
//-        RemainingIterations := RemainingIterations - 1;
//-    }
//-
//-    //-
//-    //- Take ending timestamp.
//-    //-
//-    EndHigh, EndLow := Asm_Rdtsc();
//-}

method DebugPrintSequence(Offset:int, Data:seq<int>)
    requires 0 <= Offset <= 160 - 16;
    requires IsByteSeq(Data);
    requires |Data| >= 0;
{
    var Index:int := 0;

    while (Index < |Data|)
        decreases |Data| - Index;
        invariant Index >= 0;
        invariant Index <= |Data|;
    {
        debug_print(Offset, Data[Index]);
        Index := Index + 1;
    }
}
