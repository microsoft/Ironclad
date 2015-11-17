//-<NuBuild BasmEnableSymdiff true />
include "../BenchmarkService/BenchmarkList.i.dfy"
include "../BenchmarkService/BenchmarkCore.i.dfy"
include "../../Libraries/Util/insecure_prng.i.dfy"
include "../../Libraries/Crypto/Hash/sha256opt2.i.dfy"

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

method print_state(state:BenchmarkState)
    requires WellformedBenchmarkState(state);
{
    if state.FatNatAddState? {
        var b_ref := state.b;
        reveal_WellformedBenchmarkState();
        print_array(0xa, state.a);
        reveal_WellformedBenchmarkState();
        print_array(0xb, state.b);
    }
}


//-
//- Main benchmark app entry point.
//-
method Main()
    returns (Result:int)
    ensures public(true);
    requires TPM_valid(TPM);
    requires TPM_satisfies_integrity_policy(TPM);
    requires IoMemPerm.Null?;
    modifies this`TPM;
    modifies this`IoMemPerm;
{
    lemma_2toX();

    Result := 0;

    var rand := insecure_get_random(42);            
    var dummy_array := new int[1];

    //-
    //- TPM initialization.
    //-
//- [jonh] comment next line out to build C# version
    establish_locality();
    //-var bms := BenchmarkState_c(KeyPairOptAbsent());
    ResetTally();

    var benchmark := BenchmarkSha256();
    //-var benchmark := BenchmarkFatAdd();
    var valid,state := prepare_state(benchmark, 512, true, false, 8192*8);

    if valid {
        var BeginHigh, BeginLow, EndHigh, EndLow, TestResult, state' := TimeIt(benchmark, 100000, state, dummy_array);
        //-print_state(state');
        debug_print(0x89, BeginHigh);
        debug_print(0x89, BeginLow);
        debug_print(0x89, EndHigh);
        debug_print(0x89, EndLow);
        DisplayTally();
    } else {
        debug_print(0x66, 0x666666);
    }
}
