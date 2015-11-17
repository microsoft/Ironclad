//-<NuBuild BasmEnableSymdiff true />
include "../../Drivers/CPU/assembly_premium.i.dfy"
include "../../Drivers/Network/Intel/driver.i.dfy"
include "../../Libraries/Net/ethernet.i.dfy"
include "../../Libraries/Net/IPv4.i.dfy"
include "../../Libraries/Net/Udp.i.dfy"
include "../../Libraries/Util/integer_sequences.i.dfy"
include "../../Libraries/Util/word_bits.i.dfy"
include "../../Libraries/Crypto/Hash/sha1.i.dfy"
include "../../Libraries/Crypto/Hash/sha256.i.dfy"
include "../../Libraries/Crypto/RSA/RSA.i.dfy"
include "../../Libraries/Crypto/RSA/RSAOps.i.dfy"
include "../../Libraries/Crypto/Rsa/RSA_Decrypt.i.dfy"
include "BenchmarkList.i.dfy"
include "BenchmarkCore.i.dfy"
include "Protocol.i.dfy"
include "../../Libraries/BigNum/BigNatTestLib.i.dfy"
include "../../Libraries/Crypto/RSA/RSAPublicWrapper.i.dfy"

//-
//- A wrapper utility for benchmarking various parts of the system.
//-


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

    //-
    //- TPM initialization.
    //-
    establish_locality();

    //-
    //- Network initialization.
    //-
    var NetUp, net_state := init_network_card();

    if NetUp {
        lemma_2toX();
        debug_print(0x90, 0xded0d0d0);

        var Success:bool := true;
        var EtherSource:ethernet_addr;
        var IPSource:IPv4Address;
        var IPDest:IPv4Address;
        var SourcePort:int;
        var DestPort:int;
        var Request:seq<int>;

        while (Success)
            invariant valid_network_state(net_state);
            invariant TPM_ready();
        {
            Success, net_state, EtherSource, IPSource, IPDest, SourcePort, DestPort, Request := UdpReceive(net_state);
            if (Success)
            {
                lemma_2toX();
            
//-                DebugPrintSequence(0x90, Request);
                debug_print(0x90, 0xdedadada);

                if (DestPort == 77)
                {
                    //-
                    //- Port 77 is "any private remote job entry" port.
                    //- We use our own custom protocol to issue benchmark job requests.
                    //-
                    var Response;
                    Response := RunBenchmark(Request);
                    net_state := UdpSend(net_state, EtherSource, IPDest, IPSource, DestPort, SourcePort, Response);
                }

                if (DestPort == 7)
                {
                    //-
                    //- Port 7 is the Echo Service port.
                    //- Echo the data received back to the sender.
                    //-
                    net_state := UdpSend(net_state, EtherSource, IPDest, IPSource, DestPort, SourcePort, Request);
                }

            }
            else
            {
                Result := 0xdeadbeef;
                debug_print(0x90, 0xdeadbeef);
            }
        }
    } else {
        Result := 0xdeaddead;
        debug_print(0x90, 0xdeaddead);
    }
}

//-
//- Handle a benchmark request.
//-
method RunBenchmark(Input:seq<int>)
    returns (Output:seq<int>)
    requires IsByteSeq(Input);
    requires |Input| >= 0 && |Input| <= 1472;
    requires TPM_ready();
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures TPM_ready();
    ensures IsByteSeq(Output);
    ensures |Output| <= 1472;
{
    lemma_2toX();
    var dummy_array := new int[1];

    //-
    //- Decode input to extract benchmark to run, etc.
    //-
    var Error, Operation, Benchmark, Iterations, state  := DecodeRequest(Input);

    var a_ref := if state.FatNatAddState? then state.a else 
                 if state.ShaState? then state.arr else dummy_array;  //- DafnyCC
    var b_ref := if state.FatNatAddState? then state.b else dummy_array;  //- DafnyCC

    if (Error != 0)
    {
        Output := EncodeErrorResponse(Error, Input);
        return;
    }
    if (Benchmark >= BenchmarkMax())
    {
        Output := EncodeErrorResponse(2, Input);
        return;
    }


    //-//////////////
    calc {
        true;
        ==> { reveal_WellformedBenchmarkState(); }
        WellformedBenchmarkState(state);  
    }
    //-//////////////

    //-
    //- Time the desired benchmark in a loop.
    //-
    var BeginHigh, BeginLow, EndHigh, EndLow, TestResult, state';
    BeginHigh, BeginLow, EndHigh, EndLow, TestResult, state' := TimeIt(Benchmark, Iterations, state, dummy_array);

    //-
    //- Prepare results to send back to the client.
    //-
    Output := EncodeSuccessfulResponse(Input, BeginHigh, BeginLow, EndHigh, EndLow);
}

