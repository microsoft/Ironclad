include "../../Libraries/Util/integer_sequences.i.dfy"
include "../../Libraries/Util/word_bits.i.dfy"
include "BenchmarkCore.i.dfy"

//-
//- Methods related to the custom remote job entry protocol we use for running benchmarks.
//-


//-
//- Decode a remote request to perform some benchmark tests.
//-
//- The Operation value is currently unused.
//- The Benchmark value determines what benchmark we run.
//- Iterations is the number of times to run the benchmark in a loop.
//- TestValue and the TestData are benchmark-specific arguments.
//-
//- A non-zero Error value indicates a parsing failure.
//-
method DecodeRequest(Data:seq<int>)
    returns (Error:int, Operation:int, Benchmark:int, Iterations:int, state:BenchmarkState)
    requires IsByteSeq(Data);
    requires TPM_ready();
    modifies this`TPM;   
    modifies this`IoMemPerm;
    ensures IsByte(Error);
    ensures Error == 0 ==> |Data| >= 15;
    ensures Error == 0 ==> IsByte(Operation);
    ensures Error == 0 ==> IsByte(Benchmark);
    ensures Error == 0 ==> Word32(Iterations);
    ensures Error == 0 ==> WellformedBenchmarkState(state);
    ensures Error == 0 ==> CorrectBenchmarkState(state, Benchmark);
    ensures TPM_ready();
{
    lemma_2toX();
    state := NopState();

    //-
    //- Initialize everything to keep DafnyCC happy.
    //-
    Error := 0;
    Operation := 0;
    Benchmark := 0;
    Iterations := 0;

    //-
    //- Our header is 15 bytes long.
    //-
    if (|Data| < 15)
    {
        Error := 1;
        return;
    }

    Benchmark := Data[0];
    Iterations := BEFourBytesToWord_impl(Data[1..5]);
    var key_bits := BEFourBytesToWord_impl(Data[5..9]);
    var len_bits := BEFourBytesToWord_impl(Data[9..13]);

    //-
    //- Next byte is which interface to use (> 0 = words, 0 = bytes)
    //-

    var use_words := false;
    if Data[13] > 0 {
        use_words := true;
    }

    //-
    //- Next byte is which code version to use (> 0 = old version, 0 = current)
    //-
    var use_original := false;
    if Data[14] > 0 {
        use_original := true;
    }

    var valid;
    valid, state := prepare_state(Benchmark, key_bits, use_words, use_original, len_bits);

    if !valid {
        Error := 5;
        return;
    }

}

//-
//- Encode an error response to return to the client that sent us the request.
//-
method EncodeErrorResponse(Error:int, OriginalRequest:seq<int>)
    returns (Data:seq<int>)
    requires IsByte(Error);
    requires Error != 0;
    requires IsByteSeq(OriginalRequest);
    requires |OriginalRequest| <= 1472;
    ensures IsByteSeq(Data);
    ensures |Data| <= 1472;
{
    lemma_2toX();

    //-
    //- On responses, first byte is the error code.
    //-
    Data := [Error];

    //-
    //- On *error* responses, any subsequent bytes are the same as in the original request.
    //- This is to help the sender determine what went wrong.
    //-
    if (|OriginalRequest| != 0)
    {
        Data := Data + OriginalRequest[1..];
    }
}

//-
//- Encode the benchmark results to return to the client that sent us the request.
//-
method EncodeSuccessfulResponse(OriginalRequest:seq<int>, BeginHigh:int, BeginLow:int, EndHigh:int, EndLow:int)
    returns (Data:seq<int>)
    requires Word32(BeginHigh);
    requires Word32(BeginLow);
    requires Word32(EndHigh);
    requires Word32(EndLow);
    requires IsByteSeq(OriginalRequest);
    requires |OriginalRequest| >= 15;
    requires |OriginalRequest| <= 1472;
    ensures IsByteSeq(Data);
    ensures |Data| <= 1472;
{
    //-
    //- Convert the four 32-bit words into four 4-byte sequences.
    //-
    var BeginHighSeq:seq<int> := BEWordSeqToByteSeq_impl([BeginHigh]);
    var BeginLowSeq:seq<int> := BEWordSeqToByteSeq_impl([BeginLow]);
    var EndHighSeq:seq<int> := BEWordSeqToByteSeq_impl([EndHigh]);
    var EndLowSeq:seq<int> := BEWordSeqToByteSeq_impl([EndLow]);

    //-
    //- On responses, first byte is the error code (zero indicates no error).
    //- Next 15 bytes are the request (for id purposes).
    //- The subsequent sixteen bytes are the begin and end timestamps.
    //-
    Data := [0]
        + OriginalRequest[..15]
        + BeginHighSeq
        + BeginLowSeq
        + EndHighSeq
        + EndLowSeq;
}
