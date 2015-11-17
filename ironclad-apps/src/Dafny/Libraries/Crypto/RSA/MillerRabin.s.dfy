include "../RandomNumberGen.s.dfy"
include "../../Math/power.s.dfy"

static function method Configure_MillerRabinStrength() : int { 8 }
    //- According to HAC table 4.4,
    //- 512 bit key => 256 bit prime => 12 probes,
    //- 1024 bit key => 512 bit prime => 8 probes.

//------------------------------------------------------------//

//- This worksheet is valid if a MillerRabin worksheet (from
//- MillerRabin.s) is correctly configured for this prime test,
//- valid, and its probes legitimately constructed from the
//- randoms supply.
//- The MillerRabin.s file doesn't track randomness budget,
//- hence the glue.




datatype MillerRabinWorksheet = MillerRabinWorksheet_c(
    problem:MRProblem,
    probe_candidates:seq<CandidateSeedWorksheet>,
    probe_seed_reqs:seq<SelectRandomRequest>,
        //- probe_seed_req merely defers the work of demonstrating existence
        //- of a feasible h_bits value to the implementation.
    probes:seq<MRProbe>,
    is_probably_prime:bool,
    randoms:seq<int>);

static function MillerRabinWorksheetConsumesRandoms(rows:seq<CandidateSeedWorksheet>) : seq<int>
{
    if (rows==[]) then
        []
    else
        MillerRabinWorksheetConsumesRandoms(rows[..|rows|-1]) + rows[|rows|-1].randoms
}

//-static predicate MillerRabinWorksheetConsumesRandoms(rows:seq<CandidateSeedWorksheet>, randoms:seq<int>)
//-{
//-    if (|rows|==0) then
//-        |randoms|==0
//-    else
//-        is_suffix(rows[|rows|-1].randoms, randoms)
//-        && MillerRabinWorksheetConsumesRandoms(rows[..|rows|-1], randoms[..|randoms|-|rows])
//-                |rows[0].randoms|..])
//-}

static predicate IsMillerRabinProbeSeed(n:int, req:SelectRandomRequest)
{
    req.l == 2
    && req.h == n-2
    && SelectRandomRequestValid(req)
}

static predicate MillerRabinProbeConsistency(
    n:int,
    probe_candidate:CandidateSeedWorksheet,
    probe_seed_req:SelectRandomRequest,
    probe:MRProbe)
{
    IsMillerRabinProbeSeed(n, probe_seed_req)
    && CandidateSeedWorksheetValid(probe_seed_req, probe_candidate)
    && probe.a == CandidateSeedWorksheetOutput(probe_candidate)
}

static predicate MillerRabinWorksheetValid(n:int, worksheet:MillerRabinWorksheet)
{
    |worksheet.probes|==|worksheet.probe_candidates|
    && |worksheet.probes|==|worksheet.probe_seed_reqs|
    && (forall i :: 0<=i<|worksheet.probes| ==> MillerRabinProbeConsistency(n, worksheet.probe_candidates[i], worksheet.probe_seed_reqs[i], worksheet.probes[i]))
    && worksheet.problem.n == n
    && worksheet.problem.strength == Configure_MillerRabinStrength()
    && MillerRabinSpecValid(worksheet.problem, worksheet.probes, worksheet.is_probably_prime)
    && MillerRabinWorksheetConsumesRandoms(worksheet.probe_candidates) == worksheet.randoms
}

//------------------------------------------------------------//

datatype MRProblem = MRProblem_c(
    n:nat,
    strength:nat,
    s:nat,
    d:nat)

static predicate MRProblemEarlyReject(problem:MRProblem)
{
    problem.n <= 3
    || problem.n%2 == 0
}

static predicate MRProblemNeedsProbes(problem:MRProblem)
{
    !MRProblemEarlyReject(problem)

    //- Input: k, a parameter that determines the accuracy of the test
    && problem.strength == Configure_MillerRabinStrength()

    //- write n - 1 as 2^s·d with d odd by factoring powers of 2 from n - 1
    && problem.n-1 == power(2,problem.s)*problem.d
    && problem.d%2==1
}

static predicate MRProblemValid(problem:MRProblem)
{
    MRProblemEarlyReject(problem)
    || MRProblemNeedsProbes(problem)
}

//- The algorithm describes a "WitnessLoop" as one of the following.
//- Our "MRProbe" is evidence of having done one of these.
//- It captures a, plus the fact that we have either:
//-        one x value x==1 or x==n-1 ("then do next WitnessLoop")
//- or
//-        <=s values, each the square-mod-n of the previous,
//-        with no intermediate values equal to 1, and
//-        with the last one equal to n-1.
//-
//-   pick a random integer a in the range [2, n - 2]
//-   x := a^d mod n
//-   if x = 1 or x = n - 1 then do next WitnessLoop
//-   repeat s - 1 times:
//-      x := x^2 mod n
//-      if x = 1 then return composite
//-      if x = n - 1 then do next WitnessLoop
//-   return composite

datatype MRProbe = MRProbe_c(
    a:nat,
    squares:seq<int>)

static predicate MRProbeInit(problem:MRProblem, probe:MRProbe)
    requires MRProblemNeedsProbes(problem);
    requires 0 < |probe.squares|;
{
    probe.squares[0] == power(probe.a,problem.d) % problem.n
}

static predicate MRProbeChain(problem:MRProblem, probe:MRProbe, i:nat)
    requires MRProblemNeedsProbes(problem);
    requires 0 < i < |probe.squares|;
{
    probe.squares[i]==power(probe.squares[i-1], 2) % problem.n
}

//- If problem.s == 0, then 
static predicate MRProbeValid(problem:MRProblem, probe:MRProbe)
{
    MRProblemNeedsProbes(problem)
    && 0<|probe.squares|
        
        
        
    && MRProbeInit(problem,probe)
    && (forall i:int ::
        (0<i<|probe.squares| ==> MRProbeChain(problem, probe, i)))
    && (forall i:int ::
        (0<i<|probe.squares|-1 ==> probe.squares[i]!=1))
}

static function MRProbeLimit(problem:MRProblem) : int
{
    if (problem.s==0) then 1 else problem.s
}

static predicate MRProbeSucceeds(problem:MRProblem, probe:MRProbe)
    requires MRProblemNeedsProbes(problem);
{
    MRProbeValid(problem, probe)
    //- probe length: no more than s trials.
    
    && 0 < |probe.squares| <= MRProbeLimit(problem)
    //- probe structure: two early successes, or stop if we see an n-1
    && (
        probe.squares==[1]
        || probe.squares==[problem.n-1]
        || probe.squares[|probe.squares|-1]==problem.n-1
        )
}

static predicate MRProbeFails(problem:MRProblem, probe:MRProbe)
    requires MRProblemNeedsProbes(problem);
{
    MRProbeValid(problem, probe)
    //- probe length: terminates after s trials, or if we found a 1.
    && (|probe.squares| == MRProbeLimit(problem)
        || (0 < |probe.squares|
            && probe.squares[|probe.squares|-1] == 1))
    //- probe structure: not one of the success cases
    && (
        probe.squares!=[1]
        && probe.squares!=[problem.n-1]
        && probe.squares[|probe.squares|-1]!=problem.n-1
        )
}







static predicate MillerRabinSpecFails(problem:MRProblem, probes:seq<MRProbe>)
    //- last probe fails
    //- didn't probe more than problem strength requires
{
    
    MRProblemEarlyReject(problem)
    ||
    (
        MRProblemNeedsProbes(problem)
        && (
            1 <= |probes| <= problem.strength
            && (forall i :: (0 <= i < |probes|-1 ==> MRProbeSucceeds(problem, probes[i])))
            && MRProbeFails(problem, probes[|probes|-1])
           )
    )
}

static predicate MillerRabinSpecSucceeds(problem:MRProblem, probes:seq<MRProbe>)
    //- all probes succeed
    //- probed exactly as many times as problem strength requires
{
    MRProblemNeedsProbes(problem)
    && problem.n%2==1
    && problem.n>3
    && |probes| == problem.strength
    && (forall i :: 0 <= i < |probes| ==> MRProbeSucceeds(problem, probes[i]))
}

static predicate MillerRabinSpecValid(problem:MRProblem, probes:seq<MRProbe>, result:bool)
{
    (MillerRabinSpecSucceeds(problem, probes) && result)
    || (MillerRabinSpecFails(problem, probes) && !result)
}

static predicate IsProbablyPrime(n:nat,strength:nat)

static lemma {:axiom} MillerRabinSpec(problem:MRProblem, probes:seq<MRProbe>)
    requires MRProblemValid(problem);
    requires MillerRabinSpecValid(problem, probes, true);
    ensures IsProbablyPrime(problem.n, problem.strength);




