# Code Layout

Here is a brief overview of the files of interest in this repository.  One central
convention is that all trusted specification files end in `.s.dfy`.  Everything else
should be a `.i.dfy` file and will be verified for correctness.

- `bin_tools/NuBuild` 
  Prebuilt binaries of our build tool
- `tools/Dafny` 
  Prebuilt binaries of the tools we use: 
    [Dafny](http://research.microsoft.com/en-us/projects/dafny/),
    [Boogie](https://github.com/boogie-org/boogie), and
    [Z3](https://github.com/Z3Prover/z3).
- `tools/NuBuild` 
  Source code for our build tool
- `src`
  + `IronfleetClient`     
    Unverified C# client for IronRSL
  + `IronKVClient`  
    Unverified C# client for IronKV
  + `IronfleetTestDriver` 
    C# solution and project files for building the C# code emitted
    when compiling our Dafny code.
  + `Dafny`
    - `Libraries` 
      Basic library support for various tasks, particularly for dealing with
      non-linear operations that Z3 struggles with.  These libraries were inherited from
      the [IroncladApps](http://research.microsoft.com/apps/pubs/default.aspx?id=230123) project.
    - `Distributed`
      The core IronFleet code
      + `Common`
        Code shared across our services for various core taskes
        - `Collections`
          Useful definitions, lemmas, and methods for dealing with Sets, Maps, and Sequences.
        - `Framework`
          This is the trusted framework that forms the core portion of each service's
          specification.  Each service further adds service-specific specifications in
          `src/Dafny/Distributed/Services`
        - `Logic`
          Our encoding of TLA in Dafny.
        - `Native`
          Our trusted interface to C# for networking, time, command-line arguments and
          other functionality that Dafny does not expose.
      + `Impl`
        - `Common`
          Useful libraries shared across services.  Includes command-line parsing, generic
          marshalling and parsing, end-point identities, and a UDP client.
        - `RSL`
          The core implementation of IronRSL.  These files define concrete versions of the
          types specified by the protocol.  For each role, e.g., the Acceptor, we have a
          file `AcceptorState.i.dfy` which defines the basic datatype and predicates on
          it, and a file `AcceptorModel.i.dfy` which defines the actions that can be
          performed on the data type.  ReplicaModel is the top-level role that combines
          all of the others, and ReplicaImpl interfaces with the external world to send
          and receive packets.  ReplicaModel and ReplicaImpl are split into multiple files
          to increase the file-level parallelism of our build tool.
        - `SHT`
          The core implementation of IronKV (KV = Key-Value, SHT = Sharded Hashtable).  
        - `LiveSHT`
          SHT's scheduler and functionality for sending and receiving packets.  
      + `Protocol`
        - `Common`
          Common files shared by all of our protocols
        - `RSL`
          Defines the protocol layer of our RSL system
            + `RefinementProof`
              Proof of safety, in the form of a proof that the implementation
          refines the specification given that it refines the protocol.
            + `LivenessProof`
               Proof of liveness, specifically that if a client submits a request
          repeatedly he eventually receives a reply.  It requires
          various assumptions codified in Assumptions.i.dfy, e.g.,
          a quorum of replicas is live and the network
          eventually delivers packets among the client and
          the live quorum in bounded time.
          The ultimate liveness proof, in LivenessProof.i.dfy, is a proof
          by contradiction:  if those assumptions hold and the client
          never gets a reply, then 'false'.
        - `SHT`
          Defines the protocol layer of our SHT system
            + `RefinementProof`
              Proof of safety, in the form of a proof that the implementation
          refines the specification given that it refines the protocol.
        - `LiveSHT`
          Defines a small additional layer that adds a scheduler to SHT and maps
          the low level Environment to SHT's notion of a Network.
              + `RefinementProof`
                Proof that LiveSHT is a refinement of SHT
              + `LivenessProof`
                Proof of liveness of the reliable-delivery layer, specifically
                that if a message is submitted to the reliable-delivery component
                then its intended recipient eventually receives it and queues
                it for processing.  This proof requires
                various assumptions codified in Assumptions.i.dfy,
                e.g., a message sent infinitely often
                is eventually delivered.  The ultimate
                liveness proof is in LivenessProof.i.dfy.
      + `Services`
        These directories tie the implementation, protocol, and specifications together.
        Each service has a directory with `.s.dfy` files that define the service-specific
        specifications (e.g. that RSL should be a state machine or that SHT should be a
        hash table).  The file `Main.i.dfy` in each directory instantiates the abstract
        host with the concrete implementation and supplies a proof that refinement holds
        from the implementation all the way up to the abstract specification.  See
        `src/Dafny/Distributed/Common/Framework` for the guarantees this provides.

