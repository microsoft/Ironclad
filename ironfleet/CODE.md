# Code Layout

Here is a brief overview of the files of interest in this repository.  One central
convention is that all trusted specification files end in `.s.dfy`.  Everything else
should be a `.i.dfy` file and will be verified for correctness.

- `SConstruct`
  SCons build file for verifying and compiling everything
- `src`
  + `IronLockServer`
    C# solution and project files for building the lock server.
  + `IronRSLKVServer`
    C# solution and project files for building a key-value store replica that
    uses IronRSL to coordinate with other replicas.  This directory includes
    the file `Service.cs` defining the key-value service.
  + `IronRSLKVClient`
    Unverified C# client for the key-value service replicated by IronRSL.
  + `IronRSLCounterServer`
    C# solution and project files for building a counter service replica that
    uses IronRSL to coordinate with other replicas.  This directory includes
    the file `Service.cs` defining the counter service.
  + `IronRSLCounterClient`
    Unverified C# client for the counter service replicated by IronRSL.
  + `IronSHTServer`
    C# solution and project files for building the IronSHT (sharded hash table) server.
  + `IronSHTClient`
    Unverified C# client for IronSHT.
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
          `src/Dafny/Distributed/Services`.
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
          The core implementation of IronSHT (sharded hash table).
        - `LiveSHT`
          SHT's scheduler and functionality for sending and receiving packets.
        - `Lock`
          The core implementation for IronLock. This includes the command line parser,
          the message definitions, parsing and marshalling, a simple scheduler, etc. 
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
              repeatedly he eventually receives a reply.  It requires various
              assumptions codified in Assumptions.i.dfy, e.g., a quorum of
              replicas is live and the network eventually delivers packets among
              the client and the live quorum in bounded time.  The ultimate
              liveness proof, in LivenessProof.i.dfy, is a proof by
              contradiction: if those assumptions hold and the client never gets
              a reply, then `false`.
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
                that if a message is submitted to the reliable-delivery
                component then its intended recipient eventually receives it and
                queues it for processing.  This proof requires various
                assumptions codified in `Assumptions.i.dfy`, e.g., a message sent
                infinitely often is eventually delivered.  The ultimate liveness
                proof is in `LivenessProof.i.dfy`.
        - `Lock`
          Defines the protocol layer of our Lock service
            + `RefinementProof`
               Proof that the implementation refines the specification. The proof
               uses two intermediate layers of states beyond the implementation and
               the specification. The `LS_State` layer represents the protocol states,
               while the `GLS_State` layer augments each protocol state with a history
               variable, which is used to prove refinement to the high-level specification.
      + `Services`
        These directories tie the implementation, protocol, and specifications together.
        Each service has a directory with `.s.dfy` files that define the service-specific
        specifications (e.g. that RSL should be a state machine or that SHT should be a
        hash table).  The file `Main.i.dfy` in each directory instantiates the abstract
        host with the concrete implementation and supplies a proof that refinement holds
        from the implementation all the way up to the abstract specification.  See
        `src/Dafny/Distributed/Common/Framework` for the guarantees this provides.
