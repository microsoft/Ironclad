# About

This directory contains experimental verified IronFleet code, as described in:

>  [_IronFleet: Proving Practical Distributed Systems Correct_](https://www.microsoft.com/en-us/research/publication/ironfleet-proving-practical-distributed-systems-correct/)
>  Chris Hawblitzel, Jon Howell, Manos Kapritsos, Jacob R. Lorch, 
>  Bryan Parno, Michael L. Roberts, Srinath Setty, and Brian Zill.
>  In Proceedings of the ACM Symposium on Operating Systems Principles (SOSP).
>  October 5, 2015.

>  [_IronFleet: Proving Safety and Liveness of Practical Distributed Systems_](https://www.microsoft.com/en-us/research/publication/ironfleet-proving-safety-liveness-practical-distributed-systems/)
>  Chris Hawblitzel, Jon Howell, Manos Kapritsos, Jacob R. Lorch, 
>  Bryan Parno, Michael L. Roberts, Srinath Setty, and Brian Zill.
>  Communications of the ACM (CACM) 60(7), July 2017.

As a brief summary, we are motivated by the fact that distributed systems are notorious
for harboring subtle bugs.  Verification can, in principle, eliminate these bugs a priori,
but verification has historically been difficult to apply at full-program scale, much less
distributed-system scale.

We developed a methodology for building practical and provably correct distributed systems
based on a unique blend of TLA-style state-machine refinement and Hoare-logic
verification.  In this code release, we demonstrate the methodology on a complex
implementation of a Paxos-based replicated state machine library (IronRSL) and a
lease-based sharded key-value store (IronKV).  We prove that each obeys a concise safety
specification, as well as desirable liveness requirements.  Each implementation achieves
performance competitive with a reference system.  With our methodology and lessons
learned, we aim to raise the standard for distributed systems from "tested" to "correct."

See https://research.microsoft.com/ironclad for more details.

# License

IronFleet is licensed under the MIT license included in the [LICENSE](./LICENSE) file.

# Setup

To use Ironfleet, you'll need the following tools:
  * .NET 5.0 SDK (available at `https://dotnet.microsoft.com/download`)
  * Dafny v3.0.0 (verifier, available at `https://github.com/dafny-lang/dafny`)
  * python 2 or 3 (needed for running scons)
  * scons (installable by running `pip install scons`)
    
The instructions below have been tested using Windows 10, macOS Catalina, and
Ubuntu 20.04.  They should also work for other platforms Dafny and .NET support,
such as Ubuntu 16.04 and Debian.  On Windows, they work with at least the
following shells: Command Prompt, Windows PowerShell, and Cygwin mintty.

# Verification and Compilation

To build and verify the contents of this repo, use:

  `scons --dafny-path=/path/to/directory/with/dafny/`

To use `<n>` threads in parallel, add `-j <n>` to this command.

Expect this to take up to several hours, depending on your machine and how many
cores you have available.  Also note that the prover's time limits are based on
wall clock time, so if you run the verification on a slow machine, you may see a
few timeouts not present in our build.  If that happens, try using a longer time
limit for each verification; for example, using `--time-limit=60` makes the time
limit 60 seconds instead of the default 30 seconds.

Running scons will produce the following executables:
```
  src/IronLockServer/bin/Release/net5.0/IronLockServer.dll
  src/IronRSLCounterServer/bin/Release/net5.0/IronRSLCounterServer.dll
  src/IronRSLCounterClient/bin/Release/net5.0/IronRSLCounterClient.dll
  src/IronRSLKVServer/bin/Release/net5.0/IronRSLKVServer.dll
  src/IronRSLKVClient/bin/Release/net5.0/IronRSLKVClient.dll
  src/IronSHTServer/bin/Release/net5.0/IronSHTServer.dll
  src/IronSHTClient/bin/Release/net5.0/IronSHTClient.dll
```

To produce these executables without performing verification, use `--no-verify`.

To avoid hampering performance, we've turned off most hosts' output.  To make
hosts collect and print profile information, change `false` to `true` in
`ShouldPrintProfilingInfo` in `./src/Dafny/Distributed/Impl/Common/Util.i.dfy`.
To make hosts print information about their progress, change `false` to `true`
in `ShouldPrintProgress` in the same file.

# Running

## IronLock

IronLock is the simplest of the protocols we've verified, so it may be a good
starting point.  It consists of N processes passing around a lock. To run it,
you need to supply each process with the IP-port pairs of all processes, as
well as its own IP-pair.  Also, make sure your firewall isn't blocking the TCP
ports you use.  Here's an example configuration with three processes:

```
  dotnet src/IronLockServer/bin/Release/net5.0/IronLockServer.dll localhost:4001 localhost:4002 localhost:4003 localhost:4002
  dotnet src/IronLockServer/bin/Release/net5.0/IronLockServer.dll localhost:4001 localhost:4002 localhost:4003 localhost:4003
  dotnet src/IronLockServer/bin/Release/net5.0/IronLockServer.dll localhost:4001 localhost:4002 localhost:4003 localhost:4001
```

It's important that you start the "first" process last (as in the above
example), as it initially holds the lock and will immediately start passing it
around. As this is a toy example, message retransmission isn't implemented.
Therefore, if the other processes aren't running by the time the first process
sends a grant message, the message will be lost and the protocol will stop.

If started properly, the processes will pass the lock among them as fast as they
can, printing a message everytime they accept or grant the lock.

## IronRSL - Counter

To run the counter service replicated with IronRSL, you should ideally use
four different machines, but in a pinch you can use four separate windows on
the same machine. The server executable expects a list of IP-port pairs that
identifies all of the replicas in the system (in this example we're using 3,
but more is feasible). Each server instance also needs to be told which
IP-port pair belongs to it.

The client has reasonable defaults that you can override with key=value
command-line arguments. Run the client with `--help` to get detailed usage
information. Make sure your firewall isn't blocking the TCP ports you use.

For example, to test the IronRSL counter on a single machine, you can run each
of the following four commands in a different console:

```
  dotnet src/IronRSLCounterServer/bin/Release/net5.0/IronRSLCounterServer.dll localhost:4001 localhost:4002 localhost:4003 localhost:4001
  dotnet src/IronRSLCounterServer/bin/Release/net5.0/IronRSLCounterServer.dll localhost:4001 localhost:4002 localhost:4003 localhost:4002
  dotnet src/IronRSLCounterServer/bin/Release/net5.0/IronRSLCounterServer.dll localhost:4001 localhost:4002 localhost:4003 localhost:4003
  dotnet src/IronRSLCounterClient/bin/Release/net5.0/IronRSLCounterClient.dll nthreads=10 duration=30 clientport=6000 verbose=true
```

The first three are the RSL servers, and the latter is the client.  If you use
`verbose=false`, the client's output will primarily consist of reports of the
form `#req <thread-ID> <request-number> <time-in-ms>`.

Note that the servers use non-blocking network receives, so they may be slow
to respond to Ctrl-C.

## IronRSL - Key-Value Store

To run the key-value service replicated with IronRSL, you should ideally use
four different machines, but in a pinch you can use four separate windows on
the same machine. The server executable expects a list of IP-port pairs that
identifies all of the replicas in the system (in this example we're using 3,
but more is feasible). Each server instance also needs to be told which
IP-port pair belongs to it.

The client has reasonable defaults that you can override with key=value
command-line arguments. Run the client with `--help` to get detailed usage
information. Make sure your firewall isn't blocking the TCP ports you use.

For example, to test the IronRSL key-value store on a single machine, you can
run each of the following four commands in a different console:

```
  dotnet src/IronRSLKVServer/bin/Release/net5.0/IronRSLKVServer.dll localhost:4001 localhost:4002 localhost:4003 localhost:4001
  dotnet src/IronRSLKVServer/bin/Release/net5.0/IronRSLKVServer.dll localhost:4001 localhost:4002 localhost:4003 localhost:4002
  dotnet src/IronRSLKVServer/bin/Release/net5.0/IronRSLKVServer.dll localhost:4001 localhost:4002 localhost:4003 localhost:4003
  dotnet src/IronRSLKVClient/bin/Release/net5.0/IronRSLKVClient.dll nthreads=10 duration=30 clientport=6000 setfraction=0.25 deletefraction=0.05 verbose=true
```

The first three are the RSL servers, and the latter is the client.  If you use
`verbose=false`, the client's output will primarily consist of reports of the
form `#req <thread-ID> <request-number> <time-in-ms>`.

Note that the servers use non-blocking network receives, so they may be slow
to respond to Ctrl-C.

## IronSHT

To run IronSHT (our sharded hash table), you should ideally use multiple
different machines, but in a pinch you can use separate windows on the same
machine. Like IronRSL, IronSHT server executables require a list of IP-port
pairs, and the IronSHT client takes command-line arguments of the form
key=value. Make sure your firewall isn't blocking the TCP ports you use.

For example, you can run each of the following four commands in a different
console:
```
  dotnet src/IronSHTServer/bin/Release/net5.0/IronSHTServer.dll localhost:4001 localhost:4002 localhost:4003 localhost:4001
  dotnet src/IronSHTServer/bin/Release/net5.0/IronSHTServer.dll localhost:4001 localhost:4002 localhost:4003 localhost:4002
  dotnet src/IronSHTServer/bin/Release/net5.0/IronSHTServer.dll localhost:4001 localhost:4002 localhost:4003 localhost:4003
  dotnet src/IronSHTClient/bin/Release/net5.0/IronSHTClient.dll nthreads=10 duration=30 workload=g numkeys=10000 client=localhost:6000 verbose=true
```

The client will print its output to standard output.  If you use
`verbose=false`, the client's output will primarily consist of reports of the
form `#req <thread-ID> <request-number> <time-in-ms>`.

Note that until you stop all the SHT servers, each client endpoint is expected
to use strictly increasing sequence numbers, starting with 1.  Since the test
client program always starts with 1, you should never reuse the same client
endpoint until you restart the SHT servers, and you should keep in mind that
the client uses `nthreads+1` consecutive ports: one for setup and `nthreads`
for experiments.  So, for instance, if you use `nthreads=10
client=localhost:6000`, then the next time you run you could use
`client=localhost:6011`.

# Custom Replicated Services

IronRSL-Counter and IronRSL-KV are examples showing how to write a service in C#
and replicate it using IronRSL.  If you want to replicate a different C#
service, it's fairly easy to do by just following the examples in
`src/IronRSLCounterServer/IronRSLCounterServer.sln`,
`src/IronRSLKVServer/IronRSLKVServer.sln`,
`src/IronRSLCounterClient/IronRSLCounterClient.sln`, and
`src/IronRSLKVClient/IronRSLKVClient.sln`.

Your service implementation, like in `src/IronRSLCounterServer/Service.cs`, must
look like this:
```
  namespace IronRSL {
    public class Service {
      public static string Name { get { ... } }
      public static Service Initialize() { ... }
      public byte[] Serialize() { ... }
      public static Service Deserialize(byte[] buf) { ... }
      public byte[] HandleRequest(byte[] request) { ... }
    }
  }
```
where you fill out the ellipses to provide:
* a static property to provide the service name,
* a static method to initialize the service state,
* a method to serialize the service state,
* a static method to deserialize the service state, and
* a method to handle a request and return a reply.

Your client implementation, like in `src/IronRSLKVClient/Client.cs`, will
create a connection to the replicated service with:
```
   RSLClient rslClient = new RSLClient(serverEndpoints, myClientEndpoint);
```
and submit requests to that replicated service with:
```
   byte[] reply = rslClient.SubmitRequest(request);
```

# Code Layout

See the [CODE](./CODE.md) file for more details on the various files in the
repository.

# Contributing

See the [CONTRIBUTING](./CONTRIBUTING.md) file for more details.

# Version History
- v0.1:  Initial code release
- v0.2:  Compatibility with Dafny 3.0.0 and .NET Core 5
