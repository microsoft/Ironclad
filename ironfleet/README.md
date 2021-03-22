# About

This directory contains experimental verified IronFleet code,
as described in:

>  [_IronFleet: Proving Practical Distributed Systems Correct_](http://research.microsoft.com/apps/pubs/default.aspx?id=255833)
>  Chris Hawblitzel, Jon Howell, Manos Kapritsos, Jacob R. Lorch, 
>  Bryan Parno, Michael L. Roberts, Srinath Setty, and Brian Zill.
>  In Proceedings of the ACM Symposium on Operating Systems Principles (SOSP).
>  October 5, 2015.

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

See http://research.microsoft.com/ironclad for more details.

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

# Verification and compilation

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
  src/Dafny/Distributed/Services/RSL/build/IronfleetShell.dll
  src/Dafny/Distributed/Services/Lock/build/IronfleetShell.dll
  src/Dafny/Distributed/Services/SHT/build/IronfleetShell.dll
  src/IronRSLClient/bin/Release/net5.0/IronRSLClient.dll
  src/IronKVClient/bin/Release/net5.0/IronKVClient.dll
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
you need to supply each process with the IP-port pairs of all processes, as well
as its own IP-pair. For example, this is a configuration with three processes:

```
  dotnet src/Dafny/Distributed/Services/Lock/build/IronfleetShell.dll 127.0.0.1 4001 127.0.0.1 4002 127.0.0.1 4003 127.0.0.1 4002
  dotnet src/Dafny/Distributed/Services/Lock/build/IronfleetShell.dll 127.0.0.1 4001 127.0.0.1 4002 127.0.0.1 4003 127.0.0.1 4003
  dotnet src/Dafny/Distributed/Services/Lock/build/IronfleetShell.dll 127.0.0.1 4001 127.0.0.1 4002 127.0.0.1 4003 127.0.0.1 4001
```

It's important that you start the "first" process last (as in the above
example), as it initially holds the lock and will immediately start passing it
around. As this is a toy example, message retransmission isn't implemented.
Therefore, if the other processes aren't running by the time the first process
sends a grant message, the message will be lost and the protocol will stop.

If started properly, the processes will pass the lock among them as fast as they
can, printing a message everytime they accept or grant the lock.

## IronRSL

To run IronRSL, you should ideally use four different machines, but in a pinch
you can use four separate windows on the same machine. The server executable
expects a list of IP-port pairs that identifies all of the replicas in the
system (in this example we're using 3, but more is feasible). Each server
instance also needs to be told which IP-port pair belongs to it.

The client has reasonable defaults that you can override with key=value
command-line arguments. Run the client with `--help` to get detailed usage
information. Make sure your firewall isn't blocking the UDP ports you use.

For example, to test IronRSL on a single machine, you can run each of the
following four commands in a different console:

```
  dotnet src/Dafny/Distributed/Services/RSL/build/IronfleetShell.dll 127.0.0.1 4001 127.0.0.1 4002 127.0.0.1 4003 127.0.0.1 4001
  dotnet src/Dafny/Distributed/Services/RSL/build/IronfleetShell.dll 127.0.0.1 4001 127.0.0.1 4002 127.0.0.1 4003 127.0.0.1 4002
  dotnet src/Dafny/Distributed/Services/RSL/build/IronfleetShell.dll 127.0.0.1 4001 127.0.0.1 4002 127.0.0.1 4003 127.0.0.1 4003
  dotnet src/IronRSLClient/bin/Release/net5.0/IronRSLClient.dll nthreads=10 duration=30 clientport=6000 initialseqno=0
```

The first three are the RSL servers, and the latter is the client.  The client's
output will primarily consist of reports of the time needed for each request.

Note that until you stop all the RSL servers, each client endpoint is expected
to use strictly increasing sequence numbers. So, if you run the client program
multiple times, use a different `clientip` or use a `clientport` such that
`[clientport, clientport + nthreads)` doesn't overlap with that of previous
runs.  Or, use an initialseqno greater than the last sequence number any
previous client run reported using (e.g., if a previous run output `#req100`,
use at least `initialseqno=101`).

Note also that the servers use non-blocking network receives, so they may be
slow to respond to Ctrl-C.

## IronKV

To run IronKV, you should ideally use multiple different machines, but in a
pinch you can use separate windows on the same machine. Like IronRSL, IronKV
server executables require a list of IP-port pairs, and the IronKV client
takes command-line arguments of the form key=value.

For example, you can run each of the following four commands in a different
console:
```
  dotnet src/Dafny/Distributed/Services/SHT/build/IronfleetShell.dll 127.0.0.1 4001 127.0.0.1 4002 127.0.0.1 4003 127.0.0.1 4001
  dotnet src/Dafny/Distributed/Services/SHT/build/IronfleetShell.dll 127.0.0.1 4001 127.0.0.1 4002 127.0.0.1 4003 127.0.0.1 4002
  dotnet src/Dafny/Distributed/Services/SHT/build/IronfleetShell.dll 127.0.0.1 4001 127.0.0.1 4002 127.0.0.1 4003 127.0.0.1 4003
  dotnet src/IronKVClient/bin/Release/net5.0/IronKVClient.dll nthreads=10 duration=30 workload=g numkeys=10000 clientport=6000
```

Like in IronRSL, the client will print its output to standard output.

Note that until you stop all the KV servers, each client endpoint is expected to
use a stateful protocol. And note that the client uses `nthreads+1` ports, since
it needs an additional port for setup. So, if you run the client program
multiple times, use a different `clientip` or use a `clientport` such that
`[clientport, clientport + nthreads]` doesn't overlap with that of previous
runs.

# Code Layout

See the [CODE](./CODE.md) file for more details on the various files in the
repository.

# Contributing

See the [CONTRIBUTING](./CONTRIBUTING.md) file for more details.

# Version History
- v0.1:  Initial code release
- v0.2:  Compatibility with Dafny 3.0.0 and .NET Core 5
