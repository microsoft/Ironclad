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
  * .NET 6.0 SDK (available at `https://dotnet.microsoft.com/download`)
  * Dafny v3.4.0 (verifier, available at `https://github.com/dafny-lang/dafny`)
  * python 2 or 3 (needed for running scons)
  * scons (installable by running `pip install scons`)
    
The instructions below have been tested using Windows 10 and 11, macOS
Catalina, and Ubuntu 20.04.  They should also work for other platforms
Dafny and .NET support, such as Ubuntu 16.04 and Debian.  On Windows,
they work with at least the following shells: Command Prompt, Windows
PowerShell, Cygwin mintty, and Ubuntu 20.04 on Windows Subsystem for
Linux.

# Verification and Compilation

To build and verify the contents of this repo, use:

  `scons --dafny-path=/path/to/directory/with/dafny/`

To use `<n>` threads in parallel, add `-j <n>` to this command.

Expect this to take up to several hours, depending on your machine and how many
cores you have available.  Also note that the prover's time limits are based on
wall clock time, so if you run the verification on a slow machine, you may see a
few timeouts not present in our build.  If that happens, try using a longer time
limit for each verification; for example, using `--time-limit=120` makes the time
limit 120 seconds instead of the default 60 seconds.

Running scons will produce the following executables:
```
  bin/CreateIronServiceCerts.dll
  bin/TestIoFramework.dll
  bin/IronLockServer.dll
  bin/IronRSLCounterServer.dll
  bin/IronRSLCounterClient.dll
  bin/IronRSLKVServer.dll
  bin/IronRSLKVClient.dll
  bin/IronSHTServer.dll
  bin/IronSHTClient.dll
```

To produce these executables without performing verification, use `--no-verify`.

# Running

## Creating certificates

Ironfleet servers identify themselves using certificates.  So, before running
any Ironfleet services, you need to generate certificates for the service by
running `CreateIronServiceCerts`.  On the command line you'll specify the name
and type of the service and, for each server, its public address and port.  Each
such address can be a hostname like `www.myservice.com` or an IP address like
`127.0.0.1` or `2001:db8:3333:4444:CCCC:DDDD:EEEE:FFFF`.

For instance, you can run the following command:
```
  dotnet bin/CreateIronServiceCerts.dll outputdir=certs name=MyService type=TestService addr1=server1.com port1=6000 addr2=server2.com port2=7000
```
This will create three files in the directory `certs`.  Two of these files,
`MyService.TestService.server1.private.txt` and
`MyService.TestService.server2.private.txt`, are the private key files for the
two servers.  The third, `MyService.TestService.service.txt`, contains the
service identity, including the public keys of the two servers.

You'll distribute the service file to all servers and all clients.  But,
you should only copy a private key file to the server corresponding to that
private key, and after copying it you should delete your local copy.  So, in
this example, you'd copy `MyService.TestService.server1.private.txt` only to
server1.com.

## IronLock

IronLock is the simplest of the protocols we've verified, so it may be a good
starting point.  It consists of N processes passing around a lock. To run it,
make sure your firewall isn't blocking the TCP ports you use.  Here's an example
configuration with three processes:

Create the service with:
```
  dotnet bin/CreateIronServiceCerts.dll outputdir=certs name=MyLock type=IronLock addr1=127.0.0.1 port1=4001 addr2=127.0.0.1 port2=4002 addr3=127.0.0.1 port3=4003
```

Run the service by executing the following three commands in three different
windows:
```
  dotnet bin/IronLockServer.dll certs/MyLock.IronLock.service.txt certs/MyLock.IronLock.server2.private.txt
  dotnet bin/IronLockServer.dll certs/MyLock.IronLock.service.txt certs/MyLock.IronLock.server3.private.txt
  dotnet bin/IronLockServer.dll certs/MyLock.IronLock.service.txt certs/MyLock.IronLock.server1.private.txt
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
the same machine.

The client has reasonable defaults that you can override with key=value
command-line arguments. Run the client with no arguments to get detailed usage
information. Make sure your firewall isn't blocking the TCP ports you use.

To test the IronRSL counter on a single machine, you can do the following.

First, create certificates with:
```
  dotnet bin/CreateIronServiceCerts.dll outputdir=certs name=MyCounter type=IronRSLCounter addr1=127.0.0.1 port1=4001 addr2=127.0.0.1 port2=4002 addr3=127.0.0.1 port3=4003
```

Then, run each of the following three server commands, each in a different window.
```
  dotnet bin/IronRSLCounterServer.dll certs/MyCounter.IronRSLCounter.service.txt certs/MyCounter.IronRSLCounter.server1.private.txt
  dotnet bin/IronRSLCounterServer.dll certs/MyCounter.IronRSLCounter.service.txt certs/MyCounter.IronRSLCounter.server2.private.txt
  dotnet bin/IronRSLCounterServer.dll certs/MyCounter.IronRSLCounter.service.txt certs/MyCounter.IronRSLCounter.server3.private.txt
```

Finally, run this client command in yet another window:
```
  dotnet bin/IronRSLCounterClient.dll certs/MyCounter.IronRSLCounter.service.txt nthreads=10 duration=30 print=true
```

If you don't want the client to print the counter values it receives in replies,
remove `print=true` from the client command.  In that case, its output will
primarily consist of reports of the form `#req <thread-ID> <request-number>
<time-in-ms>`.

You can run the client as many times as you want.  But, you can only run each
server once since we haven't implemented crash recovery.  To prevent you from
accidentally running a server multiple times, the server program deletes its
private key file right after reading it.

Fortunately, `IronRSLCounter` can deal with the failure of fewer than half its
servers.  But, if half of them or more fail, you'll have to create a new
service.  That is, you'll have to start over by running `CreateIronServiceCerts`,
and that new service's counter will start at 0.

Note that the servers use non-blocking network receives, so they may be slow
to respond to Ctrl-C.

## IronRSL - Key-Value Store

To run the key-value service replicated with IronRSL, you should ideally use
four different machines, but in a pinch you can use four separate windows on
the same machine.

The client has reasonable defaults that you can override with key=value
command-line arguments. Run the client with no arguments to get detailed usage
information. Make sure your firewall isn't blocking the TCP ports you use.

To test the IronRSL key-value store on a single machine, you can do the following.
First, create certificates with:
```
  dotnet bin/CreateIronServiceCerts.dll outputdir=certs name=MyKV type=IronRSLKV addr1=127.0.0.1 port1=4001 addr2=127.0.0.1 port2=4002 addr3=127.0.0.1 port3=4003
```

Then, run each of the following three server commands, each in a different window:
```
  dotnet bin/IronRSLKVServer.dll certs/MyKV.IronRSLKV.service.txt certs/MyKV.IronRSLKV.server1.private.txt
  dotnet bin/IronRSLKVServer.dll certs/MyKV.IronRSLKV.service.txt certs/MyKV.IronRSLKV.server2.private.txt
  dotnet bin/IronRSLKVServer.dll certs/MyKV.IronRSLKV.service.txt certs/MyKV.IronRSLKV.server3.private.txt
```

Finally, run this client command in yet another window:
```
  dotnet bin/IronRSLKVClient.dll certs/MyKV.IronRSLKV.service.txt nthreads=10 duration=30 setfraction=0.25 deletefraction=0.05 print=true
```

If you don't want the client to print the requests it sends and the replies it
receives, remove `print=true` from the client command.  In that case, its output
will primarily consist of reports of the form `#req <thread-ID> <request-number>
<time-in-ms>`.

You can run the client as many times as you want.  But, you can only run each
server once since we haven't implemented crash recovery.  To prevent you from
accidentally running a server multiple times, the server program deletes its
private key file right after reading it.

Fortunately, `IronRSLKV` can deal with the failure of fewer than half its
servers.  But, if half of them or more fail, you'll have to create a new
service.  That is, you'll have to start over by running `CreateIronServiceCerts`,
and that new service's key-value store will start out empty.

Note that the servers use non-blocking network receives, so they may be slow
to respond to Ctrl-C.

## IronSHT

To run IronSHT (our sharded hash table), you should ideally use multiple
different machines, but in a pinch you can use separate windows on the same
machine.

The client has reasonable defaults that you can override with key=value
command-line arguments. Run the client with no arguments to get detailed usage
information. Make sure your firewall isn't blocking the TCP ports you use.

To test the IronSHT sharded hash table on a single machine, you can do the following.
First, create certificates with:
```
  dotnet bin/CreateIronServiceCerts.dll outputdir=certs name=MySHT type=IronSHT addr1=127.0.0.1 port1=4001 addr2=127.0.0.1 port2=4002 addr3=127.0.0.1 port3=4003
```

Then, run each of the following three server commands, each in a different window:
```
  dotnet bin/IronSHTServer.dll certs/MySHT.IronSHT.service.txt certs/MySHT.IronSHT.server1.private.txt
  dotnet bin/IronSHTServer.dll certs/MySHT.IronSHT.service.txt certs/MySHT.IronSHT.server2.private.txt
  dotnet bin/IronSHTServer.dll certs/MySHT.IronSHT.service.txt certs/MySHT.IronSHT.server3.private.txt
```

Finally, run this client command in yet another window:
```
  dotnet bin/IronSHTClient.dll certs/MySHT.IronSHT.service.txt nthreads=10 duration=30 workload=g numkeys=1000
```
The client's output will primarily consist of reports of the form `#req
<thread-ID> <request-number> <time-in-ms>`. This output won't start for
several seconds since the client has a lot of setup to do.

We haven't implemented crash recovery, so if you restart a server its state will
be empty.

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
   var serviceIdentity = ServiceIdentity.ReadFromFile(serviceFileName);
   RSLClient rslClient = new RSLClient(serviceIdentity, serviceName);
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
