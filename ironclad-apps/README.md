# About

This directory contains experimental verified Ironclad Apps code,
as described in:

>  [_Ironclad Apps: End-to-End Security via Automated Full-System Verification_](http://research.microsoft.com/apps/pubs/default.aspx?id=230123)
>  Chris Hawblitzel, Jon Howell, Jacob R. Lorch, Arjun Narayan, Bryan Parno, Danfeng Zhang, and Brian Zill.
>  In Proceedings of the USENIX Symposium on Operating Systems Design and Implementation (OSDI)
>  October 6, 2014.

As a brief summary, an Ironclad App lets a user securely transmit her data to a remote
machine with the guarantee that every instruction executed on that machine adheres to a
formal abstract specification of the app’s behavior. This does more than eliminate
implementation vulnerabilities such as buffer overflows, parsing errors, or data leaks; it
tells the user exactly how the app will behave at all times. We provide these guarantees
via complete, low-level software verification. We then use cryptography and secure
hardware to enable secure channels from the verified software to remote users. To achieve
such complete verification, we developed a set of new and modified tools, a collection of
techniques and engineering disciplines, and a methodology focused on rapid development of
verified systems software. We describe our methodology, formal results, and lessons we
learned from building a full stack of verified software. That software includes a verified
kernel; verified drivers; verified system and crypto libraries including SHA, HMAC, and
RSA; and four Ironclad Apps

See http://research.microsoft.com/ironclad for more details.

# License

The Ironclad Apps code is licensed under the MIT license included in the [LICENSE](../ironfleet/LICENSE) file.

# Setup

The build process currently requires Windows PowerShell, though this should be relatively
simple to replace.  Since the build process uses PowerShell scripts, script execution must
be enabled.  (For example, launch "powershell.exe -ExecutionPolicy RemoteSigned".)

To build the tools from a PowerShell prompt, simply run: `.\build-tools`.  
This will build all of the basic tools, including NuBuild (aka IronBuild),
our distributed verification and build tool.

To use Dafny interactively, you'll need Visual Studio 2012 or newer, Vim, or Emacs.
Each has a plugin:
  - For Vim, we suggest the vim-loves-dafny plugin:
      https://github.com/mlr-msft/vim-loves-dafny
  - For Emacs, we suggest the Emacs packages boogie-mode and dafny-mode:
      https://github.com/boogie-org/boogie-friends
  - For Visual Studio, open:
      `./tools/Dafny/DafnyLanguageService.vsix`
    to install the Dafny plugin with our default settings.
    If you're running on Windows Server, and you see an error message that says Z3 has crashed,
    then you may need to install the 
    [Microsoft Visual C++ runtime](http://www.microsoft.com/en-us/download/details.aspx?id=5555).
    
These instructions assume you're running on Windows.  However, Dafny, and all of its
dependencies, also run on Linux.  You can obtain Dafny sources from:

  http://dafny.codeplex.com/

Dafny's INSTALL file contains instructions for building on Linux with Mono.  Note that we have
not yet tested building our build tool, NuBuild, on Linux, so your mileage may vary.

# Verification

To perform our definitive verifications, we use our NuBuild tool, which handles dependency
tracking, caches intermediate verification results locally and in the cloud, and can
utilize a cluster of cloud VMs to parallelize verification.  To enable cloud features,
you'll need an Azure account and an Azure storage account.  Once you have an Azure storage
account, put your storage account's connection string into the
`bin_tools/NuBuild/Nubuild.exe.config` file.  This will let you make use of the cloud
cache capabilities.  To use the cloud build functionality, you'll need to add your
subscription Id and Certificate (base64 encoded) to
`bin_tools/NuBuild/AzureManage.exe.config`, which will then let you manage a cluster of
VMs to serve as workers.
You can still use NuBuild without cloud support, however, by passing the `--no-cloudcache` option.

In the examples below, we'll assume you're using Cygwin, but other shells (e.g.,
Powershell) should work as well.  

To verify an individual Dafny file (and all of its dependencies), run:

  `./bin_tools/NuBuild/NuBuild.exe --no-cloudcache -j 3 DafnyVerifyTree src/Dafny/Libraries/Math/power2.i.dfy`

which uses the `-j` flag to add 3-way local parallelism.

To verify a forest of Dafny files (e.g., all of the IronFleet files), run:

  `./bin_tools/NuBuild/NuBuild.exe --no-cloudcache -j 3 BatchDafny src/Dafny/Apps/apps.dfy.batch`

to do a high-level Dafny verification.  This is a useful
sanity check, but it is not the definitive verification for the system.

The definitive verification, which includes all of the assembly code that will be
executed, is run via:

  `./bin_tools/NuBuild/NuBuild.exe --no-cloudcache -j 3 IroncladApp src/Dafny/Apps/DafnyCCTest/Main.i.dfy`

to verify and build a very simple Ironclad App.  Try pointing it at other files in:
  `./src/Dafny/Apps/*/Main.i.dfy`
to build the other apps.

To build a version that actually boots, use `BootableApp` in place of `IroncladApp`.

To build a debug version that runs on Windows, use the `--windows flag` to NuBuild.  
This is most useful when accompanied by the `--useFramePointer` which enables more detailed profiling.

# Running

To run an Ironclad App, you'll need an AMD machine with SVM support and a TPM. Adjust
`boot/boot-cp.cmd` to point at the executable output by the `BootableApp` verb above,
and run `boot/boot-cp.cmd`, which will start a PXE boot server that your AMD machine
should be configured to connect to.

# Contributing

See the [CONTRIBUTING](../ironfleet/CONTRIBUTING.md) file for more details.

# Version History
- v0.1:   Initial code release on GitHub.
