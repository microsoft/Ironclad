About
=====

This directory contains an experimental tool for verifying and building the
Ironclad Apps and IronFleet code.

See http://research.microsoft.com/ironclad for more details on these projects.

License
=======

NuBuild is licensed under the MIT license included in the [LICENSE](<./LICENSE>)
file.

Setup
=====

TBD

Known Issues
------------

-   Distributed build has not been regression tested (may no longer work).

-   Whitespace differences are likely to reduce caching effectiveness.

-   Linux support is untested.

-   The local (on-disk) cache cannot be safely shared between parallel
    invocations of `NuBuild.exe` (e.g. NuBuild is incompatible with `make -j`).

-   Integration with CI tools is not yet implemented.

Code Layout
===========

See the [CODE](<./CODE.md>) file for more details on the various files in the
repository.

Contributing
============

See the [CONTRIBUTING](<./CONTRIBUTING.md>) file for more details.

Version History
===============

-   v0.1: Initial code release, based on sources from the IronFleet project

-   v0.2: Added support for F\* verification.
