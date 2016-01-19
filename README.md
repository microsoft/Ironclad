About
=====

This directory contains an experimental tool for verifying and building the
Ironclad Apps and IronFleet code. Additional support has been added for F\*
verification.

See http://research.microsoft.com/ironclad for more details on these projects.

License
=======

NuBuild is licensed under the MIT license included in the [LICENSE](<./LICENSE>)
file.

Setup
=====

1.  Clone NuBuild into the root of your project directory. It must be cloned
    into a directory named `.nubuild` at the root of your project (referred to
    hereafter as `$PROJECT`).

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
git clone -b nubuild --single-branch https://github.com/Microsoft/Ironclad .nubuild
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

1.  Alternatively, you can clone NuBuild into any directory and use a symbolic
    link to point `$PROJECT/.nubuild` to the cloned repository.

2.  Build NuBuild. The Visual Studio solution is located at
    `$PROJECT/.nubuild/src/NuBuild.sln`.

3.  Customize your `$PROJECT/.nubuild/config.json` file. You can find a sample
    copy of the file at `$PROJECT/.nubuild/doc/examples/config.json`.

4.  Tools invoked by NuBuild must reside within the `$PROJECT` directory. For
    example, if you're using the *FStarVerify* verb, you're likely to need to
    either clone or link the F\* project directory into `$PROJECT`. The default
    path to find F\* is `$PROJECT/.fstar/bin/fstar.exe` but this can be
    customized in your `$PROJECT/.nubuild/config.json` file.

Known Issues
------------

-   Distributed build has not been regression tested (may no longer work).

-   Whitespace differences across developers are likely to reduce caching
    effectiveness (use `--enforce-whitespace` option to have NuBuild reject
    files with problems).

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
