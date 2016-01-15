NuBuild for Makefiles
=====================

About
-----

**NuBuild for Makefiles** (also *nubuild-mkf*) is an experimental tool for
building projects that contain verifiable sources. It is an adaptation of the
[Ironfleet
NuBuild](<http://github.com/Microsoft/Ironclad/blob/master/ironfleet/README.md>)
sources (developed by [the MSR Ironclad
team](<http://research.microsoft.com/ironclad>)) for projects that declare their
build specification using makefiles.

While *nubuild-mkf* does not perform nearly as well as *NuBuild*, it is possible
to introduce *nubuild-mkf* as an auxiliary build system into an existing project
without disrupting or preempting the team’s preexisting workflow.

*nubuild-mkf* was started with the needs the [F\*](<http://www.fstar-lang.org/>)
and [miTLS](<http://www.mitls.org/>) teams in mind. Currently, only *F\**
verification is supported. Support for additional tools and features will be
added as needs change.

License
-------

*NuBuild for Makefiles* is licensed under the **MIT license** included in the
[LICENSE](<./LICENSE>) file.

Setup
-----

TBD

Known Issues
------------

-   Distributed build is untested and unlikely to work.

-   Whitespace differences are likely to reduce caching effectiveness.

-   Linux support is untested.

-   Cache cannot be safely shared between parallel invocations of `NuBuild.exe`
    (e.g. incompatible with `make -j`).

-   Integration with CI tools is not yet implemented.

Code Layout
-----------

See the [CODE](<./CODE.md>) file for more details on the various files in the
repository.

Contributing
------------

See the [CONTRIBUTING](<./CONTRIBUTING.md>) file for more details.

Version History
---------------

-   v0.1: Initial code release, based on sources from the IronFleet project
