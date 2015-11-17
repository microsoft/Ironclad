The real purpose of this project is to run its post-build event, which creates
parser.dll.  The build system, however, will first create a bogus parser.dll
with nothing of import in it.  The post-build event will then overwrite this
with the real parser.dll.

Ideally, we'd replace this with an actual F# project that would build
parser.dll directly.  However, we're currently using specific F# tooling
(it's checked into the repository), but non-specific (whatever the user has
on their machine) C# and msbuild tooling.  So this dance is to use the
specific F# binaries in the non-specific build environment.
