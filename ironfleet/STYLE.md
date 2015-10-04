# Style Guide

These are the conventions we aspire to follow.  Note that not all of the current code has
been brought into line yet.

- Use spaces, not tabs.  4 spaces per "tab"
- Files should use Windows-style newlines (CRLF)
- We sort functions/methods within a file topologically, so that everything method M depends on should be above M in the file
- We use the lemma keyword to indicate ghost methods used for proof purposes, and we prefix the method's name with "lemma_"
- In the implementation, given a concrete type, e.g., `CPacket`, we define the following:
  + `function AbstractifyCPacket(pkt:CPacket) : Packet`
  + Which in turn requires:
      `predicate CPacketIsAbstractable(pkt:CPacket)`
    which should be the minimum necessary to call `AbstractifyCPacket`
  + We also define:
      `predicate CPacketIsValid(pkt:CPacket)`
    which should imply `CPacketIsAbstractable` and include any additional requirements necessary 
    at the implementation level (e.g., that it fits with 2^64 bytes)
- For method, lemma, class, and datatype names, we use camel case
  + Note that acronyms only capitalize the first letter (e.g., `TpmIsValid` instead of `TPMIsValid`)
  + Method names are capitalized
  + Lemmas begin with "lemma_"
- Variables:
  + Initially lower case
  + Underscores instead of camel case
- Braces:
  + If/else open on same line
  + Calc open on same line
    - Operator or tab, then hint
  + While loops are matched
  + Methods, predicates, functions: matched unless single line
- Use `predicate` instead of `function foo():bool`

