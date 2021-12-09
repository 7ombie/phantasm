The PHANTASM Web Assembler
==========================

PHANTASM is an assembler that allows you to author WebAssembly modules in a
nice, modern language, instead of repurposing the WebAssembly Text Format.

The name *PHANTASM* is an acronym derived from a description of the language
semantics: *Portable, Hardened, Asynchronous, Natively Typed, Abstract Stack Machine*.
The name is also a description of the WebAssembly Engine, which follows from
the fact that PHANTASM exposes the WebAssembly ISA directly, having no
semantics of its own.

## Project Status

The PHANTASM project is in its infancy, and everything available here is
provided purely as a preview (for those that have expressed an interest
in early adoption).

The language design is solid, and the initial implementation is fairly
comprehensive and free of known bugs. The documentation is also ready
enough that you could learn PHANTASM today. However, there is no DWARF
implementation or test suite, and no tooling, editor support *et cetera*.
There are also no users. It is just one guy, a grammar, an assembler, a
tutorial and a few wiki entries, at this stage.

Progress was steady for around six months, then I took a break from it
for a few months (I was generally burnt out, then got distracted learning
speedcubing). This pattern is pretty normal for me, though I usually
take shorter breaks (a few weeks is typical).

Ultimately, while I can only guess at how long things will take, I am
absolutely committed to this project long-term.

The current priorities are the DWARF implementation and the test suite.
After that, the focus will shift to tools and editor support. The last
big job will be a complete rewrite of the assembler. Developing the
documentation, polishing the code and adding newly standardized
proposals will be ongoing work.

TLDR: The first production version should be ready in a year or two,
very roughly.
