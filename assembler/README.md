This directory contains the four files that are required to use the assembler.
Three of the files form the pipeline (`lexer.js`, then `parser.js`, then
`compiler.js`), while `helpers.js` contains a few helper functions.

Everything outside this directory is used to document, test or license the code
within this directory.

The implementation is free of known bugs, but there are no tests, and it has not
been used extensively, so (easily fixed) oversights are bound to remain here and
there. If you report a bug, it will always be fixed before anything else.

Some of the WASM extensions have been implemented (like Multiple Memories & Tables,
Threads & Atomics, Mutable Globals, Extended Constant Expressions *et cetera*) or
are partially supported (like Reference Types). Some features need implementing,
like SIMD and annotations, others will probably be implemented, like exception
handling, and others are probably inappropriate for a source language, like
GC.

While the code works, it needs extensive refactoring. Basically, when documenting
the language, I completely redid the terminology, so the language user uses terms
like *keyword*, *operator*, *directive*, *preamble* and *statement* differently
to the implementor. I need to reclassify the word tokens (keywords, mnemonics,
prefixes, qualifiers *et cetera*), make them all subclasses of `Word`, then
unify the corresponding helper functions (`acceptKeyword`, `acceptQualifier`
*et cetera* should all just use `acceptWord`). Finally, I need to rewrite
all of the docstrings.

The refactoring described above would be a lot easier with unit tests, so I would
like to add those first. That's quite a lot of work, which begs the question of
whether to just do a rewrite, possibly using something more appropriate than
JavaScript (probably Swift, maybe Odin or Zig).

The current plan is to add more features to the current codebase, use the project
for a couple of games, and build out the ecosystem a bit (like supporting popular
editors, providing tutorials *et cetera*). Then, when the design is effectively
complete (WebAssembly can only really evolve so far), I will then consider
reimplementing the language professionally.
