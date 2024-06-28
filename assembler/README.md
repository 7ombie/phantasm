This directory contains the four files that are required to use the assembler.
Three of the files form the pipeline (`lexer.js`, then `parser.js`, then
`compiler.js`), while `helpers.js` contains a few helper functions.

Everything outside this directory is used to document, test or license the code
within this directory.

The implementation is free of known bugs, but there are no tests, and it has not
been used extensively, so (easily fixed) oversights are bound to remain here and
there. If you report a bug, it will always be fixed before anything else.

While the code works, it needs extensive refactoring. Basically, when documenting
the language, I completely redid the terminology, so the language user uses terms
like *keyword*, *operator*, *directive*, *preamble* and *statement* differently
to the implementor. I need to reclassify the word tokens (keywords, mnemonics,
prefixes, qualifiers *et cetera*), including all of there classes and helper
functions, then rewrite all of the docstrings.

Some of the WASM extensions have been implemented (like Multiple Memories & Tables,
Threads & Atomics, Mutable Globals, Extended Constant Expressions *et cetera*) or
are partially supported (like Reference Types). Some features need implementing,
like SIMD and annotations, others will probably be implemented, like exception
handling, and others are probably inappropriate for a source language, like
GC.
