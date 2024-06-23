PHANTASM: The Portable, Hardened, Asynchronous, Natively Typed, Abstract Stack Machine
======================================================================================

**NOTICE**: This is a personal project that I've published for people who wanted to
take a look at it. I'm not sure what the future of the project is.

It was unmaintained for a few years (I got into Swift and Metal), but I recently began
working on it again, and have substantially improved the language (and implementation)
since. My plan is to implement a few more features (like SIMD), build out a small eco-
system (tools, syntax highlighting for popular editors *et cetera*), and to spend some
time using the assembler, then maybe do a rewrite in a year or so (who really knows).

--------------------------------------------------------------------------------------

PHANTASM is an assembler for WebAssembly. It allows you to author WebAssembly modules
in a convenient, modern language, instead of repurposing the WebAssembly Text Format.

The name *PHANTASM* is an acronym derived from a description of the language semantics:
*Portable, Hardened, Asynchronous, Natively Typed, Abstract Stack Machine*. The name is
also a description of the WebAssembly Engine, which follows from the fact that PHANTASM
exposes the WebAssembly ISA directly, having no semantics of its own, beyond a handful
of small conveniences.

See [The PHANTASM Crashcourse][0] or [the project wiki][1] for more information.

[0]: https://github.com/7ombie/phantasm/blob/main/docs/crashcourse.pdf
[1]: https://github.com/7ombie/phantasm/wiki
