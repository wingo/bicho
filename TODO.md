TODO
====

Fix license headers in all files to be latest GPLv3+ header, with
compressed FSF copyright dates for Guile bits, personal copyright for
Bicho changes.

Write "bicho compile", "bicho disassemble", "bicho optimize", "bicho
emulate" commands.

Write expander for bicho programs that wraps input code in letrec that
includes standard prelude.

Module commentaries for all files.

Make facility for exempting runtime primitives from inlining and/or
DCE before primcalls have been resolved (??).

Implement primcall resolution (?).

Error on any toplevel-ref that survives expansion.

Implement primcalls at run-time, for the partial evaluator.

Add ability to mark primitives as optimizable in some mathematical
way.

Add primcall to call instructions by name.

Allow primitives to be inlined.

Design debugging artifact.

Implement atmega328p assembler.

Implement static linker, which also should residualize a debugging artifact.

Implement tool to disassemble statically linked image, both program
and data part.

Implement emulator for some targets.

Figure out interrupt story -- when do we mask interrupts?  What can
interrupt handlers do?  How do we define them?  Are we sure that
our interrupt design works well with GC?

Import CPS2 backend from Guile when it is done.

Scheme parameters for target configuration?

Figure out interface to I/O registers.
