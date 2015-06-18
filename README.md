Bicho, a Scheme for microcontrollers
====================================

Bicho is a Scheme for those little devices in your life: arduinos and
other microcontrollers that have teensy-weensie heaps.

Feature goals
-------------

It's early days, but the feature list will probably look like this:

 * Native compilation, initially targetting the atmega328p (the chip
   in arduinos, 2KB SRAM and 32KB flash memory)

 * Mark/compact GC (about 12.5% memory overhead, 1 or 2 KB code
   overhead)

 * Flexible stack/heap division: you can recurse as much as your
   memory allows.  If the stack pointer reaches the heap pointer, GC
   happens to try to compact the heap.  Otherwise board will reset.

 * 13-bit fixnums (-2048 to +2047)

 * Vectors, strings, 8-bit chars, `#t`/`#f`/`()`, symbols, boxes,
   pairs, closures

 * Primitives for peeking and poking I/O registers

 * Expanded, optimized, and compiled from Guile Scheme, so you can use
   powerful macros and procedural abstractions, relying on partial
   evaluation, contification, closure optimization etc to produce good
   code

 * Implemented in Guile Scheme

Status
------

Only the GC is done, really.  We'll piggy-back on Guile's compiler so
mostly what's needed is the backend, the runtime, and a way to link
static binaries.  Not sure if it's possible to allow a bootloader to
be tacked on the front, otherwise these images would need a separate
piece of hardware to install on arduino devices.
