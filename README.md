# leanInk-sphinx-test

This is a small Sphinx project with Lean 4 code, for testing with Alectryon.

The Lean 4 file being tested is `LeanSource/ModularArithmeticTheory.lean`.  See the original Lean 3 file [here](https://hrmacbeth.github.io/math2001/03_Parity_and_Divisibility.html#modular-arithmetic-theory).

Running
```
alectryon LeanSource/ModularArithmeticTheory.lean --lake lakefile.lean
```
generates a single Alectryon-enabled HTML page for the file `LeanSource/ModularArithmeticTheory.lean`.

It is easy to convert back and forth between a Lean4 file with comments in RST format and an RST file with code snippets with `.. lean4::` designation.  The RST file `source/ParityDivision/ModularArithmeticTheory-lean4.inc` has been obtained from `LeanSource/ModularArithmetic.lean` using Alectryon's utility for this (up to a few cosmetic changes).

The Alectryon directives `.. lean4::` are [not currently understood by Sphinx](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/command-line.20arguments.20for.20Alectryon.20Sphinx.20extension).  Sphinx can display non-interactive code blocks with the `.. code-block::` designation.  The file `source/ParityDivision/ModularArithmeticTheory-code-block.inc` has been obtained from `source/ParityDivision/ModularArithmeticTheory-lean4.inc` by changing all occurrences of `.. lean4::` to `.. code-block::`.  This is enough to give a non-Alectryon-enabled preview of how the project should look.  Install Sphinx and then run
```
make html
```
