Modular Optimising Compilers
============================

This is an extension of the
[Hoopl](https://hackage.haskell.org/package/hoopl) compiler library
that supports the construction of optimising compilers in a modular
fashion. This extension is based on on Wouter Swierstra's
["Data types à la carte"](http://dx.doi.org/10.1017/S0956796808006758).

To demonstrate the library, we implement a compiler with constant
propagation, constant folding, dead code elimination, and copy
propagation.
